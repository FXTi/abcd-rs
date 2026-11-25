use abcd_file_sys as sys;

use crate::error::Error;
use crate::file::ABSENT;
use crate::types::TypeId;

/// Line number entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LineEntry {
    /// Instruction index in the method's bytecode sequence.
    pub index: u32,
    pub line: u32,
}

/// Column number entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ColumnEntry {
    /// Instruction index in the method's bytecode sequence.
    pub index: u32,
    pub column: u32,
}

/// Local variable debug info.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LocalVarInfo {
    pub name: crate::StringId,
    pub type_name: crate::StringId,
    pub type_signature: crate::StringId,
    pub reg_number: i32,
    /// Instruction index where this variable's scope starts.
    pub start: u32,
    /// Instruction index where this variable's scope ends.
    pub end: u32,
}

/// Parameter debug info.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ParamInfo {
    pub name: crate::StringId,
    pub signature: crate::StringId,
}

// ---------------------------------------------------------------------------
// Pure-Rust bounded DWARF / LineNumberProgram decoder (D2)
// ---------------------------------------------------------------------------

struct ProtoGuard(*mut sys::AbcProtoAccessor);

impl Drop for ProtoGuard {
    fn drop(&mut self) {
        if !self.0.is_null() {
            // SAFETY: `self.0` was returned by `abc_proto_open` and is non-null.
            unsafe { sys::abc_proto_close(self.0) };
        }
    }
}

#[inline]
pub(crate) fn read_sleb128_slice(sp: &mut &[u8]) -> Option<i32> {
    let mut result = 0u32;
    for i in 0..5usize {
        let &b = sp.get(i)?;
        if i == 4 {
            if (b & 0x80) != 0 {
                return None;
            }
            let top = b & 0x78;
            if top != 0 && top != 0x78 {
                return None;
            }
        }
        result |= u32::from(b & 0x7F) << (7 * i);
        if (b & 0x80) == 0 {
            let shift = 7 * (i + 1);
            if shift < 32 && (b & 0x40) != 0 {
                result |= !0u32 << shift;
            }
            *sp = &sp[i + 1..];
            return Some(result as i32);
        }
    }
    None
}

fn primitive_type_signature(type_id_raw: u8) -> Option<&'static str> {
    match TypeId::try_from(type_id_raw).ok()? {
        TypeId::Void => Some("V"),
        TypeId::U1 => Some("Z"),
        TypeId::I8 => Some("B"),
        TypeId::U8 => Some("H"),
        TypeId::I16 => Some("S"),
        TypeId::U16 => Some("C"),
        TypeId::I32 => Some("I"),
        TypeId::U32 => Some("U"),
        TypeId::I64 => Some("J"),
        TypeId::U64 => Some("Q"),
        TypeId::F32 => Some("F"),
        TypeId::F64 => Some("D"),
        TypeId::Reference => Some("L"),
        TypeId::Tagged => Some("A"),
    }
}

/// Decoded debug `StringData` view (`GetStringData` + MUTF-8 normalization).
pub(crate) enum RawDebugStr<'a> {
    Empty,
    /// Static descriptor literal (e.g. primitive parameter type signature).
    Static(&'static str),
    /// Valid UTF-8 slice borrowed directly from `file_bytes[start..start + len]`.
    Borrowed(&'a str, usize, usize),
    /// Decoded MUTF-8 (embedded NUL / 6-byte CESU-8 astral) or lossy fallback.
    Owned(String),
}

pub(crate) fn decode_debug_cstr(file_bytes: &[u8], offset: u32) -> Result<RawDebugStr<'_>, Error> {
    if offset <= 60 || (offset as usize) >= file_bytes.len() {
        return Err(Error::DebugInfoExtraction);
    }
    let mut sp = &file_bytes[offset as usize..];
    let before = sp.len();
    crate::file::read_uleb128_slice(&mut sp).ok_or(Error::DebugInfoExtraction)?;
    let prefix_len = before - sp.len();
    let nul_pos = sp
        .iter()
        .position(|&b| b == 0)
        .ok_or(Error::DebugInfoExtraction)?;
    if nul_pos == 0 {
        return Ok(RawDebugStr::Empty);
    }
    let raw = &sp[..nul_pos];
    if let Ok(s) = std::str::from_utf8(raw) {
        return Ok(RawDebugStr::Borrowed(
            s,
            offset as usize + prefix_len,
            nul_pos,
        ));
    }
    if let Some(decoded) = crate::string_pool::mutf8_decode_utf8(raw) {
        return Ok(RawDebugStr::Owned(decoded));
    }
    Ok(RawDebugStr::Owned(
        String::from_utf8_lossy(raw).into_owned(),
    ))
}

pub(crate) trait DebugSink {
    fn set_source_file(&mut self, s: RawDebugStr<'_>);
    fn set_source_code(&mut self, s: RawDebugStr<'_>);
    fn push_line(&mut self, pc_offset: u32, line: u32);
    fn push_column(&mut self, pc_offset: u32, column: u32);
    fn start_local(
        &mut self,
        reg_number: i32,
        name: RawDebugStr<'_>,
        type_name: RawDebugStr<'_>,
        type_sig: Option<RawDebugStr<'_>>,
        pc_offset: u32,
    );
    fn end_local(&mut self, reg_number: i32, pc_offset: u32) -> Result<(), Error>;
    fn finish_locals(&mut self, final_pc_offset: u32);
    fn push_param(&mut self, name: RawDebugStr<'_>, sig: RawDebugStr<'_>);
}

pub(crate) struct ModelDebugSink<'s> {
    strings: &'s mut crate::StringPool,
    source_file: Option<crate::StringId>,
    source_code: Option<crate::StringId>,
    line_table: Vec<LineEntry>,
    column_table: Vec<ColumnEntry>,
    local_vars: Vec<LocalVarInfo>,
    params: Vec<ParamInfo>,
}

impl<'s> ModelDebugSink<'s> {
    pub(crate) fn new(strings: &'s mut crate::StringPool) -> Self {
        Self {
            strings,
            source_file: None,
            source_code: None,
            line_table: Vec::new(),
            column_table: Vec::new(),
            local_vars: Vec::new(),
            params: Vec::new(),
        }
    }

    #[inline]
    fn intern_required(&mut self, s: RawDebugStr<'_>) -> crate::StringId {
        match s {
            RawDebugStr::Empty => self.strings.get_or_intern(""),
            RawDebugStr::Static(text) | RawDebugStr::Borrowed(text, _, _) => {
                self.strings.get_or_intern(text)
            }
            RawDebugStr::Owned(text) => self.strings.get_or_intern(&text),
        }
    }

    #[inline]
    fn intern_optional(&mut self, s: RawDebugStr<'_>) -> Option<crate::StringId> {
        match s {
            RawDebugStr::Empty => None,
            RawDebugStr::Static(text) | RawDebugStr::Borrowed(text, _, _) => {
                Some(self.strings.get_or_intern(text))
            }
            RawDebugStr::Owned(text) => {
                (!text.is_empty()).then(|| self.strings.get_or_intern(&text))
            }
        }
    }

    pub(crate) fn into_debug_info(mut self, byte_offsets: &[u32]) -> crate::MethodDebugInfo {
        let to_index = |off: u32| -> u32 {
            if byte_offsets.is_empty() {
                off
            } else {
                byte_offsets.binary_search(&off).unwrap_or_else(|i| i) as u32
            }
        };
        for entry in &mut self.line_table {
            entry.index = to_index(entry.index);
        }
        for entry in &mut self.column_table {
            entry.index = to_index(entry.index);
        }
        for var in &mut self.local_vars {
            var.start = to_index(var.start);
            var.end = to_index(var.end);
        }
        crate::MethodDebugInfo {
            source_file: self.source_file,
            source_code: self.source_code,
            line_table: self.line_table,
            column_table: self.column_table,
            local_vars: self.local_vars,
            params: self.params,
        }
    }
}

impl DebugSink for ModelDebugSink<'_> {
    fn set_source_file(&mut self, s: RawDebugStr<'_>) {
        self.source_file = self.intern_optional(s);
    }

    fn set_source_code(&mut self, s: RawDebugStr<'_>) {
        self.source_code = self.intern_optional(s);
    }

    fn push_line(&mut self, pc_offset: u32, line: u32) {
        self.line_table.push(LineEntry {
            index: pc_offset,
            line,
        });
    }

    fn push_column(&mut self, pc_offset: u32, column: u32) {
        self.column_table.push(ColumnEntry {
            index: pc_offset,
            column,
        });
    }

    fn start_local(
        &mut self,
        reg_number: i32,
        name: RawDebugStr<'_>,
        type_name: RawDebugStr<'_>,
        type_sig: Option<RawDebugStr<'_>>,
        pc_offset: u32,
    ) {
        let name_sid = self.intern_required(name);
        let type_sid = self.intern_required(type_name);
        let sig_sid = match type_sig {
            Some(sig) => self.intern_required(sig),
            None => type_sid,
        };
        self.local_vars.push(LocalVarInfo {
            name: name_sid,
            type_name: type_sid,
            type_signature: sig_sid,
            reg_number,
            start: pc_offset,
            end: 0,
        });
    }

    fn end_local(&mut self, reg_number: i32, pc_offset: u32) -> Result<(), Error> {
        let idx = self
            .local_vars
            .iter()
            .rposition(|v| v.reg_number == reg_number)
            .ok_or(Error::DebugInfoExtraction)?;
        self.local_vars[idx].end = pc_offset;
        Ok(())
    }

    fn finish_locals(&mut self, final_pc_offset: u32) {
        for var in &mut self.local_vars {
            if var.end == 0 {
                var.end = final_pc_offset;
            }
        }
    }

    fn push_param(&mut self, name: RawDebugStr<'_>, sig: RawDebugStr<'_>) {
        let name_sid = self.intern_required(name);
        let sig_sid = self.intern_required(sig);
        self.params.push(ParamInfo {
            name: name_sid,
            signature: sig_sid,
        });
    }
}

/// Decode a single `DebugInfoItem` + its `LineNumberProgramItem` directly from
/// `file_bytes` with exact parity against upstream `DebugInfoExtractor` and
/// zero C++ `DebugInfoExtractor` heap / `LOG(FATAL)` exposure (`D2`).
pub(crate) fn decode_method_debug_item<S: DebugSink>(
    f: *const sys::AbcFileHandle,
    file_bytes: &[u8],
    class_id: u32,
    class_source_file_off: u32,
    mr: *mut sys::AbcMethodAccessor,
    debug_off: u32,
    sink: &mut S,
) -> Result<(), Error> {
    if debug_off <= 60 || (debug_off as usize) >= file_bytes.len() {
        return Err(Error::DebugInfoExtraction);
    }
    let mut sp = &file_bytes[debug_off as usize..];
    let line_start = crate::file::read_uleb128_slice(&mut sp).ok_or(Error::DebugInfoExtraction)?;
    let num_params = crate::file::read_uleb128_slice(&mut sp).ok_or(Error::DebugInfoExtraction)?;

    // Mirror DebugInfoExtractor::ExtractMethodParams (debug_info_extractor.cpp:176-232).
    // SAFETY: `mr` and `f` are live, valid handles owned by the caller.
    let has_valid_proto = unsafe { sys::abc_method_has_valid_proto(mr) } != 0;
    let pr_guard = if has_valid_proto && num_params > 0 {
        // SAFETY: `mr` is a valid `AbcMethodAccessor`.
        let proto_id = unsafe { sys::abc_method_get_proto_id(mr) };
        if proto_id == ABSENT {
            return Err(Error::DebugInfoExtraction);
        }
        // SAFETY: `f` is a valid `AbcFileHandle`.
        let p = unsafe { sys::abc_proto_open(f, proto_id) };
        if p.is_null() {
            return Err(Error::DebugInfoExtraction);
        }
        ProtoGuard(p)
    } else {
        ProtoGuard(std::ptr::null_mut())
    };
    let pr = pr_guard.0;

    if num_params > 0 {
        // SAFETY: `mr` is a valid `AbcMethodAccessor`.
        let is_static =
            (unsafe { sys::abc_method_access_flags(mr) } & sys::AbcAccessFlags_ABC_ACC_STATIC) != 0;
        let proto_num_args = if pr.is_null() {
            0
        } else {
            // SAFETY: `pr` is non-null and valid.
            unsafe { sys::abc_proto_num_args(pr) }
        };
        let proto_ref_num = if pr.is_null() {
            0
        } else {
            // SAFETY: `pr` is non-null and valid.
            unsafe { sys::abc_proto_get_ref_num(pr) }
        };
        let mut idx_arg = 0u32;
        let mut idx_ref = if !pr.is_null()
            // SAFETY: `pr` is non-null and valid.
            && unsafe { sys::abc_proto_get_return_type(pr) } == TypeId::Reference as u8
        {
            1u32
        } else {
            0u32
        };
        let mut first_param = true;

        for _ in 0..num_params {
            let param_id =
                crate::file::read_uleb128_slice(&mut sp).ok_or(Error::DebugInfoExtraction)?;
            if param_id > 60 && !has_valid_proto {
                let name = decode_debug_cstr(file_bytes, param_id)?;
                sink.push_param(name, RawDebugStr::Static("A"));
                continue;
            }
            if param_id <= 60 {
                first_param = false;
                sink.push_param(RawDebugStr::Empty, RawDebugStr::Empty);
                continue;
            }
            let name = decode_debug_cstr(file_bytes, param_id)?;
            if first_param && !is_static {
                let sig = decode_debug_cstr(file_bytes, class_id)?;
                sink.push_param(name, sig);
            } else {
                if idx_arg >= proto_num_args {
                    return Err(Error::DebugInfoExtraction);
                }
                // SAFETY: `pr` is non-null when `proto_num_args > 0` (`idx_arg < proto_num_args`).
                let arg_tid = unsafe { sys::abc_proto_get_arg_type(pr, idx_arg) };
                idx_arg += 1;
                if arg_tid == TypeId::Reference as u8 {
                    if idx_ref >= proto_ref_num {
                        return Err(Error::DebugInfoExtraction);
                    }
                    // SAFETY: `pr` is non-null and `idx_ref < proto_ref_num`.
                    let ref_off = unsafe { sys::abc_proto_get_reference_type(pr, idx_ref) };
                    idx_ref += 1;
                    let sig = decode_debug_cstr(file_bytes, ref_off)?;
                    sink.push_param(name, sig);
                } else {
                    let sig =
                        primitive_type_signature(arg_tid).ok_or(Error::DebugInfoExtraction)?;
                    sink.push_param(name, RawDebugStr::Static(sig));
                }
            }
            first_param = false;
        }
    }

    let cp_size =
        crate::file::read_uleb128_slice(&mut sp).ok_or(Error::DebugInfoExtraction)? as usize;
    if sp.len() < cp_size {
        return Err(Error::DebugInfoExtraction);
    }
    let mut cp = &sp[..cp_size];
    sp = &sp[cp_size..];
    let lnp_idx = crate::file::read_uleb128_slice(&mut sp).ok_or(Error::DebugInfoExtraction)?;

    // Header layout: num_lnps at 36..40, lnp_idx_off at 40..44.
    let num_lnps = u32::from_le_bytes(
        file_bytes
            .get(36..40)
            .and_then(|s| s.try_into().ok())
            .ok_or(Error::DebugInfoExtraction)?,
    );
    let lnp_idx_off = u32::from_le_bytes(
        file_bytes
            .get(40..44)
            .and_then(|s| s.try_into().ok())
            .ok_or(Error::DebugInfoExtraction)?,
    );
    if lnp_idx >= num_lnps {
        return Err(Error::DebugInfoExtraction);
    }
    let entry_off = lnp_idx
        .checked_mul(4)
        .and_then(|n| lnp_idx_off.checked_add(n))
        .and_then(|o| usize::try_from(o).ok())
        .ok_or(Error::DebugInfoExtraction)?;
    let lnp_off = u32::from_le_bytes(
        file_bytes
            .get(entry_off..entry_off + 4)
            .and_then(|s| s.try_into().ok())
            .ok_or(Error::DebugInfoExtraction)?,
    );
    if lnp_off <= 60 || (lnp_off as usize) >= file_bytes.len() {
        return Err(Error::DebugInfoExtraction);
    }

    // Mirror LineNumberProgramProcessor::Process (line_number_program.h).
    let mut prog = &file_bytes[lnp_off as usize..];
    let mut address = 0u32;
    let mut line = line_start;
    let mut file_off = if class_source_file_off == ABSENT {
        0
    } else {
        class_source_file_off
    };
    let mut source_code_off = 0u32;

    // ProcessBegin() unconditionally emits `{ offset: 0, line: line_start }`.
    sink.push_line(0, line_start);

    loop {
        let &opcode = prog.first().ok_or(Error::DebugInfoExtraction)?;
        prog = &prog[1..];
        let mut res = false;
        match opcode {
            0x00 => break, // END_SEQUENCE
            0x01 => {
                // ADVANCE_PC
                let pc_diff =
                    crate::file::read_uleb128_slice(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                address = address.wrapping_add(pc_diff);
                res = true;
            }
            0x02 => {
                // ADVANCE_LINE
                let line_diff = read_sleb128_slice(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                line = line.wrapping_add(line_diff as u32);
                res = true;
            }
            0x03 => {
                // START_LOCAL
                let reg = read_sleb128_slice(&mut prog).ok_or(Error::DebugInfoExtraction)?;
                let name_id =
                    crate::file::read_uleb128_slice(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                let type_id =
                    crate::file::read_uleb128_slice(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                let name = decode_debug_cstr(file_bytes, name_id)?;
                let type_name = decode_debug_cstr(file_bytes, type_id)?;
                sink.start_local(reg, name, type_name, None, address);
                res = true;
            }
            0x04 => {
                // START_LOCAL_EXTENDED
                let reg = read_sleb128_slice(&mut prog).ok_or(Error::DebugInfoExtraction)?;
                let name_id =
                    crate::file::read_uleb128_slice(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                let type_id =
                    crate::file::read_uleb128_slice(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                let sig_id =
                    crate::file::read_uleb128_slice(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                let name = decode_debug_cstr(file_bytes, name_id)?;
                let type_name = decode_debug_cstr(file_bytes, type_id)?;
                let sig_name = decode_debug_cstr(file_bytes, sig_id)?;
                sink.start_local(reg, name, type_name, Some(sig_name), address);
                res = true;
            }
            0x05 => {
                // END_LOCAL
                let reg = read_sleb128_slice(&mut prog).ok_or(Error::DebugInfoExtraction)?;
                sink.end_local(reg, address)?;
                res = true;
            }
            0x06 => {
                // RESTART_LOCAL (unsupported fatal in vendor)
                return Err(Error::DebugInfoExtraction);
            }
            0x07 | 0x08 => {
                // SET_PROLOGUE_END / SET_EPILOGUE_BEGIN: upstream handler leaves
                // `res = false`, terminating the loop immediately after!
            }
            0x09 => {
                // SET_FILE
                file_off =
                    crate::file::read_uleb128_slice(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                res = true;
            }
            0x0a => {
                // SET_SOURCE_CODE
                source_code_off =
                    crate::file::read_uleb128_slice(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                res = true;
            }
            0x0b => {
                // SET_COLUMN
                let column =
                    crate::file::read_uleb128_slice(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                sink.push_column(address, column);
                res = true;
            }
            _ => {
                // Special opcode (>= 0x0c): LINE_BASE = -4, LINE_RANGE = 15.
                let adjust = i32::from(opcode - 0x0c);
                let pc_off = (adjust / 15) as u32;
                let line_off = (adjust % 15) - 4;
                address = address.wrapping_add(pc_off);
                line = line.wrapping_add(line_off as u32);
                sink.push_line(address, line);
                res = true;
            }
        }
        if !res {
            break;
        }
    }

    sink.finish_locals(address);

    // N55: GetFile() reads GetStringData(file_), throwing if !file_.IsValid().
    let sf = decode_debug_cstr(file_bytes, file_off)?;
    sink.set_source_file(sf);
    if source_code_off > 60 {
        let sc = decode_debug_cstr(file_bytes, source_code_off)?;
        sink.set_source_code(sc);
    }
    Ok(())
}
