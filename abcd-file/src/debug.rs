//! Pure Safe Rust bounded DWARF / `LineNumberProgram` debug decoder (`D2`, `#49`).

#![forbid(unsafe_code)]

use abcd_file_sys as sys;

use crate::error::Error;
use crate::file::{AbcReader, RawMethod, read_sleb128_i32, read_uleb128};
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
    /// Valid UTF-8 slice borrowed directly from `reader.bytes()`.
    Borrowed(&'a str),
    /// Decoded MUTF-8 (embedded NUL / 6-byte CESU-8 astral) or lossy fallback.
    Owned(String),
}

pub(crate) fn decode_debug_cstr<'a>(
    reader: &AbcReader<'a>,
    offset: u32,
) -> Result<RawDebugStr<'a>, Error> {
    let raw = reader
        .raw_cstr_at(offset)
        .ok_or(Error::DebugInfoExtraction)?;
    if raw.is_empty() {
        return Ok(RawDebugStr::Empty);
    }
    if let Ok(s) = std::str::from_utf8(raw) {
        return Ok(RawDebugStr::Borrowed(s));
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
            RawDebugStr::Static(text) | RawDebugStr::Borrowed(text) => {
                self.strings.get_or_intern(text)
            }
            RawDebugStr::Owned(text) => self.strings.get_or_intern(&text),
        }
    }

    #[inline]
    fn intern_optional(&mut self, s: RawDebugStr<'_>) -> Option<crate::StringId> {
        match s {
            RawDebugStr::Empty => None,
            RawDebugStr::Static(text) | RawDebugStr::Borrowed(text) => {
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
/// `reader` with exact parity against upstream `DebugInfoExtractor` and zero
/// C++ FFI handles (`D2`, `#49`).
pub(crate) fn decode_method_debug_item<S: DebugSink>(
    reader: &AbcReader<'_>,
    class_id: u32,
    class_source_file_off: Option<u32>,
    method: &RawMethod,
    code_size: u32,
    debug_off: u32,
    sink: &mut S,
) -> Result<(), Error> {
    let mut sp = reader
        .get_span(debug_off)
        .ok_or(Error::DebugInfoExtraction)?;
    let line_start = read_uleb128(&mut sp).ok_or(Error::DebugInfoExtraction)?;
    let num_params = read_uleb128(&mut sp).ok_or(Error::DebugInfoExtraction)?;
    let header_size = reader.header_size();

    // Mirror DebugInfoExtractor::ExtractMethodParams (debug_info_extractor.cpp:176-232).
    let has_valid_proto = method.proto_idx != u16::MAX;
    let proto_opt = if has_valid_proto && num_params > 0 {
        let proto_off = reader
            .method_proto_off(method)
            .ok_or(Error::DebugInfoExtraction)?;
        Some(
            reader
                .open_proto(proto_off)
                .ok_or(Error::DebugInfoExtraction)?,
        )
    } else {
        None
    };

    if num_params > 0 {
        let is_static = (method.access_flags & sys::AbcAccessFlags_ABC_ACC_STATIC) != 0;
        let proto_num_args = proto_opt.as_ref().map_or(0, |p| p.num_args() as u32);
        let proto_ref_num = proto_opt
            .as_ref()
            .map_or(0, |p| (p.ref_types_sp.len() / 2) as u32);
        let mut idx_arg = 0u32;
        let mut idx_ref = if proto_opt
            .as_ref()
            .is_some_and(|p| p.return_type_raw() == TypeId::Reference as u8)
        {
            1u32
        } else {
            0u32
        };
        let mut first_param = true;

        for _ in 0..num_params {
            let param_id = read_uleb128(&mut sp).ok_or(Error::DebugInfoExtraction)?;
            if param_id > header_size && !has_valid_proto {
                let name = decode_debug_cstr(reader, param_id)?;
                sink.push_param(name, RawDebugStr::Static("A"));
                continue;
            }
            if param_id <= header_size {
                first_param = false;
                sink.push_param(RawDebugStr::Empty, RawDebugStr::Empty);
                continue;
            }
            let name = decode_debug_cstr(reader, param_id)?;
            if first_param && !is_static {
                let sig = decode_debug_cstr(reader, class_id)?;
                sink.push_param(name, sig);
            } else {
                if idx_arg >= proto_num_args {
                    return Err(Error::DebugInfoExtraction);
                }
                let Some(ref proto) = proto_opt else {
                    return Err(Error::DebugInfoExtraction);
                };
                let arg_tid = proto.arg_type_raw(idx_arg as usize);
                idx_arg += 1;
                if arg_tid == TypeId::Reference as u8 {
                    if idx_ref >= proto_ref_num {
                        return Err(Error::DebugInfoExtraction);
                    }
                    let ref_off = proto
                        .reference_type_off(reader, idx_ref as usize)
                        .ok_or(Error::DebugInfoExtraction)?;
                    idx_ref += 1;
                    let sig = decode_debug_cstr(reader, ref_off)?;
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

    let cp_size = read_uleb128(&mut sp).ok_or(Error::DebugInfoExtraction)? as usize;
    if sp.len() < cp_size {
        return Err(Error::DebugInfoExtraction);
    }
    let mut cp = &sp[..cp_size];
    sp = &sp[cp_size..];
    let lnp_idx = read_uleb128(&mut sp).ok_or(Error::DebugInfoExtraction)?;

    let lnp_off = reader
        .lnp_off_by_idx(lnp_idx)
        .ok_or(Error::DebugInfoExtraction)?;
    let mut prog = reader.get_span(lnp_off).ok_or(Error::DebugInfoExtraction)?;

    // Mirror LineNumberProgramProcessor::Process (line_number_program.h).
    let mut address = 0u32;
    let mut line = line_start;
    let mut file_off = class_source_file_off.unwrap_or(0);
    let mut source_code_off = 0u32;

    // ProcessBegin() unconditionally emits `{ offset: 0, line: line_start }`.
    let max_rows = (code_size as usize).saturating_mul(4).max(1_000_000);
    let mut emitted_rows = 1usize;
    let check_row_cap = |rows: &mut usize| -> Result<(), Error> {
        *rows = rows.saturating_add(1);
        if *rows > max_rows {
            return Err(Error::Malformed {
                field: "line_number_program",
                context: format!(
                    "method debug info at {debug_off:#x} exceeded LNP row cap ({max_rows})"
                ),
            });
        }
        Ok(())
    };
    sink.push_line(0, line_start);

    loop {
        let &opcode = prog.first().ok_or(Error::DebugInfoExtraction)?;
        prog = &prog[1..];
        let mut res = false;
        match opcode {
            0x00 => break, // END_SEQUENCE
            0x01 => {
                // ADVANCE_PC
                let pc_diff = read_uleb128(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                address = address.wrapping_add(pc_diff);
                res = true;
            }
            0x02 => {
                // ADVANCE_LINE
                let line_diff = read_sleb128_i32(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                line = line.wrapping_add(line_diff as u32);
                res = true;
            }
            0x03 => {
                // START_LOCAL
                check_row_cap(&mut emitted_rows)?;
                let reg = read_sleb128_i32(&mut prog).ok_or(Error::DebugInfoExtraction)?;
                let name_id = read_uleb128(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                let type_id = read_uleb128(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                let name = decode_debug_cstr(reader, name_id)?;
                let type_name = decode_debug_cstr(reader, type_id)?;
                sink.start_local(reg, name, type_name, None, address);
                res = true;
            }
            0x04 => {
                // START_LOCAL_EXTENDED
                check_row_cap(&mut emitted_rows)?;
                let reg = read_sleb128_i32(&mut prog).ok_or(Error::DebugInfoExtraction)?;
                let name_id = read_uleb128(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                let type_id = read_uleb128(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                let sig_id = read_uleb128(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                let name = decode_debug_cstr(reader, name_id)?;
                let type_name = decode_debug_cstr(reader, type_id)?;
                let sig_name = decode_debug_cstr(reader, sig_id)?;
                sink.start_local(reg, name, type_name, Some(sig_name), address);
                res = true;
            }
            0x05 => {
                // END_LOCAL
                let reg = read_sleb128_i32(&mut prog).ok_or(Error::DebugInfoExtraction)?;
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
                file_off = read_uleb128(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                res = true;
            }
            0x0a => {
                // SET_SOURCE_CODE
                source_code_off = read_uleb128(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                res = true;
            }
            0x0b => {
                // SET_COLUMN
                check_row_cap(&mut emitted_rows)?;
                let column = read_uleb128(&mut cp).ok_or(Error::DebugInfoExtraction)?;
                sink.push_column(address, column);
                res = true;
            }
            _ => {
                // Special opcode (>= 0x0c): LINE_BASE = -4, LINE_RANGE = 15.
                check_row_cap(&mut emitted_rows)?;
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
    let sf = decode_debug_cstr(reader, file_off)?;
    sink.set_source_file(sf);
    if source_code_off > header_size {
        let sc = decode_debug_cstr(reader, source_code_off)?;
        sink.set_source_code(sc);
    }
    Ok(())
}
