//! ArkCompiler ISA definitions, generated via arkcompiler's Ruby pipeline + C++ bridge.
//!
//! This crate provides opcode definitions, instruction formats, and decoding
//! functions for the ArkCompiler bytecode instruction set.

#![allow(non_upper_case_globals, non_camel_case_types, non_snake_case)]

use std::sync::LazyLock;

// --- FFI bindings from bindgen ---
#[allow(dead_code)]
pub mod ffi {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

// --- Public types (API-compatible with old generated code) ---

/// Opcode value (u16). Non-prefixed opcodes fit in u8; prefixed = prefix_byte << 8 | sub.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Opcode(pub u16);

impl Opcode {
    /// Get the mnemonic string for this opcode.
    pub fn mnemonic(self) -> &'static str {
        lookup_opcode(self.0)
            .map(|info| info.mnemonic)
            .unwrap_or("unknown")
    }
}

impl core::fmt::Display for Opcode {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.mnemonic())
    }
}

/// Instruction format determining operand layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Format(pub u8);

impl Format {
    /// Total instruction size in bytes (including opcode).
    pub fn size(self) -> usize {
        unsafe { ffi::isa_get_size(self.0) }
    }
}

/// Instruction property flags.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OpcodeFlags(u32);

impl OpcodeFlags {
    pub const JUMP: OpcodeFlags = OpcodeFlags(1 << 0);
    pub const CONDITIONAL: OpcodeFlags = OpcodeFlags(1 << 1);
    pub const CALL: OpcodeFlags = OpcodeFlags(1 << 2);
    pub const RETURN: OpcodeFlags = OpcodeFlags(1 << 3);
    pub const THROW: OpcodeFlags = OpcodeFlags(1 << 4);
    pub const SUSPEND: OpcodeFlags = OpcodeFlags(1 << 5);
    pub const FLOAT: OpcodeFlags = OpcodeFlags(1 << 6);
    pub const ACC_READ: OpcodeFlags = OpcodeFlags(1 << 7);
    pub const ACC_WRITE: OpcodeFlags = OpcodeFlags(1 << 8);
    pub const STRING_ID: OpcodeFlags = OpcodeFlags(1 << 9);
    pub const METHOD_ID: OpcodeFlags = OpcodeFlags(1 << 10);
    pub const LITERALARRAY_ID: OpcodeFlags = OpcodeFlags(1 << 11);
    pub const IC_SLOT: OpcodeFlags = OpcodeFlags(1 << 12);
    pub const NO_SIDE_EFFECT: OpcodeFlags = OpcodeFlags(1 << 13);

    pub const fn empty() -> Self {
        OpcodeFlags(0)
    }

    pub const fn contains(self, other: OpcodeFlags) -> bool {
        (self.0 & other.0) == other.0
    }

    pub const fn union(self, other: OpcodeFlags) -> Self {
        OpcodeFlags(self.0 | other.0)
    }
}

/// Kind of operand in an instruction format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperandKind {
    /// Virtual register.
    Reg,
    /// Immediate value.
    Imm,
    /// Entity ID (string, method, literalarray, etc.).
    Id,
}

/// Description of a single operand within an instruction.
#[derive(Debug, Clone, Copy)]
pub struct OperandDesc {
    pub kind: OperandKind,
    pub bit_width: usize,
    pub byte_offset: usize,
    pub bit_offset_in_byte: usize,
    pub is_jump: bool,
    pub is_float: bool,
}

/// Metadata for a single opcode.
#[derive(Debug, Clone)]
pub struct OpcodeInfo {
    pub mnemonic: &'static str,
    pub format: Format,
    pub flags: OpcodeFlags,
    pub is_prefixed: bool,
    pub operand_parts: &'static [OperandDesc],
}

// --- Static table (built once from C bridge) ---

struct IsaTable {
    entries: Vec<(u16, OpcodeInfo)>,
    /// Leaked operand slices for 'static lifetime
    _operand_storage: Vec<Box<[OperandDesc]>>,
    /// Leaked mnemonic strings for 'static lifetime
    _mnemonic_storage: Vec<Box<str>>,
}

static ISA: LazyLock<IsaTable> = LazyLock::new(|| {
    let count = unsafe { ffi::isa_opcode_count() };
    let mut entries = Vec::with_capacity(count);
    let mut operand_storage = Vec::with_capacity(count);
    let mut mnemonic_storage = Vec::with_capacity(count);

    // Iterate all opcodes: non-prefixed (0x00..0xFF) + prefixed ((sub<<8)|prefix)
    let mut opcodes_to_check: Vec<u16> = (0..=0xFFu16).collect();
    for prefix in [0xFBu16, 0xFC, 0xFD, 0xFE] {
        for sub in 1..=0xFFu16 {
            opcodes_to_check.push((sub << 8) | prefix);
        }
    }

    for opcode_val in opcodes_to_check {
        let mnemonic_ptr = unsafe { ffi::isa_get_mnemonic(opcode_val) };
        if mnemonic_ptr.is_null() {
            continue;
        }

        let mnemonic_cstr = unsafe { std::ffi::CStr::from_ptr(mnemonic_ptr) };
        let mnemonic_str = mnemonic_cstr.to_str().unwrap_or("unknown");

        // Leak the mnemonic string to get 'static lifetime
        let mnemonic_box: Box<str> = mnemonic_str.into();
        let mnemonic_static: &'static str = unsafe { &*(mnemonic_box.as_ref() as *const str) };
        mnemonic_storage.push(mnemonic_box);

        let format_val = unsafe { ffi::isa_get_format(opcode_val) };
        let format = Format(format_val);
        let is_prefixed = unsafe { ffi::isa_is_prefixed(opcode_val) } != 0;

        // Build flags from C bridge
        let raw_flags = unsafe { ffi::isa_get_flags(opcode_val) };
        let flags = map_flags(raw_flags, opcode_val);

        // Build operand descriptors from format
        let mut ops = Vec::new();
        let fmt_size = format.size();
        let opcode_bytes = if is_prefixed { 2usize } else { 1 };

        for idx in 0..8usize {
            let has_vreg = unsafe { ffi::isa_has_vreg(format_val, idx) } != 0;
            let has_imm = unsafe { ffi::isa_has_imm(format_val, idx) } != 0;
            let has_id = unsafe { ffi::isa_has_id(format_val, idx) } != 0;

            if has_vreg {
                ops.push(OperandDesc {
                    kind: OperandKind::Reg,
                    bit_width: 0, // will be refined
                    byte_offset: 0,
                    bit_offset_in_byte: 0,
                    is_jump: false,
                    is_float: false,
                });
            } else if has_imm {
                ops.push(OperandDesc {
                    kind: OperandKind::Imm,
                    bit_width: 0,
                    byte_offset: 0,
                    bit_offset_in_byte: 0,
                    is_jump: flags.contains(OpcodeFlags::JUMP),
                    is_float: flags.contains(OpcodeFlags::FLOAT),
                });
            } else if has_id {
                ops.push(OperandDesc {
                    kind: OperandKind::Id,
                    bit_width: 0,
                    byte_offset: 0,
                    bit_offset_in_byte: 0,
                    is_jump: false,
                    is_float: false,
                });
            } else {
                break;
            }
        }

        // Compute byte offsets from format size and operand count
        if !ops.is_empty() {
            let operand_bytes = fmt_size - opcode_bytes;
            let bits_per_op = if ops.len() > 0 {
                operand_bytes * 8 / ops.len()
            } else {
                0
            };
            let mut bit_offset = 0usize;
            for op in &mut ops {
                op.bit_width = bits_per_op;
                op.byte_offset = opcode_bytes + bit_offset / 8;
                op.bit_offset_in_byte = bit_offset % 8;
                bit_offset += bits_per_op;
            }
        }

        // Leak operand slice for 'static lifetime
        let ops_box: Box<[OperandDesc]> = ops.into_boxed_slice();
        let ops_static: &'static [OperandDesc] =
            unsafe { &*(ops_box.as_ref() as *const [OperandDesc]) };
        operand_storage.push(ops_box);

        entries.push((
            opcode_val,
            OpcodeInfo {
                mnemonic: mnemonic_static,
                format,
                flags,
                is_prefixed,
                operand_parts: ops_static,
            },
        ));
    }

    entries.sort_by_key(|(v, _)| *v);

    IsaTable {
        entries,
        _operand_storage: operand_storage,
        _mnemonic_storage: mnemonic_storage,
    }
});

/// Map raw C flags to our OpcodeFlags.
fn map_flags(raw: u32, opcode: u16) -> OpcodeFlags {
    let mut flags = OpcodeFlags::empty();

    // The C bridge flags come from instruction properties.
    // We check known property names via the C bridge helpers.
    if unsafe { ffi::isa_is_jump(opcode) } != 0 {
        flags = flags.union(OpcodeFlags::JUMP);
    }
    if unsafe { ffi::isa_is_conditional(opcode) } != 0 {
        flags = flags.union(OpcodeFlags::CONDITIONAL);
    }
    if unsafe { ffi::isa_is_return(opcode) } != 0 {
        flags = flags.union(OpcodeFlags::RETURN);
    }
    if unsafe { ffi::isa_is_throw(opcode) } != 0 {
        flags = flags.union(OpcodeFlags::THROW);
    }

    let info = unsafe { ffi::isa_get_operand_info(opcode) };
    if info.acc_read != 0 {
        flags = flags.union(OpcodeFlags::ACC_READ);
    }
    if info.acc_write != 0 {
        flags = flags.union(OpcodeFlags::ACC_WRITE);
    }

    // Check raw flags for other properties (from the generated tables)
    // The bit positions depend on the sorted property list from the ERB template.
    // We pass through the raw value for properties we can't easily query via C helpers.
    let _ = raw; // raw flags available for future use

    flags
}

// --- Public API (compatible with old generated code) ---

/// Lookup table: maps opcode u16 value to OpcodeInfo.
pub fn opcode_table() -> &'static [(u16, OpcodeInfo)] {
    &ISA.entries
}

/// For backward compatibility: OPCODE_TABLE as a function-like accessor.
/// Old code used `OPCODE_TABLE` as a static; now it's a lazy-initialized slice.
pub static OPCODE_TABLE: LazyLock<&'static [(u16, OpcodeInfo)]> = LazyLock::new(|| &ISA.entries);

/// Find OpcodeInfo by opcode u16 value.
pub fn lookup_opcode(value: u16) -> Option<&'static OpcodeInfo> {
    ISA.entries
        .binary_search_by_key(&value, |(v, _)| *v)
        .ok()
        .map(|idx| &ISA.entries[idx].1)
}

/// Decode an opcode from a byte stream.
pub fn decode_opcode(bytes: &[u8]) -> Option<(Opcode, &'static OpcodeInfo)> {
    if bytes.is_empty() {
        return None;
    }
    let raw = unsafe { ffi::isa_decode_opcode(bytes.as_ptr(), bytes.len()) };
    if raw == 0xFFFF {
        return None;
    }
    let info = lookup_opcode(raw)?;
    Some((Opcode(raw), info))
}

// --- Operand extraction (delegated to C bridge) ---

/// Extract a virtual register operand from instruction bytes.
pub fn get_vreg(bytes: &[u8], idx: usize) -> u16 {
    unsafe { ffi::isa_get_vreg(bytes.as_ptr(), bytes.len(), idx) }
}

/// Extract a signed 64-bit immediate operand from instruction bytes.
pub fn get_imm64(bytes: &[u8], idx: usize) -> i64 {
    unsafe { ffi::isa_get_imm64(bytes.as_ptr(), bytes.len(), idx) }
}

/// Extract an entity ID operand from instruction bytes.
pub fn get_id(bytes: &[u8], idx: usize) -> u32 {
    unsafe { ffi::isa_get_id(bytes.as_ptr(), bytes.len(), idx) }
}

/// Format an instruction as a human-readable string.
pub fn format_instruction(bytes: &[u8]) -> String {
    let mut buf = vec![0u8; 256];
    let len = unsafe {
        ffi::isa_format_instruction(
            bytes.as_ptr(),
            bytes.len(),
            buf.as_mut_ptr() as *mut i8,
            buf.len(),
        )
    };
    buf.truncate(len);
    String::from_utf8_lossy(&buf).into_owned()
}

// --- Version API ---

/// .abc file version (4 bytes: major.minor.patch.build).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AbcVersion(pub [u8; 4]);

impl core::fmt::Display for AbcVersion {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}.{}.{}.{}", self.0[0], self.0[1], self.0[2], self.0[3])
    }
}

/// Current .abc file version from the ISA definition.
pub fn current_version() -> AbcVersion {
    let mut v = [0u8; 4];
    unsafe { ffi::isa_get_version(v.as_mut_ptr()) };
    AbcVersion(v)
}

/// Minimum supported .abc file version.
pub fn min_version() -> AbcVersion {
    let mut v = [0u8; 4];
    unsafe { ffi::isa_get_min_version(v.as_mut_ptr()) };
    AbcVersion(v)
}

/// Lookup the file version corresponding to an API level.
pub fn version_by_api(api_level: u8) -> Option<AbcVersion> {
    let mut v = [0u8; 4];
    let rc = unsafe { ffi::isa_get_version_by_api(api_level, v.as_mut_ptr()) };
    if rc == 0 { Some(AbcVersion(v)) } else { None }
}

/// Check if a version is compatible with the current ISA (>= min, <= current).
pub fn is_version_compatible(ver: &AbcVersion) -> bool {
    unsafe { ffi::isa_is_version_compatible(ver.0.as_ptr()) != 0 }
}

// --- Emitter API ---

/// Error from emitter build.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmitterError {
    InternalError,
    UnboundLabels,
}

impl core::fmt::Display for EmitterError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            EmitterError::InternalError => f.write_str("internal emitter error"),
            EmitterError::UnboundLabels => f.write_str("unbound labels"),
        }
    }
}

impl std::error::Error for EmitterError {}

/// Opaque label handle for branch targets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EmitterLabel(pub u32);

/// Bytecode emitter — encodes instructions, manages labels, patches branches.
///
/// Per-mnemonic emit functions are available through the raw FFI pointer
/// returned by [`Emitter::as_ptr`]. Call `ffi::isa_emit_*` functions directly.
pub struct Emitter {
    ptr: *mut ffi::IsaEmitter,
}

impl Emitter {
    pub fn new() -> Self {
        Emitter {
            ptr: unsafe { ffi::isa_emitter_create() },
        }
    }

    /// Raw pointer for calling per-mnemonic `ffi::isa_emit_*` functions.
    pub fn as_ptr(&mut self) -> *mut ffi::IsaEmitter {
        self.ptr
    }

    /// Create a new label for branch targets.
    pub fn create_label(&mut self) -> EmitterLabel {
        EmitterLabel(unsafe { ffi::isa_emitter_create_label(self.ptr) })
    }

    /// Bind a label to the current position in the bytecode stream.
    pub fn bind(&mut self, label: EmitterLabel) {
        unsafe { ffi::isa_emitter_bind(self.ptr, label.0) };
    }

    /// Build the final bytecode. Resolves all branch offsets.
    pub fn build(&mut self) -> Result<Vec<u8>, EmitterError> {
        let mut buf: *mut u8 = std::ptr::null_mut();
        let mut len: usize = 0;
        let rc = unsafe { ffi::isa_emitter_build(self.ptr, &mut buf, &mut len) };
        match rc {
            0 => {
                let result = unsafe { std::slice::from_raw_parts(buf, len) }.to_vec();
                unsafe { ffi::isa_emitter_free_buf(buf) };
                Ok(result)
            }
            1 => Err(EmitterError::InternalError),
            _ => Err(EmitterError::UnboundLabels),
        }
    }
}

impl Default for Emitter {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for Emitter {
    fn drop(&mut self) {
        unsafe { ffi::isa_emitter_destroy(self.ptr) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_ldundefined() {
        let bytecode = [0x00u8];
        let result = decode_opcode(&bytecode);
        assert!(result.is_some(), "opcode 0x00 should decode");
        let (op, info) = result.unwrap();
        assert_eq!(op.mnemonic(), "ldundefined");
        assert_eq!(info.mnemonic, "ldundefined");
    }

    #[test]
    fn decode_empty_bytecode() {
        let bytecode: [u8; 0] = [];
        assert!(decode_opcode(&bytecode).is_none());
    }

    #[test]
    fn decode_prefixed_opcode() {
        let bytecode = [0xfbu8, 0x00];
        let result = decode_opcode(&bytecode);
        assert!(result.is_some(), "prefixed opcode 0xfb00 should decode");
        let (_, info) = result.unwrap();
        assert!(info.is_prefixed);
    }

    #[test]
    fn decode_prefixed_needs_two_bytes() {
        let bytecode = [0xfbu8];
        assert!(decode_opcode(&bytecode).is_none());
    }

    #[test]
    fn format_sizes_are_positive() {
        for &(_, ref info) in opcode_table() {
            assert!(
                info.format.size() >= 1,
                "format {:?} has size 0",
                info.format
            );
        }
    }

    #[test]
    fn non_prefixed_opcodes_fit_in_u8() {
        for &(value, ref info) in opcode_table() {
            if !info.is_prefixed {
                assert!(
                    value <= 0xFF,
                    "{} has value {:#x} > 0xFF",
                    info.mnemonic,
                    value
                );
            }
        }
    }

    #[test]
    fn prefixed_opcodes_have_prefix_low_byte() {
        for &(value, ref info) in opcode_table() {
            if info.is_prefixed {
                let lo = (value & 0xFF) as u8;
                assert!(
                    lo == 0xFB || lo == 0xFC || lo == 0xFD || lo == 0xFE,
                    "{} has value {:#x} with unexpected low byte {:#x}",
                    info.mnemonic,
                    value,
                    lo
                );
            }
        }
    }

    #[test]
    fn decode_returnundefined() {
        let info = lookup_opcode_by_mnemonic("returnundefined");
        assert!(info.is_some(), "returnundefined should exist in ISA");
        let info = info.unwrap();
        assert!(info.flags.contains(OpcodeFlags::RETURN));
    }

    #[test]
    fn opcode_count_matches() {
        let count = unsafe { ffi::isa_opcode_count() };
        assert_eq!(opcode_table().len(), count);
    }

    fn lookup_opcode_by_mnemonic(mnemonic: &str) -> Option<&'static OpcodeInfo> {
        opcode_table()
            .iter()
            .find(|(_, info)| info.mnemonic == mnemonic)
            .map(|(_, info)| info)
    }

    #[test]
    fn version_is_valid() {
        let ver = current_version();
        assert!(ver.0[0] > 0 || ver.0[1] > 0, "version should be non-zero");
        let min = min_version();
        assert!(min <= ver, "min_version should be <= current_version");
    }

    #[test]
    fn current_version_is_compatible() {
        let ver = current_version();
        assert!(is_version_compatible(&ver));
    }

    #[test]
    fn min_version_is_compatible() {
        let ver = min_version();
        assert!(is_version_compatible(&ver));
    }

    #[test]
    fn version_by_api_returns_some_for_current() {
        let ver = current_version();
        // API level = first byte of version
        let result = version_by_api(ver.0[0]);
        assert!(
            result.is_some(),
            "current API level should map to a version"
        );
    }

    #[test]
    fn emitter_create_and_drop() {
        let _e = Emitter::new();
        // Just test that create/destroy doesn't crash
    }

    #[test]
    fn emitter_roundtrip() {
        // Encode ldundefined (opcode 0x00, NONE format, 1 byte) then decode it
        let mut e = Emitter::new();
        unsafe { ffi::isa_emit_ldundefined(e.as_ptr()) };
        let bytecode = e.build().expect("build should succeed");
        assert!(!bytecode.is_empty());
        let (op, _) = decode_opcode(&bytecode).expect("should decode");
        assert_eq!(op.mnemonic(), "ldundefined");
    }

    #[test]
    fn emitter_with_label() {
        let mut e = Emitter::new();
        let label = e.create_label();
        // Emit a jump to the label
        unsafe { ffi::isa_emit_jmp(e.as_ptr(), label.0) };
        // Bind the label here
        e.bind(label);
        // Emit something after the label
        unsafe { ffi::isa_emit_ldundefined(e.as_ptr()) };
        let bytecode = e.build().expect("build should succeed");
        assert!(!bytecode.is_empty());
    }

    #[test]
    fn emitter_unbound_label_fails() {
        let mut e = Emitter::new();
        let label = e.create_label();
        unsafe { ffi::isa_emit_jmp(e.as_ptr(), label.0) };
        // Don't bind the label
        let result = e.build();
        assert_eq!(result, Err(EmitterError::UnboundLabels));
    }
}
