//! ArkCompiler ISA definitions — opcode metadata, instruction decoding, version
//! management, and bytecode assembly.
//!
//! Built on top of `abcd-isa-sys` (raw C FFI bindings). All public types are safe;
//! the `ffi` module is internal.

mod ffi {
    pub use abcd_isa_sys::*;
}

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// Opcode value (u16). Non-prefixed opcodes fit in u8; prefixed = (sub << 8) | prefix_byte.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Opcode(pub u16);

impl Opcode {
    /// Mnemonic string for this opcode, or `"unknown"`.
    pub fn mnemonic(self) -> &'static str {
        lookup(self.0).map(|i| i.mnemonic()).unwrap_or("unknown")
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

/// Instruction property flags (bit positions from generated ISA_FLAG_* constants).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OpcodeFlags(u32);

/// Exception type flags.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Exceptions(u32);

// Generated OpcodeFlags and Exceptions constants from ISA bindings.
include!(concat!(env!("OUT_DIR"), "/flag_constants.rs"));

impl OpcodeFlags {
    pub const fn raw(self) -> u32 {
        self.0
    }
    pub const fn empty() -> Self {
        Self(0)
    }
    pub const fn contains(self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

impl Exceptions {
    pub const fn raw(self) -> u32 {
        self.0
    }
    pub const fn contains(self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }
}

/// Kind of operand in an instruction format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperandKind {
    Reg,
    Imm,
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
    pub is_src: bool,
    pub is_dst: bool,
}

// ---------------------------------------------------------------------------
// OpcodeInfo — zero-allocation index into C static tables
// ---------------------------------------------------------------------------

/// Metadata for a single opcode. This is a lightweight `Copy` handle that reads
/// from the C static tables on demand (O(1) per accessor).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OpcodeInfo(u16); // index into ISA_*_TABLE arrays

impl OpcodeInfo {
    pub fn opcode(&self) -> Opcode {
        Opcode(unsafe { ffi::ISA_MNEMONIC_TABLE[self.0 as usize].opcode })
    }

    pub fn mnemonic(&self) -> &'static str {
        let ptr = unsafe { ffi::ISA_MNEMONIC_TABLE[self.0 as usize].mnemonic };
        unsafe { core::ffi::CStr::from_ptr(ptr).to_str().unwrap_unchecked() }
    }

    pub fn format(&self) -> Format {
        Format(unsafe { ffi::isa_get_format(self.raw_opcode()) })
    }

    pub fn size(&self) -> usize {
        self.format().size()
    }

    pub fn flags(&self) -> OpcodeFlags {
        let mut raw = unsafe { ffi::ISA_FLAGS_TABLE[self.0 as usize].flags };
        if unsafe { ffi::isa_is_throw(self.raw_opcode()) } != 0 {
            raw |= OpcodeFlags::THROW.0;
        }
        OpcodeFlags(raw)
    }

    pub fn exceptions(&self) -> Exceptions {
        Exceptions(unsafe { ffi::ISA_EXCEPTIONS_TABLE[self.0 as usize].exceptions })
    }

    pub fn namespace(&self) -> &'static str {
        let ptr = unsafe { ffi::ISA_NAMESPACE_TABLE[self.0 as usize].ns };
        unsafe { core::ffi::CStr::from_ptr(ptr).to_str().unwrap_unchecked() }
    }

    pub fn is_prefixed(&self) -> bool {
        unsafe { ffi::isa_is_prefixed(self.raw_opcode()) != 0 }
    }

    pub fn is_range(&self) -> bool {
        unsafe { ffi::isa_is_range(self.raw_opcode()) != 0 }
    }

    pub fn is_suspend(&self) -> bool {
        unsafe { ffi::isa_is_suspend(self.raw_opcode()) != 0 }
    }

    pub fn acc_read(&self) -> bool {
        unsafe { ffi::ISA_OPERANDS_TABLE[self.0 as usize].acc_read != 0 }
    }

    pub fn acc_write(&self) -> bool {
        unsafe { ffi::ISA_OPERANDS_TABLE[self.0 as usize].acc_write != 0 }
    }

    pub fn operands(&self) -> OperandIter {
        let entry = unsafe { &ffi::ISA_OPERANDS_TABLE[self.0 as usize] };
        let flags = self.flags();
        let opcode_bytes = if self.is_prefixed() { 2 } else { 1 };
        OperandIter {
            entry,
            idx: 0,
            count: entry.num_operands as usize,
            bit_cursor: opcode_bytes * 8,
            is_jump: flags.contains(OpcodeFlags::JUMP),
            is_float: flags.contains(OpcodeFlags::FLOAT),
        }
    }

    fn raw_opcode(&self) -> u16 {
        unsafe { ffi::ISA_MNEMONIC_TABLE[self.0 as usize].opcode }
    }
}

/// Iterator over operand descriptors for an opcode.
pub struct OperandIter {
    entry: &'static ffi::IsaOpcodeOperands,
    idx: usize,
    count: usize,
    bit_cursor: usize,
    is_jump: bool,
    is_float: bool,
}

impl Iterator for OperandIter {
    type Item = OperandDesc;

    fn next(&mut self) -> Option<OperandDesc> {
        if self.idx >= self.count {
            return None;
        }
        let op = &self.entry.operands[self.idx];
        let kind = match op.kind as u32 {
            ffi::ISA_OPERAND_KIND_REG => OperandKind::Reg,
            ffi::ISA_OPERAND_KIND_IMM => OperandKind::Imm,
            _ => OperandKind::Id,
        };
        let bit_width = op.bit_width as usize;
        let byte_offset = self.bit_cursor / 8;
        let bit_offset_in_byte = self.bit_cursor % 8;
        self.bit_cursor += bit_width;
        self.idx += 1;

        Some(OperandDesc {
            kind,
            bit_width,
            byte_offset,
            bit_offset_in_byte,
            is_jump: kind == OperandKind::Imm && self.is_jump,
            is_float: kind == OperandKind::Imm && self.is_float,
            is_src: op.is_src != 0,
            is_dst: op.is_dst != 0,
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.count - self.idx;
        (rem, Some(rem))
    }
}

impl ExactSizeIterator for OperandIter {}

// ---------------------------------------------------------------------------
// Lookup & decode
// ---------------------------------------------------------------------------

/// Find opcode metadata by raw opcode value. Binary search on the static table.
pub fn lookup(value: u16) -> Option<OpcodeInfo> {
    let table = unsafe { &ffi::ISA_MNEMONIC_TABLE };
    table
        .binary_search_by_key(&value, |e| e.opcode)
        .ok()
        .map(|idx| OpcodeInfo(idx as u16))
}

/// Decode an opcode from a byte stream.
pub fn decode(bytes: &[u8]) -> Option<(Opcode, OpcodeInfo)> {
    if bytes.is_empty() {
        return None;
    }
    let raw = unsafe { ffi::isa_decode_opcode(bytes.as_ptr(), bytes.len()) };
    if raw == ffi::ISA_INVALID_OPCODE as u16 {
        return None;
    }
    let info = lookup(raw)?;
    Some((Opcode(raw), info))
}

/// Total number of opcodes in the ISA.
pub fn opcode_count() -> usize {
    ffi::ISA_MNEMONIC_TABLE_SIZE
}

/// Iterator over all opcode metadata entries.
pub fn opcode_table() -> impl Iterator<Item = OpcodeInfo> {
    (0..ffi::ISA_MNEMONIC_TABLE_SIZE).map(|i| OpcodeInfo(i as u16))
}

/// Minimum prefix opcode byte value.
pub fn min_prefix_opcode() -> u8 {
    unsafe { ffi::isa_min_prefix_opcode() }
}

/// Number of prefix groups.
pub fn prefix_count() -> usize {
    unsafe { ffi::isa_prefix_count() }
}

/// Opcode byte for the i-th prefix group.
pub fn prefix_opcode_at(idx: usize) -> u8 {
    unsafe { ffi::isa_prefix_opcode_at(idx) }
}

/// Check if a primary (non-prefixed) opcode byte is valid.
pub fn is_primary_opcode_valid(primary: u8) -> bool {
    unsafe { ffi::isa_is_primary_opcode_valid(primary) != 0 }
}

// ---------------------------------------------------------------------------
// Inst — decoded instruction reference
// ---------------------------------------------------------------------------

/// A reference to a decoded instruction in a byte stream.
pub struct Inst<'a> {
    bytes: &'a [u8],
    info: OpcodeInfo,
}

impl<'a> Inst<'a> {
    /// Decode one instruction from the start of `bytes`.
    pub fn decode(bytes: &'a [u8]) -> Option<Self> {
        let (_, info) = decode(bytes)?;
        let size = info.size();
        if bytes.len() < size {
            return None;
        }
        Some(Inst {
            bytes: &bytes[..size],
            info,
        })
    }

    pub fn opcode(&self) -> Opcode {
        self.info.opcode()
    }
    pub fn info(&self) -> OpcodeInfo {
        self.info
    }
    pub fn size(&self) -> usize {
        self.bytes.len()
    }
    pub fn bytes(&self) -> &[u8] {
        self.bytes
    }

    // Operand extraction
    pub fn vreg(&self, idx: usize) -> u16 {
        unsafe { ffi::isa_get_vreg(self.bytes.as_ptr(), idx) }
    }
    pub fn imm64(&self, idx: usize) -> i64 {
        unsafe { ffi::isa_get_imm64(self.bytes.as_ptr(), idx) }
    }
    pub fn id(&self, idx: usize) -> u32 {
        unsafe { ffi::isa_get_id(self.bytes.as_ptr(), idx) }
    }
    pub fn imm_data(&self, idx: usize) -> i64 {
        unsafe { ffi::isa_get_imm_data(self.bytes.as_ptr(), idx) }
    }
    pub fn imm_count(&self) -> usize {
        unsafe { ffi::isa_get_imm_count(self.bytes.as_ptr()) }
    }
    pub fn literal_index(&self) -> Option<usize> {
        let idx = unsafe { ffi::isa_get_literal_index(self.bytes.as_ptr()) };
        // C bridge returns (size_t)-1 when no literal index exists
        if idx == usize::MAX { None } else { Some(idx) }
    }
    pub fn last_vreg(&self) -> Option<u64> {
        let v = unsafe { ffi::isa_get_last_vreg(self.bytes.as_ptr()) };
        if v < 0 { None } else { Some(v as u64) }
    }
    pub fn range_last_reg_idx(&self) -> Option<u64> {
        let v = unsafe { ffi::isa_get_range_last_reg_idx(self.bytes.as_ptr()) };
        if v < 0 { None } else { Some(v as u64) }
    }

    // Classification
    pub fn can_throw(&self) -> bool {
        unsafe { ffi::isa_can_throw(self.bytes.as_ptr()) != 0 }
    }
    pub fn is_terminator(&self) -> bool {
        unsafe { ffi::isa_is_terminator(self.bytes.as_ptr()) != 0 }
    }
    pub fn is_return_or_throw(&self) -> bool {
        unsafe { ffi::isa_is_return_or_throw(self.bytes.as_ptr()) != 0 }
    }

    /// Check if the `idx`-th ID operand matches a specific flag
    /// (e.g. `OpcodeFlags::STRING_ID`, `OpcodeFlags::METHOD_ID`, `OpcodeFlags::LITERALARRAY_ID`).
    pub fn is_id_match_flag(&self, idx: usize, flag: OpcodeFlags) -> bool {
        unsafe { ffi::isa_is_id_match_flag(self.bytes.as_ptr(), idx, flag.0) != 0 }
    }

    // Formatting
    pub fn format_string(&self) -> String {
        // Buffer of 512 bytes is sufficient for any instruction.
        // isa_format_instruction truncates silently if the buffer is too small.
        let mut buf = vec![0u8; 512];
        let len = unsafe {
            ffi::isa_format_instruction(
                self.bytes.as_ptr(),
                self.bytes.len(),
                buf.as_mut_ptr() as *mut i8,
                buf.len(),
            )
        };
        buf.truncate(len);
        String::from_utf8_lossy(&buf).into_owned()
    }
}

// ---------------------------------------------------------------------------
// Bytecode patching
// ---------------------------------------------------------------------------

/// Write a new entity ID at the given operand index (bytecode patching).
pub fn update_id(bytes: &mut [u8], new_id: u32, idx: u32) {
    unsafe { ffi::isa_update_id(bytes.as_mut_ptr(), new_id, idx) }
}

// ---------------------------------------------------------------------------
// Version API
// ---------------------------------------------------------------------------

/// .abc file version (4 bytes: major.minor.patch.build).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AbcVersion(pub [u8; 4]);

impl core::fmt::Display for AbcVersion {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}.{}.{}.{}", self.0[0], self.0[1], self.0[2], self.0[3])
    }
}

pub fn current_version() -> AbcVersion {
    let mut v = [0u8; 4];
    unsafe { ffi::isa_get_version(v.as_mut_ptr()) };
    AbcVersion(v)
}

pub fn min_version() -> AbcVersion {
    let mut v = [0u8; 4];
    unsafe { ffi::isa_get_min_version(v.as_mut_ptr()) };
    AbcVersion(v)
}

pub fn version_by_api(api_level: u8) -> Option<AbcVersion> {
    let mut v = [0u8; 4];
    let rc = unsafe { ffi::isa_get_version_by_api(api_level, v.as_mut_ptr()) };
    if rc == 0 { Some(AbcVersion(v)) } else { None }
}

pub fn is_version_compatible(ver: &AbcVersion) -> bool {
    unsafe { ffi::isa_is_version_compatible(ver.0.as_ptr()) != 0 }
}

/// Number of entries in the API version map.
pub fn api_version_count() -> usize {
    unsafe { ffi::isa_get_api_version_count() }
}

// ---------------------------------------------------------------------------
// Emitter
// ---------------------------------------------------------------------------

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
pub struct Label(pub u32);

/// Bytecode emitter — encodes instructions, manages labels, patches branches.
pub struct Emitter {
    ptr: *mut ffi::IsaEmitter,
}

impl Emitter {
    pub fn new() -> Self {
        Emitter {
            ptr: unsafe { ffi::isa_emitter_create() },
        }
    }

    /// Create a new label for branch targets.
    pub fn label(&mut self) -> Label {
        Label(unsafe { ffi::isa_emitter_create_label(self.ptr) })
    }

    /// Bind a label to the current position in the bytecode stream.
    pub fn bind(&mut self, label: Label) {
        unsafe { ffi::isa_emitter_bind(self.ptr, label.0) };
    }

    /// Build the final bytecode. Resolves all branch offsets.
    pub fn build(&mut self) -> Result<Vec<u8>, EmitterError> {
        let mut buf: *mut u8 = std::ptr::null_mut();
        let mut len: usize = 0;
        let rc = unsafe { ffi::isa_emitter_build(self.ptr, &mut buf, &mut len) };
        match rc as u32 {
            ffi::ISA_EMITTER_OK => {
                let result = unsafe { std::slice::from_raw_parts(buf, len) }.to_vec();
                unsafe { ffi::isa_emitter_free_buf(buf) };
                Ok(result)
            }
            ffi::ISA_EMITTER_INTERNAL_ERROR => Err(EmitterError::InternalError),
            _ => Err(EmitterError::UnboundLabels),
        }
    }

    // Per-mnemonic safe emit methods are in a separate impl block (auto-generated)
}

include!(concat!(env!("OUT_DIR"), "/emitter_methods.rs"));

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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_ldundefined() {
        let bytecode = [0x00u8];
        let result = decode(&bytecode);
        assert!(result.is_some(), "opcode 0x00 should decode");
        let (op, info) = result.unwrap();
        assert_eq!(op.mnemonic(), "ldundefined");
        assert_eq!(info.mnemonic(), "ldundefined");
    }

    #[test]
    fn decode_empty_bytecode() {
        let bytecode: [u8; 0] = [];
        assert!(decode(&bytecode).is_none());
    }

    #[test]
    fn decode_prefixed_opcode() {
        let bytecode = [0xfbu8, 0x00];
        let result = decode(&bytecode);
        assert!(result.is_some(), "prefixed opcode 0xfb00 should decode");
        let (_, info) = result.unwrap();
        assert!(info.is_prefixed());
    }

    #[test]
    fn decode_prefixed_needs_two_bytes() {
        let bytecode = [0xfbu8];
        assert!(decode(&bytecode).is_none());
    }

    #[test]
    fn format_sizes_are_positive() {
        for info in opcode_table() {
            assert!(info.size() >= 1, "format {:?} has size 0", info.format());
        }
    }

    #[test]
    fn non_prefixed_opcodes_fit_in_u8() {
        for info in opcode_table() {
            if !info.is_prefixed() {
                assert!(
                    info.opcode().0 <= 0xFF,
                    "{} has value {:#x} > 0xFF",
                    info.mnemonic(),
                    info.opcode().0
                );
            }
        }
    }

    #[test]
    fn prefixed_opcodes_have_prefix_low_byte() {
        let min_prefix = min_prefix_opcode();
        for info in opcode_table() {
            if info.is_prefixed() {
                let lo = (info.opcode().0 & 0xFF) as u8;
                assert!(
                    lo >= min_prefix,
                    "{} has low byte {:#x} < min prefix {:#x}",
                    info.mnemonic(),
                    lo,
                    min_prefix
                );
            }
        }
    }

    #[test]
    fn decode_returnundefined() {
        let info = opcode_table().find(|i| i.mnemonic() == "returnundefined");
        assert!(info.is_some(), "returnundefined should exist in ISA");
        let info = info.unwrap();
        assert!(info.flags().contains(OpcodeFlags::RETURN));
    }

    #[test]
    fn opcode_count_matches() {
        assert_eq!(opcode_table().count(), opcode_count());
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
        assert!(is_version_compatible(&current_version()));
    }

    #[test]
    fn min_version_is_compatible() {
        assert!(is_version_compatible(&min_version()));
    }

    #[test]
    fn version_by_api_returns_some_for_current() {
        let ver = current_version();
        let result = version_by_api(ver.0[0]);
        assert!(
            result.is_some(),
            "current API level should map to a version"
        );
    }

    #[test]
    fn emitter_create_and_drop() {
        let _e = Emitter::new();
    }

    #[test]
    fn emitter_roundtrip() {
        let mut e = Emitter::new();
        e.ldundefined();
        let bytecode = e.build().expect("build should succeed");
        assert!(!bytecode.is_empty());
        let (op, _) = decode(&bytecode).expect("should decode");
        assert_eq!(op.mnemonic(), "ldundefined");
    }

    #[test]
    fn emitter_with_label() {
        let mut e = Emitter::new();
        let label = e.label();
        e.jmp(label);
        e.bind(label);
        e.ldundefined();
        let bytecode = e.build().expect("build should succeed");
        assert!(!bytecode.is_empty());
    }

    #[test]
    fn emitter_unbound_label_fails() {
        let mut e = Emitter::new();
        let label = e.label();
        e.jmp(label);
        let result = e.build();
        assert_eq!(result, Err(EmitterError::UnboundLabels));
    }

    #[test]
    fn flags_raw_passthrough() {
        assert_eq!(OpcodeFlags::JUMP.raw(), ffi::ISA_FLAG_JUMP);
        assert_eq!(OpcodeFlags::RETURN.raw(), ffi::ISA_FLAG_RETURN);
        assert_eq!(OpcodeFlags::CONDITIONAL.raw(), ffi::ISA_FLAG_CONDITIONAL);
        assert_eq!(OpcodeFlags::ACC_READ.raw(), ffi::ISA_FLAG_ACC_READ);
        assert_eq!(OpcodeFlags::ACC_WRITE.raw(), ffi::ISA_FLAG_ACC_WRITE);
    }

    #[test]
    fn min_prefix_opcode_value() {
        let min = min_prefix_opcode();
        assert!(min > 0 && min < 0xFF, "min prefix should be in valid range");
        for info in opcode_table() {
            if info.is_prefixed() {
                assert!((info.opcode().0 & 0xFF) as u8 >= min);
            }
        }
    }

    #[test]
    fn prefix_count_matches() {
        let count = prefix_count();
        assert!(count > 0, "should have at least one prefix");
        let min = min_prefix_opcode();
        for i in 0..count {
            assert!(prefix_opcode_at(i) >= min);
        }
    }

    #[test]
    fn can_throw_for_throw_instruction() {
        let info = opcode_table().find(|i| i.mnemonic() == "throw");
        if let Some(info) = info {
            let _ = info; // just verify it exists
            let mut e = Emitter::new();
            e.throw();
            let bytecode = e.build().expect("build");
            let inst = Inst::decode(&bytecode).expect("decode");
            assert!(inst.can_throw(), "throw instruction should can_throw");
        }
    }

    #[test]
    fn is_terminator_for_return() {
        let info = opcode_table().find(|i| i.mnemonic() == "returnundefined");
        assert!(info.is_some());
        let mut e = Emitter::new();
        e.returnundefined();
        let bytecode = e.build().expect("build");
        let inst = Inst::decode(&bytecode).expect("decode");
        assert!(inst.is_terminator(), "returnundefined should be terminator");
    }

    #[test]
    fn operand_info_from_table() {
        // mov has 2 register operands
        let info = opcode_table().find(|i| i.mnemonic() == "mov").unwrap();
        let ops: Vec<_> = info.operands().collect();
        assert!(ops.len() >= 2, "mov should have at least 2 operands");
        assert_eq!(ops[0].kind, OperandKind::Reg);
        assert_eq!(ops[1].kind, OperandKind::Reg);
    }

    #[test]
    fn namespace_is_nonempty() {
        for info in opcode_table() {
            assert!(
                !info.namespace().is_empty(),
                "{} has empty namespace",
                info.mnemonic()
            );
        }
    }

    #[test]
    fn inst_decode_and_access() {
        let mut e = Emitter::new();
        e.ldundefined();
        let bytecode = e.build().expect("build");
        let inst = Inst::decode(&bytecode).expect("decode");
        assert_eq!(inst.opcode().mnemonic(), "ldundefined");
        assert_eq!(inst.size(), inst.info().size());
    }
}
