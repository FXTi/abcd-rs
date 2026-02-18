//! ArkCompiler ISA definitions — opcode metadata, instruction decoding, version
//! management, and bytecode assembly.
//!
//! Built on top of `abcd-isa-sys` (raw C FFI bindings). All public types are safe;
//! the `ffi` module is internal.
//!
//! # Core concepts
//!
//! - [`OpcodeInfo`] — lightweight `Copy` handle (u16 index) into C static tables.
//!   All accessors are O(1). Obtained via [`decode()`] or [`lookup()`].
//! - [`Inst`] — decoded instruction reference. Holds a byte slice + `OpcodeInfo`,
//!   provides bounds-checked operand extraction and classification methods.
//! - [`Emitter`] — bytecode assembler with per-mnemonic safe emit methods.
//! - [`OpcodeFlags`] / [`Exceptions`] — bitmask types with `BitOr`/`BitAnd`/`Not`.
//!
//! # Quick start
//!
//! ```no_run
//! use abcd_isa::{decode, Inst, OpcodeFlags, DecodeError};
//!
//! // Decode from byte stream
//! let bytecode = [0x00u8]; // ldundefined
//! let (opcode, info) = decode(&bytecode).unwrap();
//! assert_eq!(opcode.mnemonic(), "ldundefined");
//!
//! // Use Inst for operand extraction
//! if let Some(inst) = Inst::decode(&bytecode) {
//!     println!("{inst}"); // Display trait
//! }
//!
//! // Assemble bytecode
//! let mut e = abcd_isa::Emitter::new();
//! e.ldundefined();
//! e.returnundefined();
//! let assembled = e.build().unwrap();
//! ```

mod ffi {
    pub use abcd_isa_sys::*;
}

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// Opcode value (u16). Non-prefixed opcodes fit in u8; prefixed = `(sub << 8) | prefix_byte`.
///
/// Use [`Opcode::mnemonic()`] to get the human-readable name, or [`Display`](core::fmt::Display)
/// to print it directly.
///
/// ```no_run
/// let op = abcd_isa::Opcode::new(0x62);
/// assert_eq!(op.raw(), 0x62);
/// println!("{op}"); // prints the mnemonic
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Opcode(u16);

impl Opcode {
    /// Create an `Opcode` from a raw u16 value.
    #[inline]
    pub const fn new(raw: u16) -> Self {
        Self(raw)
    }

    /// Raw u16 value.
    #[inline]
    #[must_use]
    pub const fn raw(self) -> u16 {
        self.0
    }

    /// Mnemonic string for this opcode, or `"unknown"`.
    #[inline]
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
///
/// Each format defines the number, types, and bit widths of operands.
/// Use [`Format::size()`] to get the total instruction size in bytes.
///
/// ```no_run
/// let info = abcd_isa::lookup(0x62).unwrap();
/// let fmt = info.format();
/// println!("format {:?}, {} bytes", fmt, fmt.size());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Format(u8);

impl Format {
    /// Raw u8 value.
    #[inline]
    #[must_use]
    pub const fn raw(self) -> u8 {
        self.0
    }

    /// Total instruction size in bytes (including opcode).
    #[inline]
    pub fn size(self) -> usize {
        unsafe { ffi::isa_get_size(self.0) }
    }
}

/// Instruction property flags (bit positions from generated `ISA_FLAG_*` constants).
///
/// Supports bitwise operations: `BitOr` (`|`), `BitAnd` (`&`), `Not` (`!`).
///
/// ```no_run
/// use abcd_isa::OpcodeFlags;
///
/// let combined = OpcodeFlags::JUMP | OpcodeFlags::CONDITIONAL;
/// let flags = abcd_isa::lookup(0x62).unwrap().flags();
/// if flags.contains(combined) {
///     println!("conditional jump");
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OpcodeFlags(u32);

/// Exception type flags.
///
/// Bitmask indicating which exceptions an instruction may raise.
/// Same bitwise operations as [`OpcodeFlags`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Exceptions(u32);

// Generated OpcodeFlags and Exceptions constants from ISA bindings.
include!(concat!(env!("OUT_DIR"), "/flag_constants.rs"));

impl OpcodeFlags {
    #[inline]
    #[must_use]
    pub const fn raw(self) -> u32 {
        self.0
    }
    #[inline]
    #[must_use]
    pub const fn empty() -> Self {
        Self(0)
    }
    #[inline]
    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }
    #[inline]
    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

impl core::ops::BitOr for OpcodeFlags {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

impl core::ops::BitAnd for OpcodeFlags {
    type Output = Self;
    #[inline]
    fn bitand(self, rhs: Self) -> Self {
        Self(self.0 & rhs.0)
    }
}

impl core::ops::Not for OpcodeFlags {
    type Output = Self;
    #[inline]
    fn not(self) -> Self {
        Self(!self.0)
    }
}

impl Exceptions {
    #[inline]
    #[must_use]
    pub const fn raw(self) -> u32 {
        self.0
    }
    #[inline]
    #[must_use]
    pub const fn empty() -> Self {
        Self(0)
    }
    #[inline]
    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }
    #[inline]
    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

impl core::ops::BitOr for Exceptions {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

impl core::ops::BitAnd for Exceptions {
    type Output = Self;
    #[inline]
    fn bitand(self, rhs: Self) -> Self {
        Self(self.0 & rhs.0)
    }
}

impl core::ops::Not for Exceptions {
    type Output = Self;
    #[inline]
    fn not(self) -> Self {
        Self(!self.0)
    }
}

/// Kind of operand in an instruction format.
///
/// - `Reg` — virtual register (v0, v1, ...)
/// - `Imm` — immediate value (signed or unsigned, may be a jump offset or float)
/// - `Id` — entity ID (string, method, or literal array reference)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OperandKind {
    Reg,
    Imm,
    Id,
}

/// Description of a single operand within an instruction.
///
/// Obtained from [`OpcodeInfo::operands()`]. Describes the operand's kind,
/// bit width, byte offset within the instruction, and semantic flags.
///
/// ```no_run
/// use abcd_isa::OperandKind;
///
/// let info = abcd_isa::opcode_table().find(|i| i.mnemonic() == "mov").unwrap();
/// for op in info.operands() {
///     println!("{:?} {}bits @byte{}", op.kind(), op.bit_width(), op.byte_offset());
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OperandDesc {
    kind: OperandKind,
    bit_width: usize,
    byte_offset: usize,
    bit_offset_in_byte: usize,
    is_jump: bool,
    is_float: bool,
    is_src: bool,
    is_dst: bool,
}

impl OperandDesc {
    #[inline]
    pub fn kind(&self) -> OperandKind {
        self.kind
    }
    #[inline]
    pub fn bit_width(&self) -> usize {
        self.bit_width
    }
    #[inline]
    pub fn byte_offset(&self) -> usize {
        self.byte_offset
    }
    #[inline]
    pub fn bit_offset_in_byte(&self) -> usize {
        self.bit_offset_in_byte
    }
    #[inline]
    pub fn is_jump(&self) -> bool {
        self.is_jump
    }
    #[inline]
    pub fn is_float(&self) -> bool {
        self.is_float
    }
    #[inline]
    pub fn is_src(&self) -> bool {
        self.is_src
    }
    #[inline]
    pub fn is_dst(&self) -> bool {
        self.is_dst
    }
}

// ---------------------------------------------------------------------------
// OpcodeInfo — zero-allocation index into C static tables
// ---------------------------------------------------------------------------

/// Metadata for a single opcode. This is a lightweight `Copy` handle that reads
/// from the C static tables on demand (O(1) per accessor).
///
/// Obtained via [`decode()`], [`lookup()`], or [`opcode_table()`].
///
/// ```no_run
/// // From decode
/// let (_, info) = abcd_isa::decode(&[0x00]).unwrap();
/// println!("{}: {} bytes", info.mnemonic(), info.size());
///
/// // From lookup
/// let info = abcd_isa::lookup(0x62).unwrap();
/// println!("flags: {:?}", info.flags());
///
/// // Iterate all
/// for info in abcd_isa::opcode_table() {
///     if info.is_acc_read() { println!("{} reads acc", info.mnemonic()); }
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OpcodeInfo(u16); // index into ISA_*_TABLE arrays

impl OpcodeInfo {
    /// Raw opcode value as [`Opcode`].
    #[inline]
    pub fn opcode(&self) -> Opcode {
        Opcode(unsafe { ffi::ISA_MNEMONIC_TABLE[self.0 as usize].opcode })
    }

    /// Human-readable mnemonic (e.g. `"mov"`, `"ldundefined"`).
    #[inline]
    pub fn mnemonic(&self) -> &'static str {
        let ptr = unsafe { ffi::ISA_MNEMONIC_TABLE[self.0 as usize].mnemonic };
        unsafe { core::ffi::CStr::from_ptr(ptr).to_str().unwrap_unchecked() }
    }

    /// Instruction format (determines operand layout and size).
    #[inline]
    pub fn format(&self) -> Format {
        Format(unsafe { ffi::isa_get_format(self.raw_opcode()) })
    }

    /// Total instruction size in bytes (shorthand for `self.format().size()`).
    #[inline]
    pub fn size(&self) -> usize {
        self.format().size()
    }

    /// Property flags bitmask (JUMP, CONDITIONAL, RETURN, THROW, etc.).
    #[inline]
    pub fn flags(&self) -> OpcodeFlags {
        OpcodeFlags(unsafe { ffi::ISA_FLAGS_TABLE[self.0 as usize].flags })
    }

    /// Exception types this instruction may raise.
    #[inline]
    pub fn exceptions(&self) -> Exceptions {
        Exceptions(unsafe { ffi::ISA_EXCEPTIONS_TABLE[self.0 as usize].exceptions })
    }

    /// Namespace string (e.g. `"ecmascript"`, `"core"`).
    #[inline]
    pub fn namespace(&self) -> &'static str {
        let ptr = unsafe { ffi::ISA_NAMESPACE_TABLE[self.0 as usize].ns };
        unsafe { core::ffi::CStr::from_ptr(ptr).to_str().unwrap_unchecked() }
    }

    /// Whether this is a 2-byte prefixed opcode (callruntime/deprecated/wide/throw).
    #[inline]
    pub fn is_prefixed(&self) -> bool {
        unsafe { ffi::isa_is_prefixed(self.raw_opcode()) != 0 }
    }

    /// Whether this is a range instruction (variable register count).
    #[inline]
    pub fn is_range(&self) -> bool {
        unsafe { ffi::isa_is_range(self.raw_opcode()) != 0 }
    }

    /// Whether this is a suspend (coroutine yield) instruction.
    #[inline]
    pub fn is_suspend(&self) -> bool {
        unsafe { ffi::isa_is_suspend(self.raw_opcode()) != 0 }
    }

    /// Whether this instruction reads the accumulator register.
    #[inline]
    pub fn is_acc_read(&self) -> bool {
        unsafe { ffi::ISA_OPERANDS_TABLE[self.0 as usize].acc_read != 0 }
    }

    /// Whether this instruction writes the accumulator register.
    #[inline]
    pub fn is_acc_write(&self) -> bool {
        unsafe { ffi::ISA_OPERANDS_TABLE[self.0 as usize].acc_write != 0 }
    }

    /// Iterator over operand descriptors. Returns [`OperandDesc`] for each
    /// non-accumulator operand, with computed byte/bit offsets.
    #[inline]
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

    #[inline]
    fn raw_opcode(&self) -> u16 {
        unsafe { ffi::ISA_MNEMONIC_TABLE[self.0 as usize].opcode }
    }
}

/// Iterator over operand descriptors for an opcode.
///
/// Yields [`OperandDesc`] for each non-accumulator operand, computing byte and
/// bit offsets on the fly. Implements [`ExactSizeIterator`].
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

/// Error returned by [`decode()`] when decoding fails.
///
/// Distinguishes between empty input and an unrecognized opcode byte.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecodeError {
    /// Input byte slice is empty.
    EmptyInput,
    /// Opcode byte(s) do not match any known instruction.
    InvalidOpcode,
}

impl core::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DecodeError::EmptyInput => f.write_str("empty input"),
            DecodeError::InvalidOpcode => f.write_str("invalid opcode"),
        }
    }
}

impl std::error::Error for DecodeError {}

/// Find opcode metadata by raw opcode value. Binary search on the static table.
///
/// Returns `None` if the opcode value is not recognized.
///
/// ```no_run
/// if let Some(info) = abcd_isa::lookup(0x62) {
///     println!("{}: {} bytes", info.mnemonic(), info.size());
/// }
/// ```
#[must_use]
pub fn lookup(value: u16) -> Option<OpcodeInfo> {
    let table = unsafe { &ffi::ISA_MNEMONIC_TABLE };
    table
        .binary_search_by_key(&value, |e| e.opcode)
        .ok()
        .map(|idx| OpcodeInfo(idx as u16))
}

/// Decode an opcode from a byte stream.
///
/// Returns the [`Opcode`] value and its [`OpcodeInfo`] metadata handle.
/// Uses `isa_decode_index()` internally for single-lookup decoding.
///
/// ```no_run
/// let (opcode, info) = abcd_isa::decode(&[0x00]).unwrap();
/// assert_eq!(opcode.mnemonic(), "ldundefined");
/// ```
pub fn decode(bytes: &[u8]) -> Result<(Opcode, OpcodeInfo), DecodeError> {
    if bytes.is_empty() {
        return Err(DecodeError::EmptyInput);
    }
    let idx = unsafe { ffi::isa_decode_index(bytes.as_ptr(), bytes.len()) };
    if idx == usize::MAX {
        return Err(DecodeError::InvalidOpcode);
    }
    let info = OpcodeInfo(idx as u16);
    Ok((info.opcode(), info))
}

/// Total number of opcodes in the ISA.
pub fn opcode_count() -> usize {
    ffi::ISA_MNEMONIC_TABLE_SIZE
}

/// Iterator over all opcode metadata entries.
///
/// ```no_run
/// for info in abcd_isa::opcode_table() {
///     println!("{}: {} bytes", info.mnemonic(), info.size());
/// }
/// ```
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
///
/// Holds a byte slice (exactly the instruction's bytes) and its [`OpcodeInfo`].
/// Provides bounds-checked operand extraction (returns `Option`) and
/// classification methods delegating to the upstream C++ generated code.
///
/// ```no_run
/// use abcd_isa::Inst;
///
/// let bytecode = [0x00u8]; // ldundefined
/// let inst = Inst::decode(&bytecode).unwrap();
/// println!("{inst}");                    // Display
/// println!("size: {}", inst.size());     // 1
/// println!("can throw: {}", inst.can_throw());
/// ```
pub struct Inst<'a> {
    bytes: &'a [u8],
    info: OpcodeInfo,
}

impl<'a> Inst<'a> {
    /// Decode one instruction from the start of `bytes`.
    ///
    /// Returns `None` if decoding fails or if `bytes` is shorter than the
    /// instruction size.
    pub fn decode(bytes: &'a [u8]) -> Option<Self> {
        let (_, info) = decode(bytes).ok()?;
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

    // Operand extraction (bounds-checked via isa_has_* before calling C++)

    /// Get the `idx`-th virtual register operand, or `None` if out of bounds.
    pub fn vreg(&self, idx: usize) -> Option<u16> {
        let fmt = self.info.format().raw();
        if unsafe { ffi::isa_has_vreg(fmt, idx) } == 0 {
            return None;
        }
        Some(unsafe { ffi::isa_get_vreg(self.bytes.as_ptr(), idx) })
    }
    /// Get the `idx`-th signed 64-bit immediate, or `None` if out of bounds.
    pub fn imm64(&self, idx: usize) -> Option<i64> {
        let fmt = self.info.format().raw();
        if unsafe { ffi::isa_has_imm(fmt, idx) } == 0 {
            return None;
        }
        Some(unsafe { ffi::isa_get_imm64(self.bytes.as_ptr(), idx) })
    }
    /// Get the `idx`-th entity ID operand, or `None` if out of bounds.
    pub fn id(&self, idx: usize) -> Option<u32> {
        let fmt = self.info.format().raw();
        if unsafe { ffi::isa_has_id(fmt, idx) } == 0 {
            return None;
        }
        Some(unsafe { ffi::isa_get_id(self.bytes.as_ptr(), idx) })
    }
    /// Get the `idx`-th immediate with correct signedness per opcode, or `None`.
    pub fn imm_data(&self, idx: usize) -> Option<i64> {
        let fmt = self.info.format().raw();
        if unsafe { ffi::isa_has_imm(fmt, idx) } == 0 {
            return None;
        }
        Some(unsafe { ffi::isa_get_imm_data(self.bytes.as_ptr(), idx) })
    }
    /// Number of immediate operands in this instruction.
    pub fn imm_count(&self) -> usize {
        unsafe { ffi::isa_get_imm_count(self.bytes.as_ptr()) }
    }
    /// Literal array index for `LITERALARRAY_ID` instructions, or `None`.
    pub fn literal_index(&self) -> Option<usize> {
        let idx = unsafe { ffi::isa_get_literal_index(self.bytes.as_ptr()) };
        // C bridge returns (size_t)-1 when no literal index exists
        if idx == usize::MAX { None } else { Some(idx) }
    }
    /// Last virtual register used by this instruction, or `None` if no vregs.
    pub fn last_vreg(&self) -> Option<u64> {
        let v = unsafe { ffi::isa_get_last_vreg(self.bytes.as_ptr()) };
        if v < 0 { None } else { Some(v as u64) }
    }
    /// Last register index for range instructions, or `None` if not applicable.
    pub fn range_last_reg_idx(&self) -> Option<u64> {
        let v = unsafe { ffi::isa_get_range_last_reg_idx(self.bytes.as_ptr()) };
        if v < 0 { None } else { Some(v as u64) }
    }

    // Classification (delegates to upstream C++ generated methods)

    /// Whether this instruction can throw an exception at runtime.
    pub fn can_throw(&self) -> bool {
        unsafe { ffi::isa_can_throw(self.bytes.as_ptr()) != 0 }
    }
    /// Whether this instruction is a basic block terminator.
    pub fn is_terminator(&self) -> bool {
        unsafe { ffi::isa_is_terminator(self.bytes.as_ptr()) != 0 }
    }
    /// Whether this instruction is a return or throw.
    pub fn is_return_or_throw(&self) -> bool {
        unsafe { ffi::isa_is_return_or_throw(self.bytes.as_ptr()) != 0 }
    }

    /// Check if the `idx`-th ID operand matches a specific flag
    /// (e.g. `OpcodeFlags::STRING_ID`, `OpcodeFlags::METHOD_ID`, `OpcodeFlags::LITERALARRAY_ID`).
    pub fn is_id_match_flag(&self, idx: usize, flag: OpcodeFlags) -> bool {
        unsafe { ffi::isa_is_id_match_flag(self.bytes.as_ptr(), idx, flag.0) != 0 }
    }

    // Formatting

    /// Format this instruction as a human-readable string (e.g. `"mov v1, v0"`).
    pub fn format_string(&self) -> String {
        // Stack-allocated buffer — 512 bytes is sufficient for any instruction.
        let mut buf = [0u8; 512];
        let len = unsafe {
            ffi::isa_format_instruction(
                self.bytes.as_ptr(),
                self.bytes.len(),
                buf.as_mut_ptr() as *mut std::ffi::c_char,
                buf.len(),
            )
        };
        String::from_utf8_lossy(&buf[..len]).into_owned()
    }
}

impl core::fmt::Display for Inst<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut buf = [0u8; 512];
        let len = unsafe {
            ffi::isa_format_instruction(
                self.bytes.as_ptr(),
                self.bytes.len(),
                buf.as_mut_ptr() as *mut std::ffi::c_char,
                buf.len(),
            )
        };
        let s = core::str::from_utf8(&buf[..len]).unwrap_or("<invalid utf8>");
        f.write_str(s)
    }
}

// ---------------------------------------------------------------------------
// Bytecode patching
// ---------------------------------------------------------------------------

/// Write a new entity ID at the given operand index (bytecode patching).
///
/// Modifies `bytes` in place. Used for rewriting entity references in bytecode.
pub fn update_id(bytes: &mut [u8], new_id: u32, idx: u32) {
    unsafe { ffi::isa_update_id(bytes.as_mut_ptr(), new_id, idx) }
}

// ---------------------------------------------------------------------------
// Version API
// ---------------------------------------------------------------------------

/// .abc file version (4 bytes: major.minor.patch.build).
///
/// Implements `Ord` for version comparison and `Display` for `"x.y.z.w"` formatting.
///
/// ```no_run
/// let ver = abcd_isa::current_version();
/// let min = abcd_isa::min_version();
/// assert!(min <= ver);
/// println!("ISA version: {ver}");
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AbcVersion(pub [u8; 4]);

impl core::fmt::Display for AbcVersion {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}.{}.{}.{}", self.0[0], self.0[1], self.0[2], self.0[3])
    }
}

/// Current .abc file version supported by this ISA build.
pub fn current_version() -> AbcVersion {
    let mut v = [0u8; 4];
    unsafe { ffi::isa_get_version(v.as_mut_ptr()) };
    AbcVersion(v)
}

/// Minimum .abc file version that can be processed.
pub fn min_version() -> AbcVersion {
    let mut v = [0u8; 4];
    unsafe { ffi::isa_get_min_version(v.as_mut_ptr()) };
    AbcVersion(v)
}

/// Look up the file version corresponding to an API level, or `None` if unknown.
pub fn version_by_api(api_level: u8) -> Option<AbcVersion> {
    let mut v = [0u8; 4];
    let rc = unsafe { ffi::isa_get_version_by_api(api_level, v.as_mut_ptr()) };
    if rc == 0 { Some(AbcVersion(v)) } else { None }
}

/// Check if a version is within the supported range (`min_version..=current_version`).
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
///
/// Returned by [`Emitter::build()`] when bytecode assembly fails.
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
///
/// Created by [`Emitter::label()`], bound by [`Emitter::bind()`],
/// and referenced by jump emit methods (e.g. `Emitter::jmp(label)`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Label(pub u32);

/// Bytecode emitter — encodes instructions, manages labels, patches branches.
///
/// Per-mnemonic emit methods are auto-generated (e.g. `ldundefined()`, `mov(vd, vs)`,
/// `jmp(label)`). Jump targets use [`Label`] handles.
///
/// ```no_run
/// let mut e = abcd_isa::Emitter::new();
/// let target = e.label();
/// e.jmp(target);
/// e.bind(target);
/// e.ldundefined();
/// e.returnundefined();
/// let bytecode = e.build().unwrap();
/// ```
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
        assert!(result.is_ok(), "opcode 0x00 should decode");
        let (op, info) = result.unwrap();
        assert_eq!(op.mnemonic(), "ldundefined");
        assert_eq!(info.mnemonic(), "ldundefined");
    }

    #[test]
    fn decode_empty_bytecode() {
        let bytecode: [u8; 0] = [];
        assert_eq!(decode(&bytecode), Err(DecodeError::EmptyInput));
    }

    #[test]
    fn decode_prefixed_opcode() {
        let bytecode = [0xfbu8, 0x00];
        let result = decode(&bytecode);
        assert!(result.is_ok(), "prefixed opcode 0xfb00 should decode");
        let (_, info) = result.unwrap();
        assert!(info.is_prefixed());
    }

    #[test]
    fn decode_prefixed_needs_two_bytes() {
        let bytecode = [0xfbu8];
        assert_eq!(decode(&bytecode), Err(DecodeError::InvalidOpcode));
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
                    info.opcode().raw() <= 0xFF,
                    "{} has value {:#x} > 0xFF",
                    info.mnemonic(),
                    info.opcode().raw()
                );
            }
        }
    }

    #[test]
    fn prefixed_opcodes_have_prefix_low_byte() {
        let min_prefix = min_prefix_opcode();
        for info in opcode_table() {
            if info.is_prefixed() {
                let lo = (info.opcode().raw() & 0xFF) as u8;
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
                assert!((info.opcode().raw() & 0xFF) as u8 >= min);
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
        assert_eq!(ops[0].kind(), OperandKind::Reg);
        assert_eq!(ops[1].kind(), OperandKind::Reg);
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
