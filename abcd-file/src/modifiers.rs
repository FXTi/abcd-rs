//! Access flag constants from the ArkCompiler bytecode specification.
//!
//! These match the values in `modifiers.h` from upstream libpandafile.

// File-level access flags (0x0000–0xFFFF)

/// Public access — field, method, class.
pub const ACC_PUBLIC: u32 = 0x0001;
/// Private access — field, method.
pub const ACC_PRIVATE: u32 = 0x0002;
/// Protected access — field, method.
pub const ACC_PROTECTED: u32 = 0x0004;
/// Static — field, method.
pub const ACC_STATIC: u32 = 0x0008;
/// Final — field, method, class.
pub const ACC_FINAL: u32 = 0x0010;
/// Super — class.
pub const ACC_SUPER: u32 = 0x0020;
/// Synchronized — method (same bit as ACC_SUPER).
pub const ACC_SYNCHRONIZED: u32 = 0x0020;
/// Bridge method (same bit as ACC_VOLATILE).
pub const ACC_BRIDGE: u32 = 0x0040;
/// Volatile field (same bit as ACC_BRIDGE).
pub const ACC_VOLATILE: u32 = 0x0040;
/// Transient field (same bit as ACC_VARARGS).
pub const ACC_TRANSIENT: u32 = 0x0080;
/// Varargs method (same bit as ACC_TRANSIENT).
pub const ACC_VARARGS: u32 = 0x0080;
/// Native method.
pub const ACC_NATIVE: u32 = 0x0100;
/// Interface — class.
pub const ACC_INTERFACE: u32 = 0x0200;
/// Abstract — method, class.
pub const ACC_ABSTRACT: u32 = 0x0400;
/// Strict floating-point — method.
pub const ACC_STRICT: u32 = 0x0800;
/// Synthetic — field, method, class.
pub const ACC_SYNTHETIC: u32 = 0x1000;
/// Annotation type — class.
pub const ACC_ANNOTATION: u32 = 0x2000;
/// Enum — field, class.
pub const ACC_ENUM: u32 = 0x4000;

/// Mask for file-level flags (lower 16 bits).
pub const ACC_FILE_MASK: u32 = 0xFFFF;
