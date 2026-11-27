//! Pure Safe Rust API for the ArkCompiler bytecode instruction set.
//!
//! This crate operates in 100% safe, FFI-free Rust (`#![forbid(unsafe_code)]`)
//! with zero production C/C++ build or link dependencies; the vendored C++
//! implementation in `abcd-isa-sys` is linked solely under `[dev-dependencies]`
//! as an exhaustive differential test oracle.
//!
//! Core capabilities:
//!
//! - [`decode`] / [`decode_for`] — parse modern (`9.0.0.0`..`24.0.0.0`) or
//!   version-dispatched bytecode streams into `(Bytecode, byte_offset)` pairs
//!   with resolved jump targets.
//! - [`decode_legacy`] — translate legacy (`0.0.0.2`, OpenHarmony 3.0/3.1)
//!   bytecode streams into the same `(Bytecode, byte_offset)` representation.
//! - [`encode`] — assemble a slice of [`Bytecode`] instructions into raw bytes
//!   using deterministic Fenwick-tree branch relaxation, automatic narrowest
//!   format selection, and inverted-condition far-jump trampolines.
//! - [`relocate_entity_id`] — patch an instruction's `n`-th entity-ID operand
//!   in place with zero heap allocation.
//! - [`Version`] — query and compare `.abc` file format versions from the
//!   pre-generated version table.
//!
//! # Quick start
//!
//! ```
//! use abcd_isa::{
//!     Bytecode, EntityId, EntityKind, Label, Version, decode, encode, insn, relocate_entity_id,
//! };
//!
//! let program: Vec<Bytecode> = vec![
//!     insn::LdaStr::new(EntityId(1)),
//!     insn::Jmp::new(Label(3)),
//!     insn::Ldundefined::new(),
//!     insn::Return::new(),
//! ];
//!
//! let (mut bytes, offsets) = encode(&program).unwrap();
//! assert_eq!(offsets.len(), program.len());
//!
//! relocate_entity_id(&mut bytes[offsets[0] as usize..], 0, EntityId(42)).unwrap();
//!
//! let decoded = decode(&bytes).unwrap();
//! assert_eq!(
//!     decoded[0].0.entity_operands(),
//!     vec![(EntityKind::StringId, EntityId(42))]
//! );
//! assert_eq!(decoded[1].0, Bytecode::Jmp(Label(3)));
//! assert!(Version::new(12, 0, 6, 0).is_in_supported_range());
//! ```

#![forbid(unsafe_code)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]

#[allow(
    non_upper_case_globals,
    non_camel_case_types,
    non_snake_case,
    dead_code,
    unused_parens,
    clippy::all,
    clippy::allow_attributes_without_reason,
    reason = "pre-generated pure-Rust ISA and version tables emitted by scripts/vendor-gen.py"
)]
mod generated {
    include!("generated/bytecode.rs");
    include!("generated/version_table.rs");
    pub(crate) mod legacy_table {
        include!("generated/legacy_table.rs");
    }
}

pub use generated::{
    Bytecode, BytecodeFlags, EntityId, EntityKind, ExceptionType, Imm, Label, MIN_PREFIX_OPCODE,
    ModernDecodeFault, Operand, Reg, insn,
};

mod decoder;
pub use decoder::{DecodeError, decode};

mod legacy;
pub use legacy::decode_legacy;

mod emitter;
pub use emitter::{EncodeError, encode};

mod relocation;
pub use relocation::{RelocationError, relocate_entity_id};

mod version;
pub use version::Version;

/// Dispatch bytecode decoding by `.abc` container [`Version`] (`0.0.0.2` uses
/// [`decode_legacy`]; all modern versions use [`decode`]).
pub fn decode_for(version: Version, bytes: &[u8]) -> Result<Vec<(Bytecode, u32)>, DecodeError> {
    if version == Version::new(0, 0, 0, 2) {
        decode_legacy(bytes)
    } else {
        decode(bytes)
    }
}
