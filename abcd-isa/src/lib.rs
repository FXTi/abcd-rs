//! Safe Rust API for the ArkCompiler bytecode instruction set.
//!
//! This crate provides five core capabilities:
//!
//! - [`decode`] — parse modern (`9.0.0.0`..`24.0.0.0`) bytecode bytes into
//!   `(Bytecode, byte_offset)` pairs with resolved jump targets in pure Safe Rust.
//! - [`decode_legacy`] — translate legacy (`0.0.0.2`, OpenHarmony 3.0/3.1)
//!   bytecode streams into the same `(Bytecode, byte_offset)` representation in
//!   pure Safe Rust.
//! - [`encode`] — assemble a slice of [`Bytecode`] instructions into raw bytes
//!   in pure Safe Rust using deterministic Fenwick-tree branch relaxation,
//!   automatic format selection, and far-jump trampoline widening.
//! - [`relocate_entity_id`] — patch an instruction's `n`-th entity-ID operand
//!   in place in pure Safe Rust with zero heap allocation.
//! - [`Version`] — query and compare `.abc` file format versions (backed by the
//!   vendored `file_format_version` table via [`abcd_isa_sys`]).
//!
//! `decode`, `decode_legacy`, `encode`, `relocate_entity_id`, and all
//! [`Bytecode`] classification/operand helpers execute in 100% safe, FFI-free
//! Rust (`#[forbid(unsafe_code)]`), verified against the vendored C++
//! implementation as a differential test oracle. `unsafe` is confined solely to
//! internal version-table FFI queries in `version`.
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
//!
//! # Re-exported types
//!
//! The following types are re-exported from [`abcd_isa_sys`] for convenience:
//! [`Bytecode`], [`Reg`], [`Imm`], [`EntityId`], [`EntityKind`], [`Label`],
//! [`Operand`], [`insn`], [`BytecodeFlags`], [`ExceptionType`].

#![cfg_attr(not(test), deny(clippy::unwrap_used))]

pub use abcd_isa_sys::{Bytecode, EntityId, EntityKind, Imm, Label, Operand, Reg};
pub use abcd_isa_sys::{BytecodeFlags, ExceptionType, insn};

#[forbid(unsafe_code)]
mod decoder;
pub use decoder::{DecodeError, decode};

#[forbid(unsafe_code)]
mod legacy;
#[expect(
    clippy::unnecessary_cast,
    reason = "tools/gen_legacy_table.py emits uniform explicit width casts for operand clarity"
)]
#[forbid(unsafe_code)]
mod legacy_table;
pub use legacy::decode_legacy;

#[forbid(unsafe_code)]
mod emitter;
pub use emitter::{EncodeError, encode};

#[forbid(unsafe_code)]
mod relocation;
pub use relocation::{RelocationError, relocate_entity_id};

mod version;
pub use version::Version;
