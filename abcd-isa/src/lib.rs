//! Safe Rust API for the ArkCompiler bytecode instruction set.
//!
//! This crate provides three main capabilities:
//!
//! - [`decode`] — parse raw bytecode bytes into `(Bytecode, byte_offset)` pairs
//!   with resolved jump targets.
//! - [`encode`] — assemble a slice of [`Bytecode`] instructions back into raw
//!   bytes, resolving [`Label`] indices to byte offsets.
//! - [`Version`] — query and compare `.abc` file format versions.
//!
//! All public types are safe.  `unsafe` is confined to internal FFI calls into
//! the C bridge provided by [`abcd_isa_sys`].
//!
//! # Quick start
//!
//! ```no_run
//! use abcd_isa::{decode, encode, Bytecode};
//!
//! // Decode raw bytecode into instructions with byte offsets.
//! let bytes: &[u8] = &[/* raw .abc method body */];
//! let decoded: Vec<(Bytecode, u32)> = decode(bytes).unwrap();
//!
//! // Re-encode back to bytes (round-trip).
//! let bcs: Vec<Bytecode> = decoded.iter().map(|(bc, _)| *bc).collect();
//! let (output, offsets) = encode(&bcs).unwrap();
//! ```
//!
//! # Re-exported types
//!
//! The following types are re-exported from [`abcd_isa_sys`] for convenience:
//! [`Bytecode`], [`Reg`], [`Imm`], [`EntityId`], [`Label`],
//! [`insn`], [`BytecodeFlag`], [`ExceptionType`].

pub use abcd_isa_sys::{Bytecode, EntityId, Imm, Label, Reg};
pub use abcd_isa_sys::{BytecodeFlag, ExceptionType, insn};

mod decoder;
pub use decoder::{DecodeError, decode};

mod emitter;
pub use emitter::{EncodeError, encode};

mod version;
pub use version::Version;
