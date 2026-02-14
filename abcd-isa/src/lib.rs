//! ArkCompiler ISA definitions, auto-generated from `isa.yaml`.
//!
//! This crate provides opcode definitions, instruction formats, and decoding
//! functions for the ArkCompiler bytecode instruction set.

// The bitflags crate is used by generated code
pub use bitflags;

include!(concat!(env!("OUT_DIR"), "/generated.rs"));
