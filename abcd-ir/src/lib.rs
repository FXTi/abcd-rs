//! SSA-form intermediate representation for ArkCompiler bytecode.
//!
//! This crate provides:
//! - A complete IR definition modeled after Hermes, adapted for ArkCompiler
//! - Lifting: bytecode → IR (CFG construction + SSA via Braun algorithm)
//! - Lowering: IR → bytecode (register allocation + instruction selection)
//!
//! The IR preserves all metadata from `abcd_file` for complete round-trip
//! fidelity, covering both dynamic JS/TS and ArkTS static types.

pub mod analysis;
pub mod builder;
pub mod display;
pub mod entity;
pub mod inst;
pub mod module;
pub mod opt;
pub mod types;
pub mod verify;

pub mod lift;
pub mod lower;

// Re-export key types at crate root.
pub use entity::{Block, ClassId, FuncId, Inst, StringId, Value};
pub use inst::{BinOp, CallKind, InstData, PropKind, UnOp};
pub use module::{
    BasicBlockData, ClassData, FieldData, FuncDebugInfo, FunctionData, InstNode, IrAnnotation,
    IrAnnotations, Module, StringPool, ValueData, ValueDef,
};
pub use types::{DynType, IrType};
