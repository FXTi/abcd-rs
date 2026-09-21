//! # abcd-ir — the SSA IR
//!
//! The intermediate representation for ArkCompiler bytecode programs
//! (`design/ir-v0.2.md`, background in `design/ir.md` §1–§8): identity
//! tables, module/function graphs, the op taxonomy, the effects table,
//! the type lattice, and the verifier. Lift (`abcd-lift`, decode → IR),
//! optimize (`abcd-opt`, IR → IR), and lower (`abcd-lower`, IR →
//! bytecode) live in separate crates.
//!
//! This crate **is** the IR (the v2-P4 swap, 2026-09-21: the v0.1
//! `abcd-ir` crate was deleted — git history is the archive — and
//! `abcd-ir2` was renamed `abcd-ir`).
//!
//! ## Format independence (hard, structurally enforced)
//!
//! The IR describes a **program** — classes, functions, value flow,
//! types, annotations, module records, debug info — never a **file**.
//! This crate's `Cargo.toml` declares **no dependency** on `abcd-file`,
//! `abcd-isa`, `abcd-file-sys`, or `abcd-isa-sys`, and never may: the
//! crate graph is the enforcement mechanism (design/ir.md §8 invariant
//! 1).
//!
//! What must never appear here (the §6.2 v0.1 leak inventory):
//!
//! - `version` / `file_type` (file identity, not program semantics);
//! - file offsets as entity identity (`method_offset`, `EntityId`,
//!   `source_offset`) — identity is [`FuncId`]/[`ClassId`] + the
//!   [`SymbolTable`];
//! - a file string pool (`StringId`) — names are [`Sym`];
//! - literal-array indices (`LiteralArrayIdx`, `literal_array_offsets`) —
//!   literal shapes are typed [`Const`]s in the [`ConstPool`];
//! - four annotation buckets — one [`Annotation`] list per attach site;
//! - file-bound type payloads (`IrType::Static(file StringId)`, N46) —
//!   [`StaticTy::Reference`] carries a module [`ClassId`];
//! - `num_vregs` / `num_args` frame layout (SSA has no registers);
//! - file-range try blocks — structured [`TryRegion`]s;
//! - register/accumulator concepts (`RegOrAcc`) — out-of-SSA is a
//!   lowering concern only.
//!
//! ## The taint-analysis contract (T1–T10)
//!
//! - **T1** — arena ids ([`id`]) are stable across pass pipelines;
//!   [`SymbolTable`]/[`ConstPool`] are append-only.
//! - **T2** — named/index/dynamic property access are distinct ops
//!   ([`Op::LoadProp`], [`Op::LoadPropIdx`], [`Op::LoadPropDyn`]).
//! - **T3** — [`Op::effects`] is the single, mechanically derived source
//!   of effect truth ([`Effects`]).
//! - **T4** — one [`Op::Call`] with [`CallKind`] + the §5.3 binding
//!   table; [`Op::DefineFunc`] carries explicit captures; `params[0]` is
//!   `this`.
//! - **T5** — [`EdgeKind::Exceptional`] edges are first-class CFG edges;
//!   [`ValueDef::ExceptionParam`] is a real SSA value defined by the
//!   dispatch.
//! - **T6** — [`FunctionData::is_external`] + [`Sym`] keys for summary
//!   attachment.
//! - **T7** — allocation sites are distinct ops ([`Op::AllocObject`],
//!   [`Op::AllocArray`], [`Op::AllocClosure`], [`Op::AllocRegExp`],
//!   [`Op::CreateGenerator`]); the instruction id is the site identity.
//! - **T8** — [`Inst::loc`] is propagated or dropped, never fabricated.
//! - **T9** — every name is a [`Sym`]; entities are referenced by id,
//!   never by file offset.
//! - **T10** — params/return/exception wiring follows the §5.3 binding
//!   table per [`CallKind`].
//!
//! ## Library rule
//!
//! No panics on data: every lookup returns `Option`, every fallible
//! finding is collected into [`VerifyReport`]; error types derive
//! `thiserror::Error`.

#![deny(missing_docs)]

pub mod consts;
pub mod effects;
pub mod function;
pub mod id;
pub mod module;
pub mod op;
pub mod symbol;
pub mod ty;
pub mod verify;

pub use consts::{Const, ConstPool};
pub use effects::{AllocKind, CallEffect, Effects, MemClasses};
pub use function::{
    Block, Catch, ColumnEntry, DebugData, Edge, EdgeKind, FunctionData, Inst, LineEntry, Loc,
    LocalName, LocalScope, TryRegion, Value, ValueDef,
};
pub use id::{BlockId, ClassId, ConstId, FieldId, FuncId, InstId, Sym, ValueId};
pub use module::{
    AnnValue, Annotation, ClassData, ExportDecl, FieldData, FunctionKind, ImportDecl, Modifiers,
    Module, ModuleRequest, Signature, SourceLang,
};
pub use op::{Arity, BinOp, CallKind, CmpOp, Op, PropKey, SuperCheck, SuperKey, UnOp};
pub use symbol::SymbolTable;
pub use ty::{DynPrim, StaticTy, Ty};
pub use verify::{
    VerifyError, VerifyErrorKind, VerifyReport, VerifyWarning, VerifyWarningKind, verify_func,
    verify_module,
};
