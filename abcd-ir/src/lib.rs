//! # abcd-ir — the SSA IR
//!
//! Format-independent Static Single Assignment intermediate representation for
//! ArkCompiler bytecode programs (`design/ir-v0.2.md`, background in
//! `design/ir.md` §1–§8): identity tables, module/function arenas, the 88-op
//! taxonomy, the effects table, the type lattice, and the structural verifier.
//! Lifting (`abcd-lift`, container → IR), optimization (`abcd-opt`, IR → IR),
//! and lowering (`abcd-lower`, IR → container) live in separate crates.
//!
//! ## Format independence (structurally enforced)
//!
//! The IR describes a **program** — classes, functions, value flow, types,
//! annotations, module records, debug info — never a serialized **file**.
//! This crate's `Cargo.toml` declares **no dependency** on `abcd-file`,
//! `abcd-isa`, `abcd-file-sys`, or `abcd-isa-sys`, and never may (`design/ir.md`
//! §8 invariant 1):
//!
//! - file-header identity (`version`, `file_type`) stays outside the IR;
//! - entity identity uses [`FuncId`], [`ClassId`], and [`SymbolTable`], never
//!   raw 32-bit file offsets;
//! - strings intern losslessly as [`Sym`]s (valid UTF-8 or raw MUTF-8 bytes);
//! - literal shapes live as typed [`Const`] trees in [`ConstPool`], never
//!   raw literal-array table indices;
//! - annotations merge into a single ordered [`Annotation`] list per site;
//! - class/reference types carry a module [`ClassId`] ([`StaticTy::Reference`]);
//! - register counts and accumulator slots do not exist in SSA (`frame` models
//!   only the `[func][new.target][this]` calling convention);
//! - exception handlers are structured [`TryRegion`]s with explicit
//!   [`EdgeKind::Exceptional`] CFG edges.
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
//!   table; [`Op::DefineFunc`] carries explicit captures; `params` are
//!   the vendored frame slots (see [`frame`]).
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
#![cfg_attr(not(test), deny(clippy::unwrap_used))]

pub mod consts;
pub mod effects;
pub mod frame;
pub mod function;
pub mod id;
pub mod module;
pub mod op;
pub mod symbol;
pub mod ty;
pub mod verify;

pub use consts::{Const, ConstPool};
pub use effects::{AllocKind, CallEffect, Effects, MemClasses};
pub use frame::{FrameSlots, this_param_index};
pub use function::{
    Block, Catch, ColumnEntry, DebugData, Edge, EdgeKind, FunctionData, Inst, LineEntry, Loc,
    LocalName, LocalScope, TryRegion, Value, ValueDef,
};
pub use id::{BlockId, ClassId, ConstId, FieldId, FuncId, InstId, Sym, ValueId};
pub use module::{
    AnnValue, Annotation, ClassData, EsModule, ExportDecl, FieldData, FunctionKind, ImportDecl,
    Modifiers, Module, ModuleRequest, Signature, SourceLang,
};
pub use op::{
    Arity, BinOp, CallKind, CmpOp, ModuleVarKind, Op, PropKey, SuperCheck, SuperKey, UnOp,
};
pub use symbol::SymbolTable;
pub use ty::{DynPrim, StaticTy, Ty};
pub use verify::{
    VerifyError, VerifyErrorKind, VerifyReport, VerifyWarning, VerifyWarningKind, verify_func,
    verify_module,
};
