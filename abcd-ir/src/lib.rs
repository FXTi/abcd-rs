//! # abcd-ir — the SSA IR
//!
//! Format-independent Static Single Assignment intermediate representation for
//! ArkCompiler bytecode programs (`design/ir.md`; design rulings in
//! `design/decisions.md`): identity tables, module/function arenas, the 94-op
//! taxonomy, the effects table, the type lattice, the dual-dialect calling
//! convention (`D6`, [`Module::dialect`]), iterative Semi-NCA dominance, and
//! the structural verifier. Lifting (`abcd-lift`,
//! container → IR), optimization (`abcd-opt`, IR → IR), and lowering
//! (`abcd-lower`, IR → container) live in separate crates.
//!
//! ## Format independence (structurally enforced)
//!
//! The IR describes a **program** — classes, functions, value flow, types,
//! annotations, module records, debug info — never a serialized **file**.
//! This crate's `Cargo.toml` declares **no dependency** on `abcd-file`,
//! `abcd-isa`, `abcd-file-sys`, or `abcd-isa-sys`, and never may
//! (`design/ir.md`):
//!
//! - file-header identity (`version`, `file_type`) stays outside the IR;
//! - entity identity uses [`FuncId`], [`ClassId`], and [`SymbolTable`], never
//!   raw 32-bit file offsets;
//! - strings intern losslessly as [`Sym`]s (valid UTF-8 or raw MUTF-8 bytes);
//! - literal shapes live as typed [`Const`] trees in [`ConstPool`], never
//!   raw literal-array table indices;
//! - annotations merge into a single ordered [`Annotation`] list per site;
//! - class/reference types carry a module [`ClassId`] ([`StaticTy::Reference`]);
//! - register counts and accumulator slots do not exist in SSA ([`frame`] and
//!   [`Dialect`] model the explicit calling convention: dynamic ECMAScript
//!   `[func][new.target][this]` hidden leading slots vs static ArkTS `H = 0`
//!   static / `params[0] = this` instance frames);
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
//! - **T4** — one [`Op::Call`] with [`CallKind`] + the call-binding
//!   table (`design/ir.md`); [`Op::DefineFunc`] carries explicit captures;
//!   `params` follow the callee's [`FrameSlots`] per [`Dialect`] (see [`frame`]).
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
//! - **T10** — params/return/exception wiring follows the call-binding
//!   table (`design/ir.md`) per [`CallKind`] and [`FrameSlots`].
//!
//! ## Library rule
//!
//! No panics on data: every lookup returns `Option`, every fallible
//! finding is collected into [`VerifyReport`]; error types derive
//! `thiserror::Error`.

#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]

pub mod cfg;
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

pub use cfg::{
    DomTree, ExceptionHandlerMap, IndexedDom, augmented_succs, augmented_succs_with_map,
    block_succs, compute_rpo, compute_rpo_with, inst_succs, normal_succs_inline,
};
pub use consts::{Const, ConstPool, LitMethodKind, TypedArrayTag};
pub use effects::{AllocKind, CallEffect, Effects, MemClasses};
pub use frame::{FrameSlots, this_param_index};
pub use function::{
    Block, Catch, ColumnEntry, DebugData, Edge, EdgeKind, FunctionData, Inst, LineEntry, Loc,
    LocalName, LocalScope, TryRegion, Value, ValueDef,
};
pub use id::{BlockId, ClassId, ConstId, FieldId, FuncId, InstId, Sym, ValueId};
pub use module::{
    AnnValue, Annotation, ClassData, Dialect, EsModule, ExportDecl, FieldData, FunctionKind,
    ImportDecl, Modifiers, Module, ModuleRequest, Signature, SourceLang,
};
pub use op::{
    Arity, BinOp, CallKind, CmpOp, DefineClassData, LexEnvKind, MemberAttrs, ModuleVarKind, Op,
    OwnStoreKind, PropKey, SuperCheck, SuperKey, UnOp,
};
pub use symbol::SymbolTable;
pub use ty::{DynPrim, StaticTy, Ty};
pub use verify::{
    VerifyError, VerifyErrorKind, VerifyReport, VerifyWarning, VerifyWarningKind, verify_func,
    verify_module,
};
