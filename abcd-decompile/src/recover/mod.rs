//! Stage A — expression recovery (design/decompile.md §4.1).
//!
//! Per-block def-use walk over the lifted SSA:
//!
//! - **Inline** a defining expression into its use when ALL of: single
//!   use — counted per OPERAND SLOT (a value appearing twice in one
//!   instruction is two uses; this both matches the use-def commodity's
//!   notion of a use and bounds the inlined tree to the instruction
//!   count, where site-counting could duplicate a pure subtree
//!   exponentially along a chain); use is in the
//!   same block as the def (the conservative v1 rule — cross-block
//!   inlining is d-P3); the def is not a `Phi`; neither the def nor any
//!   intervening instruction has observable effects
//!   (`Effects.may_call`/`may_throw`/`writes`). Intervening-effect
//!   queries are O(1) over per-block prefix sums.
//! - **Introduce a temporary** otherwise (multi-use, cross-block, across
//!   effect boundaries, phi results). SSA values are single-assignment
//!   by construction, so temporaries are `const` — EXCEPT phi
//!   temporaries, which receive per-predecessor assignments and are
//!   `let`.
//! - **Phi**: each `Phi` result is a temporary; each incoming
//!   `(Edge, ValueId)` becomes a [`Stmt::PhiAssign`] appended at the end
//!   of the corresponding predecessor's statement list (out-of-SSA at
//!   AST level — the placement d-P3 refines).
//! - **ExceptionParam** values become the `catch (e)` binding directly
//!   ([`Stmt::CatchBind`] at the handler head) — no assignment.
//! - The `Throw*` guard family + `AsyncFunctionEnter` are **elided on
//!   purpose** ([`Stmt::Elided`] — documented per op in
//!   [`crate::fitness::elision_reason`]); the hard-7 ops become
//!   documented fallback nodes ([`crate::fitness::fallback_note`]).
//!
//! [`builder_hook`] exposes the `AllocObject`/`AllocArray` own-store
//! sequence for d-P3's literal-fold desugar rule (the fold itself is
//! deliberately NOT Stage A).

use std::collections::{BTreeMap, HashMap, HashSet};

use abcd_analysis::dataflow::UseDefChains;
use abcd_ir::function::{Edge, EdgeKind, Loc, Value, ValueDef};
use abcd_ir::id::{BlockId, FuncId, InstId, ValueId};
use abcd_ir::module::{FunctionKind, Module};
use abcd_ir::op::{CallKind, CmpOp, Op, PropKey, SuperKey};
use abcd_ir::{ConstId, Sym};

use crate::consts::{lit_of, lit_of_sym, render_regexp_flags, sym_regexp_pattern, sym_str};
use crate::expr::{Expr, IterOp, Lit, NodeStatus, ObjEntry};
use crate::fitness::{Fitness, elision_reason, fallback_note, fitness_of, op_name};
use crate::legalize::{Legalizer, is_legal_ident, sanitize};
use crate::names::{
    DecompileIndex, NameScopes, local_name_in, module_slot_fallback, module_slot_names,
    namespace_fallback, op_name_hint,
};

/// One instruction's Stage-A outcome (the coverage histogram's unit).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Outcome {
    /// Mapped to an expression/statement node (emitted or inlined).
    Expressed = 0,
    /// Mapped to a desugaring-plumbing node (operands kept verbatim;
    /// idiomatic surface form is a d-P3 fold rule).
    Plumbing = 1,
    /// Deliberately elided (guard family / async-machinery entry), with
    /// a recorded [`Stmt::Elided`] marker.
    Elided = 2,
    /// Documented fallback node (hard-7 / unrecoverable at Stage A).
    Fallback = 3,
    /// Unused and effect-free: legitimately dead (not emitted).
    DeadPure = 4,
}

/// Per-op coverage counters.
#[derive(Clone, Debug, Default)]
pub struct OpStat {
    /// The op's §5 fitness class.
    pub fitness: Option<Fitness>,
    /// Counts per [`Outcome`] (indexed by the outcome's discriminant).
    pub counts: [usize; 5],
}

impl OpStat {
    /// Record one outcome.
    pub fn add(&mut self, fitness: Fitness, outcome: Outcome) {
        self.fitness = Some(fitness);
        self.counts[outcome as usize] += 1;
    }

    /// The count of one outcome.
    pub fn get(&self, outcome: Outcome) -> usize {
        self.counts[outcome as usize]
    }
}

/// A recovered statement (block-local; d-P3 re-parents these into the
/// structured region tree).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    /// A temporary introduction: `const name = value` (`mutable = false`;
    /// the single-assignment proof for `const` is SSA itself).
    Declare {
        /// The legalized temporary name.
        name: String,
        /// `let` vs `const` (only phi temporaries are `let` — see
        /// [`Stmt::PhiDecl`]).
        mutable: bool,
        /// The initializer.
        value: Expr,
        /// The SSA value behind the temporary (provenance).
        value_id: ValueId,
    },
    /// A phi temporary without initializer (`let name;`); the incoming
    /// values arrive as [`Stmt::PhiAssign`]s on the predecessor edges.
    PhiDecl {
        /// The legalized temporary name.
        name: String,
        /// The phi's SSA result value.
        value_id: ValueId,
    },
    /// An out-of-SSA phi assignment, appended at the END of the
    /// predecessor block's statement list.
    PhiAssign {
        /// The phi temporary.
        target: String,
        /// The incoming value.
        value: Expr,
        /// The phi's home block (the edge destination).
        to: BlockId,
        /// Whether the incoming edge is exceptional (N38: handler phis
        /// stay temporaries, never folded).
        exceptional: bool,
    },
    /// An expression statement (a result whose value is unused but whose
    /// effects are observable — e.g. a call, a `yield` in statement
    /// position, a plumbing node).
    Expr(Expr),
    /// `object.name = value` (or own-property `CreateDataProperty`
    /// semantics when `own` — §5 rows 16–18; folds into literals at d-P3).
    StoreProp {
        /// The receiver.
        object: Expr,
        /// The raw property name.
        name: String,
        /// Whether dot form is legal for `name`.
        dot_legal: bool,
        /// The stored value.
        value: Expr,
        /// Own-property (define) semantics vs ordinary assignment.
        own: bool,
    },
    /// `object[index] = value` (`own` as above).
    StoreIndex {
        /// The receiver.
        object: Expr,
        /// The index.
        index: Expr,
        /// The stored value.
        value: Expr,
        /// Own-property (define) semantics.
        own: bool,
    },
    /// `object[key] = value` with a computed key (`own` as above).
    StoreDyn {
        /// The receiver.
        object: Expr,
        /// The computed key.
        key: Expr,
        /// The stored value.
        value: Expr,
        /// Own-property (define) semantics.
        own: bool,
    },
    /// `DefineMethod` — method syntax in literal/class reconstruction at
    /// d-P3; `length` is a runtime property, dropped at emission.
    DefineMethod {
        /// The home object.
        object: Expr,
        /// The method name.
        name: String,
        /// The method closure.
        func: Expr,
        /// The declared `.length` payload.
        length: u16,
    },
    /// `object.#name = value` (`define = true`: class-field definition
    /// semantics — folds into class-field declarations at d-P3).
    StorePrivate {
        /// The receiver.
        object: Expr,
        /// The private name (WITHOUT `#`).
        name: String,
        /// The stored/defined value.
        value: Expr,
        /// Definition (`DefinePrivate`) vs assignment (`StorePrivate`).
        define: bool,
    },
    /// `super.name = value` / `super[key] = value`.
    StoreSuper {
        /// The named key (iff `key` is `None`).
        name: Option<String>,
        /// The computed key (iff `name` is `None`).
        key: Option<Expr>,
        /// The stored value.
        value: Expr,
    },
    /// A lexical-binding store: `name = value` (declaration-vs-assignment
    /// reconstruction is d-P3 scope work).
    LexStore {
        /// The scope-chain level (provenance).
        level: u16,
        /// The slot (provenance).
        slot: u16,
        /// Whether the target frame was pushed inside this function (`true`)
        /// vs inherited from an enclosing closure (`false`).
        own: bool,
        /// The resolved binding name (NOT legalized — lexical bindings
        /// are source identifiers; d-P3's scope reconstruction owns the
        /// final namespace).
        name: String,
        /// The stored value.
        value: Expr,
    },
    /// `name = value` at global scope (`tolerant`: the `TryStoreGlobal`
    /// absence-tolerant form — invisible in source). N72-C4 fold:
    /// `StoreGlobalRecord` (the global LEXICAL record declaration)
    /// also recovers here — the emitted module-scope
    /// `var name; name = value;` (emit.rs predeclaration) is the
    /// validated honest surface: inside the emitted module the binding
    /// shadows the global object exactly like the source-level lexical
    /// record did, and the const/let/object distinction has no
    /// execution-observable module-scope spelling (dream gate).
    GlobalStore {
        /// The raw global name.
        name: String,
        /// The stored value.
        value: Expr,
        /// Absence-tolerant form.
        tolerant: bool,
    },
    /// A module-local slot store (gap G2: synthetic name).
    ModuleStore {
        /// The module slot.
        index: u32,
        /// The (synthetic) binding name.
        name: String,
        /// The stored value.
        value: Expr,
    },
    /// `NewLexEnv*` — a scope-entry marker (consumed by d-P3's scope
    /// reconstruction, never emitted as JS).
    ScopePush {
        /// Slot names of the pushed frame (`None` = unnamed, gap G1).
        names: Vec<Option<String>>,
    },
    /// `PopLexEnv` — a scope-exit marker (never emitted as JS).
    ScopePop,
    /// `CreatePrivateNames` — private-name registration (folds into
    /// class-body declarations at d-P3; the naming source for the
    /// private-name ops).
    PrivateNames {
        /// The registered names (WITHOUT `#`).
        names: Vec<String>,
    },
    /// `throw value`.
    Throw(Expr),
    /// `return value?`.
    Return(Option<Expr>),
    /// Unconditional branch (structurer input; never emitted directly).
    Branch {
        /// Target block.
        dest: BlockId,
    },
    /// Conditional branch; the condition expression is emitted at the
    /// region head by d-P3.
    CondBranch {
        /// The condition.
        cond: Expr,
        /// Truthy target.
        true_dest: BlockId,
        /// Falsy target.
        false_dest: BlockId,
    },
    /// The `catch (e)` binding of a handler block (its
    /// `ExceptionParam` value), at the handler head.
    CatchBind {
        /// The legalized binding name.
        name: String,
    },
    /// A deliberately elided op (guard family / async-machinery entry),
    /// with the documented reason — loud, never silent.
    Elided {
        /// The op name.
        op: &'static str,
        /// The documented elision reason (§5 row).
        reason: &'static str,
        /// Source location, when present.
        loc: Option<Loc>,
    },
    /// A documented fallback statement (an op Stage A cannot express).
    Fallback {
        /// The op name.
        op: &'static str,
        /// Why this is a fallback.
        note: &'static str,
        /// Source location, when present.
        loc: Option<Loc>,
    },
    /// `Unreachable` (dead control point).
    Unreachable,
    /// `debugger;`.
    Debugger,
}

/// One block's recovered statements.
#[derive(Clone, Debug, PartialEq)]
pub struct BlockStmts {
    /// The block.
    pub block: BlockId,
    /// The block's incoming edges (for the dump's provenance line).
    pub preds: Vec<Edge>,
    /// The statements, in program order (phi assignments from successor
    /// phis trail the block's own statements).
    pub stmts: Vec<Stmt>,
}

/// The Stage-A result for one function.
#[derive(Clone, Debug)]
pub struct RecoveredFunc {
    /// The function.
    pub func: FuncId,
    /// The function's raw name.
    pub name: String,
    /// Its kind.
    pub kind: FunctionKind,
    /// The legalized parameter names (the `this` slot is named `this`).
    pub params: Vec<String>,
    /// Hidden leading ABI slots in `params` (3 for es2abc `<static>`
    /// functions: funcobj/newtarget/this; 1 otherwise, 0 for empty).
    /// Emitted JS signatures drop them: `params[hidden..]`.
    pub hidden_params: usize,
    /// The per-block statement lists, in `func.blocks` order.
    pub blocks: Vec<BlockStmts>,
    /// The per-op coverage histogram.
    pub histogram: BTreeMap<&'static str, OpStat>,
}

/// The d-P3 literal-fold hook: the own-store/spread/proto sequence
/// targeting an `AllocObject`/`AllocArray` result, in program order
/// (block order, then instruction order). Stage A keeps these as
/// ordinary statements; this hook enumerates them for the fold rule.
pub fn builder_hook(module: &Module, chains: &UseDefChains, alloc: ValueId) -> Vec<InstId> {
    let order: HashMap<BlockId, usize> = module
        .func(chains.func)
        .map(|f| f.blocks.iter().enumerate().map(|(i, b)| (*b, i)).collect())
        .unwrap_or_default();
    let mut out: Vec<(usize, usize, InstId)> = Vec::new();
    for user in chains.users_of(alloc) {
        let Some(inst) = module.inst(*user) else {
            continue;
        };
        let is_builder_op = matches!(
            inst.op,
            Op::StoreOwnPropName { .. }
                | Op::StoreOwnPropDyn { .. }
                | Op::StoreOwnPropIdx { .. }
                | Op::StoreProp { .. }
                | Op::StorePropIdx { .. }
                | Op::StorePropDyn { .. }
                | Op::CopyDataProps { .. }
                | Op::SetObjectWithProto { .. }
                | Op::ArraySpread { .. }
                | Op::DefineMethod { .. }
                | Op::DefineGetterSetterByValue { .. }
        );
        if is_builder_op {
            let bi = order.get(&inst.block).copied().unwrap_or(usize::MAX);
            out.push((bi, user.index(), *user));
        }
    }
    out.sort();
    out.into_iter().map(|(_, _, i)| i).collect()
}

/// Run Stage A over one function.
pub fn recover_func(module: &Module, func: FuncId) -> RecoveredFunc {
    Recover::new(module, func, None).run()
}

/// Run Stage A over one function using a shared module-level [`DecompileIndex`]
/// (#29).
pub fn recover_func_with_index(
    module: &Module,
    func: FuncId,
    index: &DecompileIndex,
) -> RecoveredFunc {
    Recover::new(module, func, Some(index)).run()
}

/// The decompilation kind of a function: the file-metadata kind,
/// upgraded on definitive BODY evidence (design/decompile.md §5).
///
/// OHOS 3.2-era files (format 9.0.0.0) do not tag async functions in
/// the method metadata — an async method reads `FunctionKind::Function`
/// while its body carries the full es2abc async machinery
/// (`AsyncFunctionEnter` + the per-await suspend/resume plumbing).
/// Trusting the metadata emitted `await` into a non-async body (a JS
/// syntax error rejected by the `es2abc` recompile gate on wild OHOS 3.2
/// packages — design/decompile.md). es2abc emits
/// `AsyncFunctionEnter` ONLY for async functions (es2panda
/// `asyncFunctionBuilder.cpp` `Prepare`), so its presence is decisive:
/// a metadata-plain function carrying the entry op IS async. The
/// upgrade restores the source truth (the `async` keyword) and
/// unblocks the kind-gated async folds. Generator kinds are never
/// rewritten (the async-generator entry protocol carries NO
/// `AsyncFunctionEnter`); a missing body keeps the metadata.
pub fn effective_kind(module: &Module, func: FuncId) -> FunctionKind {
    let Some(f) = module.func(func) else {
        return FunctionKind::Function;
    };
    let upgraded = match f.kind {
        FunctionKind::Function => FunctionKind::Async,
        FunctionKind::Arrow => FunctionKind::AsyncArrow,
        _ => return f.kind,
    };
    let has_enter = f.blocks.iter().any(|b| {
        module.block(*b).is_some_and(|bl| {
            bl.insts.iter().any(|iid| {
                module
                    .inst(*iid)
                    .is_some_and(|i| matches!(i.op, Op::AsyncFunctionEnter))
            })
        })
    });
    if has_enter { upgraded } else { f.kind }
}

/// Whether an op acts as a Stage-A expression-inlining barrier (§4.1).
///
/// Value-compute operators (`BinaryOp`, `UnaryOp`, `Compare`) and
/// `GetPropIterator` (`for..in` header plumbing) inline into their single
/// same-block consumer when no side-effecting call/property/store barrier
/// intervenes; unused occurrences still stay live statements via
/// [`abcd_ir::Effects::is_removable_if_unused`] (`ADR-16` / `R2-D2`).
pub(super) fn inline_barrier(op: &Op) -> bool {
    match op {
        Op::BinaryOp { .. }
        | Op::UnaryOp { .. }
        | Op::Compare { .. }
        | Op::GetPropIterator { .. }
        | Op::AsyncGeneratorResolve { .. }
        | Op::SetGeneratorState { .. }
        | Op::NotifyConcurrentResult { .. }
        | Op::GetModuleNamespace { .. } => false,
        Op::LoadModuleVar { kind, .. } if !kind.is_lazy() => false,
        _ => !op.effects().is_removable_if_unused(),
    }
}

/// A synthetic `new ErrorKind("message")` expression for the
/// materialized unconditional guards (N74-W4).
pub(super) fn new_error(kind: &str, message: String) -> Expr {
    Expr::Call {
        callee: Box::new(Expr::Ident(kind.to_string())),
        this: None,
        args: vec![Expr::Lit(Lit::String(message))],
        kind: CallKind::New,
    }
}

/// Whether `v` is provably the TDZ hole constant (through `Mov`s).
pub(super) fn provably_hole(module: &Module, v: ValueId) -> bool {
    let v = chase_mov(module, v);
    matches!(
        const_id_of(module, v).and_then(|cid| module.consts.get(cid)),
        Some(abcd_ir::Const::Hole)
    )
}

/// The base outcome of a result-producing op (before the dead-pure
/// adjustment): hard-7 → Fallback; the desugaring-plumbing set →
/// Plumbing; everything else → Expressed.
pub(super) fn base_outcome(op: &Op) -> Outcome {
    if matches!(fitness_of(op), Fitness::Hard) {
        return Outcome::Fallback;
    }
    match op {
        Op::GetTemplateObject { .. }
        | Op::CreateIterResultObj { .. }
        | Op::GetIterator { .. }
        | Op::GetAsyncIterator { .. }
        | Op::IteratorNext { .. }
        | Op::GetPropIterator { .. }
        | Op::NextPropName { .. }
        | Op::CreateGenerator { .. }
        | Op::CreateAsyncGenerator { .. }
        | Op::ArraySpread { .. }
        | Op::CreateObjectWithExcludedKeys { .. }
        | Op::CopyRestArgs { .. } => Outcome::Plumbing,
        _ => Outcome::Expressed,
    }
}

/// Whether an op is handled at statement level (never inlined, never
/// temp-bound).
pub(super) fn is_statement_op(op: &Op) -> bool {
    matches!(
        op,
        Op::NewLexEnv { .. }
            | Op::NewLexEnvWithName { .. }
            | Op::PopLexEnv
            | Op::CreatePrivateNames { .. }
            | Op::StoreProp { .. }
            | Op::StorePropIdx { .. }
            | Op::StorePropDyn { .. }
            | Op::StoreOwnPropName { .. }
            | Op::StoreOwnPropDyn { .. }
            | Op::StoreOwnPropIdx { .. }
            | Op::DefineMethod { .. }
            | Op::DefineGetterSetterByValue { .. }
            | Op::CopyDataProps { .. }
            | Op::SetObjectWithProto { .. }
            | Op::StorePrivate { .. }
            | Op::DefinePrivate { .. }
            | Op::StoreSuper { .. }
            | Op::PutLexVar { .. }
            | Op::StoreGlobal { .. }
            | Op::StoreGlobalRecord { .. }
            | Op::TryStoreGlobal { .. }
            | Op::StoreModuleVar { .. }
            | Op::Throw { .. }
            | Op::ThrowDeleteSuperProperty
            | Op::Branch { .. }
            | Op::CondBranch { .. }
            | Op::Return { .. }
            | Op::Unreachable
            | Op::Debugger
    )
}

/// One `(pred, to, exceptional)` edge's parallel `PhiAssign` copies.
pub(super) struct PhiEdgeGroup {
    pub(super) pred: BlockId,
    pub(super) to: BlockId,
    pub(super) exceptional: bool,
    pub(super) assigns: Vec<(String, Expr)>,
}

/// A deferred out-of-SSA phi copy collected during the block walk and
/// scheduled per `(pred, to, exceptional)` edge once all blocks are visited.
pub(super) struct PendingPhiAssign {
    pub(super) pred: BlockId,
    pub(super) to: BlockId,
    pub(super) exceptional: bool,
    pub(super) target: String,
    pub(super) value: Expr,
}

pub(super) fn is_self_phi_assign(target: &str, value: &Expr) -> bool {
    matches!(value, Expr::Ident(n) | Expr::Temp { name: n, .. } if n == target)
}

pub(super) fn decode_call_type_slots(
    module: &Module,
    func: &abcd_ir::function::FunctionData,
) -> Option<abcd_ir::frame::FrameSlots> {
    if let Some(slots) = abcd_ir::frame::FrameSlots::from_call_type_annotation(module, func) {
        return Some(slots);
    }
    for ann in &func.annotations {
        let is_call_type = module
            .class(ann.class)
            .and_then(|c| module.sym.resolve(c.descriptor))
            == Some("L_ESCallTypeAnnotation;");
        if !is_call_type {
            continue;
        }
        for (name, value) in &ann.elements {
            if module.sym.resolve(*name) != Some("callType") {
                continue;
            }
            let abcd_ir::module::AnnValue::Const(cid) = value else {
                continue;
            };
            let bits = match module.consts.get(*cid)? {
                abcd_ir::Const::Int8(v) => u32::from(*v),
                abcd_ir::Const::Int32(v) => *v,
                abcd_ir::Const::Int64(v) => *v as u32,
                abcd_ir::Const::UInt64(v) => *v as u32,
                _ => continue,
            };
            return Some(abcd_ir::frame::FrameSlots {
                func: bits & 0b1000 != 0,
                new_target: bits & 0b0010 != 0,
                this: bits & 0b0001 != 0,
            });
        }
    }
    None
}

pub(super) fn mem_classes_overlap(a: abcd_ir::MemClasses, b: abcd_ir::MemClasses) -> bool {
    const CLASSES: [abcd_ir::MemClasses; 6] = [
        abcd_ir::MemClasses::HEAP,
        abcd_ir::MemClasses::LEX_ENV,
        abcd_ir::MemClasses::GLOBAL,
        abcd_ir::MemClasses::MODULE,
        abcd_ir::MemClasses::ITERATOR,
        abcd_ir::MemClasses::PROTOTYPE,
    ];
    CLASSES.iter().any(|&c| a.contains(c) && b.contains(c))
}

/// Whether reordering two instructions with effects `a` and `b` can change
/// observable runtime behavior (return value, memory state, or thrown error).
pub(super) fn effects_conflict(a: abcd_ir::Effects, b: abcd_ir::Effects) -> bool {
    use abcd_ir::effects::CallEffect;
    let a_calls = !matches!(a.may_call, CallEffect::None);
    let b_calls = !matches!(b.may_call, CallEffect::None);
    let a_mutates_or_throws = !a.writes.is_empty() || a.may_throw || a_calls;
    let b_mutates_or_throws = !b.writes.is_empty() || b.may_throw || b_calls;

    if a.may_throw && b_mutates_or_throws {
        return true;
    }
    if b.may_throw && a_mutates_or_throws {
        return true;
    }
    if mem_classes_overlap(a.writes, b.reads)
        || mem_classes_overlap(a.reads, b.writes)
        || mem_classes_overlap(a.writes, b.writes)
    {
        return true;
    }
    if a_calls && (!b.reads.is_empty() || b_mutates_or_throws) {
        return true;
    }
    if b_calls && (!a.reads.is_empty() || a_mutates_or_throws) {
        return true;
    }
    false
}

/// Operands of `op` in the exact left-to-right JS evaluation order produced
/// by Stage A + Stage C (`N36`: `BinaryOp`/`Compare` emit `right OP left`).
pub(super) fn ordered_eval_operands(op: &Op) -> Vec<ValueId> {
    match op {
        Op::BinaryOp { left, right, .. } | Op::Compare { left, right, .. } => {
            vec![*right, *left]
        }
        Op::TestProp { object, key } => match key {
            PropKey::Name(_) => vec![*object],
            PropKey::Index(k) | PropKey::Dynamic(k) => vec![*k, *object],
        },
        Op::Call {
            callee,
            this,
            args,
            kind,
        } => match kind {
            CallKind::Super
            | CallKind::SuperArrow
            | CallKind::SuperSpread
            | CallKind::SuperForwardAllArgs => args.clone(),
            CallKind::New | CallKind::NewSpread => {
                let mut out = Vec::with_capacity(1 + args.len());
                out.push(*callee);
                out.extend_from_slice(args);
                out
            }
            CallKind::Direct | CallKind::Dynamic | CallKind::Apply | CallKind::ClassInit => {
                let mut out = Vec::with_capacity(2 + args.len());
                out.push(*callee);
                if let Some(t) = this {
                    out.push(*t);
                }
                out.extend_from_slice(args);
                out
            }
        },
        Op::StoreProp { object, value, .. }
        | Op::StoreOwnPropName { object, value, .. }
        | Op::DefineMethod {
            object,
            func: value,
            ..
        }
        | Op::StorePrivate {
            obj: object, value, ..
        }
        | Op::DefinePrivate {
            obj: object, value, ..
        } => vec![*object, *value],
        Op::StorePropIdx {
            object,
            index: key,
            value,
        }
        | Op::StoreOwnPropIdx {
            object,
            index: key,
            value,
            ..
        }
        | Op::StorePropDyn { object, key, value }
        | Op::StoreOwnPropDyn {
            object, key, value, ..
        } => vec![*object, *key, *value],
        Op::StoreSuper { key, value, .. } => match key {
            SuperKey::Name(_) => vec![*value],
            SuperKey::Dynamic(k) => vec![*k, *value],
        },
        Op::LoadSuper { key, .. } => match key {
            SuperKey::Name(_) => Vec::new(),
            SuperKey::Dynamic(k) => vec![*k],
        },
        Op::DefineGetterSetterByValue {
            obj,
            key,
            getter,
            setter,
            ..
        } => vec![*obj, *key, *getter, *setter],
        Op::CopyDataProps { dst, src } => vec![*dst, *src],
        Op::SetObjectWithProto { proto, obj } => vec![*obj, *proto],
        Op::ArraySpread { dst, index, src } => vec![*dst, *src, *index],
        Op::DeleteProp { object, key }
        | Op::LoadPropIdx {
            object, index: key, ..
        }
        | Op::LoadPropDyn { object, key } => vec![*object, *key],
        Op::CreateIterResultObj { value, done } => vec![*value, *done],
        Op::AsyncGeneratorResolve {
            genobj,
            value,
            done,
        } => vec![*value, *genobj, *done],
        _ => op.operands(),
    }
}

/// Collect every identifier / temporary name read inside `e` using an
/// explicit heap work-stack (no recursion).
pub(super) fn collect_expr_reads(e: &Expr) -> HashSet<String> {
    let mut reads = HashSet::new();
    let mut stack = vec![e];
    while let Some(cur) = stack.pop() {
        match cur {
            Expr::Ident(n) | Expr::Temp { name: n, .. } => {
                reads.insert(n.clone());
            }
            _ => {
                stack.extend(crate::folds::expr_children(cur));
            }
        }
    }
    reads
}

pub(super) struct Recover<'m> {
    pub(super) module: &'m Module,
    pub(super) index: Option<&'m DecompileIndex>,
    pub(super) func: FuncId,
    pub(super) chains: UseDefChains,
    pub(super) scopes: NameScopes,
    pub(super) legal: Legalizer,
    /// Values inlined at their single use (the strict §4.1 rule).
    pub(super) inline: HashSet<ValueId>,
    /// Passthrough aliases (`DefineMethod` result → its `func` operand,
    /// `DefineGetterSetterByValue` result → its `obj` operand — vendor
    /// `acc: inout:top` passthroughs, isa.yaml:1220/1229).
    pub(super) alias: HashMap<ValueId, ValueId>,
    /// Minted temporary names per SSA value.
    pub(super) temp_names: HashMap<ValueId, String>,
    /// Legalized parameter names (`this` slot named `this`).
    pub(super) param_names: Vec<String>,
    pub(super) hidden_params: usize,
    /// Explicit leading ABI frame layout when [`abcd_ir::frame::FrameSlots`]
    /// governs `func` (`None` on legacy unannotated non-static DynamicEcma IR).
    pub(super) frame_slots: Option<abcd_ir::frame::FrameSlots>,
    /// True when `func` is a derived class constructor (`ThrowIfSuperNotCalled`
    /// or direct `super(...)` call), where the entry `this` parameter slot holds
    /// `Hole` (`undefined`) until `super(...)` returns the constructed receiver.
    pub(super) is_derived_ctor: bool,
    /// Bare global/lexical/module/symbol names referenced in `func`, collected
    /// before synthetic fallback `p{i}`/`e` names are minted so fallbacks never
    /// shadow referenced bindings while explicit debug names keep their source spelling.
    pub(super) referenced_bare_names: HashSet<String>,
    /// `ExceptionParam` value → legalized catch binding name.
    pub(super) catch_names: HashMap<ValueId, String>,
    /// Handler block → catch binding names (block-head markers).
    pub(super) handler_binds: HashMap<BlockId, Vec<String>>,
    /// inst → (block, position in block).
    pub(super) inst_pos: HashMap<InstId, (BlockId, usize)>,
    /// block → prefix sums of observable-effect instruction counts.
    pub(super) barriers: HashMap<BlockId, Vec<u32>>,
    /// B2: the class-field fold plan for THIS function when it is the
    /// ctor of a `DefineClass` (lazily computed on the first `Call`).
    pub(super) class_fold: Option<Option<crate::classfold::ClassFieldFold>>,
    /// Fallback G2 map when no [`DecompileIndex`] was supplied.
    pub(super) owned_slot_names: BTreeMap<u32, String>,
    pub(super) histogram: BTreeMap<&'static str, OpStat>,
}

impl<'m> Recover<'m> {
    fn new(module: &'m Module, func: FuncId, index: Option<&'m DecompileIndex>) -> Self {
        let is_derived_ctor = module.func(func).is_some_and(|fd| {
            fd.blocks.iter().any(|&bid| {
                module.block(bid).is_some_and(|bl| {
                    bl.insts.iter().any(|&iid| {
                        module.inst(iid).is_some_and(|inst| {
                            matches!(
                                inst.op,
                                Op::ThrowIfSuperNotCalled { .. }
                                    | Op::Call {
                                        kind: CallKind::Super
                                            | CallKind::SuperSpread
                                            | CallKind::SuperForwardAllArgs,
                                        ..
                                    }
                            )
                        })
                    })
                })
            })
        });
        let mut r = Recover {
            hidden_params: 0,
            module,
            index,
            func,
            chains: UseDefChains::build(module, func),
            scopes: NameScopes::build_with_index(module, func, index),
            legal: Legalizer::new(),
            inline: HashSet::new(),
            alias: HashMap::new(),
            temp_names: HashMap::new(),
            param_names: Vec::new(),
            frame_slots: None,
            is_derived_ctor,
            referenced_bare_names: HashSet::new(),
            catch_names: HashMap::new(),
            handler_binds: HashMap::new(),
            inst_pos: HashMap::new(),
            barriers: HashMap::new(),
            class_fold: None,
            owned_slot_names: BTreeMap::new(),
            histogram: BTreeMap::new(),
        };
        r.precompute_positions();
        r
    }

    fn precompute_positions(&mut self) {
        let Some(f) = self.module.func(self.func) else {
            return;
        };
        for &b in &f.blocks {
            let Some(block) = self.module.block(b) else {
                continue;
            };
            let mut prefix = Vec::with_capacity(block.insts.len() + 1);
            prefix.push(0u32);
            for (pos, &iid) in block.insts.iter().enumerate() {
                self.inst_pos.insert(iid, (b, pos));
                let obs = self
                    .module
                    .inst(iid)
                    .map(|i| inline_barrier(&i.op) as u32)
                    .unwrap_or(0);
                prefix.push(prefix[pos] + obs);
            }
            self.barriers.insert(b, prefix);
        }
    }

    /// Observable-effect instruction count strictly between positions
    /// `from_pos` (exclusive) and `to_pos` (exclusive) of `block`.
    pub(super) fn barrier_count(&self, block: BlockId, from_pos: usize, to_pos: usize) -> u32 {
        let Some(prefix) = self.barriers.get(&block) else {
            return u32::MAX; // unknown block: refuse inlining
        };
        let hi = to_pos.min(prefix.len().saturating_sub(1));
        let lo = (from_pos + 1).min(hi);
        prefix[hi] - prefix[lo]
    }

    pub(super) fn record(&mut self, op: &Op, outcome: Outcome) {
        self.histogram
            .entry(op_name(op))
            .or_default()
            .add(fitness_of(op), outcome);
    }

    fn run(mut self) -> RecoveredFunc {
        let Some(f) = self.module.func(self.func) else {
            return RecoveredFunc {
                func: self.func,
                name: String::new(),
                kind: FunctionKind::Function,
                params: Vec::new(),
                hidden_params: 0,
                blocks: Vec::new(),
                histogram: BTreeMap::new(),
            };
        };
        let name = sym_str(self.module, f.name);
        // Bug A: the body evidence wins over the metadata gap (3.2-era
        // files do not tag async functions) — see [`effective_kind`].
        let kind = effective_kind(self.module, self.func);
        let block_ids = f.blocks.clone();

        self.reserve_module_slot_names();
        self.collect_referenced_bare_names();
        self.mint_params();
        self.mint_catch_names();
        self.reserve_names();
        self.compute_aliases();
        self.compute_inline();

        let mut blocks: Vec<BlockStmts> = Vec::with_capacity(block_ids.len());
        let mut block_index: HashMap<BlockId, usize> = HashMap::new();
        for &b in &block_ids {
            block_index.insert(b, blocks.len());
            let preds = self
                .module
                .block(b)
                .map(|bl| bl.preds.clone())
                .unwrap_or_default();
            let mut stmts = Vec::new();
            if let Some(names) = self.handler_binds.get(&b) {
                for name in names {
                    stmts.push(Stmt::CatchBind { name: name.clone() });
                }
            }
            blocks.push(BlockStmts {
                block: b,
                preds,
                stmts,
            });
        }

        // Phi assignments trail their PREDECESSOR's statements; collect
        // during the walk (a phi block may precede a pred in exotic
        // layouts), then schedule each `(pred, to, exceptional)` parallel-copy
        // group deterministically afterwards.
        let mut phi_tail: Vec<PendingPhiAssign> = Vec::new();

        for &b in &block_ids {
            let insts = self
                .module
                .block(b)
                .map(|bl| bl.insts.clone())
                .unwrap_or_default();
            for iid in insts {
                let Some(inst) = self.module.inst(iid) else {
                    continue;
                };
                let op = inst.op.clone();
                let loc = inst.loc;
                let bi = block_index[&b];
                self.step_inst(iid, &op, loc, b, &mut blocks[bi].stmts, &mut phi_tail);
            }
        }
        self.flush_phi_tail(&mut blocks, &block_index, phi_tail);

        RecoveredFunc {
            func: self.func,
            name,
            kind,
            params: self.param_names.clone(),
            hidden_params: self.hidden_params,
            blocks,
            histogram: self.histogram.clone(),
        }
    }

    fn mint_params(&mut self) {
        self.legal.reserve("this");
        self.legal.reserve("super");
        self.legal.reserve("arguments");
        self.legal.reserve("globalThis");
        let Some(f) = self.module.func(self.func) else {
            return;
        };
        let debug_param_names: Vec<String> = f
            .debug
            .as_ref()
            .map(|d| {
                d.param_names
                    .iter()
                    .map(|s| sym_str(self.module, *s))
                    .collect()
            })
            .unwrap_or_default();
        let n = f.params.len();
        let is_static_method = f.modifiers.contains(abcd_ir::Modifiers::STATIC);
        let slots_opt = if let Some(ann_slots) = decode_call_type_slots(self.module, f) {
            Some(ann_slots)
        } else if self.module.func_dialect(f) == abcd_ir::Dialect::StaticArkTS {
            Some(abcd_ir::frame::FrameSlots::for_static_arkts(
                is_static_method,
            ))
        } else if is_static_method && n >= 3 {
            Some(abcd_ir::frame::FrameSlots::DEFAULT)
        } else {
            None
        };
        self.frame_slots = slots_opt;

        if let Some(slots) = slots_opt {
            let hidden = slots.implicit_count().min(n);
            self.hidden_params = hidden;
            let this_idx = (n >= slots.implicit_count())
                .then(|| slots.this_index())
                .flatten();
            for i in 0..n {
                if i < hidden {
                    let name = if this_idx == Some(i) {
                        "this".to_string()
                    } else {
                        format!("p{i}")
                    };
                    self.param_names.push(name);
                    continue;
                }
                let raw = if debug_param_names.len() == n {
                    debug_param_names.get(i).cloned()
                } else {
                    debug_param_names.get(i - hidden).cloned()
                };
                let name = match raw {
                    Some(explicit) => self.legal.mint(&explicit),
                    None => {
                        let fallback = format!("p{i}");
                        self.legal
                            .mint_avoiding(&fallback, &self.referenced_bare_names)
                    }
                };
                self.param_names.push(name);
            }
        } else {
            // Hand-built non-static DynamicEcma IR with no `callType`
            // annotation keeps the single-slot `params[0] = "this"` convention.
            let hidden = usize::from(n > 0);
            self.hidden_params = hidden;
            for i in 0..n {
                if i == 0 {
                    self.param_names.push("this".to_string());
                    continue;
                }
                let raw = if debug_param_names.len() == n {
                    debug_param_names.get(i).cloned()
                } else {
                    debug_param_names.get(i - hidden).cloned()
                };
                let name = match raw {
                    Some(explicit) => self.legal.mint(&explicit),
                    None => {
                        let fallback = format!("p{i}");
                        self.legal
                            .mint_avoiding(&fallback, &self.referenced_bare_names)
                    }
                };
                self.param_names.push(name);
            }
        }
    }

    fn mint_catch_names(&mut self) {
        let Some(f) = self.module.func(self.func) else {
            return;
        };
        let mut catches: Vec<(BlockId, ValueId)> = Vec::new();
        for tr in &f.try_regions {
            for c in &tr.catches {
                catches.push((c.handler, c.exception));
            }
        }
        let mut handler_names: HashMap<BlockId, String> = HashMap::new();
        for (handler, exc) in catches {
            if let Some(existing) = handler_names.get(&handler).cloned() {
                self.catch_names.entry(exc).or_insert(existing);
                continue;
            }
            if let Some(existing) = self.catch_names.get(&exc).cloned() {
                handler_names.insert(handler, existing.clone());
                self.handler_binds
                    .entry(handler)
                    .or_default()
                    .push(existing);
                continue;
            }
            let hint = self
                .module
                .block(handler)
                .and_then(|b| b.insts.first().copied())
                .and_then(|first| {
                    self.module
                        .func(self.func)
                        .and_then(|f| f.debug.as_ref())
                        .and_then(|d| local_name_in(self.module, d, first))
                });
            let name = match hint {
                Some(explicit) => self.legal.mint(&explicit),
                None => self.legal.mint_avoiding("e", &self.referenced_bare_names),
            };
            handler_names.insert(handler, name.clone());
            self.catch_names.insert(exc, name.clone());
            self.handler_binds.entry(handler).or_default().push(name);
        }
    }

    /// G2: resolve module-var slot names once and reserve them BEFORE
    /// params mint — a source param sharing a binding's name would
    /// otherwise shadow the module-scope `let` the resolved name refers
    /// to (a `StoreModuleVar` prints the resolved name verbatim).
    fn record_env(&self) -> Option<&crate::names::RecordModuleEnv> {
        let cid = self.module.func(self.func)?.class_id;
        self.index?.per_class_env.as_ref()?.get(&cid)
    }

    fn reserve_module_slot_names(&mut self) {
        if let Some(env) = self.record_env() {
            let names: Vec<String> = env
                .external_slots
                .values()
                .chain(env.local_slots.values())
                .chain(env.namespace_slots.values())
                .cloned()
                .collect();
            for n in names {
                self.legal.reserve(&n);
            }
            return;
        }
        if let Some(idx) = self.index {
            for n in idx.slot_names.values() {
                self.legal.reserve(n);
            }
        } else {
            self.owned_slot_names = module_slot_names(self.module);
            for n in self.owned_slot_names.values() {
                self.legal.reserve(n);
            }
        }
    }

    /// The emitted name of a module-var slot: the resolved binding name
    /// when file evidence pinned one (G2), else the synthetic fallback.
    pub(super) fn module_slot_name(&self, index: u32) -> String {
        if let Some(env) = self.record_env() {
            return env.local_name(index);
        }
        let map = match self.index {
            Some(idx) => &idx.slot_names,
            None => &self.owned_slot_names,
        };
        map.get(&index)
            .cloned()
            .unwrap_or_else(|| module_slot_fallback(index))
    }

    pub(super) fn load_module_var_name(&self, index: u32, kind: abcd_ir::ModuleVarKind) -> String {
        if let Some(env) = self.record_env() {
            return match kind {
                abcd_ir::ModuleVarKind::External
                | abcd_ir::ModuleVarKind::SendableExternal
                | abcd_ir::ModuleVarKind::Lazy
                | abcd_ir::ModuleVarKind::LazySendable => env.external_name(index),
                abcd_ir::ModuleVarKind::Local
                | abcd_ir::ModuleVarKind::SendableLocal
                | abcd_ir::ModuleVarKind::SendableClass => env.local_name(index),
            };
        }
        self.module_slot_name(index)
    }

    pub(super) fn module_namespace_name(&self, index: u32) -> String {
        if let Some(env) = self.record_env()
            && let Some(n) = env.namespace_slots.get(&index)
        {
            return n.clone();
        }
        namespace_fallback(index)
    }

    fn collect_referenced_bare_names(&mut self) {
        let Some(f) = self.module.func(self.func) else {
            return;
        };
        for &b in &f.blocks {
            let Some(block) = self.module.block(b) else {
                continue;
            };
            for &iid in &block.insts {
                let Some(inst) = self.module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::TryGetGlobal { name, .. }
                    | Op::StoreGlobal { name, .. }
                    | Op::StoreGlobalRecord { name, .. }
                    | Op::TryStoreGlobal { name, .. } => {
                        let n = sym_str(self.module, *name);
                        self.referenced_bare_names.insert(sanitize(&n));
                    }
                    Op::GetLexVar { .. } | Op::PutLexVar { .. } => {
                        if let Some(n) = self.scopes.name_of(iid) {
                            self.referenced_bare_names.insert(sanitize(n));
                        }
                    }
                    Op::LoadModuleVar { index, kind } => {
                        self.referenced_bare_names
                            .insert(self.load_module_var_name(*index, *kind));
                    }
                    Op::StoreModuleVar { index, .. } => {
                        self.referenced_bare_names
                            .insert(self.module_slot_name(*index));
                    }
                    Op::GetModuleNamespace { index } => {
                        self.referenced_bare_names
                            .insert(self.module_namespace_name(*index));
                    }
                    Op::LoadSymbol => {
                        self.referenced_bare_names.insert("Symbol".to_string());
                    }
                    _ => {}
                }
            }
        }
    }

    /// Reserve every name that can appear as a bare identifier in an
    /// expression (globals, resolved lexvars, module slots) so a
    /// later-minted temporary can never shadow one (`const foo = foo`
    /// would be a TDZ error in emitted JS). Runs AFTER params/catch
    /// bindings are minted (source-level params shadow globals; the
    /// residual flat-namespace collision between a lexvar and a param is
    /// d-P3 scope reconstruction's problem — documented).
    fn reserve_names(&mut self) {
        let Some(f) = self.module.func(self.func) else {
            return;
        };
        for &b in &f.blocks {
            let Some(block) = self.module.block(b) else {
                continue;
            };
            for &iid in &block.insts {
                let Some(inst) = self.module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::TryGetGlobal { name, .. }
                    | Op::StoreGlobal { name, .. }
                    | Op::StoreGlobalRecord { name, .. }
                    | Op::TryStoreGlobal { name, .. } => {
                        let n = sym_str(self.module, *name);
                        self.legal.reserve(&sanitize(&n));
                    }
                    Op::GetLexVar { .. } | Op::PutLexVar { .. } => {
                        if let Some(n) = self.scopes.name_of(iid) {
                            self.legal.reserve(&sanitize(n));
                        }
                    }
                    Op::LoadModuleVar { index, kind } => {
                        let n = self.load_module_var_name(*index, *kind);
                        self.legal.reserve(&n);
                    }
                    Op::StoreModuleVar { index, .. } => {
                        let n = self.module_slot_name(*index);
                        self.legal.reserve(&n);
                    }
                    Op::GetModuleNamespace { index } => {
                        self.legal.reserve(&self.module_namespace_name(*index));
                    }
                    Op::LoadSymbol => {
                        self.legal.reserve("Symbol");
                    }
                    _ => {}
                }
            }
        }
    }

    /// `acc: inout:top` passthroughs (see the `alias` field docs).
    fn compute_aliases(&mut self) {
        let Some(f) = self.module.func(self.func) else {
            return;
        };
        for &b in &f.blocks {
            let Some(block) = self.module.block(b) else {
                continue;
            };
            for &iid in &block.insts {
                let Some(inst) = self.module.inst(iid) else {
                    continue;
                };
                let Some(result) = inst.result else { continue };
                match &inst.op {
                    Op::DefineMethod { func, .. } => {
                        self.alias.insert(result, *func);
                    }
                    Op::DefineGetterSetterByValue { obj, .. } => {
                        self.alias.insert(result, *obj);
                    }
                    _ => {}
                }
            }
        }
    }

    /// The strict §4.1 inline rule.
    fn compute_inline(&mut self) {
        let Some(f) = self.module.func(self.func) else {
            return;
        };
        for &b in &f.blocks {
            let Some(block) = self.module.block(b) else {
                continue;
            };
            for &iid in &block.insts {
                let Some(inst) = self.module.inst(iid) else {
                    continue;
                };
                let Some(result) = inst.result else { continue };
                if self.alias.contains_key(&result) {
                    continue;
                }
                // Never inline: phis; observable defs; statement-level
                // ops (scope markers etc. — handled as statements).
                if inst.op.is_phi() || inline_barrier(&inst.op) || is_statement_op(&inst.op) {
                    continue;
                }
                let plain = self.chains.users_of(result);
                let phi = self.chains.phi_users(result);
                if plain.len() + phi.len() != 1 {
                    continue;
                }
                let Some(&(def_block, def_pos)) = self.inst_pos.get(&iid) else {
                    continue;
                };
                let ok = if let Some(&use_iid) = plain.first() {
                    match self.inst_pos.get(&use_iid) {
                        Some(&(use_block, use_pos)) => {
                            use_block == def_block
                                && use_pos > def_pos
                                && self.barrier_count(def_block, def_pos, use_pos) == 0
                        }
                        None => false,
                    }
                } else if let Some(&(_, edge)) = phi.first() {
                    // The assignment materializes at the END of the
                    // predecessor block: barrier-free from the def to the
                    // block end (same-block rule, edge use), and coercing /
                    // effectful / throwing ops must NEVER inline into
                    // conditional or exceptional `PhiAssign`s (`R5-6a`).
                    let end = self
                        .barriers
                        .get(&def_block)
                        .map(|p| p.len().saturating_sub(1))
                        .unwrap_or(usize::MAX);
                    let eff = inst.op.effects_in(self.module);
                    let uncond_normal_edge = edge.kind == EdgeKind::Normal
                        && self
                            .module
                            .block(def_block)
                            .and_then(|bb| bb.insts.last())
                            .and_then(|&last_iid| self.module.inst(last_iid))
                            .is_some_and(|last_inst| match &last_inst.op {
                                Op::Branch { .. } => true,
                                Op::CondBranch {
                                    true_dest,
                                    false_dest,
                                    ..
                                } => true_dest == false_dest,
                                _ => false,
                            });
                    let phi_safe = eff.is_pure() || uncond_normal_edge;
                    edge.from == def_block
                        && phi_safe
                        && self.barrier_count(def_block, def_pos, end) == 0
                } else {
                    false
                };
                if ok {
                    self.inline.insert(result);
                }
            }
        }
        self.validate_inline_order();
    }

    /// Fixed-point soundness check (`D11`) over `self.inline`:
    ///
    /// 1. No absorbed node `a` (`pos_a < use_pos`) may cross a live instruction
    ///    `m` (`pos_a < pos_m`) whose effective execution point precedes `use_pos`
    ///    when `effects_conflict(eff(a), eff(m))` holds (for example, an
    ///    un-inlined `+obj;` coercion statement between `saved = GetLexVar(x)`
    ///    and `return saved`).
    /// 2. Within a consumer's expression tree walked in exact JS evaluation
    ///    order (`N36`: `BinaryOp`/`Compare` evaluate `right` BEFORE `left`),
    ///    any pair `n_i` before `n_j` whose effects do not commute must have
    ///    `pos(n_i) < pos(n_j)` (so `t1 = a + b; t2 = c + d; f(t2, t1)` evicts
    ///    `t1` rather than reordering `a + b` and `c + d`).
    fn validate_inline_order(&mut self) {
        let Some(f) = self.module.func(self.func) else {
            return;
        };
        let block_ids = f.blocks.clone();
        for &b in &block_ids {
            let Some(block) = self.module.block(b) else {
                continue;
            };
            let inst_ids = block.insts.clone();
            let block_len = inst_ids.len();

            // Collect outgoing phi-edge groups `(to, exceptional) -> Vec<(phi_res, val)>`
            // in deterministic target-block / inst order.
            let mut phi_roots: Vec<Vec<(ValueId, ValueId)>> = Vec::new();
            let mut phi_root_idx: HashMap<(BlockId, bool), usize> = HashMap::new();
            for &tb in &block_ids {
                let Some(tblock) = self.module.block(tb) else {
                    continue;
                };
                for &tiid in &tblock.insts {
                    let Some(tinst) = self.module.inst(tiid) else {
                        continue;
                    };
                    let Op::Phi { entries } = &tinst.op else {
                        break;
                    };
                    let Some(phi_res) = tinst.result else {
                        continue;
                    };
                    for (edge, val) in entries {
                        if edge.from != b {
                            continue;
                        }
                        let key = (tb, edge.kind == EdgeKind::Exceptional);
                        let gi = *phi_root_idx.entry(key).or_insert_with(|| {
                            let idx = phi_roots.len();
                            phi_roots.push(Vec::new());
                            idx
                        });
                        phi_roots[gi].push((phi_res, *val));
                    }
                }
            }

            loop {
                let mut evicted = false;

                // Precompute effective JS execution position of every instruction
                // in `b`: `None` when elided/dead-pure; `Some(root_pos)` otherwise.
                let mut exec_pos: Vec<Option<usize>> = vec![None; block_len];
                let mut eff_of: Vec<abcd_ir::Effects> = Vec::with_capacity(block_len);
                for (pos, &iid) in inst_ids.iter().enumerate() {
                    let Some(inst) = self.module.inst(iid) else {
                        eff_of.push(abcd_ir::Effects::PURE);
                        continue;
                    };
                    let eff = inst.op.effects_in(self.module);
                    eff_of.push(eff);

                    let is_elided = elision_reason(&inst.op).is_some()
                        && !matches!(
                            &inst.op,
                            Op::ThrowUndefinedIfHoleWithName { value, .. }
                                | Op::ThrowUndefinedIfHole { value, .. }
                                if provably_hole(self.module, *value)
                        );
                    if is_elided {
                        continue;
                    }
                    if is_statement_op(&inst.op) || inst.op.is_phi() {
                        if !matches!(
                            &inst.op,
                            Op::Phi { .. }
                                | Op::NewLexEnv { .. }
                                | Op::NewLexEnvWithName { .. }
                                | Op::PopLexEnv
                                | Op::CreatePrivateNames { .. }
                        ) {
                            exec_pos[pos] = Some(pos);
                        }
                        continue;
                    }
                    let Some(mut cur_val) = inst.result else {
                        exec_pos[pos] = Some(pos);
                        continue;
                    };
                    if !self.inline.contains(&cur_val) && !self.alias.contains_key(&cur_val) {
                        let dead_pure = self.chains.all_users(cur_val).is_empty()
                            && inst.op.effects().is_removable_if_unused()
                            && !matches!(inst.op, Op::CopyRestArgs { .. });
                        if !dead_pure {
                            exec_pos[pos] = Some(pos);
                        }
                        continue;
                    }
                    // Chase `inline`/`alias` chain to its root consumer in `b`.
                    let mut root_pos = Some(pos);
                    for _ in 0..block_len + 2 {
                        if let Some(&aliased) = self.alias.get(&cur_val) {
                            let Some(Value {
                                def: ValueDef::Inst(aiid),
                                ..
                            }) = self.module.value(aliased)
                            else {
                                break;
                            };
                            if let Some(&(ab, apos)) = self.inst_pos.get(aiid)
                                && ab == b
                            {
                                root_pos = Some(apos);
                            }
                            cur_val = aliased;
                            continue;
                        }
                        if !self.inline.contains(&cur_val) {
                            break;
                        }
                        if let Some(&use_iid) = self.chains.users_of(cur_val).first() {
                            if let Some(&(ub, upos)) = self.inst_pos.get(&use_iid)
                                && ub == b
                            {
                                root_pos = Some(upos);
                                if let Some(uinst) = self.module.inst(use_iid)
                                    && let Some(ures) = uinst.result
                                {
                                    cur_val = ures;
                                    continue;
                                }
                            }
                            break;
                        } else if !self.chains.phi_users(cur_val).is_empty() {
                            root_pos = Some(block_len);
                            break;
                        } else {
                            break;
                        }
                    }
                    exec_pos[pos] = root_pos;
                }

                // Helper closure: validate one root consumer at `use_pos` with
                // ordered root operand `ValueId`s.
                let check_root =
                    |this: &mut Self, use_pos: usize, root_operands: &[ValueId]| -> bool {
                        // Explicit post-order traversal of inlined expression tree.
                        let mut eval_seq: Vec<(ValueId, usize)> = Vec::new();
                        let mut stack: Vec<(ValueId, bool)> =
                            root_operands.iter().rev().map(|&v| (v, false)).collect();
                        while let Some((raw_v, expanded)) = stack.pop() {
                            let mut v = raw_v;
                            let mut guard = 0usize;
                            while let Some(&target) = this.alias.get(&v) {
                                v = target;
                                guard += 1;
                                if guard > 32 {
                                    break;
                                }
                            }
                            if !this.inline.contains(&v) {
                                continue;
                            }
                            let Some(Value {
                                def: ValueDef::Inst(ciid),
                                ..
                            }) = this.module.value(v)
                            else {
                                continue;
                            };
                            let Some(&(cb, cpos)) = this.inst_pos.get(ciid) else {
                                continue;
                            };
                            if cb != b {
                                continue;
                            }
                            if expanded {
                                eval_seq.push((v, cpos));
                            } else {
                                stack.push((v, true));
                                if let Some(cinst) = this.module.inst(*ciid) {
                                    let ops = ordered_eval_operands(&cinst.op);
                                    for child_v in ops.into_iter().rev() {
                                        stack.push((child_v, false));
                                    }
                                }
                            }
                        }

                        if eval_seq.is_empty() {
                            return false;
                        }

                        let absorbed_pos: HashSet<usize> =
                            eval_seq.iter().map(|&(_, pos)| pos).collect();

                        // Check 1: moving `a` from `pos_a` to `use_pos` must commute
                        // with every un-absorbed live instruction `m` (`pos_m > pos_a`)
                        // that executes before (or on another phi edge at) `use_pos`.
                        for &(vid_a, pos_a) in &eval_seq {
                            let eff_a = eff_of[pos_a];
                            for pos_m in (pos_a + 1)..block_len {
                                if absorbed_pos.contains(&pos_m) || pos_m == use_pos {
                                    continue;
                                }
                                let Some(ep_m) = exec_pos[pos_m] else {
                                    continue;
                                };
                                let reordered =
                                    ep_m < use_pos || (ep_m == use_pos && use_pos == block_len);
                                if reordered && effects_conflict(eff_a, eff_of[pos_m]) {
                                    this.inline.remove(&vid_a);
                                    return true;
                                }
                            }
                        }

                        // Check 2: pairwise evaluation-order monotonicity inside `eval_seq`.
                        for i in 0..eval_seq.len() {
                            let (vid_i, pos_i) = eval_seq[i];
                            let eff_i = eff_of[pos_i];
                            for &(_vid_j, pos_j) in &eval_seq[(i + 1)..] {
                                if pos_i > pos_j && effects_conflict(eff_i, eff_of[pos_j]) {
                                    let victim = eval_seq[(i + 1)..]
                                        .iter()
                                        .find(|&&(_, p)| p == pos_j)
                                        .map(|&(v, _)| v)
                                        .unwrap_or(vid_i);
                                    this.inline.remove(&victim);
                                    return true;
                                }
                            }
                        }

                        false
                    };

                for (pos, &iid) in inst_ids.iter().enumerate() {
                    let Some(inst) = self.module.inst(iid) else {
                        continue;
                    };
                    if let Some(res) = inst.result
                        && (self.inline.contains(&res) || self.alias.contains_key(&res))
                    {
                        continue;
                    }
                    // Guard against dropping effectful operands on `super(...)` calls
                    // where `callee` / `this` are not printed.
                    if let Op::Call {
                        callee,
                        this,
                        kind:
                            CallKind::Super
                            | CallKind::SuperArrow
                            | CallKind::SuperSpread
                            | CallKind::SuperForwardAllArgs,
                        ..
                    } = &inst.op
                    {
                        for unprinted in std::iter::once(*callee).chain(this.iter().copied()) {
                            if self.inline.contains(&unprinted)
                                && let Some(Value {
                                    def: ValueDef::Inst(uiid),
                                    ..
                                }) = self.module.value(unprinted)
                                && let Some(uinst) = self.module.inst(*uiid)
                                && !uinst.op.effects_in(self.module).is_removable_if_unused()
                            {
                                self.inline.remove(&unprinted);
                                evicted = true;
                            }
                        }
                        if evicted {
                            break;
                        }
                    }
                    let ops = ordered_eval_operands(&inst.op);
                    if check_root(self, pos, &ops) {
                        evicted = true;
                        break;
                    }
                }

                if !evicted {
                    for group in &phi_roots {
                        let ordered_vals = self.schedule_phi_eval_order(group);
                        if check_root(self, block_len, &ordered_vals) {
                            evicted = true;
                            break;
                        }
                    }
                }

                if !evicted {
                    break;
                }
            }
        }
    }
}

mod ops;
mod phi;
#[cfg(test)]
mod tests;

use ops::{chase_mov, const_id_of};
