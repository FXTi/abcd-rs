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
#[derive(Clone, Debug, PartialEq)]
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
fn inline_barrier(op: &Op) -> bool {
    match op {
        Op::BinaryOp { .. }
        | Op::UnaryOp { .. }
        | Op::Compare { .. }
        | Op::GetPropIterator { .. }
        | Op::AsyncGeneratorResolve { .. }
        | Op::SetGeneratorState { .. }
        | Op::NotifyConcurrentResult { .. } => false,
        _ => !op.effects().is_removable_if_unused(),
    }
}

/// A synthetic `new ErrorKind("message")` expression for the
/// materialized unconditional guards (N74-W4).
fn new_error(kind: &str, message: String) -> Expr {
    Expr::Call {
        callee: Box::new(Expr::Ident(kind.to_string())),
        this: None,
        args: vec![Expr::Lit(Lit::String(message))],
        kind: CallKind::New,
    }
}

/// Whether `v` is provably the TDZ hole constant (through `Mov`s).
fn provably_hole(module: &Module, v: ValueId) -> bool {
    let v = chase_mov(module, v);
    matches!(
        const_id_of(module, v).and_then(|cid| module.consts.get(cid)),
        Some(abcd_ir::Const::Hole)
    )
}

/// The base outcome of a result-producing op (before the dead-pure
/// adjustment): hard-7 → Fallback; the desugaring-plumbing set →
/// Plumbing; everything else → Expressed.
fn base_outcome(op: &Op) -> Outcome {
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
fn is_statement_op(op: &Op) -> bool {
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
struct PhiEdgeGroup {
    pred: BlockId,
    to: BlockId,
    exceptional: bool,
    assigns: Vec<(String, Expr)>,
}

/// A deferred out-of-SSA phi copy collected during the block walk and
/// scheduled per `(pred, to, exceptional)` edge once all blocks are visited.
struct PendingPhiAssign {
    pred: BlockId,
    to: BlockId,
    exceptional: bool,
    target: String,
    value: Expr,
}

fn is_self_phi_assign(target: &str, value: &Expr) -> bool {
    matches!(value, Expr::Ident(n) | Expr::Temp { name: n, .. } if n == target)
}

fn decode_call_type_slots(
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

fn mem_classes_overlap(a: abcd_ir::MemClasses, b: abcd_ir::MemClasses) -> bool {
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
fn effects_conflict(a: abcd_ir::Effects, b: abcd_ir::Effects) -> bool {
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
fn ordered_eval_operands(op: &Op) -> Vec<ValueId> {
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
fn collect_expr_reads(e: &Expr) -> HashSet<String> {
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

struct Recover<'m> {
    module: &'m Module,
    index: Option<&'m DecompileIndex>,
    func: FuncId,
    chains: UseDefChains,
    scopes: NameScopes,
    legal: Legalizer,
    /// Values inlined at their single use (the strict §4.1 rule).
    inline: HashSet<ValueId>,
    /// Passthrough aliases (`DefineMethod` result → its `func` operand,
    /// `DefineGetterSetterByValue` result → its `obj` operand — vendor
    /// `acc: inout:top` passthroughs, isa.yaml:1220/1229).
    alias: HashMap<ValueId, ValueId>,
    /// Minted temporary names per SSA value.
    temp_names: HashMap<ValueId, String>,
    /// Legalized parameter names (`this` slot named `this`).
    param_names: Vec<String>,
    hidden_params: usize,
    /// Explicit leading ABI frame layout when [`abcd_ir::frame::FrameSlots`]
    /// governs `func` (`None` on legacy unannotated non-static DynamicEcma IR).
    frame_slots: Option<abcd_ir::frame::FrameSlots>,
    /// Bare global/lexical/module/symbol names referenced in `func`, collected
    /// before synthetic fallback `p{i}`/`e` names are minted so fallbacks never
    /// shadow referenced bindings while explicit debug names keep their source spelling.
    referenced_bare_names: HashSet<String>,
    /// `ExceptionParam` value → legalized catch binding name.
    catch_names: HashMap<ValueId, String>,
    /// Handler block → catch binding names (block-head markers).
    handler_binds: HashMap<BlockId, Vec<String>>,
    /// inst → (block, position in block).
    inst_pos: HashMap<InstId, (BlockId, usize)>,
    /// block → prefix sums of observable-effect instruction counts.
    barriers: HashMap<BlockId, Vec<u32>>,
    /// B2: the class-field fold plan for THIS function when it is the
    /// ctor of a `DefineClass` (lazily computed on the first `Call`).
    class_fold: Option<Option<crate::classfold::ClassFieldFold>>,
    /// Fallback G2 map when no [`DecompileIndex`] was supplied.
    owned_slot_names: BTreeMap<u32, String>,
    histogram: BTreeMap<&'static str, OpStat>,
}

impl<'m> Recover<'m> {
    fn new(module: &'m Module, func: FuncId, index: Option<&'m DecompileIndex>) -> Self {
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
    fn barrier_count(&self, block: BlockId, from_pos: usize, to_pos: usize) -> u32 {
        let Some(prefix) = self.barriers.get(&block) else {
            return u32::MAX; // unknown block: refuse inlining
        };
        let hi = to_pos.min(prefix.len().saturating_sub(1));
        let lo = (from_pos + 1).min(hi);
        prefix[hi] - prefix[lo]
    }

    fn record(&mut self, op: &Op, outcome: Outcome) {
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
        let slots_opt = if self.module.func_dialect(f) == abcd_ir::Dialect::StaticArkTS {
            Some(abcd_ir::frame::FrameSlots::for_static_arkts(
                is_static_method,
            ))
        } else if let Some(ann_slots) = decode_call_type_slots(self.module, f) {
            Some(ann_slots)
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
        for (handler, exc) in catches {
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
    fn module_slot_name(&self, index: u32) -> String {
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

    fn load_module_var_name(&self, index: u32, kind: abcd_ir::ModuleVarKind) -> String {
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

    fn module_namespace_name(&self, index: u32) -> String {
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
                    // block end (same-block rule, edge use).
                    let end = self
                        .barriers
                        .get(&def_block)
                        .map(|p| p.len().saturating_sub(1))
                        .unwrap_or(usize::MAX);
                    edge.from == def_block && self.barrier_count(def_block, def_pos, end) == 0
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

    /// Compute the exact evaluation order in which `flush_phi_tail` will
    /// evaluate incoming `val` expressions for a single `(pred, to, exceptional)`
    /// phi group `(phi_res, incoming_val)`.
    fn schedule_phi_eval_order(&self, entries: &[(ValueId, ValueId)]) -> Vec<ValueId> {
        let peel = |mut v: ValueId| -> ValueId {
            let mut g = 0usize;
            while let Some(&t) = self.alias.get(&v) {
                v = t;
                g += 1;
                if g > 32 {
                    break;
                }
            }
            v
        };
        if entries.len() <= 1 || entries.iter().all(|&(p, v)| peel(v) == p) {
            return entries.iter().map(|&(_, v)| v).collect();
        }

        let k = entries.len();
        let mut target_id: HashMap<ValueId, usize> = HashMap::with_capacity(k);
        let mut item_tid: Vec<usize> = Vec::with_capacity(k);
        let mut writers_of_tid: Vec<Vec<usize>> = Vec::new();
        for (j, &(phi_res, _)) in entries.iter().enumerate() {
            let tid = *target_id.entry(phi_res).or_insert_with(|| {
                let id = writers_of_tid.len();
                writers_of_tid.push(Vec::new());
                id
            });
            item_tid.push(tid);
            writers_of_tid[tid].push(j);
        }
        let nt = writers_of_tid.len();
        let mut writers_rem: Vec<usize> = writers_of_tid.iter().map(Vec::len).collect();

        let mut read_tids: Vec<Vec<usize>> = Vec::with_capacity(k);
        let mut readers_of_tid: Vec<Vec<usize>> = vec![Vec::new(); nt];
        let mut total_readers_rem: Vec<usize> = vec![0; nt];
        let mut self_reads: Vec<bool> = vec![false; k];
        let mut is_self_noop_cand: Vec<bool> = Vec::with_capacity(k);

        for (i, &(phi_res, val)) in entries.iter().enumerate() {
            is_self_noop_cand.push(peel(val) == phi_res);
            let mut r_tids: Vec<usize> = Vec::new();
            let mut visited: HashSet<ValueId> = HashSet::new();
            let mut stack: Vec<ValueId> = vec![val];
            while let Some(raw) = stack.pop() {
                let v = peel(raw);
                if !visited.insert(v) {
                    continue;
                }
                if self.inline.contains(&v) {
                    if let Some(Value {
                        def: ValueDef::Inst(ciid),
                        ..
                    }) = self.module.value(v)
                        && let Some(cinst) = self.module.inst(*ciid)
                    {
                        stack.extend(ordered_eval_operands(&cinst.op));
                    }
                } else if let Some(&rtid) = target_id.get(&v) {
                    r_tids.push(rtid);
                }
            }
            r_tids.sort_unstable();
            r_tids.dedup();
            for &rtid in &r_tids {
                if rtid == item_tid[i] {
                    self_reads[i] = true;
                }
                readers_of_tid[rtid].push(i);
                total_readers_rem[rtid] += 1;
            }
            read_tids.push(r_tids);
        }

        let mut done = vec![false; k];
        let mut victim_cleared = vec![false; k];
        let mut in_heap = vec![false; k];
        let mut ready_heap: std::collections::BinaryHeap<std::cmp::Reverse<usize>> =
            std::collections::BinaryHeap::new();
        let is_ready = |j: usize,
                        done: &[bool],
                        is_self_noop_cand: &[bool],
                        writers_rem: &[usize],
                        total_readers_rem: &[usize],
                        self_reads: &[bool],
                        item_tid: &[usize]|
         -> bool {
            if done[j] {
                return false;
            }
            let tid = item_tid[j];
            (is_self_noop_cand[j] && writers_rem[tid] == 1)
                || total_readers_rem[tid] == usize::from(self_reads[j])
        };

        for (j, in_h) in in_heap.iter_mut().enumerate().take(k) {
            if is_ready(
                j,
                &done,
                &is_self_noop_cand,
                &writers_rem,
                &total_readers_rem,
                &self_reads,
                &item_tid,
            ) {
                *in_h = true;
                ready_heap.push(std::cmp::Reverse(j));
            }
        }

        let mut remaining = k;
        let mut scan_cursor = 0usize;
        let mut reader_cursor = vec![0usize; nt];
        let mut path_pos: Vec<Option<usize>> = vec![None; k];
        let mut eval_order: Vec<ValueId> = Vec::with_capacity(k);

        while remaining > 0 {
            let mut next_ready = None;
            while let Some(std::cmp::Reverse(j)) = ready_heap.pop() {
                if !done[j] {
                    next_ready = Some(j);
                    break;
                }
            }

            if let Some(j) = next_ready {
                done[j] = true;
                remaining -= 1;
                if !victim_cleared[j] {
                    eval_order.push(entries[j].1);
                }
                let wtid = item_tid[j];
                writers_rem[wtid] -= 1;
                if writers_rem[wtid] == 1 {
                    for &w in &writers_of_tid[wtid] {
                        if !in_heap[w]
                            && is_ready(
                                w,
                                &done,
                                &is_self_noop_cand,
                                &writers_rem,
                                &total_readers_rem,
                                &self_reads,
                                &item_tid,
                            )
                        {
                            in_heap[w] = true;
                            ready_heap.push(std::cmp::Reverse(w));
                        }
                    }
                }
                for rtid in std::mem::take(&mut read_tids[j]) {
                    total_readers_rem[rtid] -= 1;
                    if total_readers_rem[rtid] <= 1 {
                        for &w in &writers_of_tid[rtid] {
                            if !in_heap[w]
                                && is_ready(
                                    w,
                                    &done,
                                    &is_self_noop_cand,
                                    &writers_rem,
                                    &total_readers_rem,
                                    &self_reads,
                                    &item_tid,
                                )
                            {
                                in_heap[w] = true;
                                ready_heap.push(std::cmp::Reverse(w));
                            }
                        }
                    }
                }
                continue;
            }

            while scan_cursor < k && (done[scan_cursor] || victim_cleared[scan_cursor]) {
                scan_cursor += 1;
            }
            let start = if scan_cursor < k {
                scan_cursor
            } else {
                match (0..k).find(|&i| !done[i]) {
                    Some(i) => i,
                    None => break,
                }
            };
            let mut path: Vec<usize> = Vec::new();
            let mut cur = start;
            let victim = loop {
                if let Some(pos) = path_pos[cur] {
                    let v = path[pos..]
                        .iter()
                        .copied()
                        .filter(|&x| !victim_cleared[x])
                        .min()
                        .unwrap_or_else(|| path[pos..].iter().copied().min().unwrap_or(cur));
                    break v;
                }
                path_pos[cur] = Some(path.len());
                path.push(cur);
                let ctid = item_tid[cur];
                let rlist = &readers_of_tid[ctid];
                let cursor = &mut reader_cursor[ctid];
                while *cursor < rlist.len() {
                    let r = rlist[*cursor];
                    if !done[r] && !victim_cleared[r] && r != cur {
                        break;
                    }
                    *cursor += 1;
                }
                if *cursor < rlist.len() {
                    cur = rlist[*cursor];
                } else {
                    break cur;
                }
            };
            for &node in &path {
                path_pos[node] = None;
            }

            eval_order.push(entries[victim].1);
            is_self_noop_cand[victim] = false;
            self_reads[victim] = false;
            victim_cleared[victim] = true;
            for rtid in std::mem::take(&mut read_tids[victim]) {
                total_readers_rem[rtid] -= 1;
                if total_readers_rem[rtid] <= 1 {
                    for &w in &writers_of_tid[rtid] {
                        if !in_heap[w]
                            && is_ready(
                                w,
                                &done,
                                &is_self_noop_cand,
                                &writers_rem,
                                &total_readers_rem,
                                &self_reads,
                                &item_tid,
                            )
                        {
                            in_heap[w] = true;
                            ready_heap.push(std::cmp::Reverse(w));
                        }
                    }
                }
            }
            if !in_heap[victim]
                && is_ready(
                    victim,
                    &done,
                    &is_self_noop_cand,
                    &writers_rem,
                    &total_readers_rem,
                    &self_reads,
                    &item_tid,
                )
            {
                in_heap[victim] = true;
                ready_heap.push(std::cmp::Reverse(victim));
            }
        }

        eval_order
    }

    /// Schedule parallel out-of-SSA `PhiAssign` copies per
    /// `(pred, to, exceptional)` edge so inlined expressions and cyclic phi
    /// updates never clobber a variable before a sibling copy reads it.
    fn flush_phi_tail(
        &mut self,
        blocks: &mut [BlockStmts],
        block_index: &HashMap<BlockId, usize>,
        phi_tail: Vec<PendingPhiAssign>,
    ) {
        let mut groups: Vec<PhiEdgeGroup> = Vec::new();
        let mut group_idx: HashMap<(BlockId, BlockId, bool), usize> = HashMap::new();
        for item in phi_tail {
            if !block_index.contains_key(&item.pred) {
                continue;
            }
            let key = (item.pred, item.to, item.exceptional);
            if let Some(&gi) = group_idx.get(&key) {
                groups[gi].assigns.push((item.target, item.value));
            } else {
                let gi = groups.len();
                group_idx.insert(key, gi);
                groups.push(PhiEdgeGroup {
                    pred: item.pred,
                    to: item.to,
                    exceptional: item.exceptional,
                    assigns: vec![(item.target, item.value)],
                });
            }
        }

        let mut synth_phi_seq: u32 = 0;
        for PhiEdgeGroup {
            pred,
            to,
            exceptional,
            assigns,
        } in groups
        {
            let Some(&bi) = block_index.get(&pred) else {
                continue;
            };
            // Fast path: <= 1 copy or all self-assignments -> byte-identical output.
            if assigns.len() <= 1
                || assigns
                    .iter()
                    .all(|(target, value)| is_self_phi_assign(target, value))
            {
                for (target, value) in assigns {
                    blocks[bi].stmts.push(Stmt::PhiAssign {
                        target,
                        value,
                        to,
                        exceptional,
                    });
                }
                continue;
            }

            let k = assigns.len();
            let mut items: Vec<(String, Expr)> = assigns;

            // Map every target name in this edge group to a dense target id `0..nt`.
            let mut target_id: HashMap<String, usize> = HashMap::with_capacity(k);
            let mut item_tid: Vec<usize> = Vec::with_capacity(k);
            let mut writers_of_tid: Vec<Vec<usize>> = Vec::new();
            for (j, (target, _)) in items.iter().enumerate() {
                let tid = *target_id.entry(target.clone()).or_insert_with(|| {
                    let id = writers_of_tid.len();
                    writers_of_tid.push(Vec::new());
                    id
                });
                item_tid.push(tid);
                writers_of_tid[tid].push(j);
            }
            let nt = writers_of_tid.len();
            let mut writers_rem: Vec<usize> = writers_of_tid.iter().map(Vec::len).collect();

            // Per-copy read target IDs (`read_tids[i]`) and inverse reader lists.
            let mut read_tids: Vec<Vec<usize>> = Vec::with_capacity(k);
            let mut readers_of_tid: Vec<Vec<usize>> = vec![Vec::new(); nt];
            let mut total_readers_rem: Vec<usize> = vec![0; nt];
            let mut self_reads: Vec<bool> = vec![false; k];
            let mut is_self_noop_cand: Vec<bool> = Vec::with_capacity(k);

            for (i, (target, value)) in items.iter().enumerate() {
                is_self_noop_cand.push(is_self_phi_assign(target, value));
                let raw_reads = collect_expr_reads(value);
                let mut r_tids: Vec<usize> = raw_reads
                    .iter()
                    .filter_map(|name| target_id.get(name).copied())
                    .collect();
                r_tids.sort_unstable();
                r_tids.dedup();
                for &rtid in &r_tids {
                    if rtid == item_tid[i] {
                        self_reads[i] = true;
                    }
                    readers_of_tid[rtid].push(i);
                    total_readers_rem[rtid] += 1;
                }
                read_tids.push(r_tids);
            }

            let mut done = vec![false; k];
            let mut victim_cleared = vec![false; k];
            let mut in_heap = vec![false; k];
            let mut ready_heap: std::collections::BinaryHeap<std::cmp::Reverse<usize>> =
                std::collections::BinaryHeap::new();
            let is_ready = |j: usize,
                            done: &[bool],
                            is_self_noop_cand: &[bool],
                            writers_rem: &[usize],
                            total_readers_rem: &[usize],
                            self_reads: &[bool],
                            item_tid: &[usize]|
             -> bool {
                if done[j] {
                    return false;
                }
                let tid = item_tid[j];
                (is_self_noop_cand[j] && writers_rem[tid] == 1)
                    || total_readers_rem[tid] == usize::from(self_reads[j])
            };

            for (j, in_h) in in_heap.iter_mut().enumerate().take(k) {
                if is_ready(
                    j,
                    &done,
                    &is_self_noop_cand,
                    &writers_rem,
                    &total_readers_rem,
                    &self_reads,
                    &item_tid,
                ) {
                    *in_h = true;
                    ready_heap.push(std::cmp::Reverse(j));
                }
            }

            let mut remaining = k;
            let mut scan_cursor = 0usize;
            let mut reader_cursor = vec![0usize; nt];
            let mut path_pos: Vec<Option<usize>> = vec![None; k];
            let mut emitted: Vec<Stmt> = Vec::with_capacity(k + 2);
            let mut decls: Vec<Stmt> = Vec::new();

            while remaining > 0 {
                let mut next_ready = None;
                while let Some(std::cmp::Reverse(j)) = ready_heap.pop() {
                    if !done[j] {
                        next_ready = Some(j);
                        break;
                    }
                }

                if let Some(j) = next_ready {
                    done[j] = true;
                    remaining -= 1;
                    emitted.push(Stmt::PhiAssign {
                        target: items[j].0.clone(),
                        value: items[j].1.clone(),
                        to,
                        exceptional,
                    });
                    let wtid = item_tid[j];
                    writers_rem[wtid] -= 1;
                    if writers_rem[wtid] == 1 {
                        for &w in &writers_of_tid[wtid] {
                            if !in_heap[w]
                                && is_ready(
                                    w,
                                    &done,
                                    &is_self_noop_cand,
                                    &writers_rem,
                                    &total_readers_rem,
                                    &self_reads,
                                    &item_tid,
                                )
                            {
                                in_heap[w] = true;
                                ready_heap.push(std::cmp::Reverse(w));
                            }
                        }
                    }
                    for rtid in std::mem::take(&mut read_tids[j]) {
                        total_readers_rem[rtid] -= 1;
                        if total_readers_rem[rtid] <= 1 {
                            for &w in &writers_of_tid[rtid] {
                                if !in_heap[w]
                                    && is_ready(
                                        w,
                                        &done,
                                        &is_self_noop_cand,
                                        &writers_rem,
                                        &total_readers_rem,
                                        &self_reads,
                                        &item_tid,
                                    )
                                {
                                    in_heap[w] = true;
                                    ready_heap.push(std::cmp::Reverse(w));
                                }
                            }
                        }
                    }
                    continue;
                }

                // Every unscheduled assignment's target is read by another
                // unscheduled assignment; walk `cur -> first active reader(cur)`
                // to locate a directed cycle and break at the smallest index.
                while scan_cursor < k && done[scan_cursor] {
                    scan_cursor += 1;
                }
                if scan_cursor >= k {
                    break;
                }
                let mut path: Vec<usize> = Vec::new();
                let mut cur = scan_cursor;
                let victim = loop {
                    if let Some(pos) = path_pos[cur] {
                        break path[pos..].iter().copied().min().unwrap_or(cur);
                    }
                    path_pos[cur] = Some(path.len());
                    path.push(cur);

                    let tid = item_tid[cur];
                    let rlist = &readers_of_tid[tid];
                    while reader_cursor[tid] < rlist.len() {
                        let cand = rlist[reader_cursor[tid]];
                        if done[cand] || victim_cleared[cand] {
                            reader_cursor[tid] += 1;
                        } else {
                            break;
                        }
                    }
                    let mut found_reader = None;
                    let mut idx = reader_cursor[tid];
                    while idx < rlist.len() {
                        let cand = rlist[idx];
                        if !done[cand] && !victim_cleared[cand] && cand != cur {
                            found_reader = Some(cand);
                            break;
                        }
                        idx += 1;
                    }
                    match found_reader {
                        Some(next) => cur = next,
                        None => break cur,
                    }
                };
                for &node in &path {
                    path_pos[node] = None;
                }

                let tmp = self.legal.mint("phi");
                let synth_vid = ValueId::new(u32::MAX.saturating_sub(synth_phi_seq));
                synth_phi_seq = synth_phi_seq.saturating_add(1);
                decls.push(Stmt::PhiDecl {
                    name: tmp.clone(),
                    value_id: synth_vid,
                });
                let old_val = std::mem::replace(&mut items[victim].1, Expr::Ident(tmp.clone()));
                emitted.push(Stmt::PhiAssign {
                    target: tmp,
                    value: old_val,
                    to,
                    exceptional,
                });
                is_self_noop_cand[victim] = false;
                self_reads[victim] = false;
                victim_cleared[victim] = true;
                for rtid in std::mem::take(&mut read_tids[victim]) {
                    total_readers_rem[rtid] -= 1;
                    if total_readers_rem[rtid] <= 1 {
                        for &w in &writers_of_tid[rtid] {
                            if !in_heap[w]
                                && is_ready(
                                    w,
                                    &done,
                                    &is_self_noop_cand,
                                    &writers_rem,
                                    &total_readers_rem,
                                    &self_reads,
                                    &item_tid,
                                )
                            {
                                in_heap[w] = true;
                                ready_heap.push(std::cmp::Reverse(w));
                            }
                        }
                    }
                }
                if !in_heap[victim]
                    && is_ready(
                        victim,
                        &done,
                        &is_self_noop_cand,
                        &writers_rem,
                        &total_readers_rem,
                        &self_reads,
                        &item_tid,
                    )
                {
                    in_heap[victim] = true;
                    ready_heap.push(std::cmp::Reverse(victim));
                }
            }

            if !decls.is_empty()
                && let Some(entry_blk) = blocks.first_mut()
            {
                let insert_at = entry_blk
                    .stmts
                    .iter()
                    .take_while(|s| matches!(s, Stmt::CatchBind { .. } | Stmt::PhiDecl { .. }))
                    .count();
                entry_blk.stmts.splice(insert_at..insert_at, decls);
            }
            blocks[bi].stmts.extend(emitted);
        }
    }

    /// One instruction → statement(s) (or nothing, when inlined/dead).
    fn step_inst(
        &mut self,
        iid: InstId,
        op: &Op,
        loc: Option<Loc>,
        block: BlockId,
        out: &mut Vec<Stmt>,
        phi_tail: &mut Vec<PendingPhiAssign>,
    ) {
        // 0. Guards that must stay EXECUTABLE (N74-W4): the blanket
        //    elision below is only sound when the emitted source
        //    reproduces the guard's semantics, which fails for:
        //    - `ThrowConstAssignment`: es2abc emits it at a const-store
        //      site; it fires unconditionally when reached. The elision
        //      reason claims "the const binding is reconstructed", but
        //      d-P8 reconstructs lexical bindings as `let`, so the store
        //      would silently succeed (test262 class/name-binding/const).
        //    - `ThrowUndefinedIfHole{,WithName}` whose checked value is
        //      PROVABLY the hole constant: the read IS the TDZ
        //      violation, firing unconditionally (test262 let/const
        //      *-before-initialization rows). A guard whose value is not
        //      provably the hole keeps the §5 elision (the common case:
        //      reads es2abc could not prove post-init statically).
        match op {
            Op::ThrowConstAssignment { name } => {
                self.record(op, Outcome::Expressed);
                let label = match &self.expr_of(*name) {
                    Expr::Lit(Lit::String(s)) => format!(" '{s}'"),
                    _ => String::new(),
                };
                out.push(Stmt::Throw(new_error(
                    "TypeError",
                    format!("Assignment to constant variable{label}."),
                )));
                return;
            }
            Op::ThrowUndefinedIfHoleWithName { name, value }
                if provably_hole(self.module, *value) =>
            {
                self.record(op, Outcome::Expressed);
                let n = sym_str(self.module, *name);
                out.push(Stmt::Throw(new_error(
                    "ReferenceError",
                    format!("Cannot access '{n}' before initialization"),
                )));
                return;
            }
            Op::ThrowUndefinedIfHole { name, value } if provably_hole(self.module, *value) => {
                self.record(op, Outcome::Expressed);
                let label = match &self.expr_of(*name) {
                    Expr::Lit(Lit::String(s)) => s.clone(),
                    _ => "binding".to_string(),
                };
                out.push(Stmt::Throw(new_error(
                    "ReferenceError",
                    format!("Cannot access '{label}' before initialization"),
                )));
                return;
            }
            Op::ThrowNotExists => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Throw(new_error(
                    "ReferenceError",
                    "Variable does not exist".to_string(),
                )));
                return;
            }
            Op::ThrowPatternNonCoercible => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Throw(new_error(
                    "TypeError",
                    "Cannot destructure undefined or null".to_string(),
                )));
                return;
            }
            _ => {}
        }

        // 1. Deliberately elided ops (guards, async entry).
        if let Some(reason) = elision_reason(op) {
            self.record(op, Outcome::Elided);
            out.push(Stmt::Elided {
                op: op_name(op),
                reason,
                loc,
            });
            // AsyncFunctionEnter has a result; if something unexpectedly
            // uses it, bind a loud fallback temp.
            if let Some(result) = self.inst_result(iid)
                && !self.chains.all_users(result).is_empty()
            {
                let name = self.mint_temp(result);
                out.push(Stmt::Declare {
                    name,
                    mutable: false,
                    value: Expr::Fallback {
                        op: op_name(op),
                        note: "async-context value used after elided AsyncFunctionEnter",
                        operands: vec![],
                    },
                    value_id: result,
                });
            }
            return;
        }

        // 1b. B2 class-field fold: the ctor's instance-initializer call
        // is elided when the fold moved its constant private-field
        // definitions into class-field declarations (emit prints
        // `#name = <const>;` — JS class fields initialize at
        // construction, when the ctor ran the initializer).
        if matches!(op, Op::Call { .. }) && self.folded_init_call(iid) {
            self.record(op, Outcome::Elided);
            out.push(Stmt::Elided {
                op: op_name(op),
                reason: "instance-initializer call — es2abc class-field lowering reversed (constant #field definitions are class-field declarations)",
                loc,
            });
            return;
        }

        // 2. Phi → temporary + per-predecessor assignments.
        if let Op::Phi { entries } = op {
            self.record(op, Outcome::Expressed);
            let Some(result) = self.inst_result(iid) else {
                return;
            };
            let name = self.mint_temp(result);
            out.push(Stmt::PhiDecl {
                name: name.clone(),
                value_id: result,
            });
            for (edge, v) in entries {
                let value = self.expr_of(*v);
                phi_tail.push(PendingPhiAssign {
                    pred: edge.from,
                    to: block,
                    exceptional: edge.kind == EdgeKind::Exceptional,
                    target: name.clone(),
                    value,
                });
            }
            return;
        }

        // 3. Statement-level ops (scope markers, control, throws,
        //    stores).
        if is_statement_op(op) {
            self.step_statement_op(iid, op, loc, out);
            return;
        }

        // 4. Result-producing ops: inline / temporary /
        //    expression-statement / dead-pure.
        let Some(result) = self.inst_result(iid) else {
            // A result-less op that escaped the statement classification
            // (defensive — the classification is total): loud fallback.
            self.record(op, Outcome::Fallback);
            out.push(Stmt::Fallback {
                op: op_name(op),
                note: "result-less op outside statement classification",
                loc,
            });
            return;
        };
        if self.inline.contains(&result) || self.alias.contains_key(&result) {
            self.record(op, base_outcome(op));
            return;
        }
        let users = self.chains.all_users(result);
        if users.is_empty() {
            // `CopyRestArgs` is never dead: it carries the rest-param
            // evidence (`...rest` reconstruction, N74-W4) even when the
            // rest array itself is unused (`function(...args) {}` —
            // `.length` still observes it).
            if !op.effects().is_removable_if_unused() || matches!(op, Op::CopyRestArgs { .. }) {
                self.record(op, base_outcome(op));
                let value = self.expr_for(iid, op);
                out.push(Stmt::Expr(value));
            } else {
                self.record(op, Outcome::DeadPure);
            }
            return;
        }
        self.record(op, base_outcome(op));
        let name = self.mint_temp(result);
        let value = self.expr_for(iid, op);
        out.push(Stmt::Declare {
            name,
            mutable: false,
            value,
            value_id: result,
        });
    }

    fn inst_result(&self, iid: InstId) -> Option<ValueId> {
        self.module.inst(iid).and_then(|i| i.result)
    }

    /// B2: `iid` is the ctor's instance-initializer call, folded into
    /// class-field declarations (lazy [`crate::classfold::plan`]).
    fn folded_init_call(&mut self, iid: InstId) -> bool {
        self.class_fold
            .get_or_insert_with(|| {
                crate::classfold::plan_with_index(self.module, self.func, self.index)
            })
            .as_ref()
            .is_some_and(|fold| fold.call_insts.contains(&iid))
    }

    /// Statement-level ops (scope markers, control, throws, stores).
    fn step_statement_op(&mut self, iid: InstId, op: &Op, loc: Option<Loc>, out: &mut Vec<Stmt>) {
        match op {
            Op::NewLexEnv { num_vars, .. } => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::ScopePush {
                    names: vec![None; *num_vars as usize],
                });
                self.emit_env_result_if_used(iid, op, out);
            }
            Op::NewLexEnvWithName {
                num_vars,
                scope_names,
            } => {
                self.record(op, Outcome::Expressed);
                let mut names: Vec<Option<String>> = lit_of(self.module, *scope_names)
                    .and_then(Lit::into_array)
                    .map(|items| items.into_iter().map(Lit::into_string).collect())
                    .unwrap_or_default();
                names.resize(*num_vars as usize, None);
                out.push(Stmt::ScopePush { names });
                self.emit_env_result_if_used(iid, op, out);
            }
            Op::PopLexEnv => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::ScopePop);
            }
            Op::CreatePrivateNames { names, .. } => {
                self.record(op, Outcome::Expressed);
                let names = lit_of(self.module, *names)
                    .and_then(Lit::into_array)
                    .map(|items| items.into_iter().filter_map(Lit::into_string).collect())
                    .unwrap_or_default();
                out.push(Stmt::PrivateNames { names });
            }
            Op::StoreProp {
                object,
                name,
                value,
            }
            | Op::StoreOwnPropName {
                object,
                name,
                value,
                ..
            } => {
                self.record(op, Outcome::Expressed);
                let own = matches!(op, Op::StoreOwnPropName { .. });
                if let Some(s) = self.module.sym.as_str(*name) {
                    let raw = s.to_string();
                    out.push(Stmt::StoreProp {
                        object: self.expr_of(*object),
                        dot_legal: is_legal_ident(&raw),
                        name: raw,
                        value: self.expr_of(*value),
                        own,
                    });
                } else {
                    out.push(Stmt::StoreDyn {
                        object: self.expr_of(*object),
                        key: Expr::Lit(lit_of_sym(self.module, *name)),
                        value: self.expr_of(*value),
                        own,
                    });
                }
            }
            Op::StorePropIdx {
                object,
                index,
                value,
            }
            | Op::StoreOwnPropIdx {
                object,
                index,
                value,
                ..
            } => {
                self.record(op, Outcome::Expressed);
                let own = matches!(op, Op::StoreOwnPropIdx { .. });
                out.push(Stmt::StoreIndex {
                    object: self.expr_of(*object),
                    index: self.expr_of(*index),
                    value: self.expr_of(*value),
                    own,
                });
            }
            Op::StorePropDyn { object, key, value }
            | Op::StoreOwnPropDyn {
                object, key, value, ..
            } => {
                self.record(op, Outcome::Expressed);
                let own = matches!(op, Op::StoreOwnPropDyn { .. });
                out.push(Stmt::StoreDyn {
                    object: self.expr_of(*object),
                    key: self.expr_of(*key),
                    value: self.expr_of(*value),
                    own,
                });
            }
            Op::DefineMethod {
                object,
                name,
                func,
                length,
            } => {
                self.record(op, Outcome::Plumbing);
                out.push(Stmt::DefineMethod {
                    object: self.expr_of(*object),
                    name: sym_str(self.module, *name),
                    func: self.expr_of(*func),
                    length: *length,
                });
            }
            Op::DefineGetterSetterByValue {
                obj,
                key,
                getter,
                setter,
                ..
            } => {
                self.record(op, Outcome::Plumbing);
                // Resolve an `undefined` constant THROUGH the temp
                // indirection: the emitter must see the absence
                // literally, or `get: undefined` clobbers an existing
                // accessor (dream gate: local/class-accessors).
                let undef_through = |v: &ValueId| -> Option<Expr> {
                    let ValueDef::Inst(iid) = self.module.value(*v)?.def else {
                        return None;
                    };
                    let Op::LoadConst(cid) = self.module.inst(iid)?.op else {
                        return None;
                    };
                    match self.module.consts.get(cid)? {
                        abcd_ir::Const::Undefined => Some(Expr::Lit(Lit::Undefined)),
                        _ => None,
                    }
                };
                let getter = undef_through(getter).unwrap_or_else(|| self.expr_of(*getter));
                let setter = undef_through(setter).unwrap_or_else(|| self.expr_of(*setter));
                out.push(Stmt::Expr(Expr::DefineGetterSetter {
                    obj: Box::new(self.expr_of(*obj)),
                    key: Box::new(self.expr_of(*key)),
                    getter: Box::new(getter),
                    setter: Box::new(setter),
                }));
            }
            Op::CopyDataProps { dst, src } => {
                self.record(op, Outcome::Plumbing);
                out.push(Stmt::Expr(Expr::CopyDataProps {
                    dst: Box::new(self.expr_of(*dst)),
                    src: Box::new(self.expr_of(*src)),
                }));
            }
            Op::SetObjectWithProto { proto, obj } => {
                self.record(op, Outcome::Plumbing);
                out.push(Stmt::Expr(Expr::SetObjectWithProto {
                    obj: Box::new(self.expr_of(*obj)),
                    proto: Box::new(self.expr_of(*proto)),
                }));
            }
            Op::StorePrivate { obj, value, .. } | Op::DefinePrivate { obj, value, .. } => {
                self.record(op, Outcome::Expressed);
                let define = matches!(op, Op::DefinePrivate { .. });
                let name = self
                    .scopes
                    .name_of(iid)
                    .map(str::to_string)
                    .unwrap_or_else(|| "p?".to_string());
                out.push(Stmt::StorePrivate {
                    object: self.expr_of(*obj),
                    name,
                    value: self.expr_of(*value),
                    define,
                });
            }
            Op::StoreSuper { key, value, .. } => {
                self.record(op, Outcome::Expressed);
                let (name, key) = match key {
                    SuperKey::Name(s) => (Some(sym_str(self.module, *s)), None),
                    SuperKey::Dynamic(k) => (None, Some(self.expr_of(*k))),
                };
                out.push(Stmt::StoreSuper {
                    name,
                    key,
                    value: self.expr_of(*value),
                });
            }
            Op::PutLexVar {
                level,
                slot,
                value,
                kind,
            } => {
                self.record(op, Outcome::Expressed);
                let name =
                    self.scopes
                        .name_of(iid)
                        .map(str::to_string)
                        .unwrap_or_else(|| match kind {
                            abcd_ir::LexEnvKind::Patch => format!("v999999_{slot}"),
                            abcd_ir::LexEnvKind::Plain | abcd_ir::LexEnvKind::Sendable => {
                                format!("v{level}_{slot}")
                            }
                        });
                let eff_level = match kind {
                    abcd_ir::LexEnvKind::Patch => u16::MAX,
                    abcd_ir::LexEnvKind::Plain | abcd_ir::LexEnvKind::Sendable => *level,
                };
                out.push(Stmt::LexStore {
                    level: eff_level,
                    slot: *slot,
                    name,
                    value: self.expr_of(*value),
                });
            }
            Op::StoreGlobal { name, value }
            | Op::StoreGlobalRecord { name, value, .. }
            | Op::TryStoreGlobal { name, value } => {
                self.record(op, Outcome::Expressed);
                let tolerant = matches!(op, Op::TryStoreGlobal { .. });
                out.push(Stmt::GlobalStore {
                    name: sym_str(self.module, *name),
                    value: self.expr_of(*value),
                    tolerant,
                });
            }
            Op::StoreModuleVar { index, value } => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::ModuleStore {
                    index: *index,
                    name: self.module_slot_name(*index),
                    value: self.expr_of(*value),
                });
            }
            Op::Throw { value } => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Throw(self.expr_of(*value)));
            }
            Op::ThrowDeleteSuperProperty => {
                self.record(op, Outcome::Fallback);
                out.push(Stmt::Fallback {
                    op: op_name(op),
                    note: fallback_note(op),
                    loc,
                });
            }
            Op::Branch { dest } => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Branch { dest: *dest });
            }
            Op::CondBranch {
                cond,
                true_dest,
                false_dest,
            } => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::CondBranch {
                    cond: self.expr_of(*cond),
                    true_dest: *true_dest,
                    false_dest: *false_dest,
                });
            }
            Op::Return { value } => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Return(value.map(|v| self.expr_of(v))));
            }
            Op::Unreachable => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Unreachable);
            }
            Op::Debugger => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Debugger);
            }
            other => {
                // A statement-op classification miss: loud fallback,
                // never silent (the classification is total, so this arm
                // is defensive).
                self.record(other, Outcome::Fallback);
                out.push(Stmt::Fallback {
                    op: op_name(other),
                    note: "statement-op classification miss",
                    loc,
                });
            }
        }
    }

    /// `NewLexEnv*` yields the environment value; SSA consumers are not
    /// expected (the env is implicit), but if one appears, bind it to a
    /// loud fallback temp rather than dropping it.
    fn emit_env_result_if_used(&mut self, iid: InstId, op: &Op, out: &mut Vec<Stmt>) {
        if let Some(result) = self.inst_result(iid)
            && !self.chains.all_users(result).is_empty()
        {
            let name = self.mint_temp(result);
            out.push(Stmt::Declare {
                name,
                mutable: false,
                value: Expr::Fallback {
                    op: op_name(op),
                    note: "lexenv value used as an SSA operand (unexpected)",
                    operands: vec![],
                },
                value_id: result,
            });
        }
    }

    /// The expression for an SSA value: alias/inline/temp resolution.
    fn expr_of(&mut self, v: ValueId) -> Expr {
        self.run_expr_steps(RecStep::Val(v))
    }

    /// Build the expression tree of one instruction's op.
    fn expr_for(&mut self, iid: InstId, op: &Op) -> Expr {
        self.run_expr_steps(RecStep::Inst(iid, op.clone()))
    }

    #[allow(
        clippy::too_many_lines,
        reason = "iterative Stage-A expression tree builder dispatches across all IR Op variants on an explicit heap workstack"
    )]
    fn run_expr_steps(&mut self, root: RecStep) -> Expr {
        let pop_expr = |vals: &mut Vec<Expr>| vals.pop().unwrap_or(Expr::SuperMarker);
        let mut steps: Vec<RecStep> = vec![root];
        let mut vals: Vec<Expr> = Vec::new();
        let mut active_inlines: HashSet<InstId> = HashSet::new();
        let max_aliases = self.module.values.len().max(1);

        while let Some(step) = steps.pop() {
            match step {
                RecStep::PopInline(iid) => {
                    active_inlines.remove(&iid);
                }
                RecStep::Val(mut v) => {
                    for _ in 0..max_aliases {
                        if let Some(&target) = self.alias.get(&v)
                            && target != v
                        {
                            v = target;
                        } else {
                            break;
                        }
                    }
                    let Some(value) = self.module.value(v) else {
                        vals.push(Expr::Fallback {
                            op: "<value>",
                            note: "unknown ValueId (data, not a panic)",
                            operands: vec![],
                        });
                        continue;
                    };
                    match value.def {
                        ValueDef::Param(i) => {
                            let i = i as usize;
                            // Hidden ABI slots read directly: map `new.target` and `funcobj`
                            // under the active `FrameSlots` layout (`#87.4`).
                            if let Some(slots) = self.frame_slots
                                && i < self.hidden_params
                            {
                                let func_idx = slots.func.then_some(0usize);
                                let new_target_idx =
                                    slots.new_target.then_some(slots.func as usize);
                                if new_target_idx == Some(i) {
                                    vals.push(Expr::NewTarget);
                                    continue;
                                }
                                if func_idx == Some(i) {
                                    vals.push(Expr::Fallback {
                                        op: "Param(funcobj)",
                                        note: "the hidden function-object slot has no JS surface form",
                                        operands: vec![],
                                    });
                                    continue;
                                }
                            }
                            vals.push(Expr::Ident(
                                self.param_names
                                    .get(i)
                                    .cloned()
                                    .unwrap_or_else(|| format!("p{i}")),
                            ));
                        }
                        ValueDef::Const(cid) => match lit_of(self.module, cid) {
                            Some(lit) => vals.push(Expr::Lit(lit)),
                            None => vals.push(Expr::Fallback {
                                op: "<const>",
                                note: "unknown ConstId (data, not a panic)",
                                operands: vec![],
                            }),
                        },
                        ValueDef::ExceptionParam(_) => {
                            let name = match self.catch_names.get(&v) {
                                Some(n) => n.clone(),
                                None => {
                                    let n =
                                        self.legal.mint_avoiding("e", &self.referenced_bare_names);
                                    self.catch_names.insert(v, n.clone());
                                    n
                                }
                            };
                            vals.push(Expr::Ident(name));
                        }
                        ValueDef::Inst(iid) => {
                            if self.inline.contains(&v) && active_inlines.insert(iid) {
                                match self.module.inst(iid).map(|i| i.op.clone()) {
                                    Some(op) => {
                                        steps.push(RecStep::PopInline(iid));
                                        steps.push(RecStep::Inst(iid, op));
                                    }
                                    None => {
                                        active_inlines.remove(&iid);
                                        vals.push(Expr::Fallback {
                                            op: "<inst>",
                                            note: "unknown InstId (data, not a panic)",
                                            operands: vec![],
                                        });
                                    }
                                }
                            } else {
                                vals.push(Expr::Temp {
                                    value: v,
                                    name: self.mint_temp(v),
                                });
                            }
                        }
                    }
                }
                RecStep::Inst(iid, op) => match &op {
                    Op::BinaryOp { op, left, right } => {
                        // Operand order (N36): semantic expression is `right OP left`.
                        steps.push(RecStep::BuildBinary(*op));
                        steps.push(RecStep::Val(*left));
                        steps.push(RecStep::Val(*right));
                    }
                    Op::UnaryOp { op, operand } => {
                        steps.push(RecStep::BuildUnary(*op));
                        steps.push(RecStep::Val(*operand));
                    }
                    Op::Compare { op, left, right } => {
                        steps.push(RecStep::BuildCompare(*op));
                        steps.push(RecStep::Val(*left));
                        steps.push(RecStep::Val(*right));
                    }
                    Op::Mov { src } => steps.push(RecStep::Val(*src)),
                    Op::LoadConst(cid) => vals.push(match lit_of(self.module, *cid) {
                        Some(lit) => Expr::Lit(lit),
                        None => Expr::Fallback {
                            op: "LoadConst",
                            note: "unknown ConstId",
                            operands: vec![],
                        },
                    }),
                    Op::AllocObject { shape } => {
                        let expr = match lit_of(self.module, *shape) {
                            Some(mut lit) => match &mut lit {
                                Lit::Object(entries) => Expr::ObjectLit {
                                    entries: std::mem::take(entries),
                                },
                                Lit::Array(items) => match self.parse_shape_buffer(items) {
                                    Some(expr) => expr,
                                    None => Expr::Fallback {
                                        op: "AllocObject",
                                        note: "shape buffer is not a flat key/value array",
                                        operands: vec![],
                                    },
                                },
                                _ => Expr::Fallback {
                                    op: "AllocObject",
                                    note: "shape constant is not an ObjectLiteral",
                                    operands: vec![],
                                },
                            },
                            None => Expr::Fallback {
                                op: "AllocObject",
                                note: "shape constant is not an ObjectLiteral",
                                operands: vec![],
                            },
                        };
                        vals.push(expr);
                    }
                    Op::AllocArray { shape } => {
                        let expr = match shape {
                            None => Expr::ArrayLit { elements: vec![] },
                            Some(cid) => {
                                match lit_of(self.module, *cid).and_then(Lit::into_array) {
                                    Some(elements) => Expr::ArrayLit { elements },
                                    None => Expr::Fallback {
                                        op: "AllocArray",
                                        note: "shape constant is not an ArrayLiteral",
                                        operands: vec![],
                                    },
                                }
                            }
                        };
                        vals.push(expr);
                    }
                    Op::AllocRegExp { pattern, flags } => vals.push(Expr::RegExp {
                        pattern: sym_regexp_pattern(self.module, *pattern),
                        flags: render_regexp_flags(*flags),
                    }),
                    Op::AllocClosure { func } => self.push_closure_of_steps(*func, &mut steps),
                    Op::LoadProp { object, name } => {
                        if let Some(s) = self.module.sym.as_str(*name) {
                            let raw = s.to_string();
                            let dot_legal = is_legal_ident(&raw);
                            steps.push(RecStep::BuildPropName {
                                name: raw,
                                dot_legal,
                            });
                            steps.push(RecStep::Val(*object));
                        } else {
                            let key = Expr::Lit(lit_of_sym(self.module, *name));
                            steps.push(RecStep::BuildPropDynConstKey(Box::new(key)));
                            steps.push(RecStep::Val(*object));
                        }
                    }
                    Op::LoadPropIdx { object, index } => {
                        steps.push(RecStep::BuildPropIndex);
                        steps.push(RecStep::Val(*index));
                        steps.push(RecStep::Val(*object));
                    }
                    Op::LoadPropDyn { object, key } => {
                        steps.push(RecStep::BuildPropDyn);
                        steps.push(RecStep::Val(*key));
                        steps.push(RecStep::Val(*object));
                    }
                    Op::DeleteProp { object, key } => {
                        steps.push(RecStep::BuildDeletePropDyn);
                        steps.push(RecStep::Val(*key));
                        steps.push(RecStep::Val(*object));
                    }
                    Op::TestProp { object, key } => match key {
                        PropKey::Name(s) => {
                            let key_expr = Expr::Lit(lit_of_sym(self.module, *s));
                            steps.push(RecStep::BuildTestPropNamed(Box::new(key_expr)));
                            steps.push(RecStep::Val(*object));
                        }
                        PropKey::Index(k) | PropKey::Dynamic(k) => {
                            steps.push(RecStep::BuildCompare(CmpOp::In));
                            steps.push(RecStep::Val(*object));
                            steps.push(RecStep::Val(*k));
                        }
                    },
                    Op::GetTemplateObject { literal } => {
                        let (raw, cooked) = self.template_strings_of(*literal);
                        vals.push(Expr::TemplateObject { raw, cooked });
                    }
                    Op::CreateIterResultObj { value, done } => {
                        steps.push(RecStep::BuildIterResultObj);
                        steps.push(RecStep::Val(*done));
                        steps.push(RecStep::Val(*value));
                    }
                    Op::GetIterator { obj } => {
                        self.push_iter_step(IterOp::GetIterator, *obj, &mut steps)
                    }
                    Op::GetAsyncIterator { obj } => {
                        self.push_iter_step(IterOp::GetAsyncIterator, *obj, &mut steps)
                    }
                    Op::IteratorNext { iterator } => {
                        self.push_iter_step(IterOp::Next, *iterator, &mut steps)
                    }
                    Op::IteratorReturn { iterator } => {
                        self.push_iter_step(IterOp::Return, *iterator, &mut steps)
                    }
                    Op::IteratorThrow { iterator } => {
                        self.push_iter_step(IterOp::Throw, *iterator, &mut steps)
                    }
                    Op::GetPropIterator { obj } => {
                        self.push_iter_step(IterOp::GetPropIterator, *obj, &mut steps)
                    }
                    Op::NextPropName { iterator } => {
                        self.push_iter_step(IterOp::NextPropName, *iterator, &mut steps)
                    }
                    Op::GetLexVar { .. } => {
                        let name = self
                            .scopes
                            .name_of(iid)
                            .map(str::to_string)
                            .unwrap_or_else(|| "v?".to_string());
                        vals.push(Expr::Ident(sanitize(&name)));
                    }
                    Op::TryGetGlobal { name, .. } => {
                        let expr = if let Some(s) = self.module.sym.as_str(*name) {
                            let raw = s.to_string();
                            if is_legal_ident(&raw) {
                                Expr::Ident(raw)
                            } else {
                                Expr::PropIndex {
                                    object: Box::new(Expr::GlobalThis),
                                    index: Box::new(Expr::Lit(Lit::String(raw))),
                                }
                            }
                        } else {
                            Expr::PropIndex {
                                object: Box::new(Expr::GlobalThis),
                                index: Box::new(Expr::Lit(lit_of_sym(self.module, *name))),
                            }
                        };
                        vals.push(expr);
                    }
                    Op::LoadModuleVar { index, kind } => {
                        vals.push(Expr::Ident(self.load_module_var_name(*index, *kind)));
                    }
                    Op::GetModuleNamespace { index } => {
                        let expr = if let Some(env) = self.record_env()
                            && let Some(ns) = env.namespace_slots.get(index)
                        {
                            Expr::Ident(ns.clone())
                        } else {
                            Expr::ModuleNamespace { index: *index }
                        };
                        vals.push(expr);
                    }
                    Op::DynamicImport { specifier } => {
                        steps.push(RecStep::BuildDynamicImport);
                        steps.push(RecStep::Val(*specifier));
                    }
                    Op::Call {
                        callee,
                        this,
                        args,
                        kind,
                    } => {
                        let super_callee = matches!(
                            kind,
                            CallKind::Super
                                | CallKind::SuperArrow
                                | CallKind::SuperSpread
                                | CallKind::SuperForwardAllArgs
                        );
                        steps.push(RecStep::BuildCall {
                            has_this: this.is_some(),
                            arg_count: args.len(),
                            kind: *kind,
                            super_callee,
                        });
                        for a in args.iter().rev() {
                            steps.push(RecStep::Val(*a));
                        }
                        if let Some(t) = this {
                            steps.push(RecStep::Val(*t));
                        }
                        if !super_callee {
                            steps.push(RecStep::Val(*callee));
                        }
                    }
                    Op::DefineFunc { body, captures, .. } => {
                        self.push_closure_node_steps(*body, captures, &mut steps);
                    }
                    Op::DefineClass(cls) => {
                        self.push_class_node_steps(
                            cls.ctor,
                            cls.heritage,
                            cls.members,
                            cls.member_attrs.clone(),
                            false,
                            &mut steps,
                            &mut vals,
                        );
                    }
                    Op::DefineSendableClass(cls) => {
                        self.push_class_node_steps(
                            cls.ctor,
                            cls.heritage,
                            cls.members,
                            cls.member_attrs.clone(),
                            true,
                            &mut steps,
                            &mut vals,
                        );
                    }
                    Op::LoadPrivate { obj, .. } => {
                        let name = self
                            .scopes
                            .name_of(iid)
                            .map(str::to_string)
                            .unwrap_or_else(|| "p?".to_string());
                        steps.push(RecStep::BuildPrivate { name, test: false });
                        steps.push(RecStep::Val(*obj));
                    }
                    Op::TestPrivate { obj, .. } => {
                        let name = self
                            .scopes
                            .name_of(iid)
                            .map(str::to_string)
                            .unwrap_or_else(|| "p?".to_string());
                        steps.push(RecStep::BuildPrivate { name, test: true });
                        steps.push(RecStep::Val(*obj));
                    }
                    Op::CreateGenerator { func } | Op::CreateAsyncGenerator { func } => {
                        steps.push(RecStep::BuildCreateGenerator);
                        steps.push(RecStep::Val(*func));
                    }
                    Op::SuspendGenerator { value, .. } => {
                        steps.push(RecStep::BuildYield);
                        steps.push(RecStep::Val(*value));
                    }
                    Op::ResumeGenerator { genobj } => {
                        steps.push(RecStep::BuildGenDriver(true));
                        steps.push(RecStep::Val(*genobj));
                    }
                    Op::GetResumeMode { genobj } => {
                        steps.push(RecStep::BuildGenDriver(false));
                        steps.push(RecStep::Val(*genobj));
                    }
                    Op::Await { value } => {
                        steps.push(RecStep::BuildAwait(false));
                        steps.push(RecStep::Val(*value));
                    }
                    Op::AwaitUncaught { value, .. } => {
                        steps.push(RecStep::BuildAwait(true));
                        steps.push(RecStep::Val(*value));
                    }
                    Op::AsyncResolve { value, .. } => {
                        steps.push(RecStep::BuildAsyncDriver(true));
                        steps.push(RecStep::Val(*value));
                    }
                    Op::AsyncReject { value, .. } | Op::AsyncGeneratorReject { value, .. } => {
                        steps.push(RecStep::BuildAsyncDriver(false));
                        steps.push(RecStep::Val(*value));
                    }
                    Op::AsyncGeneratorResolve {
                        genobj,
                        value,
                        done,
                    } => {
                        steps.push(RecStep::BuildAsyncGenResolve);
                        steps.push(RecStep::Val(*done));
                        steps.push(RecStep::Val(*value));
                        steps.push(RecStep::Val(*genobj));
                    }
                    Op::LoadSymbol => vals.push(Expr::Ident("Symbol".to_string())),
                    Op::LoadNewTarget => vals.push(Expr::NewTarget),
                    Op::LoadGlobalObject => vals.push(Expr::GlobalThis),
                    Op::LoadFunction => {
                        let name = self
                            .module
                            .func(self.func)
                            .map(|f| sym_str(self.module, f.name))
                            .unwrap_or_default();
                        vals.push(Expr::SelfFunction(name));
                    }
                    Op::GetUnmappedArgs => vals.push(Expr::Arguments),
                    Op::CopyRestArgs { start_index } => vals.push(Expr::RestArgs {
                        start_index: *start_index,
                    }),
                    Op::LoadSuper { key, .. } => match key {
                        SuperKey::Name(s) => vals.push(Expr::SuperProp {
                            name: Some(sym_str(self.module, *s)),
                            key: None,
                        }),
                        SuperKey::Dynamic(k) => {
                            steps.push(RecStep::BuildSuperDyn);
                            steps.push(RecStep::Val(*k));
                        }
                    },
                    Op::ArraySpread { dst, index, src } => {
                        steps.push(RecStep::BuildArraySpread);
                        steps.push(RecStep::Val(*src));
                        steps.push(RecStep::Val(*index));
                        steps.push(RecStep::Val(*dst));
                    }
                    Op::CreateObjectWithExcludedKeys { obj, keys } => {
                        steps.push(RecStep::BuildRestObject(keys.len()));
                        for k in keys.iter().rev() {
                            steps.push(RecStep::Val(*k));
                        }
                        steps.push(RecStep::Val(*obj));
                    }
                    other => {
                        let op_s = op_name(other);
                        let note_s = fallback_note(other);
                        let ops = other.operands();
                        steps.push(RecStep::BuildFallback {
                            op: op_s,
                            note: note_s,
                            count: ops.len(),
                        });
                        for v in ops.iter().rev() {
                            steps.push(RecStep::Val(*v));
                        }
                    }
                },
                RecStep::BuildBinary(op) => {
                    let right = Box::new(pop_expr(&mut vals));
                    let left = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Binary { op, left, right });
                }
                RecStep::BuildUnary(op) => {
                    let operand = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Unary { op, operand });
                }
                RecStep::BuildCompare(op) => {
                    let right = Box::new(pop_expr(&mut vals));
                    let left = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Compare { op, left, right });
                }
                RecStep::BuildPropName { name, dot_legal } => {
                    let object = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::PropName {
                        object,
                        name,
                        dot_legal,
                    });
                }
                RecStep::BuildPropDynConstKey(key) => {
                    let object = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::PropDyn { object, key });
                }
                RecStep::BuildPropIndex => {
                    let index = Box::new(pop_expr(&mut vals));
                    let object = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::PropIndex { object, index });
                }
                RecStep::BuildPropDyn => {
                    let key = Box::new(pop_expr(&mut vals));
                    let object = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::PropDyn { object, key });
                }
                RecStep::BuildDeletePropDyn => {
                    let key = Box::new(pop_expr(&mut vals));
                    let object = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Delete {
                        target: Box::new(Expr::PropDyn { object, key }),
                    });
                }
                RecStep::BuildTestPropNamed(left) => {
                    let right = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Compare {
                        op: CmpOp::In,
                        left,
                        right,
                    });
                }
                RecStep::BuildIterResultObj => {
                    let done = Box::new(pop_expr(&mut vals));
                    let value = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::IterResultObj { value, done });
                }
                RecStep::BuildIter { op, status } => {
                    let obj = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Iter { op, obj, status });
                }
                RecStep::BuildDynamicImport => {
                    let specifier = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::DynamicImport { specifier });
                }
                RecStep::BuildCall {
                    has_this,
                    arg_count,
                    kind,
                    super_callee,
                } => {
                    let start = vals.len().saturating_sub(arg_count);
                    let args = vals.split_off(start);
                    let this = has_this.then(|| Box::new(pop_expr(&mut vals)));
                    let callee = if super_callee {
                        Box::new(Expr::SuperMarker)
                    } else {
                        Box::new(pop_expr(&mut vals))
                    };
                    vals.push(Expr::Call {
                        callee,
                        this,
                        args,
                        kind,
                    });
                }
                RecStep::BuildClosure {
                    body,
                    name,
                    kind,
                    cap_names,
                } => {
                    let start = vals.len().saturating_sub(cap_names.len());
                    let mut drain = vals.drain(start..);
                    let mut captures = Vec::with_capacity(cap_names.len());
                    for cname in cap_names {
                        captures.push((cname, drain.next().unwrap_or(Expr::SuperMarker)));
                    }
                    drop(drain);
                    vals.push(Expr::Closure {
                        body,
                        name,
                        kind,
                        captures,
                    });
                }
                RecStep::BuildClassWithHeritage {
                    ctor,
                    name,
                    members,
                    member_attrs,
                    sendable,
                } => {
                    let heritage = Some(Box::new(pop_expr(&mut vals)));
                    vals.push(Expr::Class {
                        ctor,
                        name,
                        heritage,
                        members,
                        member_attrs,
                        sendable,
                    });
                }
                RecStep::BuildPrivate { name, test } => {
                    let object = Box::new(pop_expr(&mut vals));
                    vals.push(if test {
                        Expr::PrivateTest { object, name }
                    } else {
                        Expr::PrivateLoad { object, name }
                    });
                }
                RecStep::BuildCreateGenerator => {
                    let func = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::CreateGenerator { func });
                }
                RecStep::BuildYield => {
                    let value = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Yield { value });
                }
                RecStep::BuildGenDriver(resume) => {
                    let genobj = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::GeneratorDriver { resume, genobj });
                }
                RecStep::BuildAwait(uncaught) => {
                    let value = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Await { value, uncaught });
                }
                RecStep::BuildAsyncDriver(resolve) => {
                    let value = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::AsyncDriver { resolve, value });
                }
                RecStep::BuildAsyncGenResolve => {
                    let done = Box::new(pop_expr(&mut vals));
                    let value = Box::new(pop_expr(&mut vals));
                    let genobj = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::AsyncGeneratorResolve {
                        genobj,
                        value,
                        done,
                    });
                }
                RecStep::BuildSuperDyn => {
                    let key = Some(Box::new(pop_expr(&mut vals)));
                    vals.push(Expr::SuperProp { name: None, key });
                }
                RecStep::BuildArraySpread => {
                    let src = Box::new(pop_expr(&mut vals));
                    let index = Box::new(pop_expr(&mut vals));
                    let dst = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::ArraySpread { dst, index, src });
                }
                RecStep::BuildRestObject(count) => {
                    let start = vals.len().saturating_sub(count);
                    let excluded = vals.split_off(start);
                    let obj = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::RestObject { obj, excluded });
                }
                RecStep::BuildFallback { op, note, count } => {
                    let start = vals.len().saturating_sub(count);
                    let operands = vals.split_off(start);
                    vals.push(Expr::Fallback { op, note, operands });
                }
            }
        }

        pop_expr(&mut vals)
    }

    /// Mint (once) the temporary name of an SSA value:
    /// `DebugData.local_names` scope hit → defining-op `Sym` hint →
    /// module/namespace slot fallback → `v{n}`.
    fn mint_temp(&mut self, v: ValueId) -> String {
        if let Some(n) = self.temp_names.get(&v) {
            return n.clone();
        }
        let mut raw: Option<String> = None;
        if let Some(Value {
            def: ValueDef::Inst(iid),
            ..
        }) = self.module.value(v)
        {
            if let Some(d) = self.module.func(self.func).and_then(|f| f.debug.as_ref()) {
                raw = local_name_in(self.module, d, *iid);
            }
            if raw.is_none()
                && let Some(inst) = self.module.inst(*iid)
            {
                raw = match &inst.op {
                    Op::LoadModuleVar { index, kind } => {
                        Some(self.load_module_var_name(*index, *kind))
                    }
                    Op::GetModuleNamespace { index } => Some(self.module_namespace_name(*index)),
                    Op::GetLexVar { .. } => self.scopes.name_of(*iid).map(str::to_string),
                    other => op_name_hint(self.module, other),
                };
            }
        }
        let fallback = format!("v{}", v.index());
        let name = self.legal.mint(raw.as_deref().unwrap_or(&fallback));
        self.temp_names.insert(v, name.clone());
        name
    }

    /// Parse a `createobjectwithbuffer` flat shape buffer: plain
    /// `[key, value]` pairs, plus `[name, MethodRef, attrs]` method
    /// entries (attrs dropped — runtime metadata). Pure key/value
    /// buffers stay [`Expr::ObjectLit`]; method-bearing buffers become
    /// [`Expr::ObjectBuild`] directly. `None` when the shape is
    /// unrecognizable (the caller falls back loudly).
    fn parse_shape_buffer(&mut self, items: &[Lit]) -> Option<Expr> {
        let mut plain: Vec<(Lit, Lit)> = Vec::new();
        let mut build: Vec<ObjEntry> = Vec::new();
        let mut has_methods = false;
        let mut i = 0;
        while i < items.len() {
            let key = match &items[i] {
                Lit::String(s) => s.clone(),
                Lit::Number(_) | Lit::Int64(_) | Lit::UInt64(_) => {
                    // Numeric key of a plain pair.
                    if i + 1 < items.len() && !matches!(items[i + 1], Lit::MethodRef(_)) {
                        plain.push((items[i].clone(), items[i + 1].clone()));
                        build.push(ObjEntry::KeyValue(
                            items[i].clone(),
                            Expr::Lit(items[i + 1].clone()),
                        ));
                        i += 2;
                        continue;
                    }
                    return None;
                }
                _ => return None,
            };
            match items.get(i + 1) {
                Some(Lit::MethodRef(fid)) => {
                    has_methods = true;
                    let name = self
                        .module
                        .func(*fid)
                        .map(|f| sym_str(self.module, f.name))
                        .unwrap_or_else(|| format!("m${}", fid.index()));
                    // Bug A: body evidence over the metadata gap.
                    let kind = effective_kind(self.module, *fid);
                    build.push(ObjEntry::Method(
                        key,
                        Expr::Closure {
                            body: *fid,
                            name,
                            kind,
                            captures: Vec::new(),
                        },
                    ));
                    // Skip the trailing attributes payload when present.
                    i += if matches!(
                        items.get(i + 2),
                        Some(Lit::Number(_) | Lit::Int64(_) | Lit::UInt64(_))
                    ) {
                        3
                    } else {
                        2
                    };
                }
                Some(v) => {
                    plain.push((items[i].clone(), v.clone()));
                    build.push(ObjEntry::KeyValue(items[i].clone(), Expr::Lit(v.clone())));
                    i += 2;
                }
                None => return None,
            }
        }
        if has_methods {
            Some(Expr::ObjectBuild { entries: build })
        } else {
            Some(Expr::ObjectLit { entries: plain })
        }
    }

    /// Push iteration-plumbing steps onto `steps` (hard-7 members flagged Fallback).
    fn push_iter_step(&self, op: IterOp, obj: ValueId, steps: &mut Vec<RecStep>) {
        let status = match op {
            IterOp::Return | IterOp::Throw => NodeStatus::Fallback,
            _ => NodeStatus::Plumbing,
        };
        steps.push(RecStep::BuildIter { op, status });
        steps.push(RecStep::Val(obj));
    }

    /// `AllocClosure`: pair with the `DefineFunc` def (through `Mov`s).
    fn push_closure_of_steps(&self, func: ValueId, steps: &mut Vec<RecStep>) {
        let mut cur = func;
        for _ in 0..16 {
            let Some(value) = self.module.value(cur) else {
                break;
            };
            match value.def {
                ValueDef::Inst(iid) => match self.module.inst(iid).map(|i| i.op.clone()) {
                    Some(Op::Mov { src }) => {
                        cur = src;
                        continue;
                    }
                    Some(Op::DefineFunc { body, captures, .. }) => {
                        self.push_closure_node_steps(body, &captures, steps);
                        return;
                    }
                    _ => break,
                },
                _ => break,
            }
        }
        steps.push(RecStep::BuildFallback {
            op: "AllocClosure",
            note: "func operand is not a DefineFunc def-chain",
            count: 1,
        });
        steps.push(RecStep::Val(func));
    }

    /// Push deferred closure steps onto `steps`.
    fn push_closure_node_steps(
        &self,
        body: FuncId,
        captures: &[(Sym, ValueId)],
        steps: &mut Vec<RecStep>,
    ) {
        let name = self
            .module
            .func(body)
            .map(|f| sym_str(self.module, f.name))
            .unwrap_or_else(|| format!("<fn#{}>", body.index()));
        let kind = effective_kind(self.module, body);
        let cap_names: Vec<String> = captures
            .iter()
            .map(|(s, _)| sym_str(self.module, *s))
            .collect();
        steps.push(RecStep::BuildClosure {
            body,
            name,
            kind,
            cap_names,
        });
        for (_, v) in captures.iter().rev() {
            steps.push(RecStep::Val(*v));
        }
    }

    /// Push deferred class steps onto `steps` (or directly onto `vals` when no heritage).
    #[allow(
        clippy::too_many_arguments,
        reason = "class recovery step helper threads ctor, heritage, member buffer, and workstacks"
    )]
    fn push_class_node_steps(
        &self,
        ctor: FuncId,
        heritage: Option<ValueId>,
        members: ConstId,
        member_attrs: Vec<abcd_ir::op::MemberAttrs>,
        sendable: bool,
        steps: &mut Vec<RecStep>,
        vals: &mut Vec<Expr>,
    ) {
        let name = self
            .module
            .func(ctor)
            .map(|f| sym_str(self.module, f.name))
            .unwrap_or_else(|| format!("<fn#{}>", ctor.index()));
        let suppress = heritage.is_some_and(|h| provably_hole(self.module, h));
        match heritage {
            Some(h) if !suppress => {
                steps.push(RecStep::BuildClassWithHeritage {
                    ctor,
                    name,
                    members,
                    member_attrs,
                    sendable,
                });
                steps.push(RecStep::Val(h));
            }
            _ => vals.push(Expr::Class {
                ctor,
                name,
                heritage: None,
                members,
                member_attrs,
                sendable,
            }),
        }
    }

    /// Resolve a `gettemplateobject` literal operand to its
    /// `(raw, cooked)` template-string lists (G4, resolved by d-P10).
    ///
    /// Vendor grounding:
    /// - es2panda `compiler/base/literals.cpp`
    ///   `Literals::GetTemplateObject` builds `rawArr` (each quasi's
    ///   `element->Raw()`) and `cookedArr` (`element->Cooked()`), then
    ///   `templateArg = [rawArr, cookedArr]` — raw at index 0, cooked at
    ///   index 1 — via `createemptyarray` + `callruntime.definefieldbyvalue`.
    /// - The runtime `ecmascript/template_string.cpp`
    ///   `TemplateString::GetTemplateObject` reads `templateLiteral[0]`
    ///   as the raw strings and `[1]` as the cooked strings.
    ///
    /// Two IR shapes carry the pair: a const-pool array constant, or
    /// the imperative `AllocArray` + integer-keyed own-store build
    /// sequence (the form es2abc actually emits).
    fn template_strings_of(&self, literal: ValueId) -> (Option<Vec<Lit>>, Option<Vec<Lit>>) {
        let v = chase_mov(self.module, literal);
        // Const-pool form: the whole literal array is one constant.
        if let Some(cid) = const_id_of(self.module, v) {
            return match lit_of(self.module, cid).and_then(Lit::into_array) {
                Some(items) => {
                    // Vendor pair layout [raw, cooked]: both elements are
                    // themselves arrays. Anything else keeps the pre-d-P10
                    // interpretation (the flat list is the cooked list).
                    if items.len() == 2
                        && let (Lit::Array(raw), Lit::Array(cooked)) = (&items[0], &items[1])
                    {
                        return (Some(raw.clone()), Some(cooked.clone()));
                    }
                    (None, Some(items))
                }
                None => (None, None),
            };
        }
        // Imperative form: slots 0 (raw) and 1 (cooked) of the literal
        // array are own-stored element arrays. Lenient about the pair
        // array's other uses (it is read at the `gettemplateobject`
        // point regardless); strict about each element array.
        let mut slots: [Option<ValueId>; 2] = [None, None];
        for &user in self.chains.users_of(v) {
            let Some(inst) = self.module.inst(user) else {
                continue;
            };
            let (object, index, value) = match &inst.op {
                Op::StoreOwnPropDyn {
                    object, key, value, ..
                }
                | Op::StorePropDyn { object, key, value } => {
                    let Some(i) = self.const_index_of(*key) else {
                        continue;
                    };
                    (*object, i, *value)
                }
                Op::StoreOwnPropIdx {
                    object,
                    index,
                    value,
                    ..
                }
                | Op::StorePropIdx {
                    object,
                    index,
                    value,
                } => {
                    let Some(i) = self.const_index_of(*index) else {
                        continue;
                    };
                    (*object, i, *value)
                }
                _ => continue,
            };
            if chase_mov(self.module, object) == v && (index as usize) < 2 {
                slots[index as usize] = Some(value);
            }
        }
        let raw = slots[0].and_then(|a| self.string_elems_of(a));
        let cooked = slots[1].and_then(|a| self.string_elems_of(a));
        (raw, cooked)
    }

    /// Resolve an array value to its element literals — a const-pool
    /// array, or an `AllocArray` whose every use is accounted for by the
    /// es2panda template build: integer-keyed own/prop stores into it,
    /// `Mov` passthroughs, or appearing as a stored VALUE (the literal
    /// pair array's slot store). Any other use → unresolved (honest
    /// bail, the cooked-only fallback emits).
    fn string_elems_of(&self, arr: ValueId) -> Option<Vec<Lit>> {
        let arr = chase_mov(self.module, arr);
        if let Some(cid) = const_id_of(self.module, arr) {
            return lit_of(self.module, cid)?.into_array();
        }
        // The array must be a fresh allocation we can fully account for.
        let is_alloc = matches!(
            self.module.value(arr)?.def,
            ValueDef::Inst(iid)
                if matches!(
                    self.module.inst(iid).map(|i| &i.op),
                    Some(Op::AllocArray { .. })
                )
        );
        if !is_alloc {
            return None;
        }
        let mut elems: BTreeMap<u32, Lit> = BTreeMap::new();
        for &user in self.chains.users_of(arr) {
            let inst = self.module.inst(user)?;
            match &inst.op {
                Op::StoreOwnPropDyn {
                    object, key, value, ..
                }
                | Op::StorePropDyn { object, key, value } => {
                    if chase_mov(self.module, *object) == arr {
                        let i = self.const_index_of(*key)?;
                        let lit = self.lit_value_of(*value)?;
                        elems.insert(i, lit);
                    }
                    // else: arr is the stored value (the pair-array slot
                    // store) — accounted for, nothing to record.
                }
                Op::StoreOwnPropIdx {
                    object,
                    index,
                    value,
                    ..
                }
                | Op::StorePropIdx {
                    object,
                    index,
                    value,
                } => {
                    if chase_mov(self.module, *object) == arr {
                        let i = self.const_index_of(*index)?;
                        let lit = self.lit_value_of(*value)?;
                        elems.insert(i, lit);
                    }
                }
                Op::Mov { .. } => {}
                _ => return None,
            }
        }
        // Contiguity: elements are exactly indices 0..n.
        let n = elems.len() as u32;
        let mut out = Vec::with_capacity(elems.len());
        for i in 0..n {
            out.push(elems.get(&i)?.clone());
        }
        Some(out)
    }

    /// Resolve a value to a constant integer index (`ldai` →
    /// `Const::Number`), through `Mov`s.
    fn const_index_of(&self, v: ValueId) -> Option<u32> {
        let cid = const_id_of(self.module, chase_mov(self.module, v))?;
        match lit_of(self.module, cid)? {
            Lit::Number(bits) => {
                let x = f64::from_bits(bits);
                if x.fract() == 0.0 && x >= 0.0 && x <= u32::MAX as f64 {
                    Some(x as u32)
                } else {
                    None
                }
            }
            Lit::Int64(x) => u32::try_from(x).ok(),
            Lit::UInt64(x) => u32::try_from(x).ok(),
            _ => None,
        }
    }

    /// Resolve a value to a constant literal, through `Mov`s.
    fn lit_value_of(&self, v: ValueId) -> Option<Lit> {
        let cid = const_id_of(self.module, chase_mov(self.module, v))?;
        lit_of(self.module, cid)
    }
}

enum RecStep {
    Val(ValueId),
    Inst(InstId, Op),
    PopInline(InstId),
    BuildBinary(abcd_ir::op::BinOp),
    BuildUnary(abcd_ir::op::UnOp),
    BuildCompare(CmpOp),
    BuildPropName {
        name: String,
        dot_legal: bool,
    },
    BuildPropDynConstKey(Box<Expr>),
    BuildPropIndex,
    BuildPropDyn,
    BuildDeletePropDyn,
    BuildTestPropNamed(Box<Expr>),
    BuildIterResultObj,
    BuildIter {
        op: IterOp,
        status: NodeStatus,
    },
    BuildDynamicImport,
    BuildCall {
        has_this: bool,
        arg_count: usize,
        kind: CallKind,
        super_callee: bool,
    },
    BuildClosure {
        body: FuncId,
        name: String,
        kind: FunctionKind,
        cap_names: Vec<String>,
    },
    BuildClassWithHeritage {
        ctor: FuncId,
        name: String,
        members: ConstId,
        member_attrs: Vec<abcd_ir::op::MemberAttrs>,
        sendable: bool,
    },
    BuildPrivate {
        name: String,
        test: bool,
    },
    BuildCreateGenerator,
    BuildYield,
    BuildGenDriver(bool),
    BuildAwait(bool),
    BuildAsyncDriver(bool),
    BuildAsyncGenResolve,
    BuildSuperDyn,
    BuildArraySpread,
    BuildRestObject(usize),
    BuildFallback {
        op: &'static str,
        note: &'static str,
        count: usize,
    },
}

/// Chase `Mov` passthroughs to the underlying definition (bounded).
fn chase_mov(module: &Module, mut v: ValueId) -> ValueId {
    for _ in 0..16 {
        let Some(value) = module.value(v) else {
            break;
        };
        match value.def {
            ValueDef::Inst(iid) => match module.inst(iid) {
                Some(inst) => match &inst.op {
                    Op::Mov { src } => {
                        v = *src;
                        continue;
                    }
                    _ => break,
                },
                None => break,
            },
            _ => break,
        }
    }
    v
}

/// Resolve a value to the constant it loads, if any.
fn const_id_of(module: &Module, v: ValueId) -> Option<ConstId> {
    match module.value(v)?.def {
        ValueDef::Const(cid) => Some(cid),
        ValueDef::Inst(iid) => match &module.inst(iid)?.op {
            Op::LoadConst(cid) => Some(*cid),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use abcd_ir::function::{Block, DebugData, FunctionData, Inst};
    use abcd_ir::module::ClassData;
    use abcd_ir::ty::Ty;
    use abcd_ir::{ClassId, Const};

    // ── Hand-built module scaffolding (mirrors tests/common) ─────────

    fn mk_module() -> Module {
        let mut m = Module::new();
        let name = m.sym.intern("Ltest;");
        m.classes.push(ClassData::new(name, name));
        m
    }

    /// A fresh function with one empty entry block.
    fn add_fn(m: &mut Module, name: &str) -> FuncId {
        let sym = m.sym.intern(name);
        let id = FuncId::new(m.functions.len() as u32);
        m.functions.push(FunctionData::new(
            ClassId::new(0),
            sym,
            FunctionKind::Function,
        ));
        let b = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(id).unwrap().blocks.push(b);
        id
    }

    /// A fresh function whose entry block is `[return]`.
    fn add_ret_fn(m: &mut Module, name: &str) -> FuncId {
        let id = add_fn(m, name);
        let b = entry_of(m, id);
        push_inst(m, b, Op::Return { value: None });
        id
    }

    fn entry_of(m: &Module, f: FuncId) -> BlockId {
        m.func(f).unwrap().blocks[0]
    }

    fn push_inst(m: &mut Module, b: BlockId, op: Op) -> InstId {
        assert!(!op.has_result(), "{op:?} has a result");
        let id = InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op,
            result: None,
            block: b,
            loc: None,
        });
        m.block_mut(b).unwrap().insts.push(id);
        id
    }

    fn emit_val(m: &mut Module, b: BlockId, op: Op) -> ValueId {
        assert!(op.has_result(), "{op:?} has no result");
        let inst = {
            let id = InstId::new(m.insts.len() as u32);
            m.insts.push(Inst {
                op,
                result: None,
                block: b,
                loc: None,
            });
            m.block_mut(b).unwrap().insts.push(id);
            id
        };
        let val = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Inst(inst),
            ty: Ty::Any,
        });
        m.inst_mut(inst).unwrap().result = Some(val);
        val
    }

    fn add_param(m: &mut Module, f: FuncId) -> ValueId {
        let idx = m.func(f).unwrap().params.len() as u16;
        let val = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Param(idx),
            ty: Ty::Any,
        });
        m.func_mut(f).unwrap().params.push(val);
        val
    }

    fn load_const(m: &mut Module, b: BlockId, c: Const) -> ValueId {
        let cid = m.consts.push(c);
        emit_val(m, b, Op::LoadConst(cid))
    }

    fn load_number(m: &mut Module, b: BlockId, x: f64) -> ValueId {
        load_const(m, b, Const::number(x))
    }

    fn load_string(m: &mut Module, b: BlockId, s: &str) -> ValueId {
        let sym = m.sym.intern(s);
        load_const(m, b, Const::String(sym))
    }

    /// A constant-defined SSA value (no instruction).
    fn const_value(m: &mut Module, c: Const) -> ValueId {
        let cid = m.consts.push(c);
        let val = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Const(cid),
            ty: Ty::Any,
        });
        val
    }

    fn ident(s: &str) -> Expr {
        Expr::Ident(s.to_string())
    }

    /// The `new ReferenceError(msg)` expression the TDZ guards emit.
    fn reference_error(msg: &str) -> Stmt {
        Stmt::Throw(Expr::Call {
            callee: Box::new(Expr::Ident("ReferenceError".to_string())),
            this: None,
            args: vec![Expr::Lit(Lit::String(msg.to_string()))],
            kind: CallKind::New,
        })
    }

    // ── OpStat::get (88-90) ──────────────────────────────────────────

    #[test]
    fn opstat_get() {
        let mut s = OpStat::default();
        assert_eq!(s.get(Outcome::Expressed), 0);
        s.add(Fitness::Trivial, Outcome::Expressed);
        s.add(Fitness::Hard, Outcome::Fallback);
        s.add(Fitness::Hard, Outcome::Fallback);
        assert_eq!(s.get(Outcome::Expressed), 1);
        assert_eq!(s.get(Outcome::Fallback), 2);
        assert_eq!(s.get(Outcome::DeadPure), 0);
        assert_eq!(s.fitness, Some(Fitness::Hard));
    }

    // ── Debug param names, equal-length path (779) ───────────────────

    #[test]
    fn debug_params_equal_length() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        add_param(&mut m, f);
        add_param(&mut m, f);
        let a = m.sym.intern("a");
        let bb = m.sym.intern("b");
        m.func_mut(f).unwrap().debug = Some(DebugData {
            source_file: None,
            source_code: None,
            line_table: Vec::new(),
            column_table: Vec::new(),
            local_names: Vec::new(),
            // Same length as the IR param list: direct indexing (779).
            param_names: vec![a, bb],
            scope_names: None,
        });
        let rf = recover_func(&m, f);
        assert_eq!(rf.params, vec!["this".to_string(), "b".to_string()]);
    }

    // ── Provably-hole TDZ guards (1016-1025 + WithName + label arm) ──

    #[test]
    fn tdz_guard_provably_hole() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let hole_cid = m.consts.push(Const::Hole);
        // Hole through a Mov (chase_mov 2194-2196).
        let hole_load = emit_val(&mut m, b, Op::LoadConst(hole_cid));
        let hole_mov = emit_val(&mut m, b, Op::Mov { src: hole_load });
        let x_sym = m.sym.intern("x");
        let name_val = const_value(&mut m, Const::String(x_sym));
        push_inst(
            &mut m,
            b,
            Op::ThrowUndefinedIfHole {
                name: name_val,
                value: hole_mov,
            },
        );
        // A non-string name expression falls back to "binding" (1019).
        let num_val = const_value(&mut m, Const::number(1.0));
        let hole2 = emit_val(&mut m, b, Op::LoadConst(hole_cid));
        push_inst(
            &mut m,
            b,
            Op::ThrowUndefinedIfHole {
                name: num_val,
                value: hole2,
            },
        );
        // The with-name form materializes the same ReferenceError.
        let hole3 = emit_val(&mut m, b, Op::LoadConst(hole_cid));
        let y = m.sym.intern("y");
        push_inst(
            &mut m,
            b,
            Op::ThrowUndefinedIfHoleWithName {
                name: y,
                value: hole3,
            },
        );
        let rf = recover_func(&m, f);
        assert_eq!(
            rf.blocks[0].stmts,
            vec![
                reference_error("Cannot access 'x' before initialization"),
                reference_error("Cannot access 'binding' before initialization"),
                reference_error("Cannot access 'y' before initialization"),
            ]
        );
    }

    // ── undef_through: non-Undefined const (1303) ────────────────────

    #[test]
    fn define_getter_setter_undef_through_non_undef() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let obj = add_param(&mut m, f);
        let key = add_param(&mut m, f);
        // Getter is a NON-Undefined const load: the undef-through probe
        // declines (1303) and the ordinary expression path resolves it.
        let getter = load_number(&mut m, b, 1.0);
        let undef_cid = m.consts.push(Const::Undefined);
        let setter = emit_val(&mut m, b, Op::LoadConst(undef_cid));
        let set_name = load_const(&mut m, b, Const::Bool(false));
        emit_val(
            &mut m,
            b,
            Op::DefineGetterSetterByValue {
                obj,
                key,
                getter,
                setter,
                set_name,
            },
        );
        let rf = recover_func(&m, f);
        assert_eq!(
            rf.blocks[0].stmts,
            vec![Stmt::Expr(Expr::DefineGetterSetter {
                obj: Box::new(ident("this")),
                key: Box::new(ident("p1")),
                getter: Box::new(Expr::Lit(Lit::Number(1.0f64.to_bits()))),
                setter: Box::new(Expr::Lit(Lit::Undefined)),
            })]
        );
    }

    // ── SetObjectWithProto statement (1322-1328) ─────────────────────

    #[test]
    fn set_object_with_proto_stmt() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let obj = add_param(&mut m, f);
        let proto = add_param(&mut m, f);
        push_inst(&mut m, b, Op::SetObjectWithProto { proto, obj });
        let rf = recover_func(&m, f);
        assert_eq!(
            rf.blocks[0].stmts,
            vec![Stmt::Expr(Expr::SetObjectWithProto {
                obj: Box::new(ident("this")),
                proto: Box::new(ident("p1")),
            })]
        );
        assert_eq!(rf.histogram["SetObjectWithProto"].get(Outcome::Plumbing), 1);
    }

    // ── Lazy catch-name mint (1512-1514) ─────────────────────────────

    #[test]
    fn lazy_catch_name_mint() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        // An ExceptionParam value with NO try region: `mint_catch_names`
        // never saw it, so `expr_of` mints lazily (1512-1514).
        let exc = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::ExceptionParam(b),
            ty: Ty::Any,
        });
        push_inst(&mut m, b, Op::Throw { value: exc });
        let rf = recover_func(&m, f);
        assert_eq!(
            rf.blocks[0].stmts,
            vec![Stmt::Throw(Expr::Ident("e".to_string()))]
        );
    }

    // ── Shape buffers: numeric-key plain pairs (1588-1597) ───────────

    #[test]
    fn shape_buffer_numeric_keys() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let sa = m.sym.intern("a");
        let sb = m.sym.intern("b");
        let c0 = m.consts.intern(Const::number(0.0));
        let csa = m.consts.intern(Const::String(sa));
        let c1 = m.consts.intern(Const::number(1.0));
        let csb = m.consts.intern(Const::String(sb));
        let shape = m.consts.push_array(vec![c0, csa, c1, csb]);
        let v = emit_val(&mut m, b, Op::AllocObject { shape });
        push_inst(&mut m, b, Op::Return { value: Some(v) });
        let rf = recover_func(&m, f);
        assert_eq!(
            rf.blocks[0].stmts,
            vec![Stmt::Return(Some(Expr::ObjectLit {
                entries: vec![
                    (Lit::Number(0.0f64.to_bits()), Lit::String("a".to_string())),
                    (Lit::Number(1.0f64.to_bits()), Lit::String("b".to_string())),
                ],
            }))]
        );
    }

    // ── Shape-buffer parse failures (1597/1599/1632 → 1687-1691) ─────

    #[test]
    fn shape_buffer_parse_failures() {
        let mut m = mk_module();
        let meth = add_fn(&mut m, "mm");
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let c0 = m.consts.intern(Const::number(0.0));
        let cmeth = m.consts.intern(Const::method_ref(meth));
        let ctrue = m.consts.intern(Const::Bool(true));
        // (a) numeric key followed by a MethodRef (1597).
        let shape_a = m.consts.push_array(vec![c0, cmeth]);
        // (b) a key that is neither String nor Number (1599).
        let shape_b = m.consts.push_array(vec![ctrue, c0]);
        // (c) a trailing key without a value (1632).
        let key_c = m.sym.intern("a");
        let ckey_c = m.consts.intern(Const::String(key_c));
        let shape_c = m.consts.push_array(vec![ckey_c]);
        for shape in [shape_a, shape_b, shape_c] {
            let v = emit_val(&mut m, b, Op::AllocObject { shape });
            push_inst(&mut m, b, Op::Return { value: Some(v) });
        }
        let rf = recover_func(&m, f);
        let fallback = Expr::Fallback {
            op: "AllocObject",
            note: "shape buffer is not a flat key/value array",
            operands: Vec::new(),
        };
        assert_eq!(
            rf.blocks[0].stmts,
            vec![
                Stmt::Return(Some(fallback.clone())),
                Stmt::Return(Some(fallback.clone())),
                Stmt::Return(Some(fallback)),
            ]
        );
        // The loud marker is the Expr::Fallback node; the histogram
        // records the op's base outcome (Expressed for AllocObject).
        assert_eq!(rf.histogram["AllocObject"].get(Outcome::Expressed), 3);
    }

    // ── Shape-buffer method entries: attrs skip / absent (1621-1624) ──

    #[test]
    fn shape_buffer_method_entries() {
        let mut m = mk_module();
        let meth = add_ret_fn(&mut m, "meth");
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let mname = m.sym.intern("m");
        let cmname = m.consts.intern(Const::String(mname));
        let cmeth = m.consts.intern(Const::method_ref(meth));
        let c7 = m.consts.intern(Const::number(7.0));
        // No trailing attrs payload: `i += 2` (1624).
        let shape_plain = m.consts.push_array(vec![cmname, cmeth]);
        // Trailing numeric attrs payload: `i += 3` (1621-1622).
        let shape_attrs = m.consts.push_array(vec![cmname, cmeth, c7]);
        for shape in [shape_plain, shape_attrs] {
            let v = emit_val(&mut m, b, Op::AllocObject { shape });
            push_inst(&mut m, b, Op::Return { value: Some(v) });
        }
        let rf = recover_func(&m, f);
        let expected = Stmt::Return(Some(Expr::ObjectBuild {
            entries: vec![ObjEntry::Method(
                "m".to_string(),
                Expr::Closure {
                    body: meth,
                    name: "meth".to_string(),
                    kind: FunctionKind::Function,
                    captures: Vec::new(),
                },
            )],
        }));
        assert_eq!(rf.blocks[0].stmts, vec![expected.clone(), expected.clone()]);
    }

    // ── TestProp Index/Dynamic keys (1740) ───────────────────────────

    #[test]
    fn testprop_index_dynamic_keys() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let obj = add_param(&mut m, f);
        let k1 = load_number(&mut m, b, 7.0);
        let t1 = emit_val(
            &mut m,
            b,
            Op::TestProp {
                object: obj,
                key: PropKey::Index(k1),
            },
        );
        let k2 = load_number(&mut m, b, 8.0);
        // Result unused but observable (Proxy `has` trap): an expression
        // statement, never dead code.
        emit_val(
            &mut m,
            b,
            Op::TestProp {
                object: obj,
                key: PropKey::Dynamic(k2),
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(t1) });
        let rf = recover_func(&m, f);
        let cmp = |bits: u64| Expr::Compare {
            op: CmpOp::In,
            left: Box::new(Expr::Lit(Lit::Number(bits))),
            right: Box::new(ident("this")),
        };
        let stmts = &rf.blocks[0].stmts;
        assert!(
            matches!(&stmts[0], Stmt::Declare { value, .. } if *value == cmp(7.0f64.to_bits())),
            "index-keyed TestProp declare: {stmts:?}"
        );
        assert_eq!(stmts[1], Stmt::Expr(cmp(8.0f64.to_bits())));
    }

    // ── AllocClosure: Mov-chased DefineFunc (1939-1941) + fallback ───

    #[test]
    fn alloc_closure_mov_chain() {
        let mut m = mk_module();
        let inner = add_ret_fn(&mut m, "inner");
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let df = emit_val(
            &mut m,
            b,
            Op::DefineFunc {
                body: inner,
                captures: Vec::new(),
                length: 0,
            },
        );
        let mv = emit_val(&mut m, b, Op::Mov { src: df });
        let clo = emit_val(&mut m, b, Op::AllocClosure { func: mv });
        push_inst(&mut m, b, Op::Return { value: Some(clo) });
        let rf = recover_func(&m, f);
        assert_eq!(
            rf.blocks[0].stmts,
            vec![Stmt::Return(Some(Expr::Closure {
                body: inner,
                name: "inner".to_string(),
                kind: FunctionKind::Function,
                captures: Vec::new(),
            }))]
        );
    }

    #[test]
    fn alloc_closure_not_a_definefunc_chain() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        // The func operand is a number load, not a DefineFunc chain:
        // loud fallback (1951-1955).
        let c = load_number(&mut m, b, 5.0);
        let clo = emit_val(&mut m, b, Op::AllocClosure { func: c });
        push_inst(&mut m, b, Op::Return { value: Some(clo) });
        let rf = recover_func(&m, f);
        assert_eq!(
            rf.blocks[0].stmts,
            vec![Stmt::Return(Some(Expr::Fallback {
                op: "AllocClosure",
                note: "func operand is not a DefineFunc def-chain",
                operands: vec![Expr::Lit(Lit::Number(5.0f64.to_bits()))],
            }))]
        );
        // The loud marker is the Expr::Fallback node; the histogram
        // records the op's base outcome (AllocClosure is expressible —
        // the fallback is data-driven, not fitness-driven).
        assert_eq!(rf.histogram["AllocClosure"].get(Outcome::Expressed), 1);
    }

    // ── GetTemplateObject: non-array const literal (2046, 2211) ──────

    #[test]
    fn template_const_literal_non_array() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        // A const-defined literal that is NOT an array (2046); the
        // direct `ValueDef::Const` arm of `const_id_of` resolves it
        // (2211).
        let lit_sym = m.sym.intern("not-an-array");
        let lit = const_value(&mut m, Const::String(lit_sym));
        let g = emit_val(&mut m, b, Op::GetTemplateObject { literal: lit });
        push_inst(&mut m, b, Op::Return { value: Some(g) });
        let rf = recover_func(&m, f);
        assert!(
            matches!(
                &rf.blocks[0].stmts[0],
                Stmt::Declare {
                    value: Expr::TemplateObject {
                        raw: None,
                        cooked: None
                    },
                    ..
                }
            ),
            "{:?}",
            rf.blocks[0].stmts
        );
    }

    // ── GetTemplateObject: the imperative pair-array build ────────────
    // (2060-2079 pair-slot evidence, 2101-2103 const-array fast path,
    //  2123-2146 element stores, 2148 Mov user, 2171/2174 bad keys)

    #[test]
    fn template_imperative_build() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let c0 = load_number(&mut m, b, 0.0);
        let c1 = load_number(&mut m, b, 1.0);
        let c2 = load_number(&mut m, b, 2.0);
        let sa = load_string(&mut m, b, "a");
        let sb = load_string(&mut m, b, "b");
        let sc = load_string(&mut m, b, "c");
        // The cooked list as a direct const-array value (2101-2103).
        let ck_sym = m.sym.intern("ck");
        let ck_cid = m.consts.intern(Const::String(ck_sym));
        let cooked = const_value(&mut m, Const::ArrayLiteral(vec![ck_cid]));
        let pair = emit_val(&mut m, b, Op::AllocArray { shape: None });
        let raw = emit_val(&mut m, b, Op::AllocArray { shape: None });
        // Element stores into `raw`: all three store forms.
        push_inst(
            &mut m,
            b,
            Op::StoreOwnPropIdx {
                object: raw,
                index: c0,
                value: sa,
                kind: abcd_ir::OwnStoreKind::OwnProp,
            },
        );
        push_inst(
            &mut m,
            b,
            Op::StorePropDyn {
                object: raw,
                key: c1,
                value: sb,
            },
        );
        push_inst(
            &mut m,
            b,
            Op::StorePropIdx {
                object: raw,
                index: c2,
                value: sc,
            },
        );
        // A `Mov` user of the element array is accounted for (2148).
        emit_val(&mut m, b, Op::Mov { src: raw });
        // Bad-key pair stores are skipped: non-number const key (2174),
        // fractional number key (2171).
        let bad_str = load_string(&mut m, b, "nope");
        push_inst(
            &mut m,
            b,
            Op::StorePropDyn {
                object: pair,
                key: bad_str,
                value: raw,
            },
        );
        let bad_frac = load_number(&mut m, b, 1.5);
        push_inst(
            &mut m,
            b,
            Op::StorePropIdx {
                object: pair,
                index: bad_frac,
                value: raw,
            },
        );
        // The vendor pair stores: slot 0 = raw strings, slot 1 = cooked.
        push_inst(
            &mut m,
            b,
            Op::StorePropDyn {
                object: pair,
                key: c0,
                value: raw,
            },
        );
        push_inst(
            &mut m,
            b,
            Op::StorePropIdx {
                object: pair,
                index: c1,
                value: cooked,
            },
        );
        let g = emit_val(&mut m, b, Op::GetTemplateObject { literal: pair });
        push_inst(&mut m, b, Op::Return { value: Some(g) });
        let rf = recover_func(&m, f);
        let tpl = rf.blocks[0]
            .stmts
            .iter()
            .find_map(|s| match s {
                Stmt::Declare {
                    value: Expr::TemplateObject { raw, cooked },
                    ..
                } => Some((raw.clone(), cooked.clone())),
                _ => None,
            })
            .expect("a TemplateObject declare");
        assert_eq!(
            tpl,
            (
                Some(vec![
                    Lit::String("a".to_string()),
                    Lit::String("b".to_string()),
                    Lit::String("c".to_string()),
                ]),
                Some(vec![Lit::String("ck".to_string())]),
            )
        );
    }

    // ── Template slot value that is not an allocation (2116) ─────────

    #[test]
    fn template_slot_value_not_alloc() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let p = add_param(&mut m, f);
        let c0 = load_number(&mut m, b, 0.0);
        let pair = emit_val(&mut m, b, Op::AllocArray { shape: None });
        // Slot 0 holds a PARAMETER: neither a const array nor an
        // AllocArray the walk can account for (2116).
        push_inst(
            &mut m,
            b,
            Op::StorePropDyn {
                object: pair,
                key: c0,
                value: p,
            },
        );
        let g = emit_val(&mut m, b, Op::GetTemplateObject { literal: pair });
        push_inst(&mut m, b, Op::Return { value: Some(g) });
        let rf = recover_func(&m, f);
        let tpl = rf.blocks[0]
            .stmts
            .iter()
            .find_map(|s| match s {
                Stmt::Declare {
                    value: Expr::TemplateObject { raw, cooked },
                    ..
                } => Some((raw.clone(), cooked.clone())),
                _ => None,
            })
            .expect("a TemplateObject declare");
        assert_eq!(tpl, (None, None));
    }

    // ── Template slot value that is a non-array const (2103) ─────────

    #[test]
    fn template_slot_value_non_array_const() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let c0 = load_number(&mut m, b, 0.0);
        let pair = emit_val(&mut m, b, Op::AllocArray { shape: None });
        // Slot 0 holds a const STRING: the const fast path of
        // `string_elems_of` declines non-array literals (2103).
        let s_sym = m.sym.intern("s");
        let slot_val = const_value(&mut m, Const::String(s_sym));
        push_inst(
            &mut m,
            b,
            Op::StorePropDyn {
                object: pair,
                key: c0,
                value: slot_val,
            },
        );
        let g = emit_val(&mut m, b, Op::GetTemplateObject { literal: pair });
        push_inst(&mut m, b, Op::Return { value: Some(g) });
        let rf = recover_func(&m, f);
        let tpl = rf.blocks[0]
            .stmts
            .iter()
            .find_map(|s| match s {
                Stmt::Declare {
                    value: Expr::TemplateObject { raw, cooked },
                    ..
                } => Some((raw.clone(), cooked.clone())),
                _ => None,
            })
            .expect("a TemplateObject declare");
        assert_eq!(tpl, (None, None));
    }

    // ── Template element array with a foreign user (2149) ────────────

    #[test]
    fn template_elem_array_foreign_user() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let c0 = load_number(&mut m, b, 0.0);
        let pair = emit_val(&mut m, b, Op::AllocArray { shape: None });
        let elems = emit_val(&mut m, b, Op::AllocArray { shape: None });
        push_inst(
            &mut m,
            b,
            Op::StoreOwnPropIdx {
                object: pair,
                index: c0,
                value: elems,
                kind: abcd_ir::OwnStoreKind::OwnProp,
            },
        );
        let g = emit_val(&mut m, b, Op::GetTemplateObject { literal: pair });
        push_inst(&mut m, b, Op::Return { value: Some(g) });
        // A use of the element array that is not a store/Mov: the walk
        // bails (2149) and the template stays unresolved.
        push_inst(&mut m, b, Op::Throw { value: elems });
        let rf = recover_func(&m, f);
        let tpl = rf.blocks[0]
            .stmts
            .iter()
            .find_map(|s| match s {
                Stmt::Declare {
                    value: Expr::TemplateObject { raw, cooked },
                    ..
                } => Some((raw.clone(), cooked.clone())),
                _ => None,
            })
            .expect("a TemplateObject declare");
        assert_eq!(tpl, (None, None));
    }

    #[test]
    fn parallel_phi_swap_cycle_and_bridge() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "swapLoop");
        let b_entry = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p_x = add_param(&mut m, f);
        let p_y = add_param(&mut m, f);
        let p_z = add_param(&mut m, f);

        let b_hdr = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(f).unwrap().blocks.push(b_hdr);

        let b_latch = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(f).unwrap().blocks.push(b_latch);

        push_inst(&mut m, b_entry, Op::Branch { dest: b_hdr });
        m.block_mut(b_hdr).unwrap().preds.push(Edge {
            from: b_entry,
            kind: EdgeKind::Normal,
        });
        m.block_mut(b_hdr).unwrap().preds.push(Edge {
            from: b_latch,
            kind: EdgeKind::Normal,
        });

        // Bridge `m = z` read by cycle `[a, b] = [m + b, a]` on the latch edge:
        // only ONE cycle-breaking temp (`phi`) should be minted (not on `m`).
        let v_m = emit_val(
            &mut m,
            b_hdr,
            Op::Phi {
                entries: Vec::new(),
            },
        );
        let v_a = emit_val(
            &mut m,
            b_hdr,
            Op::Phi {
                entries: Vec::new(),
            },
        );
        let v_b = emit_val(
            &mut m,
            b_hdr,
            Op::Phi {
                entries: Vec::new(),
            },
        );
        push_inst(&mut m, b_hdr, Op::Branch { dest: b_latch });
        m.block_mut(b_latch).unwrap().preds.push(Edge {
            from: b_hdr,
            kind: EdgeKind::Normal,
        });

        let mb = emit_val(
            &mut m,
            b_latch,
            Op::BinaryOp {
                op: abcd_ir::op::BinOp::Add,
                left: v_b,
                right: v_m,
            },
        );
        push_inst(&mut m, b_latch, Op::Branch { dest: b_hdr });

        let e0 = Edge {
            from: b_entry,
            kind: EdgeKind::Normal,
        };
        let e1 = Edge {
            from: b_latch,
            kind: EdgeKind::Normal,
        };
        for (pv, entries) in [
            (v_m, vec![(e0, p_x), (e1, p_z)]),
            (v_a, vec![(e0, p_x), (e1, mb)]),
            (v_b, vec![(e0, p_y), (e1, v_a)]),
        ] {
            let ValueDef::Inst(iid) = m.value(pv).unwrap().def else {
                panic!("phi inst");
            };
            m.inst_mut(iid).unwrap().op = Op::Phi { entries };
        }

        let rf = recover_func(&m, f);
        let synth_decls: Vec<&str> = rf.blocks[0]
            .stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::PhiDecl { name, .. } => Some(name.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(synth_decls, vec!["phi"]);
    }
}
