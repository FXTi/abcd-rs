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

use crate::consts::{lit_of, render_regexp_flags, sym_str};
use crate::expr::{Expr, IterOp, Lit, NodeStatus, ObjEntry};
use crate::fitness::{Fitness, elision_reason, fallback_note, fitness_of, op_name};
use crate::legalize::{Legalizer, is_legal_ident, sanitize};
use crate::names::{
    NameScopes, local_name_in, module_slot_fallback, module_slot_names, namespace_fallback,
    op_name_hint,
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
    /// absence-tolerant form — invisible in source).
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
    Recover::new(module, func).run()
}

/// Whether an op has observable effects for the inline barrier
/// (`Effects.may_call`/`may_throw`/`writes` — §4.1).
fn observable(op: &Op) -> bool {
    let e = op.effects();
    e.may_throw || e.may_call != abcd_ir::effects::CallEffect::None || !e.writes.is_empty()
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

struct Recover<'m> {
    module: &'m Module,
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
    /// Hidden leading ABI slot count (es2abc `<static>`: 3).
    param_names: Vec<String>,
    hidden_params: usize,
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
    /// G2: resolved module-var slot↔name map (computed once, in
    /// [`Recover::reserve_module_slot_names`], before params mint).
    slot_names: BTreeMap<u32, String>,
    histogram: BTreeMap<&'static str, OpStat>,
}

impl<'m> Recover<'m> {
    fn new(module: &'m Module, func: FuncId) -> Self {
        let mut r = Recover {
            hidden_params: 0,
            module,
            func,
            chains: UseDefChains::build(module, func),
            scopes: NameScopes::build(module, func),
            legal: Legalizer::new(),
            inline: HashSet::new(),
            alias: HashMap::new(),
            temp_names: HashMap::new(),
            param_names: Vec::new(),
            catch_names: HashMap::new(),
            handler_binds: HashMap::new(),
            inst_pos: HashMap::new(),
            barriers: HashMap::new(),
            class_fold: None,
            slot_names: BTreeMap::new(),
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
                    .map(|i| observable(&i.op) as u32)
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
        let kind = f.kind;
        let block_ids = f.blocks.clone();

        self.reserve_module_slot_names();
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
        // layouts), append afterwards in deterministic walk order.
        let mut phi_tail: Vec<(BlockId, Stmt)> = Vec::new();

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
        for (pred, stmt) in phi_tail {
            if let Some(&bi) = block_index.get(&pred) {
                blocks[bi].stmts.push(stmt);
            }
        }

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
        // The calling convention's hidden leading slots: es2abc marks
        // every function <static> and frames carry (funcobj, newtarget,
        // this) — so for static functions with ≥3 params the user
        // formals start at params[3] and params[2] is `this` (the
        // vendored frame-slot model, abcd_ir::frame). Non-static
        // functions (hand-crafted IR, the golden suites) keep the
        // naming heuristic's single hidden slot: params[0] prints as
        // `this`. (d-P4: the recompile gate found this —
        // `add(20, 22)` read its args from the wrong slots.)
        let hidden = if f.modifiers.contains(abcd_ir::Modifiers::STATIC) && n >= 3 {
            3
        } else {
            usize::from(n > 0)
        };
        self.hidden_params = hidden;
        for i in 0..n {
            let this_idx = hidden - 1;
            if i == this_idx && hidden == 1 {
                // The naming heuristic's single hidden slot is `this`.
                self.param_names.push("this".to_string());
                continue;
            }
            if hidden == 3 && i < 3 {
                // The hidden es2abc slots: funcobj/newtarget are nearly
                // never read (bodies use LoadFunction/LoadNewTarget);
                // `this` gets its JS name so ctor bodies read right.
                let name = if i == 2 {
                    "this".to_string()
                } else {
                    format!("p{i}")
                };
                self.param_names.push(name);
                continue;
            }
            // The debug param list may or may not include the hidden
            // slots: equal length → direct index; otherwise assume it
            // holds only the user formals (offset by `hidden`).
            let raw = if debug_param_names.len() == n {
                debug_param_names.get(i).cloned()
            } else {
                debug_param_names.get(i - hidden).cloned()
            };
            let fallback = format!("p{i}");
            let name = self.legal.mint(raw.as_deref().unwrap_or(&fallback));
            self.param_names.push(name);
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
            let name = self.legal.mint(hint.as_deref().unwrap_or("e"));
            self.catch_names.insert(exc, name.clone());
            self.handler_binds.entry(handler).or_default().push(name);
        }
    }

    /// G2: resolve module-var slot names once and reserve them BEFORE
    /// params mint — a source param sharing a binding's name would
    /// otherwise shadow the module-scope `let` the resolved name refers
    /// to (a `StoreModuleVar` prints the resolved name verbatim).
    fn reserve_module_slot_names(&mut self) {
        self.slot_names = module_slot_names(self.module);
        for n in self.slot_names.values() {
            self.legal.reserve(n);
        }
    }

    /// The emitted name of a module-var slot: the resolved binding name
    /// when file evidence pinned one (G2), else the synthetic fallback.
    fn module_slot_name(&self, index: u32) -> String {
        self.slot_names
            .get(&index)
            .cloned()
            .unwrap_or_else(|| module_slot_fallback(index))
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
                    | Op::TryStoreGlobal { name, .. } => {
                        let n = sym_str(self.module, *name);
                        self.legal.reserve(&sanitize(&n));
                    }
                    Op::GetLexVar { .. } | Op::PutLexVar { .. } => {
                        if let Some(n) = self.scopes.name_of(iid) {
                            self.legal.reserve(&sanitize(n));
                        }
                    }
                    Op::LoadModuleVar { index } | Op::StoreModuleVar { index, .. } => {
                        let n = self.module_slot_name(*index);
                        self.legal.reserve(&n);
                    }
                    Op::GetModuleNamespace { index } => {
                        self.legal.reserve(&namespace_fallback(*index));
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
                if inst.op.is_phi() || observable(&inst.op) || is_statement_op(&inst.op) {
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
    }

    /// One instruction → statement(s) (or nothing, when inlined/dead).
    fn step_inst(
        &mut self,
        iid: InstId,
        op: &Op,
        loc: Option<Loc>,
        block: BlockId,
        out: &mut Vec<Stmt>,
        phi_tail: &mut Vec<(BlockId, Stmt)>,
    ) {
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
                phi_tail.push((
                    edge.from,
                    Stmt::PhiAssign {
                        target: name.clone(),
                        value,
                        to: block,
                        exceptional: edge.kind == EdgeKind::Exceptional,
                    },
                ));
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
            if observable(op) {
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
            .get_or_insert_with(|| crate::classfold::plan(self.module, self.func))
            .as_ref()
            .is_some_and(|fold| fold.call_insts.contains(&iid))
    }

    /// Statement-level ops (scope markers, control, throws, stores).
    fn step_statement_op(&mut self, iid: InstId, op: &Op, loc: Option<Loc>, out: &mut Vec<Stmt>) {
        match op {
            Op::NewLexEnv { num_vars } => {
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
                    .and_then(|lit| match lit {
                        Lit::Array(items) => Some(
                            items
                                .into_iter()
                                .map(|i| match i {
                                    Lit::String(s) => Some(s),
                                    _ => None,
                                })
                                .collect(),
                        ),
                        _ => None,
                    })
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
                    .and_then(|lit| match lit {
                        Lit::Array(items) => Some(
                            items
                                .into_iter()
                                .filter_map(|i| match i {
                                    Lit::String(s) => Some(s),
                                    _ => None,
                                })
                                .collect(),
                        ),
                        _ => None,
                    })
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
            } => {
                self.record(op, Outcome::Expressed);
                let own = matches!(op, Op::StoreOwnPropName { .. });
                let raw = sym_str(self.module, *name);
                out.push(Stmt::StoreProp {
                    object: self.expr_of(*object),
                    dot_legal: is_legal_ident(&raw),
                    name: raw,
                    value: self.expr_of(*value),
                    own,
                });
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
            | Op::StoreOwnPropDyn { object, key, value } => {
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
            Op::StoreSuper { key, value } => {
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
            Op::PutLexVar { level, slot, value } => {
                self.record(op, Outcome::Expressed);
                let name = self
                    .scopes
                    .name_of(iid)
                    .map(str::to_string)
                    .unwrap_or_else(|| format!("v{level}_{slot}"));
                out.push(Stmt::LexStore {
                    level: *level,
                    slot: *slot,
                    name,
                    value: self.expr_of(*value),
                });
            }
            Op::StoreGlobal { name, value } | Op::TryStoreGlobal { name, value } => {
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
        if let Some(&target) = self.alias.get(&v) {
            return self.expr_of(target);
        }
        let Some(value) = self.module.value(v) else {
            return Expr::Fallback {
                op: "<value>",
                note: "unknown ValueId (data, not a panic)",
                operands: vec![],
            };
        };
        match value.def {
            ValueDef::Param(i) => {
                let i = i as usize;
                // Hidden es2abc ABI slots read directly (some es2abc
                // versions read a1 via `mov` instead of ldnewtarget):
                // map them to their JS surface forms. (Dream gate:
                // newtarget-this referenced a dropped `p1`.)
                if self.hidden_params == 3 && i == 1 {
                    Expr::NewTarget
                } else if self.hidden_params == 3 && i == 0 {
                    Expr::Fallback {
                        op: "Param(funcobj)",
                        note: "the hidden function-object slot has no JS surface form",
                        operands: vec![],
                    }
                } else {
                    Expr::Ident(
                        self.param_names
                            .get(i)
                            .cloned()
                            .unwrap_or_else(|| format!("p{i}")),
                    )
                }
            }
            ValueDef::Const(cid) => match lit_of(self.module, cid) {
                Some(lit) => Expr::Lit(lit),
                None => Expr::Fallback {
                    op: "<const>",
                    note: "unknown ConstId (data, not a panic)",
                    operands: vec![],
                },
            },
            ValueDef::ExceptionParam(_) => {
                let name = match self.catch_names.get(&v) {
                    Some(n) => n.clone(),
                    None => {
                        let n = self.legal.mint("e");
                        self.catch_names.insert(v, n.clone());
                        n
                    }
                };
                Expr::Ident(name)
            }
            ValueDef::Inst(iid) => {
                if self.inline.contains(&v) {
                    match self.module.inst(iid).map(|i| i.op.clone()) {
                        Some(op) => self.expr_for(iid, &op),
                        None => Expr::Fallback {
                            op: "<inst>",
                            note: "unknown InstId (data, not a panic)",
                            operands: vec![],
                        },
                    }
                } else {
                    Expr::Temp {
                        value: v,
                        name: self.mint_temp(v),
                    }
                }
            }
        }
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
                    Op::LoadModuleVar { index } => Some(self.module_slot_name(*index)),
                    Op::GetModuleNamespace { index } => Some(namespace_fallback(*index)),
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
                Lit::Number(_) => {
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
                    let (name, kind) = self
                        .module
                        .func(*fid)
                        .map(|f| (sym_str(self.module, f.name), f.kind))
                        .unwrap_or_else(|| (format!("m${}", fid.index()), FunctionKind::Function));
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
                    i += if matches!(items.get(i + 2), Some(Lit::Number(_))) {
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

    /// Build the expression tree of one instruction's op.
    fn expr_for(&mut self, iid: InstId, op: &Op) -> Expr {
        match op {
            Op::BinaryOp { op, left, right } => Expr::Binary {
                op: *op,
                // Operand order (N36): the IR stores `left` = the acc
                // operand and `right` = the vreg operand, but the
                // vendored two-address handlers compute `vreg OP acc` —
                // the semantic expression is `right OP left`. (The d-P4
                // dream gate caught this: `i > 0` decompiled to `0 > i`
                // and local/decrement printed nothing.)
                left: Box::new(self.expr_of(*right)),
                right: Box::new(self.expr_of(*left)),
            },
            Op::UnaryOp { op, operand } => Expr::Unary {
                op: *op,
                operand: Box::new(self.expr_of(*operand)),
            },
            Op::Compare { op, left, right } => Expr::Compare {
                op: *op,
                // Operand order (N36) — same swap as BinaryOp.
                left: Box::new(self.expr_of(*right)),
                right: Box::new(self.expr_of(*left)),
            },
            Op::Mov { src } => self.expr_of(*src),
            Op::LoadConst(cid) => match lit_of(self.module, *cid) {
                Some(lit) => Expr::Lit(lit),
                None => Expr::Fallback {
                    op: "LoadConst",
                    note: "unknown ConstId",
                    operands: vec![],
                },
            },
            Op::AllocObject { shape } => match lit_of(self.module, *shape) {
                Some(Lit::Object(entries)) => Expr::ObjectLit { entries },
                // `createobjectwithbuffer`'s vendor buffer is a FLAT
                // array `[k0, v0, k1, v1, …]` (probe-verified on the
                // corpus, e.g. 9.0.0.0 for-in); interpret pairwise.
                // Method entries pack as `[name, MethodRef, attrs]` —
                // the numeric attributes payload is runtime metadata
                // (dropped, like the class member buffer's). (d-P4
                // dream gate: local/proxy's handler object fell back to
                // `undefined` — "ProxyCreate: handler is not Object".)
                Some(Lit::Array(items)) => match self.parse_shape_buffer(&items) {
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
            Op::AllocArray { shape } => match shape {
                None => Expr::ArrayLit { elements: vec![] },
                Some(cid) => match lit_of(self.module, *cid) {
                    Some(Lit::Array(elements)) => Expr::ArrayLit { elements },
                    _ => Expr::Fallback {
                        op: "AllocArray",
                        note: "shape constant is not an ArrayLiteral",
                        operands: vec![],
                    },
                },
            },
            Op::AllocRegExp { pattern, flags } => Expr::RegExp {
                pattern: sym_str(self.module, *pattern),
                flags: render_regexp_flags(*flags),
            },
            Op::AllocClosure { func } => self.closure_of(*func),
            Op::LoadProp { object, name } => {
                let raw = sym_str(self.module, *name);
                Expr::PropName {
                    object: Box::new(self.expr_of(*object)),
                    dot_legal: is_legal_ident(&raw),
                    name: raw,
                }
            }
            Op::LoadPropIdx { object, index } => Expr::PropIndex {
                object: Box::new(self.expr_of(*object)),
                index: Box::new(self.expr_of(*index)),
            },
            Op::LoadPropDyn { object, key } => Expr::PropDyn {
                object: Box::new(self.expr_of(*object)),
                key: Box::new(self.expr_of(*key)),
            },
            Op::DeleteProp { object, key } => Expr::Delete {
                target: Box::new(Expr::PropDyn {
                    object: Box::new(self.expr_of(*object)),
                    key: Box::new(self.expr_of(*key)),
                }),
            },
            Op::TestProp { object, key } => {
                let key_expr = match key {
                    PropKey::Name(s) => Expr::Lit(Lit::String(sym_str(self.module, *s))),
                    PropKey::Index(k) | PropKey::Dynamic(k) => self.expr_of(*k),
                };
                Expr::Compare {
                    op: CmpOp::In,
                    left: Box::new(key_expr),
                    right: Box::new(self.expr_of(*object)),
                }
            }
            Op::GetTemplateObject { literal } => {
                // G4 RESOLVED (d-P10): the literal operand is the vendor
                // pair [rawStrings, cookedStrings] — resolve BOTH lists.
                let (raw, cooked) = self.template_strings_of(*literal);
                Expr::TemplateObject { raw, cooked }
            }
            Op::CreateIterResultObj { value, done } => Expr::IterResultObj {
                value: Box::new(self.expr_of(*value)),
                done: Box::new(self.expr_of(*done)),
            },
            Op::GetIterator { obj } => self.iter_node(IterOp::GetIterator, *obj),
            Op::GetAsyncIterator { obj } => self.iter_node(IterOp::GetAsyncIterator, *obj),
            Op::IteratorNext { iterator } => self.iter_node(IterOp::Next, *iterator),
            Op::IteratorReturn { iterator } => self.iter_node(IterOp::Return, *iterator),
            Op::IteratorThrow { iterator } => self.iter_node(IterOp::Throw, *iterator),
            Op::GetPropIterator { obj } => self.iter_node(IterOp::GetPropIterator, *obj),
            Op::NextPropName { iterator } => self.iter_node(IterOp::NextPropName, *iterator),
            Op::GetLexVar { .. } => {
                let name = self
                    .scopes
                    .name_of(iid)
                    .map(str::to_string)
                    .unwrap_or_else(|| "v?".to_string());
                Expr::Ident(sanitize(&name))
            }
            Op::TryGetGlobal { name, .. } => {
                let raw = sym_str(self.module, *name);
                if is_legal_ident(&raw) {
                    Expr::Ident(raw)
                } else {
                    // A global whose name is not a legal identifier can
                    // only be referenced through the global object.
                    Expr::PropIndex {
                        object: Box::new(Expr::GlobalThis),
                        index: Box::new(Expr::Lit(Lit::String(raw))),
                    }
                }
            }
            Op::LoadModuleVar { index } => Expr::Ident(self.module_slot_name(*index)),
            Op::GetModuleNamespace { index } => Expr::ModuleNamespace { index: *index },
            Op::DynamicImport { specifier } => Expr::DynamicImport {
                specifier: Box::new(self.expr_of(*specifier)),
            },
            Op::Call {
                callee,
                this,
                args,
                kind,
            } => {
                let callee_expr = if matches!(
                    kind,
                    CallKind::Super | CallKind::SuperSpread | CallKind::SuperForwardAllArgs
                ) {
                    Expr::SuperMarker
                } else {
                    self.expr_of(*callee)
                };
                Expr::Call {
                    callee: Box::new(callee_expr),
                    this: this.map(|t| Box::new(self.expr_of(t))),
                    args: args.iter().map(|a| self.expr_of(*a)).collect(),
                    kind: *kind,
                }
            }
            Op::DefineFunc { body, captures, .. } => self.closure_node(*body, captures.clone()),
            Op::DefineClass {
                ctor,
                heritage,
                members,
                member_attrs,
                ..
            } => self.class_node(*ctor, *heritage, *members, member_attrs.clone(), false),
            Op::DefineSendableClass {
                ctor,
                heritage,
                members,
                member_attrs,
                ..
            } => self.class_node(*ctor, *heritage, *members, member_attrs.clone(), true),
            Op::LoadPrivate { obj, .. } => Expr::PrivateLoad {
                object: Box::new(self.expr_of(*obj)),
                name: self
                    .scopes
                    .name_of(iid)
                    .map(str::to_string)
                    .unwrap_or_else(|| "p?".to_string()),
            },
            Op::TestPrivate { obj, .. } => Expr::PrivateTest {
                object: Box::new(self.expr_of(*obj)),
                name: self
                    .scopes
                    .name_of(iid)
                    .map(str::to_string)
                    .unwrap_or_else(|| "p?".to_string()),
            },
            Op::CreateGenerator { func } => Expr::CreateGenerator {
                func: Box::new(self.expr_of(*func)),
            },
            Op::SuspendGenerator { value, .. } => Expr::Yield {
                value: Box::new(self.expr_of(*value)),
            },
            Op::ResumeGenerator { genobj } => Expr::GeneratorDriver {
                resume: true,
                genobj: Box::new(self.expr_of(*genobj)),
            },
            Op::GetResumeMode { genobj } => Expr::GeneratorDriver {
                resume: false,
                genobj: Box::new(self.expr_of(*genobj)),
            },
            Op::Await { value } => Expr::Await {
                value: Box::new(self.expr_of(*value)),
                uncaught: false,
            },
            Op::AwaitUncaught { value, .. } => Expr::Await {
                // N68/G6: `value` is the accumulator-carried awaited
                // value (the funcobj register operand is machinery,
                // folded away with the async driver).
                value: Box::new(self.expr_of(*value)),
                uncaught: true,
            },
            Op::AsyncResolve { value, .. } => Expr::AsyncDriver {
                resolve: true,
                value: Box::new(self.expr_of(*value)),
            },
            Op::AsyncReject { value, .. } => Expr::AsyncDriver {
                resolve: false,
                value: Box::new(self.expr_of(*value)),
            },
            Op::LoadNewTarget => Expr::NewTarget,
            Op::LoadGlobalObject => Expr::GlobalThis,
            Op::LoadFunction => {
                let name = self
                    .module
                    .func(self.func)
                    .map(|f| sym_str(self.module, f.name))
                    .unwrap_or_default();
                Expr::SelfFunction(name)
            }
            Op::GetUnmappedArgs => Expr::Arguments,
            Op::CopyRestArgs { start_index } => Expr::RestArgs {
                start_index: *start_index,
            },
            Op::LoadSuper { key } => match key {
                SuperKey::Name(s) => Expr::SuperProp {
                    name: Some(sym_str(self.module, *s)),
                    key: None,
                },
                SuperKey::Dynamic(k) => Expr::SuperProp {
                    name: None,
                    key: Some(Box::new(self.expr_of(*k))),
                },
            },
            Op::ArraySpread { dst, index, src } => Expr::ArraySpread {
                dst: Box::new(self.expr_of(*dst)),
                index: Box::new(self.expr_of(*index)),
                src: Box::new(self.expr_of(*src)),
            },
            Op::CreateObjectWithExcludedKeys { obj, keys } => Expr::RestObject {
                obj: Box::new(self.expr_of(*obj)),
                excluded: keys.iter().map(|k| self.expr_of(*k)).collect(),
            },
            other => Expr::Fallback {
                op: op_name(other),
                note: fallback_note(other),
                operands: other.operands().iter().map(|v| self.expr_of(*v)).collect(),
            },
        }
    }

    /// An iteration-plumbing node (hard-7 members flagged Fallback).
    fn iter_node(&mut self, op: IterOp, obj: ValueId) -> Expr {
        let status = match op {
            IterOp::Return | IterOp::Throw => NodeStatus::Fallback,
            _ => NodeStatus::Plumbing,
        };
        Expr::Iter {
            op,
            obj: Box::new(self.expr_of(obj)),
            status,
        }
    }

    /// `AllocClosure`: pair with the `DefineFunc` def (through `Mov`s).
    fn closure_of(&mut self, func: ValueId) -> Expr {
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
                        return self.closure_node(body, captures);
                    }
                    _ => break,
                },
                _ => break,
            }
        }
        Expr::Fallback {
            op: "AllocClosure",
            note: "func operand is not a DefineFunc def-chain",
            operands: vec![self.expr_of(func)],
        }
    }

    /// The deferred closure node.
    fn closure_node(&mut self, body: FuncId, captures: Vec<(Sym, ValueId)>) -> Expr {
        let (name, kind) = self
            .module
            .func(body)
            .map(|f| (sym_str(self.module, f.name), f.kind))
            .unwrap_or_else(|| (format!("<fn#{}>", body.index()), FunctionKind::Function));
        Expr::Closure {
            body,
            name,
            kind,
            captures: captures
                .into_iter()
                .map(|(s, v)| (sym_str(self.module, s), self.expr_of(v)))
                .collect(),
        }
    }

    /// The deferred class node.
    fn class_node(
        &mut self,
        ctor: FuncId,
        heritage: Option<ValueId>,
        members: ConstId,
        member_attrs: Vec<abcd_ir::op::MemberAttrs>,
        sendable: bool,
    ) -> Expr {
        let name = self
            .module
            .func(ctor)
            .map(|f| sym_str(self.module, f.name))
            .unwrap_or_else(|| format!("<fn#{}>", ctor.index()));
        Expr::Class {
            ctor,
            name,
            heritage: heritage.map(|h| Box::new(self.expr_of(h))),
            members,
            member_attrs,
            sendable,
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
            return match lit_of(self.module, cid) {
                Some(Lit::Array(items)) => {
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
                _ => (None, None),
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
                Op::StoreOwnPropDyn { object, key, value }
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
            return match lit_of(self.module, cid)? {
                Lit::Array(items) => Some(items),
                _ => None,
            };
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
            let Some(inst) = self.module.inst(user) else {
                return None;
            };
            match &inst.op {
                Op::StoreOwnPropDyn { object, key, value }
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
            _ => None,
        }
    }

    /// Resolve a value to a constant literal, through `Mov`s.
    fn lit_value_of(&self, v: ValueId) -> Option<Lit> {
        let cid = const_id_of(self.module, chase_mov(self.module, v))?;
        lit_of(self.module, cid)
    }
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
