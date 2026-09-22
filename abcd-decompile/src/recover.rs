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
use crate::expr::{Expr, IterOp, Lit, NodeStatus};
use crate::fitness::{Fitness, elision_reason, fallback_note, fitness_of, op_name};
use crate::legalize::{Legalizer, is_legal_ident, sanitize};
use crate::names::{
    NameScopes, local_name_in, module_slot_fallback, namespace_fallback, op_name_hint,
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
    /// The legalized parameter names (`params[0]` is `this`, T4).
    pub params: Vec<String>,
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
    /// Legalized parameter names (`params[0]` = `this`).
    param_names: Vec<String>,
    /// `ExceptionParam` value → legalized catch binding name.
    catch_names: HashMap<ValueId, String>,
    /// Handler block → catch binding names (block-head markers).
    handler_binds: HashMap<BlockId, Vec<String>>,
    /// inst → (block, position in block).
    inst_pos: HashMap<InstId, (BlockId, usize)>,
    /// block → prefix sums of observable-effect instruction counts.
    barriers: HashMap<BlockId, Vec<u32>>,
    histogram: BTreeMap<&'static str, OpStat>,
}

impl<'m> Recover<'m> {
    fn new(module: &'m Module, func: FuncId) -> Self {
        let mut r = Recover {
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
                blocks: Vec::new(),
                histogram: BTreeMap::new(),
            };
        };
        let name = sym_str(self.module, f.name);
        let kind = f.kind;
        let block_ids = f.blocks.clone();

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
        for i in 0..n {
            if i == 0 {
                // T4: params[0] is the `this` binding.
                self.param_names.push("this".to_string());
                continue;
            }
            // The debug param list may or may not include `this`:
            // equal length → direct index; otherwise assume it excludes
            // `this` (offset by one).
            let raw = if debug_param_names.len() == n {
                debug_param_names.get(i).cloned()
            } else {
                debug_param_names.get(i - 1).cloned()
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
                        self.legal.reserve(&module_slot_fallback(*index));
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
                out.push(Stmt::Expr(Expr::DefineGetterSetter {
                    obj: Box::new(self.expr_of(*obj)),
                    key: Box::new(self.expr_of(*key)),
                    getter: Box::new(self.expr_of(*getter)),
                    setter: Box::new(self.expr_of(*setter)),
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
                    name: module_slot_fallback(*index),
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
            ValueDef::Param(i) => Expr::Ident(
                self.param_names
                    .get(i as usize)
                    .cloned()
                    .unwrap_or_else(|| format!("p{i}")),
            ),
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
                    Op::LoadModuleVar { index } => Some(module_slot_fallback(*index)),
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

    /// Build the expression tree of one instruction's op.
    fn expr_for(&mut self, iid: InstId, op: &Op) -> Expr {
        match op {
            Op::BinaryOp { op, left, right } => Expr::Binary {
                op: *op,
                left: Box::new(self.expr_of(*left)),
                right: Box::new(self.expr_of(*right)),
            },
            Op::UnaryOp { op, operand } => Expr::Unary {
                op: *op,
                operand: Box::new(self.expr_of(*operand)),
            },
            Op::Compare { op, left, right } => Expr::Compare {
                op: *op,
                left: Box::new(self.expr_of(*left)),
                right: Box::new(self.expr_of(*right)),
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
                Some(Lit::Array(items)) => {
                    if items.len() % 2 == 0
                        && items
                            .chunks_exact(2)
                            .all(|p| matches!(p[0], Lit::String(_) | Lit::Number(_)))
                    {
                        Expr::ObjectLit {
                            entries: items
                                .chunks_exact(2)
                                .map(|p| (p[0].clone(), p[1].clone()))
                                .collect(),
                        }
                    } else {
                        Expr::Fallback {
                            op: "AllocObject",
                            note: "shape buffer is not a flat key/value array",
                            operands: vec![],
                        }
                    }
                }
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
                // G4 (registered by d-P0): cooked-only fallback. The
                // cooked strings resolve only when the literal operand is
                // a const string array.
                let cooked = self.const_string_array_of(*literal);
                Expr::TemplateObject { cooked }
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
            Op::LoadModuleVar { index } => Expr::Ident(module_slot_fallback(*index)),
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
                ..
            } => self.class_node(*ctor, *heritage, *members, false),
            Op::DefineSendableClass {
                ctor,
                heritage,
                members,
                ..
            } => self.class_node(*ctor, *heritage, *members, true),
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
            Op::AwaitUncaught { value } => Expr::Await {
                value: Box::new(self.expr_of(*value)),
                uncaught: true,
            },
            Op::AsyncResolve { value } => Expr::AsyncDriver {
                resolve: true,
                value: Box::new(self.expr_of(*value)),
            },
            Op::AsyncReject { value } => Expr::AsyncDriver {
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
            sendable,
        }
    }

    /// Resolve a value to a const string array (template cooked strings).
    fn const_string_array_of(&self, v: ValueId) -> Option<Vec<Lit>> {
        let value = self.module.value(v)?;
        let cid = match value.def {
            ValueDef::Const(cid) => Some(cid),
            ValueDef::Inst(iid) => match &self.module.inst(iid)?.op {
                Op::LoadConst(cid) => Some(*cid),
                _ => None,
            },
            _ => None,
        }?;
        match lit_of(self.module, cid)? {
            Lit::Array(items) => Some(items),
            _ => None,
        }
    }
}
