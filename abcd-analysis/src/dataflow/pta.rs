//! Rung 2 — whole-module `k=1` context-sensitive Andersen-style subset
//! pointer analysis (`design/analysis.md`, `design/ir.md`,
//! `design/decisions.md` N20/N66).
//!
//! ## Core algorithmic model
//!
//! An Andersen-style, subset-based, **field-sensitive, 1-call-site
//! context-sensitive** pointer analysis over the whole module:
//!
//! - **Abstract objects keyed by `(alloc InstId, context)`**: each allocation
//!   site has a unique, stable [`InstId`] paired with a **1-call-site**
//!   context (`None` = the module-wide base activation; `Some(call)` = the
//!   activation entered through `call`), `k`-limited to depth 1. Deeper
//!   call-string contexts and receiver-object sensitivity are intentionally
//!   out of scope at this rung (`design/analysis.md`).
//! - **On-the-fly call-graph/PTA co-evolution**: a call
//!   site's callee value gaining a closure object wires the edge
//!   (arguments → parameters through the N66 frame-slot model, callee
//!   returns → the call result) and activates the callee body under
//!   `Some(call)`; new edges feed propagation and new points-to feeds
//!   resolution in ONE worklist. The output [`CallGraph`] therefore
//!   resolves callees loaded from object fields, array elements, global
//!   bindings, and own-property method stores through value flow.
//! - **Per-object field sensitivity**: each abstract
//!   object has three field buckets — `Named(Sym)`, `Index`
//!   (integer-index stores), `Dynamic` (computed-key stores) — matching
//!   the [`crate::dataflow::heap::FieldKey`] vocabulary. Reads are
//!   may-conservative across buckets: a named read sees `Named ∪
//!   Dynamic`, an index read sees `Index ∪ Dynamic`, a computed read
//!   sees every bucket (re-armed when a new bucket appears on an object
//!   it already read).
//! - **Two-half delta worklist propagation**: a new `(pointer, object)` fact
//!   replays down every existing out-edge, and a new edge `s → t`
//!   immediately emits `(t, o)` for every object already in `s`.
//!   Statement-level handlers (stores/loads/calls) are indexed by base
//!   pointer and fire once per `(handler, object)` pair without whole-graph
//!   re-sweeps.
//! - **Scope gating**: the module is the whole program;
//!   every function gets a base (`None`-context) activation so alloc
//!   sites in never-called code still key objects, and context-variant
//!   activations appear only through resolved edges. Framework/native
//!   behavior enters only through explicit downstream summaries or lifecycle
//!   harnesses ([`crate::ohos_lifecycle`]), never by reaching outside the
//!   module.
//!
//! ## Bytecode-native function values
//!
//! There is **no CHA fallback**: dynamic Panda-bytecode values carry no
//! declared receiver types, so the call graph uses ONE resolution mechanism
//! — points-to on the callee value. Function values are first-class heap
//! objects: `AllocClosure`/`CreateGenerator`/`DefineFunc`/
//! `LoadConst(MethodRef)`/`LoadFunction` seed *callable* abstract objects
//! whose body drives call resolution. Allocation seeding covers all four
//! keyed `Alloc*` ops (`AllocObject`, `AllocArray`, `AllocClosure`,
//! `AllocRegExp`), so object and array literals that never touch `new` are
//! first-class allocations.
//!
//! ## The soundness contract (rung-0 floor, unchanged)
//!
//! [`Rung2AliasOracle::site_info_at`] returns the PTA answer only when it
//! is complete (no `Obj::Unknown` in the value's set, no unkeyed
//! objects, no cap cut); anything else degrades to the rung-0 local
//! def-chain answer — the ladder's rule that climbing can only make
//! keying *more* precise, never less sound. `Unknown` is seeded by:
//! `TryGetGlobal` results (host bindings/absence), parameters of base
//! activations (unrecorded callers), calls whose callee set contains
//! `Unknown` (partial resolution), and loads whose field buckets stayed
//! empty (inherited/reflected/native properties — the documented
//! reflection gap). Parameter answers use the **balanced discipline**:
//! when a function has recorded call-site contexts, its parameter's
//! answer is the union over those contexts only (the base activation's
//! `Unknown` is the "called from nowhere recorded" marker and applies
//! only when no recorded context exists).
//!
//! ## Lexical environments (b2)
//!
//! `GetLexVar`/`PutLexVar` carry no environment operand, so environment
//! identity is reconstructed by a dedicated flow analysis (the
//! `EnvTables` built by [`analyze`]): `NewLexEnv`/
//! `NewLexEnvWithName` instructions are environment allocation sites; a
//! forward per-function dataflow tracks the environment stack at every
//! instruction (push on `NewLexEnv`, pop on `PopLexEnv`); a closure's
//! captured chain is the stack at its `AllocClosure`/`DefineFunc` site,
//! computed to a fixed point over the module (recursion merges — the
//! documented context-insensitivity of this channel). The rung-2 oracle
//! exposes it as [`Rung2AliasOracle::lex_env_at`]; the taint layer keys
//! lexical-slot facts by environment site instead of the
//! function-agnostic `(level, slot)` pair, which is what separates b2's
//! two colliding captures.
//!
//! ## Determinism and budgets (N20)
//!
//! All sets and maps are `BTree*`; the worklist pops the minimum
//! `(pointer, object)` pair; activations are scanned in `(FuncId,
//! context)` order; handler ids are assigned in scan order. Two runs
//! over the same module are byte-identical (the corpus smoke pins it).
//! The engine is finite by construction (objects = sites × contexts,
//! pointers bounded likewise), so the fixed point always terminates; a
//! generous [`PtaConfig::step_budget`] guards pathological inputs — a
//! cut sets [`PtaStats::capped`] and the driver degrades to rung 1
//! (sound, loud).

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::sync::Arc;

use abcd_ir::{
    CallKind, ClassId, Const, ConstId, FuncId, InstId, Module, Op, Sym, ValueDef, ValueId,
};

use super::alias::QueryAnswer;
use super::heap::{AliasOracle, AllocSiteSet, SiteInfo, is_keyed_alloc, resolve_alloc_sites};
use super::ifds::CallGraphOracle;
use crate::callgraph::{CallEdge, CallEdgeKind, CallGraph, CallTargets};
use crate::frame::frame_slots_of;
use crate::module_link::{ModuleLinkTable, ModuleSlotRef};

/// Default propagation-step budget (worklist pops). Generous — corpus
/// modules are small; the cap exists so a pathological module degrades
/// loudly to rung 1 instead of hanging the driver.
pub const DEFAULT_STEP_BUDGET: usize = 25_000_000;

/// Default lexical-environment stack depth cap. Closure capture chains
/// in real bytecode are short (registration → wrapper → callback ≈ 3–4);
/// beyond the cap the outer environments are dropped, so deep
/// `GetLexVar` levels answer unknown (sound).
pub const DEFAULT_MAX_ENV_DEPTH: usize = 8;

/// Maximum static forward call-graph / module-import BFS hops in root-sliced PTA.
const MAX_SLICED_BASE_HOP: u8 = 3;

/// Maximum dynamic closure / module-init / lex-owner hops in root-sliced PTA.
const MAX_SLICED_DYN_HOP: u8 = 5;

/// Maximum non-root / non-harness-seed functions added by `compute_sliced_bfs`.
const MAX_SLICED_EXTRA_FUNCS: usize = 768;

/// The 1-call-site calling context: `None` is the module-wide base
/// activation, `Some(call)` the activation entered through `call`.
pub type Ctx = Option<InstId>;

/// An abstract heap object.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Obj {
    /// Provenance the analysis cannot see (host bindings, unrecorded
    /// callers, partial resolution, inherited properties). Presence in a
    /// points-to set marks the answer incomplete (the rung-0 fallback
    /// trigger) — never a keyed site.
    Unknown,
    /// An allocation-site object.
    Site {
        /// The allocating instruction (`InstId` — unique and stable across
        /// the module arena).
        site: InstId,
        /// The activation context the allocation ran in.
        ctx: Ctx,
        /// The function body, when this object is callable (closures,
        /// `DefineFunc` values, pooled method references).
        callable: Option<FuncId>,
        /// Whether the site is one of the four rung-0 keyed `Alloc*`
        /// kinds (T7). Unkeyed objects (function values, generators)
        /// drive call resolution but are never REPORTED as sites — the
        /// taint layer's key vocabulary is unchanged by climbing.
        keyed: bool,
    },
}

/// A field bucket of an abstract object (the
/// [`super::heap::FieldKey`] vocabulary, per object).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Slot {
    /// A statically named property.
    Named(Sym),
    /// An integer-index element.
    Index,
    /// A computed-key property.
    Dynamic,
}

/// A pointer (a node of the pointer-flow graph).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Ptr {
    /// An SSA value in an activation.
    Local(ValueId, Ctx),
    /// A field bucket of one abstract object `(site, ctx)`.
    Field(InstId, Ctx, Slot),
    /// A named global binding (the module-global object's field — d4).
    Global(Sym),
    /// A per-record module-variable slot `(ClassId, local_slot)`.
    ModuleVar(ClassId, u32),
    /// A lexical-environment slot `(NewLexEnv InstId, slot, is_recorded_ctx)`.
    LexVar(InstId, u16, bool),
}

/// Which buckets a load reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Read {
    /// `Named(name)` ∪ `Dynamic`.
    Named(Sym),
    /// `Index` ∪ `Dynamic`.
    Index,
    /// Every bucket (re-armed when a new bucket appears).
    All,
}

/// A statement-level handler, fired once per `(handler, object)`:
/// stores and loads indexed by their base pointer, calls by their
/// callee pointer.
#[derive(Clone, Copy, Debug)]
enum Handler {
    /// `object.slot = value`: on object `o`, edge `value → o.slot`.
    Store { value: Ptr, slot: Slot },
    /// `result = object[read]`: on object `o`, edges `o.bucket → result`.
    Load { result: Ptr, read: Read },
    /// `object(...)`: on callable object, wire the call edge.
    Call { call: InstId, caller_ctx: Ctx },
}

/// Engine configuration.
#[derive(Clone, Copy, Debug)]
pub struct PtaConfig {
    /// Propagation-step budget (worklist pops); a cut sets
    /// [`PtaStats::capped`] and the driver degrades to rung 1.
    pub step_budget: usize,
    /// Lexical-environment stack depth cap.
    pub max_env_depth: usize,
}

impl Default for PtaConfig {
    fn default() -> Self {
        PtaConfig {
            step_budget: DEFAULT_STEP_BUDGET,
            max_env_depth: DEFAULT_MAX_ENV_DEPTH,
        }
    }
}

/// Engine counters (cost accounting + the cap-cut metric).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PtaStats {
    /// Function activations scanned (`(FuncId, context)` pairs).
    pub activations: usize,
    /// Points-to facts propagated (worklist inserts).
    pub facts: usize,
    /// Pointer-flow edges created.
    pub flow_edges: usize,
    /// Call edges the co-evolution resolved (PTA side, before the
    /// base-graph union).
    pub call_edges_resolved: usize,
    /// Call-site activations whose callee set contained `Unknown`.
    pub call_sites_partial: usize,
    /// Fixed-point rounds of the lexical-environment capture analysis.
    pub env_rounds: usize,
    /// The step budget fired (the driver degrades to rung 1).
    pub capped: bool,
}

/// The rung-2 answer to a lexical-environment query: the environment
/// objects a `GetLexVar`/`PutLexVar` at `level` may denote.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EnvAnswer {
    /// The `NewLexEnv`/`NewLexEnvWithName` sites (context-insensitive —
    /// recursion merges, documented).
    pub sites: AllocSiteSet,
    /// The access read past the known stack (or through an unknown
    /// entry): the answer is a lower bound.
    pub has_unknown: bool,
}

/// One lexical-environment stack entry.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct EnvEntry {
    sites: BTreeSet<InstId>,
    unknown: bool,
}

/// A value's stripped answer.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ValueAnswer {
    sites: AllocSiteSet,
    has_unknown: bool,
}

/// The precomputed query tables (the oracle's data; built once at the
/// end of [`analyze`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rung2Tables {
    /// Value index → stripped answer (keyed sites + completeness).
    answers: Vec<ValueAnswer>,
    /// Instruction index → lexical-environment stack BEFORE it, innermost
    /// last.
    env_stack_at: Vec<Arc<[EnvEntry]>>,
    /// Instruction index → whether it is a `NewLexEnv`/`NewLexEnvWithName`.
    env_sites: Vec<bool>,
}

/// The outcome of [`analyze`]: the co-evolved call graph plus the
/// query tables and counters.
pub struct PtaOutcome {
    graph: CallGraph,
    tables: Rung2Tables,
    stats: PtaStats,
}

impl PtaOutcome {
    /// The co-evolved call graph (base edges ∪ PTA-resolved edges).
    pub fn graph(&self) -> &CallGraph {
        &self.graph
    }

    /// The engine counters.
    pub fn stats(&self) -> &PtaStats {
        &self.stats
    }

    /// Split into the graph (for the solver), the tables (for the
    /// oracle), and the counters.
    pub fn into_parts(self) -> (CallGraph, Rung2Tables, PtaStats) {
        (self.graph, self.tables, self.stats)
    }
}

/// The function body a closure-creating op wraps, through the
/// `DefineFunc`/`Mov` def chain (T4) — the call graph's
/// `trace_alloc_site` discipline as an `Option` query.
fn closure_body(module: &Module, func: ValueId) -> Option<FuncId> {
    let mut visiting = BTreeSet::new();
    let mut current = func;
    loop {
        if !visiting.insert(current) {
            return None;
        }
        let v = module.value(current)?;
        let ValueDef::Inst(iid) = v.def else {
            return None;
        };
        match module.inst(iid).map(|i| &i.op) {
            Some(Op::Mov { src }) => current = *src,
            Some(Op::DefineFunc { body, .. }) => return Some(*body),
            _ => return None,
        }
    }
}

/// Resolve any callable `FuncId` wrapped by `val` across `Mov`,
/// `AllocClosure`, `CreateGenerator`, `DefineMethod`, `DefineFunc`, and
/// `MethodRef` constants (cycle-guarded).
fn callable_body(module: &Module, mut val: ValueId) -> Option<FuncId> {
    let mut visiting = BTreeSet::new();
    loop {
        if !visiting.insert(val) {
            return None;
        }
        let v = module.value(val)?;
        match v.def {
            ValueDef::Const(c) => {
                return match module.consts.get(c) {
                    Some(Const::MethodRef(f)) => Some(*f),
                    _ => None,
                };
            }
            ValueDef::Inst(iid) => match &module.inst(iid)?.op {
                Op::Mov { src }
                | Op::AllocClosure { func: src }
                | Op::CreateGenerator { func: src }
                | Op::DefineMethod { func: src, .. } => {
                    val = *src;
                }
                Op::DefineFunc { body, .. } => return Some(*body),
                Op::LoadConst(c) => {
                    return match module.consts.get(*c) {
                        Some(Const::MethodRef(f)) => Some(*f),
                        _ => None,
                    };
                }
                _ => return None,
            },
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return None,
        }
    }
}

/// Whether `val` traces (through `Mov`) to a constant (`ValueDef::Const` or
/// `Op::LoadConst`).
fn is_load_const(module: &Module, mut val: ValueId) -> bool {
    let mut visiting = BTreeSet::new();
    loop {
        if !visiting.insert(val) {
            return false;
        }
        let Some(v) = module.value(val) else {
            return false;
        };
        match v.def {
            ValueDef::Const(_) => return true,
            ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
                Some(Op::Mov { src }) => val = *src,
                Some(Op::LoadConst(_)) => return true,
                _ => return false,
            },
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return false,
        }
    }
}

/// Extract all member `FuncId`s from a `DefineClass` / `DefineSendableClass`
/// member-buffer constant.
fn class_member_funcs(module: &Module, members: ConstId) -> Vec<FuncId> {
    let mut out = Vec::new();
    match module.consts.get(members) {
        Some(Const::ArrayLiteral(items)) => {
            for &item_cid in items {
                if let Some(Const::MethodRef(mfid)) = module.consts.get(item_cid) {
                    out.push(*mfid);
                }
            }
        }
        Some(Const::ObjectLiteral { values, .. }) => {
            for &item_cid in values {
                if let Some(Const::MethodRef(mfid)) = module.consts.get(item_cid) {
                    out.push(*mfid);
                }
            }
        }
        _ => {}
    }
    out
}

/// Collect component `this` receivers inside `__abcd_ohos_harness__` that
/// belong to an Ability / ExtensionAbility (`StoreProp(inst, "context", ..)`
/// or non-`LoadConst` lifecycle arguments) or to a component with at least
/// one method/constructor in `root_keep`.
fn collect_active_harness_receivers_in(
    module: &Module,
    base: &CallGraph,
    blocks: &[abcd_ir::BlockId],
    root_keep: &BTreeSet<FuncId>,
) -> BTreeSet<ValueId> {
    let mut active = BTreeSet::new();
    for &b in blocks {
        let Some(bb) = module.block(b) else {
            continue;
        };
        for &iid in &bb.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            match &inst.op {
                Op::StoreProp { object, name, .. }
                    if module.sym.resolve(*name) == Some("context")
                        && !is_load_const(module, *object) =>
                {
                    active.insert(*object);
                }
                Op::Call {
                    this: Some(t),
                    args,
                    ..
                } if !is_load_const(module, *t) => {
                    let has_non_const_arg = args.iter().any(|&a| !is_load_const(module, a));
                    let has_rooted_callee = base
                        .callees_of_call_at(iid)
                        .iter()
                        .any(|c| root_keep.contains(c));
                    if has_non_const_arg || has_rooted_callee {
                        active.insert(*t);
                    }
                }
                _ => {}
            }
        }
    }
    active
}

/// Precompute the deterministic bounded forward slice (`slice_allow`, `func_hop`)
/// for root-sliced PTA (`roots = Some(root_funcs)`), starting at hop `0` from
/// non-harness `root_funcs` and hop `1` from active `OHOS_HARNESS_FUNC` callees,
/// expanding up to `max_base_hop` hops (capped at [`MAX_SLICED_EXTRA_FUNCS`]
/// newly discovered functions) without recursion.
fn compute_sliced_bfs(
    module: &Module,
    links: &ModuleLinkTable,
    base: &CallGraph,
    env_stack_at: &[Arc<[EnvEntry]>],
    root_funcs: &[FuncId],
    root_keep: &BTreeSet<FuncId>,
    max_base_hop: u8,
) -> (Vec<bool>, Vec<u8>) {
    let mut func_hop = vec![u8::MAX; module.functions.len()];
    let mut queue: VecDeque<FuncId> = VecDeque::new();

    let enqueue_seed = |f: FuncId, hop: u8, func_hop: &mut [u8], queue: &mut VecDeque<FuncId>| {
        if hop > max_base_hop {
            return;
        }
        let Some(fd) = module.func(f) else {
            return;
        };
        if fd.is_external || fd.blocks.is_empty() {
            return;
        }
        if let Some(slot) = func_hop.get_mut(f.index())
            && hop < *slot
        {
            *slot = hop;
            queue.push_back(f);
        }
    };

    let mut harness_roots = Vec::new();
    for &func in root_funcs {
        let Some(fd) = module.func(func) else {
            continue;
        };
        if fd.is_external || fd.blocks.is_empty() {
            continue;
        }
        if module.sym.resolve(fd.name) == Some(crate::ohos_lifecycle::OHOS_HARNESS_FUNC) {
            if let Some(slot) = func_hop.get_mut(func.index()) {
                *slot = 0;
            }
            harness_roots.push(func);
        } else {
            enqueue_seed(func, 0, &mut func_hop, &mut queue);
        }
    }

    // Enqueue active harness callees at hop `1` after all hop-`0` roots so
    // `queue` stays monotonically ordered by hop distance.
    for hfunc in harness_roots {
        let Some(fd) = module.func(hfunc) else {
            continue;
        };
        let active_receivers =
            collect_active_harness_receivers_in(module, base, &fd.blocks, root_keep);
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if let Op::Call { this, args, .. } = &inst.op {
                    let has_non_const_arg = args.iter().any(|&a| !is_load_const(module, a));
                    let has_active_this = this.is_some_and(|t| active_receivers.contains(&t))
                        || inst.result.is_some_and(|r| active_receivers.contains(&r));
                    for &target_callee in base.callees_of_call_at(iid) {
                        if has_non_const_arg
                            || has_active_this
                            || root_keep.contains(&target_callee)
                        {
                            enqueue_seed(target_callee, 1, &mut func_hop, &mut queue);
                        }
                    }
                }
            }
        }
    }

    let mut extra_enqueued = 0usize;
    let enqueue_extra = |f: FuncId,
                         hop: u8,
                         func_hop: &mut [u8],
                         queue: &mut VecDeque<FuncId>,
                         extra_enqueued: &mut usize| {
        if hop > max_base_hop || *extra_enqueued >= MAX_SLICED_EXTRA_FUNCS {
            return;
        }
        let Some(fd) = module.func(f) else {
            return;
        };
        if fd.is_external || fd.blocks.is_empty() {
            return;
        }
        if let Some(slot) = func_hop.get_mut(f.index())
            && hop < *slot
        {
            if *slot == u8::MAX {
                *extra_enqueued += 1;
            }
            *slot = hop;
            queue.push_back(f);
        }
    };

    while let Some(cur) = queue.pop_front() {
        if extra_enqueued >= MAX_SLICED_EXTRA_FUNCS {
            break;
        }
        let cur_hop = func_hop.get(cur.index()).copied().unwrap_or(u8::MAX);
        if cur_hop >= max_base_hop {
            continue;
        }
        let next_hop = cur_hop + 1;
        let Some(fd) = module.func(cur) else {
            continue;
        };
        let func_class_id = fd.class_id;
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                if extra_enqueued >= MAX_SLICED_EXTRA_FUNCS {
                    break;
                }
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::Call { .. } => {
                        for &callee in base.callees_of_call_at(iid) {
                            enqueue_extra(
                                callee,
                                next_hop,
                                &mut func_hop,
                                &mut queue,
                                &mut extra_enqueued,
                            );
                        }
                    }
                    Op::DefineFunc { body, .. } => {
                        enqueue_extra(
                            *body,
                            next_hop,
                            &mut func_hop,
                            &mut queue,
                            &mut extra_enqueued,
                        );
                    }
                    Op::DefineMethod { func: inner, .. } => {
                        if let Some(body) = callable_body(module, *inner) {
                            enqueue_extra(
                                body,
                                next_hop,
                                &mut func_hop,
                                &mut queue,
                                &mut extra_enqueued,
                            );
                        }
                    }
                    Op::LoadModuleVar { index, kind } => {
                        if kind.is_local() {
                            let slot_ref = ModuleSlotRef {
                                class_id: func_class_id,
                                slot: *index,
                            };
                            for &(def_fn, _) in links.stored_values(slot_ref) {
                                enqueue_extra(
                                    def_fn,
                                    next_hop,
                                    &mut func_hop,
                                    &mut queue,
                                    &mut extra_enqueued,
                                );
                            }
                        } else if let Some(target) = links.external_load(func_class_id, *index) {
                            for &slot_ref in &target.slots {
                                for &(def_fn, _) in links.stored_values(slot_ref) {
                                    enqueue_extra(
                                        def_fn,
                                        next_hop,
                                        &mut func_hop,
                                        &mut queue,
                                        &mut extra_enqueued,
                                    );
                                }
                            }
                        }
                    }
                    Op::GetModuleNamespace { index } => {
                        if let Some(target_cid) = links.namespace_target(func_class_id, *index)
                            && let Some(exports) = links.namespace_exports(target_cid)
                        {
                            for slots in exports.values() {
                                for &sr in slots {
                                    for &(def_fn, _) in links.stored_values(sr) {
                                        enqueue_extra(
                                            def_fn,
                                            next_hop,
                                            &mut func_hop,
                                            &mut queue,
                                            &mut extra_enqueued,
                                        );
                                    }
                                }
                            }
                        }
                    }
                    Op::GetLexVar { level, .. } => {
                        if let Some(stack) = env_stack_at.get(iid.index())
                            && (*level as usize) < stack.len()
                        {
                            let entry = &stack[stack.len() - 1 - *level as usize];
                            if !entry.unknown {
                                for &env_site in &entry.sites {
                                    if let Some(owner_fn) = links.inst_func(module, env_site) {
                                        enqueue_extra(
                                            owner_fn,
                                            next_hop,
                                            &mut func_hop,
                                            &mut queue,
                                            &mut extra_enqueued,
                                        );
                                    }
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    let slice_allow = func_hop.iter().map(|&h| h <= max_base_hop).collect();
    (slice_allow, func_hop)
}

/// Initial root-slicing state passed into `Pta::new`.
struct SliceInit {
    root_keep: BTreeSet<FuncId>,
    slice_allow: Vec<bool>,
    func_hop: Vec<u8>,
    max_dyn_hop: u8,
}

/// The engine state.
struct Pta<'m> {
    module: &'m Module,
    links: &'m ModuleLinkTable,
    base: &'m CallGraph,
    config: &'m PtaConfig,
    env_stack_at: &'m [Arc<[EnvEntry]>],
    /// Root set when running in demand-driven / root-sliced mode (`None` =
    /// whole-module mode).
    root_keep: Option<BTreeSet<FuncId>>,
    /// Bounded static forward-slice allowlist (`Some` iff `roots.is_some()`).
    slice_allow: Option<Vec<bool>>,
    /// Per-function hop distance from roots in sliced mode (`u8::MAX` if unreached).
    func_hop: Vec<u8>,
    /// Maximum dynamic closure / module-init / lex-owner hop distance in sliced mode.
    max_dyn_hop: u8,
    /// Points-to sets.
    pts: BTreeMap<Ptr, BTreeSet<Obj>>,
    /// Subset edges `s → t`.
    edges: BTreeMap<Ptr, BTreeSet<Ptr>>,
    /// Pending `(pointer, object)` facts (the delta worklist — pop min).
    worklist: BTreeSet<(Ptr, Obj)>,
    /// Activations requested so far.
    activated: BTreeSet<(FuncId, Ctx)>,
    /// Activations requested but not yet scanned (pop min).
    pending_activations: BTreeSet<(FuncId, Ctx)>,
    /// Activations already scanned.
    scanned: BTreeSet<(FuncId, Ctx)>,
    /// Handlers in registration (scan) order — the id is the index.
    handlers: Vec<(Ptr, Handler)>,
    /// Handler ids registered per base pointer (lookup-only map).
    handlers_by_base: HashMap<Ptr, Vec<u32>>,
    /// `(handler, object)` pairs already fired.
    fired: BTreeSet<(u32, Obj)>,
    /// Dynamic-read `(handler id, object)` pairs indexed by `(site, ctx)`
    /// (lookup-only map; `BTreeSet` values preserve deterministic `(id, o)` order).
    dyn_loads_by_obj: HashMap<(InstId, Ctx), BTreeSet<(u32, Obj)>>,
    /// Buckets known per object `(site, ctx)` — a NEW bucket re-arms
    /// the dynamic reads that already fired on the object.
    buckets: BTreeMap<(InstId, Ctx), BTreeSet<Slot>>,
    /// Wired call edges `(call, caller ctx, callee)`.
    wired: BTreeSet<(InstId, Ctx, FuncId)>,
    /// PTA-resolved call targets `(call, caller ctx)` → bodies.
    call_targets: BTreeMap<(InstId, Ctx), BTreeSet<FuncId>>,
    /// Call-site activations whose callee set contained `Unknown`.
    call_unknown: BTreeSet<(InstId, Ctx)>,
    /// Load-result pointers (the empty-bucket post-pass).
    load_results: Vec<Ptr>,
    /// Lazily populated `FuncId` → returned values (block/inst order).
    returns_of: HashMap<FuncId, Vec<ValueId>>,
    stats: PtaStats,
}

impl<'m> Pta<'m> {
    fn new(
        module: &'m Module,
        links: &'m ModuleLinkTable,
        base: &'m CallGraph,
        config: &'m PtaConfig,
        env_stack_at: &'m [Arc<[EnvEntry]>],
        slice_init: Option<SliceInit>,
    ) -> Self {
        let (root_keep, slice_allow, func_hop, max_dyn_hop) = match slice_init {
            Some(s) => (
                Some(s.root_keep),
                Some(s.slice_allow),
                s.func_hop,
                s.max_dyn_hop,
            ),
            None => (None, None, Vec::new(), MAX_SLICED_DYN_HOP),
        };
        Pta {
            module,
            links,
            base,
            config,
            env_stack_at,
            root_keep,
            slice_allow,
            func_hop,
            max_dyn_hop,
            pts: BTreeMap::new(),
            edges: BTreeMap::new(),
            worklist: BTreeSet::new(),
            activated: BTreeSet::new(),
            pending_activations: BTreeSet::new(),
            scanned: BTreeSet::new(),
            handlers: Vec::new(),
            handlers_by_base: HashMap::new(),
            fired: BTreeSet::new(),
            dyn_loads_by_obj: HashMap::new(),
            buckets: BTreeMap::new(),
            wired: BTreeSet::new(),
            call_targets: BTreeMap::new(),
            call_unknown: BTreeSet::new(),
            load_results: Vec::new(),
            returns_of: HashMap::new(),
            stats: PtaStats::default(),
        }
    }

    fn is_base_slice_allowed(&self, callee: FuncId) -> bool {
        self.slice_allow
            .as_ref()
            .is_none_or(|allow| allow.get(callee.index()).copied().unwrap_or(false))
    }

    fn try_record_dyn_hop(&mut self, callee: FuncId, next_hop: u8) -> bool {
        if self.slice_allow.is_none() {
            return true;
        }
        let Some(slot) = self.func_hop.get_mut(callee.index()) else {
            return false;
        };
        let updated = (*slot).min(next_hop);
        if updated > self.max_dyn_hop {
            return false;
        }
        *slot = updated;
        true
    }

    /// Returned SSA values of `callee` in deterministic block/inst order,
    /// populated lazily on first `wire_call` into `callee`.
    fn returns_of_func(&mut self, callee: FuncId) -> Vec<ValueId> {
        if let Some(cached) = self.returns_of.get(&callee) {
            return cached.clone();
        }
        let mut returns = Vec::new();
        if let Some(f) = self.module.func(callee) {
            for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    let Some(inst) = self.module.inst(iid) else {
                        continue;
                    };
                    if let Op::Return { value: Some(v) } = &inst.op {
                        returns.push(*v);
                    }
                }
            }
        }
        self.returns_of.insert(callee, returns.clone());
        returns
    }

    /// Queue fact `o ∈ pts(p)`.
    fn add_fact(&mut self, p: Ptr, o: Obj) {
        if self.pts.get(&p).is_some_and(|s| s.contains(&o)) {
            return;
        }
        self.worklist.insert((p, o));
    }

    /// Add subset edge `s → t` (delta half two: a new edge catches up
    /// with everything already in `s`).
    fn add_edge(&mut self, s: Ptr, t: Ptr) {
        if s == t {
            return;
        }
        if !self.edges.entry(s).or_default().insert(t) {
            return;
        }
        self.stats.flow_edges += 1;
        let Pta { pts, worklist, .. } = self;
        if let Some(objs) = pts.get(&s) {
            for &o in objs {
                worklist.insert((t, o));
            }
        }
    }

    /// Register a statement handler on a base pointer. Handlers
    /// register during activation scans, but an aliased base pointer
    /// may already carry facts — fire on those immediately (the
    /// statement-level delta discipline).
    fn register(&mut self, base: Ptr, handler: Handler) {
        let id = self.handlers.len() as u32;
        self.handlers.push((base, handler));
        self.handlers_by_base.entry(base).or_default().push(id);
        // Defensive catch-up if `base` already carries facts (under the
        // activation-priority pump discipline, pending activations scan
        // before worklist facts populate `pts`).
        if let Some(objs) = self.pts.get(&base).cloned() {
            for o in objs {
                self.fire(id, o);
            }
        }
    }

    /// Fire one handler on one object (once per pair), driving any bucket
    /// re-arm cascade over an explicit stack rather than mutual recursion.
    fn fire(&mut self, first_id: u32, first_o: Obj) {
        enum FireStep {
            Fire(u32, Obj),
            AddEdge(Ptr, Ptr),
        }
        let mut stack = vec![FireStep::Fire(first_id, first_o)];
        while let Some(step) = stack.pop() {
            match step {
                FireStep::AddEdge(s, t) => self.add_edge(s, t),
                FireStep::Fire(id, o) => {
                    if !self.fired.insert((id, o)) {
                        continue;
                    }
                    let (_, handler) = self.handlers[id as usize];
                    match handler {
                        Handler::Store { value, slot } => {
                            let Obj::Site { site, ctx, .. } = o else {
                                // A store through an unknown base may reach any
                                // field; the taint layer's own unknown-base
                                // wildcard already over-approximates that — the
                                // value's flow is unaffected, nothing to wire.
                                continue;
                            };
                            stack.push(FireStep::AddEdge(value, Ptr::Field(site, ctx, slot)));
                            let rearm = self.note_bucket_rearms(site, ctx, slot);
                            for (rid, ro) in rearm.into_iter().rev() {
                                stack.push(FireStep::Fire(rid, ro));
                            }
                        }
                        Handler::Load { result, read } => {
                            let Obj::Site { site, ctx, .. } = o else {
                                self.add_fact(result, Obj::Unknown);
                                continue;
                            };
                            let slots: Vec<Slot> = match read {
                                Read::Named(n) => vec![Slot::Named(n), Slot::Dynamic],
                                Read::Index => vec![Slot::Index, Slot::Dynamic],
                                Read::All => {
                                    self.dyn_loads_by_obj
                                        .entry((site, ctx))
                                        .or_default()
                                        .insert((id, o));
                                    self.buckets
                                        .get(&(site, ctx))
                                        .map(|b| b.iter().copied().collect())
                                        .unwrap_or_default()
                                }
                            };
                            for slot in slots {
                                self.add_edge(Ptr::Field(site, ctx, slot), result);
                            }
                        }
                        Handler::Call { call, caller_ctx } => {
                            self.resolve_call(call, caller_ctx, o);
                        }
                    }
                }
            }
        }
    }

    /// Record a bucket on an object and return any `(handler_id, obj)` dynamic
    /// reads that need to re-fire (already cleared from `self.fired`).
    fn note_bucket_rearms(&mut self, site: InstId, ctx: Ctx, slot: Slot) -> Vec<(u32, Obj)> {
        if !self.buckets.entry((site, ctx)).or_default().insert(slot) {
            return Vec::new();
        }
        let Some(loads) = self.dyn_loads_by_obj.get(&(site, ctx)) else {
            return Vec::new();
        };
        let rearm: Vec<(u32, Obj)> = loads.iter().copied().collect();
        for &(id, o) in &rearm {
            self.fired.remove(&(id, o));
        }
        rearm
    }

    /// Note a bucket on an object; a NEW bucket re-arms the dynamic
    /// reads that already fired on it (a computed read sees every
    /// bucket, including ones created after the read first fired).
    fn note_bucket(&mut self, site: InstId, ctx: Ctx, slot: Slot) {
        let rearm = self.note_bucket_rearms(site, ctx, slot);
        for (id, o) in rearm {
            self.fire(id, o);
        }
    }

    /// An object reached a callee pointer: `Unknown` marks the site
    /// partial and poisons the result; a callable object wires the
    /// edge; a non-callable object is a TypeError path (no edge, no
    /// unknown — the base trace's discipline).
    fn resolve_call(&mut self, call: InstId, caller_ctx: Ctx, o: Obj) {
        match o {
            Obj::Unknown => {
                if self.call_unknown.insert((call, caller_ctx)) {
                    self.stats.call_sites_partial += 1;
                }
                if let Some(result) = self.module.inst(call).and_then(|i| i.result) {
                    self.add_fact(Ptr::Local(result, caller_ctx), Obj::Unknown);
                }
            }
            Obj::Site {
                callable: Some(body),
                ..
            } => {
                if self
                    .call_targets
                    .entry((call, caller_ctx))
                    .or_default()
                    .insert(body)
                {
                    self.stats.call_edges_resolved += 1;
                }
                let next_hop = self
                    .links
                    .inst_func(self.module, call)
                    .and_then(|f| self.func_hop.get(f.index()).copied())
                    .unwrap_or(u8::MAX)
                    .saturating_add(1);
                if self.try_record_dyn_hop(body, next_hop) {
                    self.wire_call(call, caller_ctx, body);
                }
            }
            Obj::Site { callable: None, .. } => {}
        }
    }

    /// Wire call `call` (in `caller_ctx`) into `callee`: activation +
    /// argument/return edges. Idempotent per triple.
    fn wire_call(&mut self, call: InstId, caller_ctx: Ctx, callee: FuncId) {
        if !self.wired.insert((call, caller_ctx, callee)) {
            return;
        }
        let Some(fd) = self.module.func(callee) else {
            return;
        };
        if fd.is_external || fd.blocks.is_empty() {
            return;
        }
        let callee_ctx = Some(call);
        self.activate(callee, callee_ctx);
        let Some(Op::Call {
            callee: callee_val,
            this,
            args,
            kind,
        }) = self.module.inst(call).map(|i| &i.op)
        else {
            return;
        };
        let (callee_val, this, args, kind) = (*callee_val, *this, args.clone(), *kind);
        let local = |v: ValueId| Ptr::Local(v, caller_ctx);
        // For `new Cls(...)` into an internal constructor body, materialize a
        // concrete instance allocation keyed by the `New` call instruction so
        // constructor field writes (`this.f = v`) and caller reads (`inst.f`)
        // meet on a concrete site.
        let constructed_instance = (kind == CallKind::New).then_some(Obj::Site {
            site: call,
            ctx: caller_ctx,
            callable: None,
            keyed: true,
        });
        match frame_slots_of(self.module, callee) {
            Some(slots) if fd.params.len() >= slots.implicit_count() => {
                // Implicit slots, ordered func, newTarget, this (N66).
                if slots.func {
                    self.add_edge(local(callee_val), Ptr::Local(fd.params[0], callee_ctx));
                }
                if let Some(this_idx) = slots.this_index() {
                    if let Some(t) = this {
                        self.add_edge(local(t), Ptr::Local(fd.params[this_idx], callee_ctx));
                    } else if let Some(inst_obj) = constructed_instance {
                        self.add_fact(Ptr::Local(fd.params[this_idx], callee_ctx), inst_obj);
                    }
                }
                let formal_base = slots.implicit_count();
                match kind {
                    abcd_ir::CallKind::Apply
                    | abcd_ir::CallKind::SuperSpread
                    | abcd_ir::CallKind::SuperForwardAllArgs => {
                        // Formals come out of an argument array / the
                        // caller's own frame — opaque at this rung (the
                        // rung-1 discipline): unknown, never wrong.
                        for &p in fd.params.iter().skip(formal_base) {
                            self.add_fact(Ptr::Local(p, callee_ctx), Obj::Unknown);
                        }
                    }
                    _ => {
                        for (i, a) in args.iter().enumerate() {
                            if let Some(&p) = fd.params.get(formal_base + i) {
                                self.add_edge(local(*a), Ptr::Local(p, callee_ctx));
                            }
                        }
                    }
                }
            }
            _ => {
                // No reliable slot model: conservative — every operand
                // reaches every parameter (the taint layer's
                // OverApproxAll parity; never silently drop).
                let mut operands = args.clone();
                if let Some(t) = this {
                    operands.push(t);
                }
                for a in operands {
                    for &p in &fd.params {
                        self.add_edge(local(a), Ptr::Local(p, callee_ctx));
                    }
                }
            }
        }
        // Returns → the call result, in the caller's context.
        if let Some(result) = self.module.inst(call).and_then(|i| i.result) {
            if let Some(inst_obj) = constructed_instance {
                self.add_fact(Ptr::Local(result, caller_ctx), inst_obj);
            }
            let returns = self.returns_of_func(callee);
            for v in returns {
                self.add_edge(Ptr::Local(v, callee_ctx), Ptr::Local(result, caller_ctx));
            }
        }
    }

    /// Queue an activation for scanning (idempotent; external/bodyless
    /// functions are ignored).
    fn activate(&mut self, func: FuncId, ctx: Ctx) {
        let Some(fd) = self.module.func(func) else {
            return;
        };
        if fd.is_external || fd.blocks.is_empty() {
            return;
        }
        if self.activated.insert((func, ctx)) {
            self.pending_activations.insert((func, ctx));
        }
    }

    /// Scan one activation: seed allocations and register statement
    /// handlers, in deterministic block/inst order.
    fn scan(&mut self, func: FuncId, ctx: Ctx) {
        self.stats.activations += 1;
        let Some(fd) = self.module.func(func) else {
            return;
        };
        let func_class_id = fd.class_id;
        let is_harness = self.root_keep.is_some()
            && self.module.sym.resolve(fd.name) == Some(crate::ohos_lifecycle::OHOS_HARNESS_FUNC);
        // Base-activation parameters are opaque (unrecorded callers —
        // the balanced discipline's floor); context activations are
        // bound by their call edge.
        if ctx.is_none() {
            for &p in &fd.params {
                self.add_fact(Ptr::Local(p, ctx), Obj::Unknown);
            }
        }
        let blocks = fd.blocks.clone();
        let active_harness_receivers = if is_harness && let Some(rk) = &self.root_keep {
            collect_active_harness_receivers_in(self.module, self.base, &blocks, rk)
        } else {
            BTreeSet::new()
        };
        let links = self.links;
        let base = self.base;
        let sliced = self.root_keep.is_some();
        let next_dyn_hop = self
            .func_hop
            .get(func.index())
            .copied()
            .unwrap_or(u8::MAX)
            .saturating_add(1);
        for b in blocks {
            let Some(bb) = self.module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                let Some(inst) = self.module.inst(iid) else {
                    continue;
                };
                let local = |v: ValueId| Ptr::Local(v, ctx);
                match &inst.op {
                    op if is_keyed_alloc(op) => {
                        let callable = match op {
                            Op::AllocClosure { func } => closure_body(self.module, *func),
                            _ => None,
                        };
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable,
                                    keyed: true,
                                },
                            );
                        }
                    }
                    Op::CreateGenerator { func } => {
                        // Not one of the four keyed allocs (unreported),
                        // but callable — it resolves like a closure.
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: closure_body(self.module, *func),
                                    keyed: false,
                                },
                            );
                        }
                    }
                    Op::DefineFunc { body, .. } => {
                        let body_fn = *body;
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: Some(body_fn),
                                    keyed: false,
                                },
                            );
                        }
                        if sliced && self.try_record_dyn_hop(body_fn, next_dyn_hop) {
                            self.activate(body_fn, None);
                        }
                    }
                    Op::DefineMethod { func: inner, .. } => {
                        if sliced
                            && let Some(body_fn) = callable_body(self.module, *inner)
                            && self.try_record_dyn_hop(body_fn, next_dyn_hop)
                        {
                            self.activate(body_fn, None);
                        }
                    }
                    Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: Some(cls.ctor),
                                    keyed: false,
                                },
                            );
                        }
                    }
                    Op::LoadConst(c) => {
                        if let Some(Const::MethodRef(f)) = self.module.consts.get(*c)
                            && let Some(r) = inst.result
                        {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: Some(*f),
                                    keyed: false,
                                },
                            );
                        }
                    }
                    Op::LoadFunction => {
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: Some(func),
                                    keyed: false,
                                },
                            );
                        }
                    }
                    Op::Mov { src } => {
                        if let Some(r) = inst.result {
                            self.add_edge(local(*src), local(r));
                        }
                    }
                    Op::Phi { entries } => {
                        if let Some(r) = inst.result {
                            for (_, incoming) in entries {
                                self.add_edge(local(*incoming), local(r));
                            }
                        }
                    }
                    Op::LoadProp { object, name } => {
                        if let Some(r) = inst.result {
                            let result = local(r);
                            self.load_results.push(result);
                            self.register(
                                local(*object),
                                Handler::Load {
                                    result,
                                    read: Read::Named(*name),
                                },
                            );
                        }
                    }
                    Op::LoadPropIdx { object, .. } => {
                        if let Some(r) = inst.result {
                            let result = local(r);
                            self.load_results.push(result);
                            self.register(
                                local(*object),
                                Handler::Load {
                                    result,
                                    read: Read::Index,
                                },
                            );
                        }
                    }
                    Op::LoadPropDyn { object, .. } => {
                        if let Some(r) = inst.result {
                            let result = local(r);
                            self.load_results.push(result);
                            self.register(
                                local(*object),
                                Handler::Load {
                                    result,
                                    read: Read::All,
                                },
                            );
                        }
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
                        self.register(
                            local(*object),
                            Handler::Store {
                                value: local(*value),
                                slot: Slot::Named(*name),
                            },
                        );
                    }
                    Op::StorePropIdx { object, value, .. }
                    | Op::StoreOwnPropIdx { object, value, .. } => {
                        self.register(
                            local(*object),
                            Handler::Store {
                                value: local(*value),
                                slot: Slot::Index,
                            },
                        );
                    }
                    Op::StorePropDyn { object, value, .. }
                    | Op::StoreOwnPropDyn { object, value, .. } => {
                        self.register(
                            local(*object),
                            Handler::Store {
                                value: local(*value),
                                slot: Slot::Dynamic,
                            },
                        );
                    }
                    Op::StoreGlobal { name, value }
                    | Op::StoreGlobalRecord { name, value, .. }
                    | Op::TryStoreGlobal { name, value } => {
                        // The record store (N72-C4) and the object store
                        // feed the same named-global pointer — reads model
                        // both through `Ptr::Global`.
                        self.add_edge(local(*value), Ptr::Global(*name));
                    }
                    Op::TryGetGlobal { name, .. } => {
                        if let Some(r) = inst.result {
                            self.add_edge(Ptr::Global(*name), local(r));
                            // Host bindings and absence are opaque —
                            // eager unknown (module stores still flow
                            // through the edge).
                            self.add_fact(local(r), Obj::Unknown);
                        }
                    }
                    Op::PutLexVar { level, slot, value } => {
                        let env_stack_at = self.env_stack_at;
                        if let Some(stack) = env_stack_at.get(iid.index())
                            && (*level as usize) < stack.len()
                        {
                            let entry = &stack[stack.len() - 1 - *level as usize];
                            for &env_site in &entry.sites {
                                self.add_edge(
                                    local(*value),
                                    Ptr::LexVar(env_site, *slot, ctx.is_some()),
                                );
                            }
                        }
                    }
                    Op::GetLexVar { level, slot } => {
                        if let Some(r) = inst.result {
                            let env_stack_at = self.env_stack_at;
                            if let Some(stack) = env_stack_at.get(iid.index())
                                && (*level as usize) < stack.len()
                            {
                                let entry = &stack[stack.len() - 1 - *level as usize];
                                if !entry.unknown && !entry.sites.is_empty() {
                                    for &env_site in &entry.sites {
                                        if sliced
                                            && let Some(owner_fn) =
                                                links.inst_func(self.module, env_site)
                                            && self.try_record_dyn_hop(owner_fn, next_dyn_hop)
                                        {
                                            self.activate(owner_fn, None);
                                        }
                                        self.add_edge(Ptr::LexVar(env_site, *slot, true), local(r));
                                        self.add_edge(
                                            Ptr::LexVar(env_site, *slot, false),
                                            local(r),
                                        );
                                    }
                                } else {
                                    self.add_fact(local(r), Obj::Unknown);
                                }
                            } else {
                                self.add_fact(local(r), Obj::Unknown);
                            }
                        }
                    }
                    Op::StoreModuleVar { index, value } => {
                        self.add_edge(local(*value), Ptr::ModuleVar(func_class_id, *index));
                    }
                    Op::LoadModuleVar { index, kind } => {
                        if let Some(r) = inst.result {
                            if kind.is_local() {
                                let slot_ref = ModuleSlotRef {
                                    class_id: func_class_id,
                                    slot: *index,
                                };
                                if sliced {
                                    for &(def_fn, _) in links.stored_values(slot_ref) {
                                        if self.try_record_dyn_hop(def_fn, next_dyn_hop) {
                                            self.activate(def_fn, None);
                                        }
                                    }
                                }
                                self.add_edge(Ptr::ModuleVar(func_class_id, *index), local(r));
                                if !links.has_multi_record_esm()
                                    || links.stored_values(slot_ref).is_empty()
                                {
                                    self.add_fact(local(r), Obj::Unknown);
                                }
                            } else if let Some(target) = links.external_load(func_class_id, *index)
                            {
                                for &slot_ref in &target.slots {
                                    if sliced {
                                        for &(def_fn, _) in links.stored_values(slot_ref) {
                                            if self.try_record_dyn_hop(def_fn, next_dyn_hop) {
                                                self.activate(def_fn, None);
                                            }
                                        }
                                    }
                                    self.add_edge(
                                        Ptr::ModuleVar(slot_ref.class_id, slot_ref.slot),
                                        local(r),
                                    );
                                }
                                let any_empty = target
                                    .slots
                                    .iter()
                                    .any(|&sr| links.stored_values(sr).is_empty());
                                if target.unresolved_external
                                    || target.slots.is_empty()
                                    || any_empty
                                {
                                    self.add_fact(local(r), Obj::Unknown);
                                }
                            } else {
                                self.add_fact(local(r), Obj::Unknown);
                            }
                        }
                    }
                    Op::GetModuleNamespace { index } => {
                        if let Some(r) = inst.result {
                            if let Some(target_cid) = links.namespace_target(func_class_id, *index)
                            {
                                self.add_fact(
                                    local(r),
                                    Obj::Site {
                                        site: iid,
                                        ctx: None,
                                        callable: None,
                                        keyed: false,
                                    },
                                );
                                if let Some(exports) = links.namespace_exports(target_cid) {
                                    for (&export_sym, slots) in exports {
                                        self.note_bucket(iid, None, Slot::Named(export_sym));
                                        for &sr in slots {
                                            if sliced {
                                                for &(def_fn, _) in links.stored_values(sr) {
                                                    if self.try_record_dyn_hop(def_fn, next_dyn_hop)
                                                    {
                                                        self.activate(def_fn, None);
                                                    }
                                                }
                                            }
                                            self.add_edge(
                                                Ptr::ModuleVar(sr.class_id, sr.slot),
                                                Ptr::Field(iid, None, Slot::Named(export_sym)),
                                            );
                                        }
                                    }
                                }
                            } else {
                                self.add_fact(local(r), Obj::Unknown);
                            }
                        }
                    }
                    Op::Await { value } | Op::AwaitUncaught { value, .. } => {
                        if let Some(r) = inst.result {
                            self.add_edge(local(*value), local(r));
                        }
                    }
                    Op::ResumeGenerator { genobj } => {
                        if let Some(r) = inst.result {
                            // Pair async-machine `AwaitUncaught(funcobj, val)` -> `ResumeGenerator(funcobj)`.
                            for &prev_iid in &bb.insts {
                                if prev_iid == iid {
                                    break;
                                }
                                if let Some(Op::AwaitUncaught { funcobj, value, .. }) =
                                    self.module.inst(prev_iid).map(|i| &i.op)
                                    && funcobj == genobj
                                {
                                    self.add_edge(local(*value), local(r));
                                }
                            }
                        }
                    }
                    Op::Call {
                        callee, this, args, ..
                    } => {
                        let callee_val = *callee;
                        if is_harness {
                            let has_non_const_arg =
                                args.iter().any(|&a| !is_load_const(self.module, a));
                            let has_active_this = this
                                .is_some_and(|t| active_harness_receivers.contains(&t))
                                || inst
                                    .result
                                    .is_some_and(|r| active_harness_receivers.contains(&r));
                            let base_callees = base.callees_of_call_at(iid);
                            let any_kept = base_callees.is_empty()
                                || has_non_const_arg
                                || has_active_this
                                || self
                                    .root_keep
                                    .as_ref()
                                    .is_some_and(|rk| base_callees.iter().any(|c| rk.contains(c)));
                            if any_kept {
                                self.register(
                                    local(callee_val),
                                    Handler::Call {
                                        call: iid,
                                        caller_ctx: ctx,
                                    },
                                );
                                for &target_callee in base_callees {
                                    let keep_target = has_non_const_arg
                                        || has_active_this
                                        || self
                                            .root_keep
                                            .as_ref()
                                            .is_some_and(|rk| rk.contains(&target_callee));
                                    if keep_target {
                                        let _ = self.try_record_dyn_hop(target_callee, 1);
                                        self.wire_call(iid, ctx, target_callee);
                                    }
                                }
                            }
                        } else {
                            self.register(
                                local(callee_val),
                                Handler::Call {
                                    call: iid,
                                    caller_ctx: ctx,
                                },
                            );
                            if sliced {
                                for &target_callee in base.callees_of_call_at(iid) {
                                    if self.is_base_slice_allowed(target_callee) {
                                        self.wire_call(iid, ctx, target_callee);
                                    }
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    /// The main loop: activations (in `(FuncId, ctx)` order) and facts
    /// (pop-min) through one deterministic worklist, to the fixed
    /// point (or the budget cut), followed by at most one empty-bucket
    /// post-pass (adding `Unknown` never empties a bucket).
    fn pump(&mut self, steps: &mut usize) {
        let mut post_pass_done = false;
        loop {
            loop {
                if let Some((func, ctx)) = self.pending_activations.pop_first() {
                    self.scanned.insert((func, ctx));
                    self.scan(func, ctx);
                    continue;
                }
                let Some((p, o)) = self.worklist.pop_first() else {
                    break;
                };
                *steps += 1;
                if *steps > self.config.step_budget {
                    self.stats.capped = true;
                    return;
                }
                if !self.pts.entry(p).or_default().insert(o) {
                    continue;
                }
                self.stats.facts += 1;
                // Delta half one: replay down existing out-edges.
                let Pta {
                    edges, worklist, ..
                } = self;
                if let Some(targets) = edges.get(&p) {
                    for &t in targets {
                        worklist.insert((t, o));
                    }
                }
                // Statement handlers registered on this base pointer.
                let handler_len = self.handlers_by_base.get(&p).map_or(0, Vec::len);
                for hi in 0..handler_len {
                    let Some(&id) = self.handlers_by_base.get(&p).and_then(|ids| ids.get(hi))
                    else {
                        break;
                    };
                    self.fire(id, o);
                }
            }
            if post_pass_done {
                break;
            }
            post_pass_done = true;
            // The empty-bucket post-pass: a load whose buckets stayed
            // empty reads an inherited/reflected/native property —
            // opaque. Runs once: adding Unknown never empties a bucket.
            let mut added = false;
            let results = self.load_results.clone();
            for result in results {
                if self.pts.get(&result).is_none_or(|s| s.is_empty()) {
                    self.add_fact(result, Obj::Unknown);
                    added = true;
                }
            }
            if !added {
                break;
            }
        }
    }

    fn run(&mut self, roots: Option<&[FuncId]>) {
        match roots {
            None => {
                // Whole-module seeding: every function with a body gets a base
                // activation (scope gating §4.1 item 5 — the module is the
                // program; context activations arrive through resolved edges).
                for fi in 0..self.module.functions.len() {
                    self.activate(FuncId::new(fi as u32), None);
                }
            }
            Some(root_funcs) => {
                for &func in root_funcs {
                    self.activate(func, None);
                }
            }
        }
        let mut steps = 0usize;
        self.pump(&mut steps);
    }
}

/// Run the whole-module PTA: the co-evolution fixed point, then the
/// graph assembly (base edges ∪ PTA edges), the stripped value answers,
/// and the lexical-environment tables.
pub fn analyze(module: &Module, base: &CallGraph, config: &PtaConfig) -> PtaOutcome {
    let links = ModuleLinkTable::build(module);
    analyze_with_links_and_roots(module, &links, base, config, None)
}

/// Demand-driven / root-sliced `k=1` pointer analysis reusing a prebuilt
/// [`ModuleLinkTable`].
///
/// - When `roots` is `None`, runs whole-module PTA (identical to [`analyze`]).
/// - When `roots` is `Some(root_funcs)`:
///   - Seeds initial `(func, None)` activations ONLY for `func` in `root_funcs`
///     (filtering `!f.is_external && !f.blocks.is_empty()`).
///   - Expands on-the-fly during `scan(func, ctx)`:
///     1. For every [`Op::Call`] at `iid`: in addition to registering `Handler::Call`,
///        wires every callee `&callee` already resolved in `base.callees_of_call_at(iid)`
///        via `wire_call(iid, ctx, callee)` — EXCEPT when `func` is named
///        [`crate::ohos_lifecycle::OHOS_HARNESS_FUNC`] (`"__abcd_ohos_harness__"`),
///        only wire harness calls whose target `callee` is either in `root_keep`
///        (the `root_funcs` set) OR is called with `args` containing a non-[`Op::LoadConst`]
///        operand (e.g. Ability/ExtensionAbility `onCreate(want)` lifecycle calls)
///        OR shares its concrete `this` receiver with such an Ability/rooted call or
///        `StoreProp(inst, "context", ...)`.
///     2. For [`Op::DefineFunc`] and [`Op::DefineMethod`] scanned in an active
///        function: activates `(body, None)` so closures passed as callbacks to
///        external/SDK functions are scanned.
///     3. For [`Op::LoadModuleVar`] and [`Op::GetModuleNamespace`]: for every
///        referenced [`ModuleSlotRef`], activates `(def_fn, None)` for all
///        `&(def_fn, _)` in [`ModuleLinkTable::stored_values`] so imported modules
///        initialize on demand.
pub fn analyze_with_links_and_roots(
    module: &Module,
    links: &ModuleLinkTable,
    base: &CallGraph,
    config: &PtaConfig,
    roots: Option<&[FuncId]>,
) -> PtaOutcome {
    let (env_stack_at, env_sites, env_rounds) = env_analysis(module, config.max_env_depth);
    let slice_init = roots.map(|root_funcs| {
        let max_base_hop = if root_funcs.len() > 128 {
            1
        } else {
            MAX_SLICED_BASE_HOP
        };
        let max_dyn_hop = if root_funcs.len() > 128 {
            2
        } else {
            MAX_SLICED_DYN_HOP
        };
        let rk: BTreeSet<FuncId> = root_funcs.iter().copied().collect();
        let (slice_allow, func_hop) = compute_sliced_bfs(
            module,
            links,
            base,
            &env_stack_at,
            root_funcs,
            &rk,
            max_base_hop,
        );
        SliceInit {
            root_keep: rk,
            slice_allow,
            func_hop,
            max_dyn_hop,
        }
    });
    let mut engine = Pta::new(module, links, base, config, &env_stack_at, slice_init);
    engine.run(roots);
    let stats_engine = engine.stats;
    let scanned_funcs: BTreeSet<FuncId> = engine.scanned.iter().map(|&(f, _)| f).collect();

    // ── Graph assembly ───────────────────────────────────────────────
    // Aggregate the PTA's resolutions per call instruction first (the
    // per-site scan then stays linear).
    let mut pta_targets: BTreeMap<InstId, BTreeSet<FuncId>> = BTreeMap::new();
    for ((call, _), bodies) in engine.call_targets.iter() {
        pta_targets
            .entry(*call)
            .or_default()
            .extend(bodies.iter().copied());
    }
    let pta_partial: BTreeSet<InstId> = engine.call_unknown.iter().map(|(call, _)| *call).collect();
    let mut sites: BTreeMap<InstId, CallEdge> = BTreeMap::new();
    for (iid, base_edge) in base.sites() {
        let mut targets: BTreeSet<FuncId> = BTreeSet::new();
        if let CallTargets::Resolved(ts) = &base_edge.targets {
            targets.extend(ts.iter().copied());
        }
        if let Some(ts) = pta_targets.get(&iid) {
            targets.extend(ts.iter().copied());
        }
        let edge = if targets.is_empty() {
            CallEdge {
                caller: base_edge.caller,
                kind: base_edge.kind,
                edge_kind: CallEdgeKind::UnknownCallees,
                targets: CallTargets::UnknownCallees,
                resolution_complete: false,
            }
        } else {
            let resolution_complete =
                if roots.is_none() || scanned_funcs.contains(&base_edge.caller) {
                    // Completeness is the PTA's own: the callee value's set
                    // contained no Unknown (the PTA subsumes the base trace —
                    // a base dead-end the PTA closes completely is complete).
                    !pta_partial.contains(&iid)
                } else {
                    base_edge.resolution_complete
                };
            CallEdge {
                caller: base_edge.caller,
                kind: base_edge.kind,
                edge_kind: if base_edge.edge_kind == CallEdgeKind::UnknownCallees {
                    CallEdgeKind::ResolvedValueFlow
                } else {
                    base_edge.edge_kind
                },
                targets: CallTargets::Resolved(targets.into_iter().collect()),
                resolution_complete,
            }
        };
        sites.insert(iid, edge);
    }
    let graph = CallGraph::from_edges(sites);

    // ── Value answers ────────────────────────────────────────────────
    // Aggregate each value's object union in ONE pass over the
    // points-to tables: `(all contexts, recorded-contexts-only, has a
    // recorded context)`.
    let mut acc: HashMap<ValueId, (BTreeSet<Obj>, BTreeSet<Obj>, bool)> = HashMap::new();
    for (p, objs) in &engine.pts {
        let Ptr::Local(v, ctx) = p else { continue };
        let entry = acc.entry(*v).or_default();
        entry.0.extend(objs.iter().copied());
        if ctx.is_some() {
            entry.1.extend(objs.iter().copied());
            entry.2 = true;
        }
    }
    let mut answers = Vec::with_capacity(module.values.len());
    for v in 0..module.values.len() {
        let vid = ValueId::new(v as u32);
        answers.push(value_answer(module, vid, acc.get(&vid)));
    }

    // Balanced lexical-capture answers: when an enclosing function owning
    // `env_site` has recorded call-site contexts (`ctx.is_some()`), ignore the
    // synthetic `ctx == None` parameter `Obj::Unknown` marker on its captured
    // lexical slots (mirroring `value_answer`'s parameter rule).
    let recorded_funcs: BTreeSet<FuncId> = engine
        .scanned
        .iter()
        .filter_map(|&(f, c)| c.map(|_| f))
        .collect();
    let lex_funcs: Vec<FuncId> = if roots.is_some() {
        scanned_funcs.iter().copied().collect()
    } else {
        (0..module.functions.len())
            .map(|fi| FuncId::new(fi as u32))
            .collect()
    };
    for func in lex_funcs {
        let Some(f) = module.func(func) else {
            continue;
        };
        for &b in &f.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if let Op::GetLexVar { level, slot } = &inst.op
                    && let Some(res_vid) = inst.result
                    && let Some(stack) = env_stack_at.get(iid.index())
                    && (*level as usize) < stack.len()
                {
                    let entry = &stack[stack.len() - 1 - *level as usize];
                    if !entry.unknown && !entry.sites.is_empty() {
                        let mut union = BTreeSet::new();
                        for &env_site in &entry.sites {
                            let use_rec = links
                                .inst_func(module, env_site)
                                .is_some_and(|of| recorded_funcs.contains(&of));
                            if let Some(objs) =
                                engine.pts.get(&Ptr::LexVar(env_site, *slot, use_rec))
                            {
                                union.extend(objs.iter().copied());
                            }
                        }
                        let mut ans = ValueAnswer::default();
                        for o in &union {
                            match o {
                                Obj::Unknown => ans.has_unknown = true,
                                Obj::Site { site, keyed, .. } => {
                                    if *keyed {
                                        ans.sites.union_with(&AllocSiteSet::one(*site));
                                    } else {
                                        ans.has_unknown = true;
                                    }
                                }
                            }
                        }
                        if union.is_empty() {
                            ans.has_unknown = true;
                        }
                        if let Some(slot_ans) = answers.get_mut(res_vid.index()) {
                            *slot_ans = ans;
                        }
                    }
                }
            }
        }
    }

    let stats = PtaStats {
        env_rounds,
        ..stats_engine
    };
    PtaOutcome {
        graph,
        tables: Rung2Tables {
            answers,
            env_stack_at,
            env_sites,
        },
        stats,
    }
}

/// The stripped answer for one value: keyed sites + completeness,
/// unioned across contexts (params: across recorded call-site contexts
/// when any exist — the balanced discipline, folded into the fixed
/// point).
fn value_answer(
    module: &Module,
    value: ValueId,
    acc: Option<&(BTreeSet<Obj>, BTreeSet<Obj>, bool)>,
) -> ValueAnswer {
    let unknown = || ValueAnswer {
        has_unknown: true,
        ..ValueAnswer::default()
    };
    let Some(v) = module.value(value) else {
        return unknown();
    };
    match v.def {
        // Constants are not heap allocations (rung-0 parity).
        ValueDef::Const(_) => ValueAnswer::default(),
        ValueDef::ExceptionParam(_) => unknown(),
        ValueDef::Param(_) | ValueDef::Inst(_) => {
            let Some((all, recorded, has_recorded)) = acc else {
                return unknown();
            };
            let union = if *has_recorded {
                // Balanced: recorded call-site contexts only — the base
                // (`ctx == None`) activation's synthetic parameter `Unknown`
                // marker means "called from nowhere recorded" and applies
                // only when no recorded context exists.
                recorded
            } else {
                all
            };
            let mut answer = ValueAnswer::default();
            for o in union {
                match o {
                    Obj::Unknown => answer.has_unknown = true,
                    Obj::Site { site, keyed, .. } => {
                        if *keyed {
                            answer.sites.union_with(&AllocSiteSet::one(*site));
                        } else {
                            // Unkeyed objects (function values,
                            // generators) are never reported — the
                            // rung-0 parity for unkeyed allocs.
                            answer.has_unknown = true;
                        }
                    }
                }
            }
            if union.is_empty() {
                // Opaque definitions (unmodeled ops, never-bound
                // params): no keyed site, and not provably object-free.
                answer.has_unknown = true;
            }
            answer
        }
    }
}

/// Apply one instruction's lexical-environment transfer to `state`, returning
/// `true` iff `state` mutated.
fn step_env_inst(op: &Op, iid: InstId, max_depth: usize, state: &mut Vec<EnvEntry>) -> bool {
    match op {
        Op::NewLexEnv { .. } | Op::NewLexEnvWithName { .. } => {
            state.push(EnvEntry {
                sites: BTreeSet::from([iid]),
                unknown: false,
            });
            // Depth cap: drop the OUTERMOST environments (level indexing is
            // from the innermost end).
            if state.len() > max_depth {
                let overflow = state.len() - max_depth;
                state.drain(0..overflow);
            }
            true
        }
        Op::PopLexEnv => {
            if state.pop().is_none() {
                state.push(EnvEntry {
                    sites: BTreeSet::new(),
                    unknown: true,
                });
            }
            true
        }
        _ => false,
    }
}

/// The lexical-environment analysis: per-instruction environment stacks
/// plus the capture fixed point (see module docs). Context-insensitive:
/// recursion merges; the depth cap drops outer environments (deep
/// levels answer unknown — sound).
fn env_analysis(module: &Module, max_depth: usize) -> (Vec<Arc<[EnvEntry]>>, Vec<bool>, usize) {
    // Environment allocation sites per instruction; capture points
    // (AllocClosure/CreateGenerator sites + unwrapped DefineFunc sites)
    // per defined body; per-function lexical-op presence and block reachability.
    let mut env_sites = vec![false; module.insts.len()];
    let mut has_lex_ops = vec![false; module.functions.len()];
    let mut block_func = vec![None; module.blocks.len()];
    let mut block_reached = vec![false; module.blocks.len()];
    let mut inst_reached = vec![false; module.insts.len()];
    // body → capture instructions (in deterministic discovery order).
    let mut capture_points: BTreeMap<FuncId, BTreeSet<InstId>> = BTreeMap::new();

    for (fi, f) in module.functions.iter().enumerate() {
        let func = FuncId::new(fi as u32);
        for &b in &f.blocks {
            if let Some(slot) = block_func.get_mut(b.index()) {
                *slot = Some(func);
            }
        }
        let mut sweeps = 0usize;
        loop {
            let mut changed = false;
            sweeps += 1;
            for &b in &f.blocks {
                if block_reached.get(b.index()).copied().unwrap_or(false) {
                    continue;
                }
                let Some(bb) = module.block(b) else { continue };
                let reached = bb.preds.is_empty()
                    || bb.preds.iter().any(|pred| {
                        block_func.get(pred.from.index()) == Some(&Some(func))
                            && block_reached
                                .get(pred.from.index())
                                .copied()
                                .unwrap_or(false)
                    });
                if reached && let Some(slot) = block_reached.get_mut(b.index()) {
                    *slot = true;
                    changed = true;
                }
            }
            if !changed || sweeps >= 64 {
                break;
            }
        }

        for &b in &f.blocks {
            let Some(bb) = module.block(b) else { continue };
            let b_reached = block_reached.get(b.index()).copied().unwrap_or(false);
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if b_reached && let Some(slot) = inst_reached.get_mut(iid.index()) {
                    *slot = true;
                }
                match &inst.op {
                    Op::NewLexEnv { .. } | Op::NewLexEnvWithName { .. } => {
                        if let Some(slot) = env_sites.get_mut(iid.index()) {
                            *slot = true;
                        }
                        has_lex_ops[fi] = true;
                    }
                    Op::PopLexEnv => {
                        has_lex_ops[fi] = true;
                    }
                    Op::AllocClosure { func } | Op::CreateGenerator { func } => {
                        if let Some(body) = closure_body(module, *func) {
                            capture_points.entry(body).or_default().insert(iid);
                        }
                    }
                    Op::DefineFunc { body, .. } => {
                        // A bare function value also captures (it may be
                        // called without an AllocClosure wrapper).
                        capture_points.entry(*body).or_default().insert(iid);
                    }
                    Op::DefineMethod { func, .. } => {
                        if let Some(body) = callable_body(module, *func) {
                            capture_points.entry(body).or_default().insert(iid);
                        }
                    }
                    Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                        capture_points.entry(cls.ctor).or_default().insert(iid);
                        for mfid in class_member_funcs(module, cls.members) {
                            capture_points.entry(mfid).or_default().insert(iid);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    let empty_stack: Arc<[EnvEntry]> = Arc::from([]);
    let mut func_stacks: Vec<Arc<[EnvEntry]>> = vec![Arc::clone(&empty_stack); module.insts.len()];

    // Recompute one function's instruction stacks in `func_stacks` given its
    // entry capture chain.
    let compute_func_stacks =
        |fi: usize, entry_state: &[EnvEntry], func_stacks: &mut [Arc<[EnvEntry]>]| {
            let f = &module.functions[fi];
            if !has_lex_ops[fi] {
                // Fast path: without NewLexEnv/PopLexEnv inside `f`, every
                // reachable instruction shares the entry stack identically.
                let entry_arc: Arc<[EnvEntry]> = if entry_state.is_empty() {
                    Arc::clone(&empty_stack)
                } else {
                    Arc::from(entry_state)
                };
                for &b in &f.blocks {
                    if !block_reached.get(b.index()).copied().unwrap_or(false) {
                        continue;
                    }
                    let Some(bb) = module.block(b) else { continue };
                    for &iid in &bb.insts {
                        if module.inst(iid).is_some()
                            && let Some(slot) = func_stacks.get_mut(iid.index())
                        {
                            *slot = Arc::clone(&entry_arc);
                        }
                    }
                }
                return;
            }

            // Phase 1: converge block `out_state` to fixed point without touching
            // per-instruction `func_stacks` on intermediate sweeps.
            let mut in_state: HashMap<abcd_ir::BlockId, Vec<EnvEntry>> = HashMap::new();
            let mut out_state: HashMap<abcd_ir::BlockId, Vec<EnvEntry>> = HashMap::new();
            let mut changed = true;
            let mut sweeps = 0usize;
            while changed && sweeps < 64 {
                changed = false;
                sweeps += 1;
                for &b in &f.blocks {
                    let Some(bb) = module.block(b) else { continue };
                    let mut state: Option<Vec<EnvEntry>> = if bb.preds.is_empty() {
                        Some(entry_state.to_vec())
                    } else {
                        None
                    };
                    for pred in &bb.preds {
                        if let Some(ps) = out_state.get(&pred.from) {
                            state = Some(match state.take() {
                                None => ps.clone(),
                                Some(cur) => join_stacks(&cur, ps),
                            });
                        }
                    }
                    let Some(mut state) = state else {
                        continue;
                    };
                    in_state.insert(b, state.clone());
                    for &iid in &bb.insts {
                        let Some(inst) = module.inst(iid) else {
                            continue;
                        };
                        step_env_inst(&inst.op, iid, max_depth, &mut state);
                    }
                    if out_state.get(&b) != Some(&state) {
                        out_state.insert(b, state);
                        changed = true;
                    }
                }
            }

            // Phase 2: materialize per-instruction `Arc<[EnvEntry]>` in ONE final
            // pass, reusing `Arc::clone` across consecutive non-lex instructions.
            for &b in &f.blocks {
                let Some(bb) = module.block(b) else { continue };
                let Some(entry_vec) = in_state.get(&b) else {
                    continue;
                };
                let mut state = entry_vec.clone();
                let mut cur_arc: Arc<[EnvEntry]> = if state.is_empty() {
                    Arc::clone(&empty_stack)
                } else {
                    Arc::from(state.as_slice())
                };
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    if let Some(slot) = func_stacks.get_mut(iid.index()) {
                        *slot = Arc::clone(&cur_arc);
                    }
                    if step_env_inst(&inst.op, iid, max_depth, &mut state) {
                        cur_arc = if state.is_empty() {
                            Arc::clone(&empty_stack)
                        } else {
                            Arc::from(state.as_slice())
                        };
                    }
                }
            }
        };

    // The capture fixed point: captured[body] = union of the stacks at
    // the body's capture points. Monotone over a finite lattice
    // (entries are subsets of the finite env-site set, depth capped).
    let mut captured: BTreeMap<FuncId, Vec<EnvEntry>> = BTreeMap::new();
    let mut dirty_funcs = vec![false; module.functions.len()];
    let mut rounds = 0usize;
    loop {
        rounds += 1;
        if rounds == 1 {
            // Round 1: `captured` is empty everywhere — functions without lex
            // ops already hold `empty_stack`, so only compute `has_lex_ops[fi]`.
            for (fi, &has_lex) in has_lex_ops.iter().enumerate() {
                if has_lex {
                    compute_func_stacks(fi, &[], &mut func_stacks);
                }
            }
        } else {
            for (fi, dirty) in dirty_funcs.iter_mut().enumerate() {
                if *dirty {
                    *dirty = false;
                    let func = FuncId::new(fi as u32);
                    let entry = captured.get(&func).map_or(&[][..], Vec::as_slice);
                    compute_func_stacks(fi, entry, &mut func_stacks);
                }
            }
        }

        let mut changed = false;
        for (body, points) in &capture_points {
            // Alternative capture points UNION (the body may be defined
            // at any of them). The first alternative seeds the chain;
            // later ones join with unknown-padding (one-sided positions
            // are genuinely uncertain — a may-semantics union).
            let mut chain: Option<Vec<EnvEntry>> = None;
            for p in points {
                if inst_reached.get(p.index()).copied().unwrap_or(false)
                    && let Some(stack) = func_stacks.get(p.index())
                {
                    chain = Some(match chain.take() {
                        None => stack.to_vec(),
                        Some(cur) => join_stacks(&cur, stack),
                    });
                }
            }
            let chain = chain.unwrap_or_default();
            let prev_effective = captured.get(body).map_or(&[][..], Vec::as_slice);
            if prev_effective != chain.as_slice()
                && let Some(slot) = dirty_funcs.get_mut(body.index())
            {
                *slot = true;
            }
            if captured.get(body) != Some(&chain) {
                captured.insert(*body, chain);
                changed = true;
            }
        }
        if !changed {
            return (func_stacks, env_sites, rounds);
        }
    }
}

/// Join two environment stacks at a CFG merge (or between alternative
/// capture chains): bottom-aligned elementwise union; positions present
/// on only one side become unknown entries (genuinely different shapes
/// are uncertainty — a may-semantics union).
fn join_stacks(a: &[EnvEntry], b: &[EnvEntry]) -> Vec<EnvEntry> {
    let len = a.len().max(b.len());
    let mut out = Vec::with_capacity(len);
    for i in 0..len {
        match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) => out.push(EnvEntry {
                sites: x.sites.union(&y.sites).copied().collect(),
                unknown: x.unknown || y.unknown,
            }),
            (Some(x), None) | (None, Some(x)) => out.push(EnvEntry {
                sites: x.sites.clone(),
                unknown: true,
            }),
            // Unreachable: `len = max(a.len(), b.len())`, so for `i < len` at least one side is `Some`.
            (None, None) => unreachable!(),
        }
    }
    out
}

/// The rung-2 oracle: whole-module PTA answers behind the same seam —
/// [`Rung2AliasOracle::site_info_at`] keeps the ladder's fallback rule
/// (complete answers only; anything else is the rung-0 floor), and
/// [`Rung2AliasOracle::lex_env_at`] exposes the environment-identity
/// channel to the taint layer's lexical-slot rules.
pub struct Rung2AliasOracle<'m> {
    module: &'m Module,
    tables: Rung2Tables,
    stats: PtaStats,
}

impl<'m> Rung2AliasOracle<'m> {
    /// An oracle over `module` from the analysis tables.
    pub fn new(module: &'m Module, tables: Rung2Tables, stats: PtaStats) -> Self {
        Rung2AliasOracle {
            module,
            tables,
            stats,
        }
    }

    /// The module the engine ran over.
    pub fn module(&self) -> &'m Module {
        self.module
    }

    /// The rich query, in the rung-1 [`QueryAnswer`] vocabulary:
    /// `sites` are the keyed alloc sites (contexts stripped),
    /// `has_unknown` marks any incompleteness (unknown object, unkeyed
    /// object, empty/unanalyzed definition), `has_phi` comes from the
    /// local def-chain walk (the strong-update discipline's phi flag —
    /// unchanged across rungs). `unbalanced` never fires: the balanced
    /// discipline is folded into the fixed point (parameter answers
    /// union over recorded contexts only). `at` is point-independent
    /// (the analysis is flow-insensitive over SSA values, like rung 1).
    pub fn query(&self, base: ValueId, at: InstId) -> QueryAnswer {
        let _ = at;
        let answer = self
            .tables
            .answers
            .get(base.index())
            .cloned()
            .unwrap_or(ValueAnswer {
                has_unknown: true,
                ..ValueAnswer::default()
            });
        let has_phi = !answer.has_unknown
            && !answer.sites.is_empty()
            && resolve_alloc_sites(self.module, base).has_phi;
        QueryAnswer {
            sites: answer.sites,
            has_phi,
            has_unknown: answer.has_unknown,
            unbalanced: false,
            capped: self.stats.capped,
        }
    }

    /// The consumer-facing answer: the PTA result when it is complete,
    /// else the rung-0 local def-chain answer (the sound floor — the
    /// ladder's unchanged fallback rule).
    pub fn site_info_at(&self, base: ValueId, at: InstId) -> SiteInfo {
        let ans = self.query(base, at);
        if ans.precise_for_keying() {
            SiteInfo {
                sites: ans.sites,
                has_phi: ans.has_phi,
                has_unknown: false,
            }
        } else {
            resolve_alloc_sites(self.module, base)
        }
    }

    /// The lexical environment a `GetLexVar`/`PutLexVar` at `at` with
    /// scope-chain `level` denotes (see module docs).
    pub fn lex_env_at(&self, at: InstId, level: u16) -> EnvAnswer {
        let Some(stack) = self.tables.env_stack_at.get(at.index()) else {
            return EnvAnswer {
                has_unknown: true,
                ..EnvAnswer::default()
            };
        };
        let level = level as usize;
        if level >= stack.len() {
            return EnvAnswer {
                has_unknown: true,
                ..EnvAnswer::default()
            };
        }
        let entry = &stack[stack.len() - 1 - level];
        let mut sites = AllocSiteSet::new();
        for s in &entry.sites {
            sites.union_with(&AllocSiteSet::one(*s));
        }
        EnvAnswer {
            sites,
            has_unknown: entry.unknown,
        }
    }

    /// Whether `site` is a lexical-environment allocation (used by the
    /// taint layer's may-direction env fallback: an imprecise
    /// `GetLexVar` may read any env-keyed fact).
    pub fn is_env_site(&self, site: InstId) -> bool {
        self.tables
            .env_sites
            .get(site.index())
            .copied()
            .unwrap_or(false)
    }
}

impl<F> AliasOracle<F> for Rung2AliasOracle<'_> {
    fn inject_calling_context(&mut self, _call: InstId, _callee: FuncId, _fact: &F) {
        // The fixed point already co-evolved every context the module
        // records — there is nothing per-query left to learn.
    }
}

#[cfg(test)]
mod tests;
