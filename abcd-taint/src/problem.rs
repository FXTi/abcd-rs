//! The taint IFDS problem: the four flow functions of
//! [`abcd_analysis::dataflow::ifds::IfdsProblem`] specialized to
//! [`Fact`].
//!
//! ## Design rule (`design/analysis.md`)
//!
//! Flow functions are driven by `Op::operands()` + `Op::has_result()` —
//! the generic rule "a tainted operand taints the result" covers
//! `Mov`/binops/unops/compares/coercions/iterators — with explicit
//! per-family rules ONLY where semantics demand:
//!
//! - **LoadProp family** (`LoadProp`/`LoadPropIdx`/`LoadPropDyn`):
//!   access-path push/cut at the leading field key, matching heap facts by
//!   alloc-site intersection and local facts by positive-alias evidence.
//! - **StoreProp family** (incl. the `StoreOwnProp*` own-stores): the
//!   stored value's taint is re-keyed to a heap fact
//!   `(sites(object), key ++ fields)`; strong kills only under a single-site
//!   must-alias proof (`update_kind == Strong`), weak otherwise.
//! - **Calls** ([`IfdsProblem::call_flow`] /
//!   [`IfdsProblem::call_to_return_flow`]): N66 frame-slot arg→param
//!   mapping, summary application on the call-to-return edge, exclusive-kill
//!   of the call edge into the callee, and the fallback ladder.
//! - **Return wiring** ([`IfdsProblem::return_flow`]): return value →
//!   call result on the normal continuation; thrown value → the catch
//!   handler's `ExceptionParam` binding on handler return sites (T5).
//! - **Exception edges**: intraprocedural `Throw` → handler entry maps
//!   the thrown value's taint onto the catch binding
//!   ([`abcd_ir::ValueDef::ExceptionParam`]) — "ExceptionParam taints the catch
//!   binding".
//!
//! Everything else is pass-through (facts survive) plus the generic
//! operand→result rule.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::dataflow::heap::{AllocSiteSet, UpdateKind};
use abcd_analysis::dataflow::heap::{FieldChain, FieldKey, update_kind};
use abcd_analysis::dataflow::ifds::{CallGraphOracle, IfdsProblem};
use abcd_analysis::module_link::ModuleLinkTable;
use abcd_ir::op::SuperKey;
use abcd_ir::{
    BlockId, CallKind, ClassId, Const, FuncId, InstId, Module, Op, Sym, ValueDef, ValueId,
};

use crate::driver::{SinkSpec, SourceSpec, TaintConfig};
use crate::fact::{Fact, TaintBase, TaintFact, UNCAUGHT_EXCEPTION_VALUE};
use crate::gap;
use crate::names::{
    ClassPropStores, call_base_value, call_method_leaf, callee_name_candidates_indexed,
    kit_canonical_alias, normalize_sdk_specifier, quick_callee_leaf_sym,
};
use crate::oracle::Oracle;
use crate::prototype::{FamilyAnswer, PrototypeResolver};
use crate::summary::{CallbackGap, Endpoint, FallbackStep, SummaryRegistry};

/// How a call site is handled — the fallback ladder, memoized per site.
#[derive(Clone, Debug, PartialEq, Eq)]
enum SiteClass {
    /// A summary applies (registry hit).
    Summary { name: String, exclusive: bool },
    /// No summary; at least one resolved callee has a body — normal
    /// IFDS steps into it.
    BodyStep,
    /// No summary; callees are external or the callee is unknown but
    /// named (a global we have not summarized) — conservative keep.
    NativeKeep,
    /// No summary and no resolvable name — conservative keep.
    UnknownKeep,
}

/// How caller operands bind to callee params (N66; the frame-slot model
/// itself lives in `abcd_analysis::frame` — the alias engine's
/// interprocedural hops consume the same model).
///
/// When the annotation is ABSENT on a `<static>` callee the vendored
/// default is `callType = 0xF` — all three implicit slots — which is
/// exactly the es2abc corpus shape (every corpus function declares
/// `num_args = 3 + formals` and reads its first formal from `a3`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ParamBinding {
    /// The frame-slot model resolved: `this` → `this_slot`, args[i] →
    /// `params[formal_base + i]` (left-aligned formals).
    Precise {
        /// Index of the this slot, when the callee has one.
        this_slot: Option<usize>,
        /// First formal's index in `params` (= implicit slot count).
        formal_base: usize,
    },
    /// No reliable slot model (NON-STATIC callee without a callType
    /// annotation — inline REFUSES these, but taint must never silently
    /// drop a flow — or a callee with fewer params than its implicit
    /// slots, e.g. hand-built test modules): conservative
    /// over-approximation — a tainted `this`/arg taints EVERY param.
    OverApproxAll,
}

/// Resolve the param binding for `callee`.
fn param_binding(module: &Module, callee: FuncId) -> ParamBinding {
    let Some(fd) = module.func(callee) else {
        return ParamBinding::OverApproxAll;
    };
    let Some(slots) = abcd_analysis::frame::frame_slots_of(module, callee) else {
        return ParamBinding::OverApproxAll;
    };
    if fd.params.len() < slots.implicit_count() {
        return ParamBinding::OverApproxAll;
    }
    ParamBinding::Precise {
        this_slot: slots.this_index(),
        formal_base: slots.implicit_count(),
    }
}

type ModuleSlotUsers = HashMap<(ClassId, u32), Vec<FuncId>>;
type JsBridgePropIndex = HashMap<ValueId, Vec<(Sym, ValueId)>>;

struct PropTouchIndex {
    by_prop: HashMap<Sym, Vec<FuncId>>,
    dyn_funcs: Vec<FuncId>,
}

struct HeapSiteIndex {
    by_site: HashMap<InstId, Vec<FuncId>>,
    unknown_deref_cone: Vec<bool>,
    imprecise_lex_cone: Vec<bool>,
}

/// The taint problem over a module + call graph + the rung-selected
/// alias oracle ([`Oracle`]: rung-0 baseline, rung-1 demand-driven
/// engine, or rung-2 whole-module PTA) + summary registry + source/sink config.
pub struct TaintProblem<'m> {
    module: &'m Module,
    callgraph: &'m CallGraph,
    links: ModuleLinkTable,
    prop_stores: ClassPropStores,
    global_stores: HashMap<Sym, Vec<ValueId>>,
    /// Dense `BlockId::index() -> Option<FuncId>` owning-function index.
    block_to_func: Vec<Option<FuncId>>,
    /// Scoped `(FuncId, handler BlockId) -> exception ValueId` for intraprocedural
    /// and per-call exceptional dispatch.
    func_handler_exc: HashMap<(FuncId, BlockId), ValueId>,
    /// Per-function backward SSA local liveness for pruning dead `TaintBase::Local` facts.
    liveness: LocalLiveness,
    /// Lazy memo per `ValueId::index()`: `0 = unknown`, `1 = dead-prunable`,
    /// `2 = has aliasing property loads in its owning function`.
    value_keep_flag: RefCell<Vec<u8>>,
    /// Per-function lazy index of property loads with non-empty `site_info_at(object).sites`.
    func_alias_loads: RefCell<Vec<Option<FuncAliasLoads>>>,
    /// Cached `(func_idx, matching_load_indices)` for locals with `value_keep_flag == 2`.
    value_alias_loads: RefCell<HashMap<ValueId, ValueAliasLoads>>,
    oracle: RefCell<Oracle<'m>>,
    registry: &'m SummaryRegistry,
    config: &'m TaintConfig,
    /// Final `.`-segment leaves of configured [`SinkSpec::Call`] targets.
    sink_leaves: HashSet<String>,
    /// Per-function `(InstId, Option<start_index>)` of `GetUnmappedArgs` (`None`)
    /// and `CopyRestArgs` (`Some(start_index)`) instructions.
    variadic_ops: Vec<Vec<(InstId, Option<u16>)>>,
    /// `(func, param indices)` seeds, resolved from the config's
    /// function-name source specs and JSBridge proxy registrations at construction.
    param_seeds: Vec<(FuncId, Vec<ValueId>)>,
    /// Module-interned names whose `TryGetGlobal` / `globalThis.<name>` results are sources.
    global_sources: HashSet<Sym>,
    /// Call sites whose return values are tainted via `SourceSpec::CallReturn` (`N20` ordered).
    call_return_sources: BTreeSet<InstId>,
    /// Trailing `(err, data)` / `(data)` callback edges at `CallReturn` source sites.
    source_cb_edges: BTreeMap<InstId, Vec<FuncId>>,
    /// `(ClassId, ext_slot)` external imports tainted via `SourceSpec::ModuleImport`:
    /// `None` = whole-value taint, `Some(syms)` = field-sensitive namespace taint.
    module_import_sources: HashMap<(ClassId, u32), Option<Vec<Sym>>>,
    /// Async-machine `ResumeGenerator` instruction -> backward-paired awaited
    /// `ValueId`s from preceding `AwaitUncaught` / `SuspendGenerator` instructions.
    await_resume: HashMap<InstId, Vec<ValueId>>,
    /// Per-site fallback-ladder classification (memo).
    site_class: RefCell<HashMap<InstId, SiteClass>>,
    /// Sites already counted (counters are per-site, not per-fact).
    counted: RefCell<HashSet<InstId>>,
    /// The applied-summary log: `(call site, summary name)` in
    /// application order — reported by the driver.
    applied: RefCell<Vec<(InstId, String)>>,
    /// Fast dedup set accompanying `applied` so logging stays `O(1)` per fact.
    applied_seen: RefCell<HashSet<InstId>>,
    /// Receiver-family memo (one entry per queried receiver
    /// value; engine answers are point-independent at rung 1).
    proto_memo: RefCell<HashMap<ValueId, FamilyAnswer>>,
    /// Callback-gap edges (eager scan, [`crate::gap`]): summary call
    /// site → resolved callback bodies. The driver layers them onto
    /// the solver's call graph (`GapCallGraph`); the flow functions
    /// consult them to recognize gap edges.
    gap_edges: BTreeMap<InstId, Vec<FuncId>>,
    /// Fresh-result memo ([`TaintProblem::fresh_result_site`]).
    fresh_memo: RefCell<HashMap<ValueId, Option<InstId>>>,
    /// Callback-gap counters: call
    /// sites whose callback summary applied AND the callback value
    /// resolved to at least one user body.
    gap_resolved: usize,
    /// Callback-gap sites whose callback value did NOT resolve —
    /// the honest fallback (mini-gap tag only; gap.rs module docs).
    gap_unresolved: usize,
    /// Dense `FuncId::index() -> bool` backward caller cone of functions that
    /// can generate `0 -> d` taint facts across `callgraph ∪ gap_edges`.
    zero_needed: Vec<bool>,
    /// Precomputed synthetic `__abcd_ohos_harness__` call and allocation-site guard.
    harness: HarnessGuard,
    /// Reverse callback-gap caller index (`callee FuncId::index() -> caller FuncIds`).
    rev_gap_callers: Vec<Vec<FuncId>>,
    /// One-time lazy index `(src_cid, src_slot) -> Vec<FuncId>` of functions
    /// reading `TaintBase::ModuleVar(src_cid, src_slot)` directly or via ES links.
    module_slot_users: RefCell<Option<ModuleSlotUsers>>,
    /// Lazily memoized `(src_cid, src_slot) -> Vec<bool>` of functions that can
    /// transitively reach a module-variable reader of `(src_cid, src_slot)`.
    module_var_readers: RefCell<HashMap<(ClassId, u32), Vec<bool>>>,
    /// Lazily memoized `sym -> Vec<bool>` of functions that can transitively
    /// reach an `Op::TryGetGlobal` reader of `sym`.
    global_readers: RefCell<HashMap<Sym, Vec<bool>>>,
    /// One-time lazy heap-site dereference index across all rungs (`0`/`1`/`2`),
    /// with precomputed `O(1)` `unknown_deref_cone` and `imprecise_lex_cone`.
    heap_site_index: RefCell<Option<HeapSiteIndex>>,
    /// Lazily memoized `site_iid -> Vec<bool>` backward caller cone of `HeapSiteIndex::by_site`.
    heap_site_cone: RefCell<HashMap<InstId, Vec<bool>>>,
    /// Lazily memoized `Vec<bool>` backward caller cone of `Op::GetLexVar` readers.
    lex_var_readers: RefCell<Option<Vec<bool>>>,
    /// One-time lazy index of functions touching named/dynamic properties.
    prop_touch_index: RefCell<Option<PropTouchIndex>>,
    /// Lazily memoized `prop_sym -> Vec<bool>` backward caller cone of `prop_touch_index`.
    prop_touch_cone: RefCell<HashMap<Sym, Vec<bool>>>,
}

impl<'m> TaintProblem<'m> {
    /// Build the problem over `module`. Source specs that name functions
    /// are resolved against [`abcd_ir::FunctionData::name`]; global-load
    /// source names are interned into the module's symbol table copy —
    /// interning is by string equality, so a spec for a name the module
    /// never mentions simply never fires (the local table internment is
    /// keyed on the same strings via a side table below).
    pub fn new(
        module: &'m Module,
        callgraph: &'m CallGraph,
        oracle: Oracle<'m>,
        registry: &'m SummaryRegistry,
        config: &'m TaintConfig,
    ) -> Self {
        let links = ModuleLinkTable::build(module);
        Self::new_with_links(module, links, callgraph, oracle, registry, config)
    }

    /// Build the problem reusing a precomputed [`ModuleLinkTable`].
    pub fn new_with_links(
        module: &'m Module,
        links: ModuleLinkTable,
        callgraph: &'m CallGraph,
        oracle: Oracle<'m>,
        registry: &'m SummaryRegistry,
        config: &'m TaintConfig,
    ) -> Self {
        let prop_stores = ClassPropStores::build(module);
        Self::new_with_indexed(
            module,
            links,
            prop_stores,
            callgraph,
            oracle,
            registry,
            config,
        )
    }

    /// Build the problem reusing both [`ModuleLinkTable`] and [`ClassPropStores`].
    pub(crate) fn new_with_indexed(
        module: &'m Module,
        links: ModuleLinkTable,
        prop_stores: ClassPropStores,
        callgraph: &'m CallGraph,
        oracle: Oracle<'m>,
        registry: &'m SummaryRegistry,
        config: &'m TaintConfig,
    ) -> Self {
        let mut param_seeds = Vec::new();
        let global_sources = resolve_global_sources(module, config);
        for spec in &config.sources {
            if let SourceSpec::FunctionParams { name, params } = spec {
                for (fi, f) in module.functions.iter().enumerate() {
                    // `"*"` is the sensitivity-analysis wildcard (every
                    // function's params are sources).
                    if name == "*" || module.sym.resolve(f.name) == Some(name.as_str()) {
                        let values: Vec<ValueId> = match params {
                            Some(indices) => indices
                                .iter()
                                .filter_map(|&i| f.params.get(i as usize).copied())
                                .collect(),
                            None => f.params.clone(),
                        };
                        if !values.is_empty() {
                            param_seeds.push((FuncId::new(fi as u32), values));
                        }
                    }
                }
            }
        }
        let global_stores = build_global_stores_map(module);
        let (block_to_func, func_handler_exc) = build_exception_indexes(module);
        let module_import_sources = resolve_module_import_sources(module, &links, config);
        let sink_leaves: HashSet<String> = config
            .sinks
            .iter()
            .map(|s| match s {
                SinkSpec::Call { name } => name.rsplit('.').next().unwrap_or(name).to_owned(),
            })
            .collect();
        let variadic_ops = build_variadic_ops_index(module);

        let call_source_names: HashSet<&str> = config
            .sources
            .iter()
            .filter_map(|s| match s {
                SourceSpec::CallReturn { name } => Some(name.as_str()),
                _ => None,
            })
            .collect();

        let mut call_return_sources = BTreeSet::new();
        let mut source_cb_edges: BTreeMap<InstId, Vec<FuncId>> = BTreeMap::new();
        let mut jsbridge_props: Option<JsBridgePropIndex> = None;
        if !call_source_names.is_empty() || config.ohos_lifecycle {
            let mut wanted_leaves: HashSet<&str> = call_source_names
                .iter()
                .map(|s| s.rsplit('.').next().unwrap_or(s))
                .collect();
            if config.ohos_lifecycle {
                wanted_leaves.insert("registerJavaScriptProxy");
            }
            for (call, edge) in callgraph.sites() {
                let Some(inst) = module.inst(call) else {
                    continue;
                };
                let Op::Call { callee, args, .. } = &inst.op else {
                    continue;
                };
                if let Some(leaf_sym) =
                    quick_callee_leaf_sym(module, &links, &prop_stores, edge.caller, *callee)
                {
                    let direct_match = module
                        .sym
                        .resolve(leaf_sym)
                        .map(|s| s.rsplit('.').next().unwrap_or(s))
                        .is_some_and(|l| wanted_leaves.contains(l));
                    let resolved_match = !direct_match
                        && callgraph.callees_of_call_at(call).iter().any(|f| {
                            module
                                .func(*f)
                                .and_then(|fd| module.sym.resolve(fd.name))
                                .map(|n| n.rsplit('.').next().unwrap_or(n))
                                .is_some_and(|l| wanted_leaves.contains(l))
                        });
                    if !direct_match && !resolved_match {
                        continue;
                    }
                }
                let mut cands = callee_name_candidates_indexed(
                    module,
                    &links,
                    Some(&prop_stores),
                    edge.caller,
                    *callee,
                );
                for f in callgraph.callees_of_call_at(call) {
                    if let Some(fd) = module.func(*f)
                        && let Some(n) = module.sym.resolve(fd.name)
                        && !cands.iter().any(|x| x == n)
                    {
                        cands.push(n.to_owned());
                    }
                }
                if !call_source_names.is_empty()
                    && cands.iter().any(|c| call_source_names.contains(c.as_str()))
                {
                    call_return_sources.insert(call);
                    if let Some(&last_arg) = args.last() {
                        let cb_funcs = gap::resolve_callback_funcs(module, &oracle, last_arg, call);
                        if !cb_funcs.is_empty() {
                            source_cb_edges.insert(call, cb_funcs);
                        }
                    }
                }
                if config.ohos_lifecycle
                    && cands
                        .iter()
                        .any(|c| c == "@ohos.web.webview.WebviewController.registerJavaScriptProxy")
                    && let Some(&proxy_obj) = args.first()
                {
                    let prop_idx =
                        jsbridge_props.get_or_insert_with(|| build_jsbridge_prop_index(module));
                    collect_jsbridge_seeds(
                        module,
                        &oracle,
                        prop_idx,
                        proxy_obj,
                        args.get(2).copied(),
                        call,
                        &mut param_seeds,
                    );
                }
            }
        }

        let await_resume = abcd_analysis::control::build_await_resume_map(module);
        let liveness = LocalLiveness::build(module);
        let value_keep_flag = RefCell::new(vec![0u8; module.values.len()]);
        let func_alias_loads = RefCell::new((0..module.functions.len()).map(|_| None).collect());
        let value_alias_loads = RefCell::new(HashMap::new());

        let mut problem = TaintProblem {
            module,
            callgraph,
            links,
            prop_stores,
            global_stores,
            block_to_func,
            func_handler_exc,
            liveness,
            value_keep_flag,
            func_alias_loads,
            value_alias_loads,
            oracle: RefCell::new(oracle),
            registry,
            config,
            sink_leaves,
            variadic_ops,
            param_seeds,
            global_sources,
            call_return_sources,
            source_cb_edges: source_cb_edges.clone(),
            module_import_sources,
            await_resume,
            site_class: RefCell::new(HashMap::new()),
            counted: RefCell::new(HashSet::new()),
            applied: RefCell::new(Vec::new()),
            applied_seen: RefCell::new(HashSet::new()),
            proto_memo: RefCell::new(HashMap::new()),
            gap_edges: BTreeMap::new(),
            fresh_memo: RefCell::new(HashMap::new()),
            gap_resolved: 0,
            gap_unresolved: 0,
            zero_needed: Vec::new(),
            harness: build_harness_guard(module),
            rev_gap_callers: Vec::new(),
            module_slot_users: RefCell::new(None),
            module_var_readers: RefCell::new(HashMap::new()),
            global_readers: RefCell::new(HashMap::new()),
            heap_site_index: RefCell::new(None),
            heap_site_cone: RefCell::new(HashMap::new()),
            lex_var_readers: RefCell::new(None),
            prop_touch_index: RefCell::new(None),
            prop_touch_cone: RefCell::new(HashMap::new()),
        };
        // Eager gap scan (gap.rs): static edges, counter-free.
        let (mut edges, resolved, unresolved) = problem.scan_gap_edges();
        for (call, cb_funcs) in source_cb_edges {
            let entry = edges.entry(call).or_default();
            for f in cb_funcs {
                if !entry.contains(&f) {
                    entry.push(f);
                }
            }
            entry.sort();
        }
        let mut rev_gap_callers = vec![Vec::new(); module.functions.len()];
        for (&call_iid, callees) in &edges {
            if let Some(inst) = module.inst(call_iid)
                && let Some(caller_fid) = problem
                    .block_to_func
                    .get(inst.block.index())
                    .copied()
                    .flatten()
            {
                for &cb in callees {
                    if let Some(list) = rev_gap_callers.get_mut(cb.index()) {
                        list.push(caller_fid);
                    }
                }
            }
        }
        problem.gap_edges = edges;
        problem.rev_gap_callers = rev_gap_callers;
        problem.gap_resolved = resolved;
        problem.gap_unresolved = unresolved;
        problem.zero_needed = problem.compute_zero_needed();
        problem
    }

    /// Compute the dense backward caller cone (`callgraph ∪ gap_edges`) of
    /// functions capable of generating `0 -> d` taint facts.
    fn compute_zero_needed(&self) -> Vec<bool> {
        let n_funcs = self.module.functions.len();
        if !self.config.seed_all_functions {
            return vec![true; n_funcs];
        }
        let mut zero_needed = vec![false; n_funcs];
        let mut queue: VecDeque<FuncId> = VecDeque::new();
        let mark = |fid: FuncId, zn: &mut [bool], q: &mut VecDeque<FuncId>| {
            if let Some(f) = self.module.func(fid)
                && !f.blocks.is_empty()
                && let Some(slot) = zn.get_mut(fid.index())
                && !*slot
            {
                *slot = true;
                q.push_back(fid);
            }
        };

        for &(fid, _) in &self.param_seeds {
            mark(fid, &mut zero_needed, &mut queue);
        }
        for &call_iid in &self.call_return_sources {
            if let Some(inst) = self.module.inst(call_iid)
                && let Some(fid) = self
                    .block_to_func
                    .get(inst.block.index())
                    .copied()
                    .flatten()
            {
                mark(fid, &mut zero_needed, &mut queue);
            }
        }
        if !self.global_sources.is_empty() || !self.module_import_sources.is_empty() {
            for (fi, f) in self.module.functions.iter().enumerate() {
                if f.blocks.is_empty() || zero_needed[fi] {
                    continue;
                }
                let fid = FuncId::new(fi as u32);
                'blocks: for &b in &f.blocks {
                    let Some(bb) = self.module.block(b) else {
                        continue;
                    };
                    for &iid in &bb.insts {
                        let Some(inst) = self.module.inst(iid) else {
                            continue;
                        };
                        let matched = match &inst.op {
                            Op::TryGetGlobal { name, .. } => {
                                inst.result.is_some() && self.global_sources.contains(name)
                            }
                            Op::LoadProp { object, name } => {
                                inst.result.is_some()
                                    && self.global_sources.contains(name)
                                    && is_global_object(self.module, *object)
                            }
                            Op::LoadModuleVar { index, kind } => {
                                inst.result.is_some()
                                    && !kind.is_local()
                                    && self.links.inst_class(self.module, iid).is_some_and(|cid| {
                                        self.module_import_sources.get(&(cid, *index)).is_some_and(
                                            |opt| opt.as_ref().is_none_or(|syms| !syms.is_empty()),
                                        )
                                    })
                            }
                            _ => false,
                        };
                        if matched {
                            mark(fid, &mut zero_needed, &mut queue);
                            break 'blocks;
                        }
                    }
                }
            }
        }

        let mut rev_gap: Vec<Vec<FuncId>> = vec![Vec::new(); n_funcs];
        for (&call_iid, callees) in &self.gap_edges {
            let Some(inst) = self.module.inst(call_iid) else {
                continue;
            };
            let Some(caller_fid) = self
                .block_to_func
                .get(inst.block.index())
                .copied()
                .flatten()
            else {
                continue;
            };
            for &cb in callees {
                if let Some(list) = rev_gap.get_mut(cb.index()) {
                    list.push(caller_fid);
                }
            }
        }

        while let Some(curr) = queue.pop_front() {
            for &call_iid in self.callgraph.callers_of(curr) {
                if let Some(inst) = self.module.inst(call_iid)
                    && let Some(caller_fid) = self
                        .block_to_func
                        .get(inst.block.index())
                        .copied()
                        .flatten()
                {
                    mark(caller_fid, &mut zero_needed, &mut queue);
                }
            }
            if let Some(gap_callers) = rev_gap.get(curr.index()) {
                for &caller_fid in gap_callers {
                    mark(caller_fid, &mut zero_needed, &mut queue);
                }
            }
        }

        zero_needed
    }

    #[inline]
    fn is_harness_call(&self, call: InstId) -> bool {
        self.harness.calls.contains(&call)
    }

    fn expand_backward_callers(&self, reach: &mut [bool], queue: &mut VecDeque<FuncId>) {
        while let Some(curr) = queue.pop_front() {
            for &call_iid in self.callgraph.callers_of(curr) {
                if let Some(inst) = self.module.inst(call_iid)
                    && let Some(caller_fid) = self
                        .block_to_func
                        .get(inst.block.index())
                        .copied()
                        .flatten()
                    && Some(caller_fid) != self.harness.fid
                    && let Some(slot) = reach.get_mut(caller_fid.index())
                    && !*slot
                {
                    *slot = true;
                    queue.push_back(caller_fid);
                }
            }
            if let Some(gap_callers) = self.rev_gap_callers.get(curr.index()) {
                for &caller_fid in gap_callers {
                    if Some(caller_fid) != self.harness.fid
                        && let Some(slot) = reach.get_mut(caller_fid.index())
                        && !*slot
                    {
                        *slot = true;
                        queue.push_back(caller_fid);
                    }
                }
            }
        }
    }

    fn can_callee_read_module_var(&self, src_cid: ClassId, src_slot: u32, callee: FuncId) -> bool {
        if let Some(reach) = self.module_var_readers.borrow().get(&(src_cid, src_slot)) {
            return reach.get(callee.index()).copied().unwrap_or(false);
        }
        if self.module_slot_users.borrow().is_none() {
            let mut slot_to_funcs: HashMap<(ClassId, u32), Vec<FuncId>> = HashMap::new();
            let mut push_fn = |cid: ClassId, slot: u32, fid: FuncId| {
                let list = slot_to_funcs.entry((cid, slot)).or_default();
                if list.last() != Some(&fid) {
                    list.push(fid);
                }
            };
            for (fi, f) in self.module.functions.iter().enumerate() {
                let fid = FuncId::new(fi as u32);
                if Some(fid) == self.harness.fid || f.blocks.is_empty() {
                    continue;
                }
                for &b in &f.blocks {
                    let Some(bb) = self.module.block(b) else {
                        continue;
                    };
                    for &iid in &bb.insts {
                        let Some(inst) = self.module.inst(iid) else {
                            continue;
                        };
                        match &inst.op {
                            Op::LoadModuleVar { index, kind } => {
                                if kind.is_local() {
                                    push_fn(f.class_id, *index, fid);
                                } else if let Some(t) = self.links.external_load(f.class_id, *index)
                                {
                                    for sr in &t.slots {
                                        push_fn(sr.class_id, sr.slot, fid);
                                    }
                                }
                            }
                            Op::LoadProp { object, name } => {
                                if let Some(req_idx) = peel_ns_index(self.module, *object)
                                    && let Some(slots) = self
                                        .links
                                        .resolve_namespace_member(f.class_id, req_idx, *name)
                                {
                                    for sr in slots {
                                        push_fn(sr.class_id, sr.slot, fid);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            *self.module_slot_users.borrow_mut() = Some(slot_to_funcs);
        }

        let n_funcs = self.module.functions.len();
        let mut reach = vec![false; n_funcs];
        let mut fn_queue = VecDeque::new();
        {
            let users_borrow = self.module_slot_users.borrow();
            if let Some(funcs) = users_borrow
                .as_ref()
                .and_then(|m| m.get(&(src_cid, src_slot)))
            {
                for &fid in funcs {
                    if let Some(slot) = reach.get_mut(fid.index())
                        && !*slot
                    {
                        *slot = true;
                        fn_queue.push_back(fid);
                    }
                }
            }
        }
        self.expand_backward_callers(&mut reach, &mut fn_queue);
        let ans = reach.get(callee.index()).copied().unwrap_or(false);
        self.module_var_readers
            .borrow_mut()
            .insert((src_cid, src_slot), reach);
        ans
    }

    fn can_callee_read_global(&self, sym: Sym, callee: FuncId) -> bool {
        if let Some(reach) = self.global_readers.borrow().get(&sym) {
            return reach.get(callee.index()).copied().unwrap_or(false);
        }
        let n_funcs = self.module.functions.len();
        let mut reach = vec![false; n_funcs];
        let mut fn_queue = VecDeque::new();
        for (fi, f) in self.module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) == self.harness.fid || f.blocks.is_empty() {
                continue;
            }
            'scan_g: for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    if let Some(Op::TryGetGlobal { name, .. }) =
                        self.module.inst(iid).map(|i| &i.op)
                        && *name == sym
                    {
                        reach[fi] = true;
                        fn_queue.push_back(fid);
                        break 'scan_g;
                    }
                }
            }
        }
        self.expand_backward_callers(&mut reach, &mut fn_queue);
        let ans = reach.get(callee.index()).copied().unwrap_or(false);
        self.global_readers.borrow_mut().insert(sym, reach);
        ans
    }

    fn can_callee_read_lex_var(&self, callee: FuncId) -> bool {
        if let Some(reach) = self.lex_var_readers.borrow().as_ref() {
            return reach.get(callee.index()).copied().unwrap_or(false);
        }
        let n_funcs = self.module.functions.len();
        let mut reach = vec![false; n_funcs];
        let mut fn_queue = VecDeque::new();
        for (fi, f) in self.module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) == self.harness.fid || f.blocks.is_empty() {
                continue;
            }
            'scan_l: for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    if matches!(
                        self.module.inst(iid).map(|i| &i.op),
                        Some(Op::GetLexVar { .. })
                    ) {
                        reach[fi] = true;
                        fn_queue.push_back(fid);
                        break 'scan_l;
                    }
                }
            }
        }
        self.expand_backward_callers(&mut reach, &mut fn_queue);
        let ans = reach.get(callee.index()).copied().unwrap_or(false);
        *self.lex_var_readers.borrow_mut() = Some(reach);
        ans
    }

    fn call_has_body_callee(&self, call: InstId) -> bool {
        self.callgraph.callees_of_call_at(call).iter().any(|c| {
            self.module
                .func(*c)
                .is_some_and(|fd| !fd.is_external && !fd.blocks.is_empty())
        })
    }

    fn call_resolution_incomplete(&self, call: InstId) -> bool {
        let Some(edge) = self.callgraph.edge_at(call) else {
            return true;
        };
        if !edge.resolution_complete {
            return true;
        }
        self.callgraph.callees_of_call_at(call).iter().any(|&f| {
            self.module
                .func(f)
                .is_none_or(|fd| fd.is_external || fd.blocks.is_empty())
        })
    }

    fn call_matches_sink_leaf(&self, caller: FuncId, call: InstId, inst: &abcd_ir::Inst) -> bool {
        if self.sink_leaves.is_empty() {
            return false;
        }
        let Op::Call { callee, .. } = &inst.op else {
            return false;
        };
        if let Some(leaf) = call_method_leaf(self.module, inst)
            && self
                .module
                .sym
                .resolve(leaf)
                .map(|s| s.rsplit('.').next().unwrap_or(s))
                .is_some_and(|l| self.sink_leaves.contains(l))
        {
            return true;
        }
        if self.callgraph.callees_of_call_at(call).iter().any(|&f| {
            self.module
                .func(f)
                .and_then(|fd| self.module.sym.resolve(fd.name))
                .map(|s| s.rsplit('.').next().unwrap_or(s))
                .is_some_and(|l| self.sink_leaves.contains(l))
        }) {
            return true;
        }
        if let Some(leaf_sym) =
            quick_callee_leaf_sym(self.module, &self.links, &self.prop_stores, caller, *callee)
        {
            return self
                .module
                .sym
                .resolve(leaf_sym)
                .map(|s| s.rsplit('.').next().unwrap_or(s))
                .is_some_and(|l| self.sink_leaves.contains(l));
        }
        callee_name_candidates_indexed(
            self.module,
            &self.links,
            Some(&self.prop_stores),
            caller,
            *callee,
        )
        .iter()
        .any(|c| self.sink_leaves.contains(c.rsplit('.').next().unwrap_or(c)))
    }

    fn callee_may_return_this(&self, callee: FuncId) -> bool {
        let Some(fd) = self.module.func(callee) else {
            return false;
        };
        let this_v = match param_binding(self.module, callee) {
            ParamBinding::OverApproxAll => return true,
            ParamBinding::Precise {
                this_slot: Some(slot),
                ..
            } => match fd.params.get(slot).copied() {
                Some(v) => v,
                None => return false,
            },
            ParamBinding::Precise {
                this_slot: None, ..
            } => return false,
        };
        for &b in &fd.blocks {
            let Some(bb) = self.module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                if let Some(Op::Return { value: Some(rv) }) = self.module.inst(iid).map(|i| &i.op) {
                    let root = abcd_analysis::dataflow::heap::peel_movs(self.module, *rv);
                    if root == this_v {
                        return true;
                    }
                    if let Some(ValueDef::Inst(def_iid)) = self.module.value(root).map(|v| v.def)
                        && matches!(
                            self.module.inst(def_iid).map(|i| &i.op),
                            Some(Op::Phi { .. })
                        )
                    {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn can_callee_touch_this_prop(&self, prop: Sym, callee: FuncId) -> bool {
        self.can_callee_touch_prop(prop, callee) || self.callee_may_return_this(callee)
    }

    fn can_callee_touch_prop(&self, prop: Sym, callee: FuncId) -> bool {
        if let Some(reach) = self.prop_touch_cone.borrow().get(&prop) {
            return reach.get(callee.index()).copied().unwrap_or(false);
        }
        if self.prop_touch_index.borrow().is_none() {
            let mut by_prop: HashMap<Sym, Vec<FuncId>> = HashMap::new();
            let mut dyn_funcs: Vec<FuncId> = Vec::new();
            for (fi, f) in self.module.functions.iter().enumerate() {
                let fid = FuncId::new(fi as u32);
                if Some(fid) == self.harness.fid || f.blocks.is_empty() {
                    continue;
                }
                let mut has_dyn = false;
                for &b in &f.blocks {
                    let Some(bb) = self.module.block(b) else {
                        continue;
                    };
                    for &iid in &bb.insts {
                        let Some(inst) = self.module.inst(iid) else {
                            continue;
                        };
                        match &inst.op {
                            Op::LoadProp { name, .. }
                            | Op::StoreProp { name, .. }
                            | Op::StoreOwnPropName { name, .. }
                            | Op::LoadSuper {
                                key: SuperKey::Name(name),
                                ..
                            }
                            | Op::StoreSuper {
                                key: SuperKey::Name(name),
                                ..
                            } => {
                                let list = by_prop.entry(*name).or_default();
                                if list.last() != Some(&fid) {
                                    list.push(fid);
                                }
                            }
                            Op::LoadPropIdx { .. }
                            | Op::LoadPropDyn { .. }
                            | Op::StorePropIdx { .. }
                            | Op::StoreOwnPropIdx { .. }
                            | Op::StorePropDyn { .. }
                            | Op::StoreOwnPropDyn { .. }
                            | Op::LoadSuper {
                                key: SuperKey::Dynamic(_),
                                ..
                            }
                            | Op::StoreSuper {
                                key: SuperKey::Dynamic(_),
                                ..
                            }
                            | Op::GetIterator { .. }
                            | Op::CopyDataProps { .. }
                            | Op::ArraySpread { .. }
                            | Op::CreateObjectWithExcludedKeys { .. }
                            | Op::Throw { .. } => {
                                has_dyn = true;
                            }
                            Op::Call { .. }
                                if !self.call_has_body_callee(iid)
                                    || self.call_resolution_incomplete(iid)
                                    || self.call_matches_sink_leaf(fid, iid, inst)
                                    || matches!(
                                        self.compute_class(iid, true).0,
                                        SiteClass::Summary { .. }
                                    ) =>
                            {
                                has_dyn = true;
                            }
                            _ => {}
                        }
                    }
                }
                if has_dyn {
                    dyn_funcs.push(fid);
                }
            }
            *self.prop_touch_index.borrow_mut() = Some(PropTouchIndex { by_prop, dyn_funcs });
        }

        let n_funcs = self.module.functions.len();
        let mut reach = vec![false; n_funcs];
        let mut fn_queue = VecDeque::new();
        {
            let idx_borrow = self.prop_touch_index.borrow();
            if let Some(idx) = idx_borrow.as_ref() {
                for &fid in &idx.dyn_funcs {
                    if let Some(slot) = reach.get_mut(fid.index())
                        && !*slot
                    {
                        *slot = true;
                        fn_queue.push_back(fid);
                    }
                }
                if let Some(funcs) = idx.by_prop.get(&prop) {
                    for &fid in funcs {
                        if let Some(slot) = reach.get_mut(fid.index())
                            && !*slot
                        {
                            *slot = true;
                            fn_queue.push_back(fid);
                        }
                    }
                }
            }
        }
        self.expand_backward_callers(&mut reach, &mut fn_queue);
        let ans = reach.get(callee.index()).copied().unwrap_or(false);
        self.prop_touch_cone.borrow_mut().insert(prop, reach);
        ans
    }

    fn ensure_heap_site_index(&self) {
        if self.heap_site_index.borrow().is_some() {
            return;
        }
        let n_funcs = self.module.functions.len();
        let mut by_site: HashMap<InstId, Vec<FuncId>> = HashMap::new();
        let mut unknown_deref_cone = vec![false; n_funcs];
        let mut unk_queue = VecDeque::new();
        let mut imprecise_lex_cone = vec![false; n_funcs];
        let mut lex_queue = VecDeque::new();

        fn push_fn(by_site: &mut HashMap<InstId, Vec<FuncId>>, s: InstId, fid: FuncId) {
            let list = by_site.entry(s).or_default();
            if list.last() != Some(&fid) {
                list.push(fid);
            }
        }

        for (fi, f) in self.module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) == self.harness.fid || f.blocks.is_empty() {
                continue;
            }
            let mut has_unknown_deref = false;
            let mut has_imprecise_lex = false;

            for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    let Some(inst) = self.module.inst(iid) else {
                        continue;
                    };
                    let record_deref =
                        |v: ValueId, by_site: &mut HashMap<InstId, Vec<FuncId>>, unk: &mut bool| {
                            let (info, may) = {
                                let oracle = self.oracle.borrow();
                                (oracle.site_info_at(v, iid), oracle.may_sites_at(v, iid))
                            };
                            for s in info.sites.iter() {
                                push_fn(by_site, s, fid);
                            }
                            for s in may.iter() {
                                push_fn(by_site, s, fid);
                            }
                            if info.has_unknown {
                                match self.fresh_result_site(v) {
                                    Some(fs) => push_fn(by_site, fs, fid),
                                    None => *unk = true,
                                }
                            }
                        };
                    let record_val_sites =
                        |v: ValueId, by_site: &mut HashMap<InstId, Vec<FuncId>>| {
                            let (info_sites, may, known) = {
                                let oracle = self.oracle.borrow();
                                (
                                    oracle.site_info_at(v, iid).sites,
                                    oracle.may_sites_at(v, iid),
                                    oracle.known_sites_at(v, iid),
                                )
                            };
                            for s in info_sites.iter() {
                                push_fn(by_site, s, fid);
                            }
                            for s in may.iter() {
                                push_fn(by_site, s, fid);
                            }
                            for s in known.iter() {
                                push_fn(by_site, s, fid);
                            }
                            if let Some(fs) = self.fresh_result_site(v) {
                                push_fn(by_site, fs, fid);
                            }
                        };

                    match &inst.op {
                        Op::LoadProp { object, .. }
                        | Op::LoadPropIdx { object, .. }
                        | Op::LoadPropDyn { object, .. }
                        | Op::LoadSuper {
                            this_value: object, ..
                        }
                        | Op::GetIterator { obj: object }
                        | Op::CopyDataProps { src: object, .. }
                        | Op::CreateObjectWithExcludedKeys { obj: object, .. }
                        | Op::ArraySpread { src: object, .. } => {
                            record_deref(*object, &mut by_site, &mut has_unknown_deref);
                        }
                        Op::StoreProp { object, .. }
                        | Op::StoreOwnPropName { object, .. }
                        | Op::StorePropIdx { object, .. }
                        | Op::StoreOwnPropIdx { object, .. }
                        | Op::StorePropDyn { object, .. }
                        | Op::StoreOwnPropDyn { object, .. }
                        | Op::StoreSuper {
                            this_value: object, ..
                        } => {
                            record_val_sites(*object, &mut by_site);
                        }
                        Op::Throw { value } => {
                            record_val_sites(*value, &mut by_site);
                        }
                        Op::Call {
                            callee,
                            this,
                            args,
                            kind,
                        } => {
                            if matches!(
                                kind,
                                CallKind::Apply | CallKind::NewSpread | CallKind::SuperSpread
                            ) && let Some(&arr) = args.first()
                            {
                                record_deref(arr, &mut by_site, &mut has_unknown_deref);
                            }
                            if !self.call_has_body_callee(iid)
                                || self.call_resolution_incomplete(iid)
                                || self.call_matches_sink_leaf(fid, iid, inst)
                                || self.gap_edges.contains_key(&iid)
                                || matches!(
                                    self.compute_class(iid, true).0,
                                    SiteClass::Summary { .. }
                                )
                            {
                                record_val_sites(*callee, &mut by_site);
                                if let Some(t) = this {
                                    record_val_sites(*t, &mut by_site);
                                }
                                if let Some(bv) = call_base_value(self.module, inst) {
                                    record_val_sites(bv, &mut by_site);
                                }
                                for &a in args {
                                    record_val_sites(a, &mut by_site);
                                }
                            }
                        }
                        Op::GetLexVar { level, .. } => {
                            if let Some(env) = self.oracle.borrow().lex_env_at(iid, *level) {
                                for s in env.sites.iter() {
                                    push_fn(&mut by_site, s, fid);
                                }
                                if env.has_unknown || env.sites.is_empty() {
                                    has_imprecise_lex = true;
                                }
                            }
                        }
                        Op::PutLexVar { level, .. } => {
                            if let Some(env) = self.oracle.borrow().lex_env_at(iid, *level) {
                                for s in env.sites.iter() {
                                    push_fn(&mut by_site, s, fid);
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }

            if has_unknown_deref {
                unknown_deref_cone[fi] = true;
                unk_queue.push_back(fid);
            }
            if has_imprecise_lex {
                imprecise_lex_cone[fi] = true;
                lex_queue.push_back(fid);
            }
        }

        self.expand_backward_callers(&mut unknown_deref_cone, &mut unk_queue);
        self.expand_backward_callers(&mut imprecise_lex_cone, &mut lex_queue);

        *self.heap_site_index.borrow_mut() = Some(HeapSiteIndex {
            by_site,
            unknown_deref_cone,
            imprecise_lex_cone,
        });
    }

    fn can_callee_use_heap_site(&self, site: InstId, callee: FuncId) -> bool {
        self.ensure_heap_site_index();
        let is_env = self.oracle.borrow().is_env_site(site);
        {
            let idx_borrow = self.heap_site_index.borrow();
            if let Some(idx) = idx_borrow.as_ref() {
                if is_env {
                    if idx
                        .imprecise_lex_cone
                        .get(callee.index())
                        .copied()
                        .unwrap_or(false)
                    {
                        return true;
                    }
                } else if idx
                    .unknown_deref_cone
                    .get(callee.index())
                    .copied()
                    .unwrap_or(false)
                {
                    return true;
                }
            }
        }
        if let Some(reach) = self.heap_site_cone.borrow().get(&site) {
            return reach.get(callee.index()).copied().unwrap_or(false);
        }

        let n_funcs = self.module.functions.len();
        let mut reach = vec![false; n_funcs];
        let mut fn_queue = VecDeque::new();
        {
            let idx_borrow = self.heap_site_index.borrow();
            if let Some(funcs) = idx_borrow.as_ref().and_then(|idx| idx.by_site.get(&site)) {
                for &fid in funcs {
                    if let Some(slot) = reach.get_mut(fid.index())
                        && !*slot
                    {
                        *slot = true;
                        fn_queue.push_back(fid);
                    }
                }
            }
        }
        self.expand_backward_callers(&mut reach, &mut fn_queue);
        let ans = reach.get(callee.index()).copied().unwrap_or(false);
        self.heap_site_cone.borrow_mut().insert(site, reach);
        ans
    }

    /// Gate state-base facts entering `callee` across any call edge (reader-cone
    /// pruning for monotone `ModuleVar`, `Global`, `LexVar`, and `Heap` state
    /// across all module sizes and rungs, plus synthetic `__abcd_ohos_harness__`
    /// component isolation).
    fn allow_state_into_callee(&self, call: InstId, callee: FuncId, fact: &TaintFact) -> bool {
        match &fact.base {
            TaintBase::ModuleVar(src_cid, src_slot) => {
                if !self.can_callee_read_module_var(*src_cid, *src_slot, callee) {
                    return false;
                }
            }
            TaintBase::Global(sym) => {
                if !self.can_callee_read_global(*sym, callee) {
                    return false;
                }
            }
            TaintBase::LexVar(_, _) if !self.can_callee_read_lex_var(callee) => {
                return false;
            }
            TaintBase::Heap(sites) if !sites.is_empty() => {
                if !sites
                    .iter()
                    .any(|s| self.can_callee_use_heap_site(s, callee))
                {
                    return false;
                }
                if let Some(&FieldKey::Named(prop)) = fact.fields.elements().first() {
                    let has_env = {
                        let oracle = self.oracle.borrow();
                        sites.iter().any(|s| oracle.is_env_site(s))
                    };
                    if !has_env && !self.can_callee_touch_prop(prop, callee) {
                        return false;
                    }
                }
            }
            _ => {}
        }
        !self.is_harness_call(call) || self.allow_state_across_harness(call, callee, fact, true)
    }

    /// Gate state-base facts crossing synthetic `__abcd_ohos_harness__` call
    /// and return edges so component-local `this`/`this.context`, `LexVar`,
    /// `NewLexEnv`, `Heap(EMPTY)` wildcards, and scoped `ModuleVar` exports do
    /// not cross-pollute unrelated modules or `ViewPU` components.
    fn allow_state_across_harness(
        &self,
        call: InstId,
        callee: FuncId,
        fact: &TaintFact,
        is_enter: bool,
    ) -> bool {
        match &fact.base {
            TaintBase::Local(_) | TaintBase::Global(_) => true,
            TaintBase::LexVar(_, _) => false,
            TaintBase::Heap(sites) => {
                if sites.is_empty() {
                    return false;
                }
                if is_enter {
                    if sites.iter().all(|s| self.harness.alloc_sites.contains(&s)) {
                        return self
                            .harness
                            .call_allowed_sites
                            .get(&call)
                            .is_some_and(|allowed| sites.iter().any(|s| allowed.contains(&s)));
                    }
                    let all_env = {
                        let oracle = self.oracle.borrow();
                        sites.iter().all(|s| oracle.is_env_site(s))
                    };
                    if all_env {
                        return sites.iter().any(|s| {
                            self.links.inst_class(self.module, s) == self.links.func_class(callee)
                        });
                    }
                }
                true
            }
            TaintBase::ModuleVar(src_cid, src_slot) => {
                if is_enter {
                    self.can_callee_read_module_var(*src_cid, *src_slot, callee)
                } else {
                    true
                }
            }
        }
    }

    /// Borrow the cross-module linkage index.
    pub fn links(&self) -> &ModuleLinkTable {
        &self.links
    }

    /// Borrow the prebuilt per-class property-store index.
    pub(crate) fn prop_stores(&self) -> &ClassPropStores {
        &self.prop_stores
    }

    /// Static callback-gap edges — the driver layers them onto
    /// the solver's call graph via [`crate::gap::GapCallGraph`].
    pub fn gap_edges(&self) -> &BTreeMap<InstId, Vec<FuncId>> {
        &self.gap_edges
    }

    /// The gap-wrapper counters: `(sites with resolved callbacks, sites
    /// with unresolved callbacks)` (the honest fallback count).
    pub fn gap_counts(&self) -> (usize, usize) {
        (self.gap_resolved, self.gap_unresolved)
    }

    /// The eager gap scan (`gap.rs`): for every call site whose
    /// winning summary declares a full callback gap, resolve the
    /// callback argument to user bodies. COUNTER-FREE by construction —
    /// classification peeks (`compute_class(call, true)`), so the
    /// fallback-ladder counters keep classifying only solver-processed
    /// sites.
    fn scan_gap_edges(&self) -> (BTreeMap<InstId, Vec<FuncId>>, usize, usize) {
        let mut edges = BTreeMap::new();
        let mut resolved = 0usize;
        let mut unresolved = 0usize;
        for (call, edge) in self.callgraph.sites() {
            let Some(inst) = self.module.inst(call) else {
                continue;
            };
            let Op::Call { callee, args, .. } = &inst.op else {
                continue;
            };
            if let Some(leaf_sym) = quick_callee_leaf_sym(
                self.module,
                &self.links,
                &self.prop_stores,
                edge.caller,
                *callee,
            ) {
                let direct_match = self
                    .module
                    .sym
                    .resolve(leaf_sym)
                    .map(|s| s.rsplit('.').next().unwrap_or(s))
                    .is_some_and(|l| self.registry.has_callback_leaf(l));
                let resolved_match = !direct_match
                    && self.callgraph.callees_of_call_at(call).iter().any(|f| {
                        self.module
                            .func(*f)
                            .and_then(|fd| self.module.sym.resolve(fd.name))
                            .map(|n| n.rsplit('.').next().unwrap_or(n))
                            .is_some_and(|l| self.registry.has_callback_leaf(l))
                    });
                if !direct_match && !resolved_match {
                    continue;
                }
            }
            let SiteClass::Summary { name, .. } = self.compute_class(call, true).0 else {
                continue;
            };
            let Some(summary) = self.registry.peek(&name, args.len()) else {
                continue;
            };
            let Some(cb_gap) = &summary.callback else {
                continue;
            };
            if cb_gap.enter.is_empty() && !cb_gap.spawn_always {
                continue; // mini-gap only — nothing to spawn
            }
            let Some(&cbv) = args.get(cb_gap.param as usize) else {
                if !cb_gap.spawn_always {
                    unresolved += 1; // the callback argument is absent entirely
                }
                continue;
            };
            let funcs = gap::resolve_callback_funcs(self.module, &self.oracle.borrow(), cbv, call);
            if funcs.is_empty() {
                // Not-a-callback refinement: a slot filled
                // with a provably non-callable constant (the dual-form
                // `String.prototype.replace`'s string replacement) is
                // not a gap site at all — counting it as unresolved
                // would dilute the honest-fallback counter with sites
                // that have no user code to spawn into.
                if !cb_gap.spawn_always && !gap::definitely_not_callable(self.module, cbv) {
                    unresolved += 1;
                }
            } else {
                if !cb_gap.spawn_always {
                    resolved += 1;
                }
                edges.insert(call, funcs);
            }
        }
        (edges, resolved, unresolved)
    }

    /// The gap spec when `(call, callee)` is a gap edge: the eager
    /// scan's map carries the edge; the site's winning summary carries
    /// the spec. Returns an owned copy (the registry borrow must not
    /// outlive the caller's flow-function borrows).
    fn gap_at(&self, call: InstId, callee: FuncId) -> Option<CallbackGap> {
        let funcs = self.gap_edges.get(&call)?;
        if !funcs.contains(&callee) {
            return None;
        }
        let SiteClass::Summary { name, .. } = self.classify(call) else {
            return None;
        };
        let argc = match self.module.inst(call).map(|i| &i.op) {
            Some(Op::Call { args, .. }) => args.len(),
            _ => return None,
        };
        self.registry
            .peek(&name, argc)
            .and_then(|s| s.callback.clone())
    }

    /// The applied-summary log (application order).
    pub fn applied_summaries(&self) -> Vec<(InstId, String)> {
        self.applied.borrow().clone()
    }

    /// The k-limit for field chains.
    fn cap(&self) -> usize {
        self.config.max_field_chain
    }

    /// Classify a call site on the fallback ladder (memoized; counters
    /// fire once per site).
    ///
    /// The lookup precedence (`design/analysis.md`):
    ///
    /// 1. **direct user summary** (`SummaryRegistry::register` /
    ///    `TaintConfig::extra_summaries`) — overrides both builtins and
    ///    resolved bodies (`exclusive` kills the callee-body edge);
    /// 2. **resolved user body** — a callee the call graph resolved to
    ///    a function with a body is stepped into (concrete user code
    ///    beats preloaded builtin summaries and prototype heuristics);
    /// 3. **direct builtin summary** (`SummaryRegistry::with_builtins`);
    /// 4. **prototype-resolution path** — the receiver's alloc-kind /
    ///    constant / global-provenance family qualifies the method
    ///    leaf (`a.pop` + Array ⇒ `Array.prototype.pop`);
    ///    prototype-applied summaries are ALWAYS applied
    ///    non-exclusively (additive: flows are added, incoming taint
    ///    is retained — a may-typed receiver must never kill);
    /// 5. **native keep** (named) / **unknown keep** (no name).
    fn classify(&self, call: InstId) -> SiteClass {
        if let Some(c) = self.site_class.borrow().get(&call) {
            return c.clone();
        }
        // Non-call instructions keep the pre-refactor early-return
        // semantics: never memoized, never counted.
        let is_call = self
            .module
            .inst(call)
            .is_some_and(|i| matches!(i.op, Op::Call { .. }));
        if !is_call {
            return SiteClass::UnknownKeep;
        }
        let (class, tried) = self.compute_class(call, false);
        // Counters fire once per site.
        if self.counted.borrow_mut().insert(call) {
            match &class {
                SiteClass::Summary { name, .. } => self.registry.record_hit(name),
                SiteClass::BodyStep => self.registry.record_fallback(FallbackStep::BodyStep),
                SiteClass::NativeKeep => self.registry.record_fallback(FallbackStep::NativeKeep),
                SiteClass::UnknownKeep => self.registry.record_fallback(FallbackStep::Unknown),
            }
            if !matches!(&class, SiteClass::Summary { .. }) {
                for n in &tried {
                    // es2abc-mangled internal names (`#*#…`) can never be
                    // builtin summaries — counting them would dilute the
                    // backlog log (rung 2 resolves many more internal
                    // callees, whose FunctionData names enter the
                    // candidate list).
                    if !n.starts_with('#') {
                        self.registry.record_miss(n);
                    }
                }
            }
        }
        self.site_class.borrow_mut().insert(call, class.clone());
        class
    }

    /// The classification computation (the precedence table of
    /// [`TaintProblem::classify`]) without memoization or counters.
    /// `peek = true` routes registry queries through
    /// [`SummaryRegistry::peek`] — the eager gap scan's discipline, so
    /// the scan never perturbs the per-site counters. Returns the class
    /// plus the candidate names that missed (the backlog log's input
    /// when nothing rescues the site).
    fn compute_class(&self, call: InstId, peek: bool) -> (SiteClass, Vec<String>) {
        let Some(inst) = self.module.inst(call) else {
            return (SiteClass::UnknownKeep, Vec::new());
        };
        let Op::Call { callee, args, .. } = &inst.op else {
            return (SiteClass::UnknownKeep, Vec::new());
        };
        let argc = args.len();
        let caller = self
            .links
            .inst_func(self.module, call)
            .unwrap_or(FuncId::new(0));
        let mut names = callee_name_candidates_indexed(
            self.module,
            &self.links,
            Some(&self.prop_stores),
            caller,
            *callee,
        );
        let callees = self.callgraph.callees_of_call_at(call);
        let has_body = callees.iter().any(|f| {
            self.module
                .func(*f)
                .is_some_and(|fd| !fd.is_external && !fd.blocks.is_empty())
        });
        // Resolved callees contribute their FunctionData names (directly
        // resolved internal functions named like a user-summarized callable
        // match too; preloaded builtins yield to concrete user bodies).
        for f in callees {
            if let Some(fd) = self.module.func(*f)
                && let Some(n) = self.module.sym.resolve(fd.name)
                && !names.iter().any(|x| x == n)
            {
                names.push(n.to_owned());
            }
        }
        // Candidate names that missed — the backlog log counts them
        // when NO candidate rescues the site (a rescued name is not
        // backlog: `a.pop` resolved through the Array family must not
        // stay in the miss log).
        let mut tried: Vec<String> = Vec::new();
        let mut found = None;
        for n in &names {
            if has_body && self.registry.is_builtin_hit(n, argc) {
                continue;
            }
            let hit = if peek {
                self.registry.peek(n, argc)
            } else {
                self.registry.lookup(n, argc)
            };
            if let Some(s) = hit {
                found = Some((n.clone(), s.exclusive));
                break;
            }
            tried.push(n.clone());
        }
        let class = match found {
            Some((name, exclusive)) => SiteClass::Summary { name, exclusive },
            None => {
                if has_body {
                    SiteClass::BodyStep
                } else if let Some(name) =
                    self.prototype_summary(inst, call, argc, &mut tried, peek)
                {
                    // Prototype-path applications are additive-only
                    // (exclusive: false) — see the precedence table.
                    SiteClass::Summary {
                        name,
                        exclusive: false,
                    }
                } else if names.is_empty() {
                    SiteClass::UnknownKeep
                } else {
                    SiteClass::NativeKeep
                }
            }
        };
        (class, tried)
    }

    /// Prototype-resolution path: `recv.m(...)` → the
    /// receiver's prototype families ([`crate::prototype`]) →
    /// `Family.prototype.m` candidates, in family order. Returns the
    /// first registered summary key; every miss appends its
    /// synthesized key to `tried` (counted into the backlog log by the
    /// caller when nothing rescues the site). An empty/unknown
    /// receiver typing produces NO candidate at all — the site falls
    /// through to the fallback ladder unchanged (never invent).
    fn prototype_summary(
        &self,
        call_inst: &abcd_ir::Inst,
        call: InstId,
        argc: usize,
        tried: &mut Vec<String>,
        peek: bool,
    ) -> Option<String> {
        let leaf = call_method_leaf(self.module, call_inst)?;
        let leaf = self.module.sym.resolve(leaf)?.to_owned();
        let base = call_base_value(self.module, call_inst)?;
        let oracle = self.oracle.borrow();
        let resolver = PrototypeResolver::with_indexes(
            self.module,
            &oracle,
            &self.proto_memo,
            &self.links,
            &self.prop_stores,
            &self.global_stores,
        );
        let answer = resolver.families_of(base, call);
        drop(oracle);
        let mut hit = None;
        for family in &answer.families {
            let key = format!("{}.{leaf}", family.key());
            let found = if peek {
                self.registry.peek(&key, argc).is_some()
            } else {
                self.registry.lookup(&key, argc).is_some()
            };
            if found {
                hit = Some(key);
                break;
            }
            tried.push(key);
        }
        hit
    }

    /// Returns `Some(exc)` iff `return_site` is the first instruction of a catch
    /// handler block covering `call`'s block (`R4-H4` — normal continuations of
    /// calls inside a `catch` block are never mistaken for handler entries).
    fn exceptional_handler_for_call(&self, call: InstId, return_site: InstId) -> Option<ValueId> {
        let call_inst = self.module.inst(call)?;
        let rs_inst = self.module.inst(return_site)?;
        let rs_block = self.module.block(rs_inst.block)?;
        if rs_block.insts.first().copied() != Some(return_site) {
            return None;
        }
        self.handler_exception_for(call_inst.block, rs_inst.block)
    }

    /// The catch binding of the handler whose entry block is
    /// `succ_block`, restricted to try regions of the function owning
    /// `from_block` (intraprocedural throw dispatch; `O(1)` pre-indexed lookup).
    fn handler_exception_for(&self, from_block: BlockId, succ_block: BlockId) -> Option<ValueId> {
        let fid = self
            .block_to_func
            .get(from_block.index())
            .copied()
            .flatten()?;
        self.func_handler_exc.get(&(fid, succ_block)).copied()
    }

    /// Whether `TaintBase::Local(v)` must survive pass-through onto `target_inst`.
    fn should_retain_local_at(&self, v: ValueId, target_inst: InstId) -> bool {
        if v == UNCAUGHT_EXCEPTION_VALUE {
            return false;
        }
        if self
            .liveness
            .is_live_at(self.module, &self.await_resume, target_inst, v)
        {
            return true;
        }
        match self.module.value(v).map(|val| val.def) {
            None | Some(ValueDef::Param(_) | ValueDef::Const(_)) => return true,
            Some(ValueDef::Inst(_) | ValueDef::ExceptionParam(_)) => {}
        }
        let idx = v.index();
        let cached = self.value_keep_flag.borrow().get(idx).copied().unwrap_or(0);
        if cached == 1 {
            return false;
        }
        let Some(&loc) = self.liveness.inst_loc.get(target_inst.index()) else {
            return true;
        };
        if loc.func == UNSEEN_FUNC {
            return true;
        }
        let func_idx = loc.func as usize;
        let has_func_entry = self
            .func_alias_loads
            .borrow()
            .get(func_idx)
            .is_some_and(Option::is_some);
        if !has_func_entry {
            let built = {
                let oracle = self.oracle.borrow();
                FuncAliasLoads::build(self.module, FuncId::new(loc.func), &oracle)
            };
            if let Some(slot) = self.func_alias_loads.borrow_mut().get_mut(func_idx) {
                *slot = Some(built);
            }
        }
        if cached == 2
            && let Some(entry) = self.value_alias_loads.borrow().get(&v)
            && entry.func == loc.func
        {
            let fal_borrow = self.func_alias_loads.borrow();
            let Some(Some(fal)) = fal_borrow.get(func_idx) else {
                return true;
            };
            return fal.any_reachable_at(loc, &entry.load_ids);
        }

        let v_sites = self.oracle.borrow().site_info_at(v, InstId::new(0)).sites;
        if v_sites.is_empty() {
            if let Some(slot) = self.value_keep_flag.borrow_mut().get_mut(idx) {
                *slot = 1;
            }
            return false;
        }

        let matching = {
            let fal_borrow = self.func_alias_loads.borrow();
            let Some(Some(fal)) = fal_borrow.get(func_idx) else {
                return true;
            };
            fal.matching_loads_for(v, &v_sites)
        };
        if matching.is_empty() {
            if let Some(slot) = self.value_keep_flag.borrow_mut().get_mut(idx) {
                *slot = 1;
            }
            return false;
        }
        let matching_box = matching.into_boxed_slice();
        let reachable = {
            let fal_borrow = self.func_alias_loads.borrow();
            let Some(Some(fal)) = fal_borrow.get(func_idx) else {
                return true;
            };
            fal.any_reachable_at(loc, &matching_box)
        };
        if let Some(slot) = self.value_keep_flag.borrow_mut().get_mut(idx) {
            *slot = 2;
        }
        self.value_alias_loads.borrow_mut().insert(
            v,
            ValueAliasLoads {
                func: loc.func,
                load_ids: matching_box,
            },
        );
        reachable
    }

    /// Emit pass-through survival of `source` into `target_inst`, pruning dead
    /// non-aliased SSA local temporaries.
    fn push_passthrough_at(&self, source: &Fact, target_inst: InstId, out: &mut Vec<Fact>) {
        if let Fact::Taint(tf) = source
            && let TaintBase::Local(v) = tf.base
            && !self.should_retain_local_at(v, target_inst)
        {
            return;
        }
        out.push(source.clone());
    }

    /// Map incoming facts arriving at the first instruction of a block across
    /// **all** leading `Op::Phi` instructions in that block simultaneously
    /// (`R4-C1`), keyed by `from_block`.
    fn apply_block_entry_phis(
        &self,
        from_block: BlockId,
        target_inst: InstId,
        out: &mut Vec<Fact>,
    ) {
        let Some(target) = self.module.inst(target_inst) else {
            return;
        };
        let Some(bb) = self.module.block(target.block) else {
            return;
        };
        if bb.insts.first().copied() != Some(target_inst) {
            return;
        }
        let initial_len = out.len();
        if initial_len == 0 {
            return;
        }
        for &iid in &bb.insts {
            let Some(phi_inst) = self.module.inst(iid) else {
                break;
            };
            let Op::Phi { entries } = &phi_inst.op else {
                break;
            };
            let Some(phi_res) = phi_inst.result else {
                continue;
            };
            for idx in 0..initial_len {
                let rebased = match &out[idx] {
                    Fact::Taint(tf) => match tf.local_base() {
                        Some(v)
                            if entries
                                .iter()
                                .any(|(edge, val)| *val == v && edge.from == from_block) =>
                        {
                            Some(Fact::of(tf.rebased(TaintBase::Local(phi_res))))
                        }
                        _ => None,
                    },
                    Fact::Zero => None,
                };
                if let Some(fact) = rebased {
                    out.push(fact);
                }
            }
        }
    }

    /// Whether a load through `object` may pick up a heap fact keyed by
    /// `sites` (positive intersection, or unknown-provenance wildcard
    /// modulo [`Self::fresh_result_site`]).
    fn heap_may_reach(&self, sites: &AllocSiteSet, object: ValueId, at: InstId) -> bool {
        if sites.is_empty() {
            return true;
        }
        let obj = self.oracle.borrow().site_info_at(object, at);
        if sites.intersects(&obj.sites) {
            return true;
        }
        if obj.has_unknown {
            match self.fresh_result_site(object) {
                Some(site) => sites.iter().any(|s| s == site),
                None => true,
            }
        } else {
            false
        }
    }

    /// Fresh container keying: instructions that unconditionally allocate a
    /// fresh container (`CreateObjectWithExcludedKeys`, `CopyRestArgs`,
    /// `GetUnmappedArgs`) across all rungs (`0`/`1`/`2`), plus summary call
    /// results with no static `Return*` inflow at rung 2 (probe e13).
    fn fresh_result_site(&self, value: ValueId) -> Option<InstId> {
        if let Some(hit) = self.fresh_memo.borrow().get(&value) {
            return *hit;
        }
        let site = self.fresh_result_site_uncached(value);
        self.fresh_memo.borrow_mut().insert(value, site);
        site
    }

    /// The uncached worker of [`TaintProblem::fresh_result_site`].
    fn fresh_result_site_uncached(&self, value: ValueId) -> Option<InstId> {
        let abcd_ir::ValueDef::Inst(iid) = self.module.value(value)?.def else {
            return None;
        };
        let inst = self.module.inst(iid)?;
        if inst.result != Some(value) {
            return None;
        }
        if matches!(
            inst.op,
            Op::CreateObjectWithExcludedKeys { .. } | Op::CopyRestArgs { .. } | Op::GetUnmappedArgs
        ) {
            return Some(iid);
        }
        if self.config.alias_rung < 2 {
            return None;
        }
        let Op::Call { args, .. } = &inst.op else {
            return None;
        };
        let SiteClass::Summary { name, .. } = self.compute_class(iid, true).0 else {
            return None;
        };
        let summary = self.registry.peek(&name, args.len())?;
        let result_inflow = summary
            .flows
            .iter()
            .any(|f| matches!(f.to, Endpoint::Return | Endpoint::ReturnField(_)));
        if result_inflow { None } else { Some(iid) }
    }

    /// Whether local fact base `v` has positive-alias evidence with
    /// `object` (same value, or non-empty intersecting site sets).
    /// Unknown-on-either-side is deliberately NOT evidence for locals:
    /// params/globals would alias every load (documented rung-0 choice,
    /// kept under rung 1 — the engine only sharpens the site sets).
    fn local_alias_evidence(&self, v: ValueId, object: ValueId, at: InstId) -> bool {
        if v == object {
            return true;
        }
        let oracle = self.oracle.borrow();
        let a = oracle.site_info_at(v, at);
        let b = oracle.site_info_at(object, at);
        !a.sites.is_empty() && a.sites.intersects(&b.sites)
    }

    /// Whether call operand `v` at instruction `at` carries `fact` (either
    /// directly as `TaintBase::Local(v)` or via a tainted heap allocation site
    /// reachable from `v`).
    pub(crate) fn operand_matches_fact(&self, v: ValueId, fact: &TaintFact, at: InstId) -> bool {
        match &fact.base {
            TaintBase::Local(lv) => *lv == v,
            TaintBase::Heap(sites) => {
                if sites.is_empty() {
                    return false;
                }
                let (known, may, info) = {
                    let oracle = self.oracle.borrow();
                    (
                        oracle.known_sites_at(v, at),
                        oracle.may_sites_at(v, at),
                        oracle.site_info_at(v, at).sites,
                    )
                };
                sites.intersects(&known)
                    || sites.intersects(&may)
                    || sites.intersects(&info)
                    || self
                        .fresh_result_site(v)
                        .is_some_and(|fs| sites.iter().any(|s| s == fs))
            }
            _ => false,
        }
    }

    /// Access-path leading-field cut: what
    /// remains of `fields` after reading `key`. An empty chain means the
    /// base itself was tainted — any property read is tainted one step.
    fn cut_first(&self, fields: &FieldChain, key: FieldKey) -> Option<FieldChain> {
        if fields.is_empty() {
            return Some(FieldChain::new().pushed(key, self.cap()));
        }
        let first = fields.elements()[0];
        let compatible = match (first, key) {
            (FieldKey::Named(a), FieldKey::Named(b)) => a == b,
            // AnyIndex/AnyDynamic are wildcards (heap.rs discipline).
            _ => true,
        };
        if compatible {
            let mut rest = FieldChain::new();
            for &k in &fields.elements()[1..] {
                rest = rest.pushed(k, self.cap());
            }
            Some(rest)
        } else {
            None
        }
    }

    /// Access-path load rule: `result = object.key` at instruction `at`.
    fn load_rule(
        &self,
        fact: &TaintFact,
        object: ValueId,
        key: FieldKey,
        at: InstId,
        out: &mut Vec<Fact>,
    ) {
        let Some(result) = self.module.inst(at).and_then(|i| i.result) else {
            return;
        };
        let try_cut = |fields: &FieldChain| self.cut_first(fields, key);
        match &fact.base {
            TaintBase::Local(v) if self.local_alias_evidence(*v, object, at) => {
                if let Some(rest) = try_cut(&fact.fields) {
                    out.push(Fact::of(
                        fact.with_fields(rest).rebased(TaintBase::Local(result)),
                    ));
                }
            }
            TaintBase::Heap(sites) if self.heap_may_reach(sites, object, at) => {
                if let Some(rest) = try_cut(&fact.fields) {
                    out.push(Fact::of(
                        fact.with_fields(rest).rebased(TaintBase::Local(result)),
                    ));
                }
            }
            _ => {}
        }
    }

    /// Access-path store rule: `object.key = value` at instruction `at`.
    /// Returns whether the incoming fact survives (strong kills return
    /// false for the killed fact, restricted to matching `FieldKey::Named`
    /// properties per `R4-H1`).
    fn store_rule(
        &self,
        fact: &TaintFact,
        object: ValueId,
        key: FieldKey,
        value: ValueId,
        at: InstId,
        out: &mut Vec<Fact>,
    ) -> bool {
        let mut survive = true;
        let obj_info = self.oracle.borrow().site_info_at(object, at);
        if update_kind(&obj_info) == UpdateKind::Strong {
            let site = obj_info.sites;
            let at_location = match &fact.base {
                TaintBase::Heap(sites) => *sites == site,
                TaintBase::Local(v) => *v == object,
                _ => false,
            };
            if at_location && !fact.fields.is_empty() {
                let first = fact.fields.elements()[0];
                if matches!((first, key), (FieldKey::Named(a), FieldKey::Named(b)) if a == b) {
                    survive = false;
                }
            }
        }
        if fact.base == TaintBase::Local(value) {
            let mut chain = FieldChain::new().pushed(key, self.cap());
            for &k in fact.fields.elements() {
                chain = chain.pushed(k, self.cap());
            }
            if let Some(this_param) = self.new_ctor_this_param(object, at) {
                out.push(Fact::of(TaintFact {
                    base: TaintBase::Local(this_param),
                    fields: chain,
                }));
            } else {
                let injected = {
                    let oracle = self.oracle.borrow();
                    oracle.aliases_of_store(fact, object, key, at, self.cap())
                };
                if !injected.is_empty() {
                    out.extend(injected.into_iter().map(Fact::of));
                } else {
                    let sites = self.oracle.borrow().resolve(object).sites;
                    if sites.is_empty() {
                        out.push(Fact::of(TaintFact {
                            base: TaintBase::Local(object),
                            fields: chain.clone(),
                        }));
                    }
                    out.push(Fact::of(TaintFact {
                        base: TaintBase::Heap(sites),
                        fields: chain,
                    }));
                }
            }
        }
        survive
    }

    /// When `at` is inside a `FunctionKind::Constructor` whose recorded callers
    /// are all `CallKind::New`, return its `this` parameter `ValueId` if
    /// `object` is that `this` parameter.
    fn new_ctor_this_param(&self, object: ValueId, at: InstId) -> Option<ValueId> {
        let fid = self.links.inst_func(self.module, at)?;
        let this_param = self.ctor_this_of(fid)?;
        if object != this_param {
            return None;
        }
        let callers = self.callgraph.callers_of(fid);
        if callers.is_empty() {
            return None;
        }
        let all_new = callers.iter().all(|&c| {
            matches!(
                self.module.inst(c).map(|i| &i.op),
                Some(Op::Call {
                    kind: CallKind::New | CallKind::NewSpread,
                    ..
                })
            )
        });
        all_new.then_some(this_param)
    }

    fn ctor_this_of(&self, fid: FuncId) -> Option<ValueId> {
        ctor_this_of_module(self.module, fid)
    }

    fn emit_excess_variadic_arg(
        &self,
        callee: FuncId,
        arg_idx: usize,
        fields: &FieldChain,
        out: &mut Vec<Fact>,
    ) {
        let Some(entries) = self.variadic_ops.get(callee.index()) else {
            return;
        };
        for &(var_iid, min_start) in entries {
            if min_start.is_none_or(|s| arg_idx >= s as usize) {
                let mut chain = FieldChain::new().pushed(FieldKey::AnyIndex, self.cap());
                for &k in fields.elements() {
                    chain = chain.pushed(k, self.cap());
                }
                out.push(Fact::of(TaintFact {
                    base: TaintBase::Heap(AllocSiteSet::one(var_iid)),
                    fields: chain,
                }));
            }
        }
    }

    fn emit_spread_variadic_arg(
        &self,
        callee: FuncId,
        elem_fields: &FieldChain,
        out: &mut Vec<Fact>,
    ) {
        let Some(entries) = self.variadic_ops.get(callee.index()) else {
            return;
        };
        for &(var_iid, _) in entries {
            let mut chain = FieldChain::new().pushed(FieldKey::AnyIndex, self.cap());
            for &k in elem_fields.elements() {
                chain = chain.pushed(k, self.cap());
            }
            out.push(Fact::of(TaintFact {
                base: TaintBase::Heap(AllocSiteSet::one(var_iid)),
                fields: chain,
            }));
        }
    }

    /// The generic operand→result rule (Mov/binop/unop/compare/
    /// coercion/iterator families — everything with a result that is not
    /// in an explicitly handled family).
    fn generic_propagate(&self, inst: &abcd_ir::Inst, fact: &TaintFact, out: &mut Vec<Fact>) {
        let Some(result) = inst.result else { return };
        let Some(v) = fact.local_base() else { return };
        if !inst.op.has_operand(v) {
            return;
        }
        match &inst.op {
            Op::Compare { .. } => {
                if fact.fields.is_empty() {
                    out.push(Fact::of(TaintFact::local(result)));
                }
            }
            Op::UnaryOp { op, .. } => {
                if matches!(op, abcd_ir::UnOp::ToPropertyKey) || fact.fields.is_empty() {
                    out.push(Fact::of(TaintFact::local(result)));
                }
            }
            Op::BinaryOp { .. } => {
                out.push(Fact::of(TaintFact::local(result)));
            }
            _ => {
                out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
            }
        }
    }

    /// Match an incoming fact against a summary endpoint at a call site.
    /// Returns the leftover field chain below the endpoint path.
    fn match_endpoint(
        endpoint: &Endpoint,
        fact: &TaintFact,
        args: &[ValueId],
        base: Option<ValueId>,
    ) -> Option<FieldChain> {
        let local = fact.local_base()?;
        let path = match endpoint {
            Endpoint::Param(i) => {
                if *args.get(*i as usize)? != local {
                    return None;
                }
                None
            }
            Endpoint::AnyParamFrom(start) => {
                if !args.get(*start as usize..)?.contains(&local) {
                    return None;
                }
                None
            }
            Endpoint::Base => {
                if base? != local {
                    return None;
                }
                None
            }
            Endpoint::Return | Endpoint::ReturnField(_) => return None,
            Endpoint::Field(path) => {
                if base? != local {
                    return None;
                }
                Some(path)
            }
        };
        match path {
            None => Some(fact.fields.clone()),
            Some(path) => {
                let elems = fact.fields.elements();
                let p = path.elements();
                if elems.len() < p.len() {
                    return None;
                }
                for (a, b) in elems.iter().zip(p.iter()) {
                    if let (FieldKey::Named(x), FieldKey::Named(y)) = (a, b)
                        && x != y
                    {
                        return None;
                    }
                }
                let mut rest = FieldChain::new();
                for &k in &elems[p.len()..] {
                    rest = rest.pushed(k, usize::MAX);
                }
                Some(rest)
            }
        }
    }

    /// Match a summary FLOW's source endpoint against an incoming fact
    /// at call site `at`: the static local match first; otherwise the
    /// rung-1 heap-fact match — a fact `Heap(sites).chain` where `sites`
    /// positively intersects the points-to set of the endpoint's value
    /// (the e5 case: a field-tainted literal passed to `Object.assign`).
    /// Positive intersection is required on both sides (an unknown side
    /// is not evidence — the same discipline as
    /// [`TaintProblem::local_alias_evidence`]), so this adds flows over
    /// rung 0 without re-keying any existing match. `Field(path)`
    /// endpoints additionally require the fact's chain to start with
    /// `path` (the leftover below the path flows on — e.g.
    /// an `[AnyIndex]`-tagged array element read by
    /// `Array.prototype.pop` / `Iterator.prototype.next`). Returns the
    /// leftover chain and whether the match was heap-sourced (the
    /// substitute then re-keys to `Heap`, keeping the fact
    /// function-global instead of dying on a local). `may = true` (the
    /// gap enter) reads the endpoint value's sites through the
    /// MAY-direction query ([`Oracle::may_sites_at`] — the engine's
    /// resolution-complete caller fan-out is accepted, the
    /// `refine_with_points_to` discipline); `may = false` keeps the
    /// keying-precise `site_info_at` answer.
    fn match_flow_endpoint(
        &self,
        endpoint: &Endpoint,
        fact: &TaintFact,
        args: &[ValueId],
        base: Option<ValueId>,
        at: InstId,
        may: bool,
    ) -> Option<(FieldChain, bool)> {
        if let Some(leftover) = Self::match_endpoint(endpoint, fact, args, base) {
            return Some((leftover, false));
        }
        let TaintBase::Heap(sites) = &fact.base else {
            return None;
        };
        if sites.is_empty() {
            return None;
        }
        let path = match endpoint {
            Endpoint::Param(i) => {
                let value = *args.get(*i as usize)?;
                let pts = if may {
                    self.oracle.borrow().may_sites_at(value, at)
                } else {
                    self.oracle.borrow().site_info_at(value, at).sites
                };
                if pts.is_empty() || !pts.intersects(sites) {
                    return None;
                }
                None
            }
            Endpoint::AnyParamFrom(start) => {
                let slice = args.get(*start as usize..)?;
                let matched = slice.iter().any(|&value| {
                    let pts = if may {
                        self.oracle.borrow().may_sites_at(value, at)
                    } else {
                        self.oracle.borrow().site_info_at(value, at).sites
                    };
                    !pts.is_empty() && pts.intersects(sites)
                });
                if !matched {
                    return None;
                }
                None
            }
            Endpoint::Base => {
                let value = base?;
                let pts = if may {
                    self.oracle.borrow().may_sites_at(value, at)
                } else {
                    self.oracle.borrow().site_info_at(value, at).sites
                };
                if pts.is_empty() || !pts.intersects(sites) {
                    return None;
                }
                None
            }
            Endpoint::Field(path) => {
                let value = base?;
                let pts = if may {
                    self.oracle.borrow().may_sites_at(value, at)
                } else {
                    self.oracle.borrow().site_info_at(value, at).sites
                };
                if pts.is_empty() || !pts.intersects(sites) {
                    return None;
                }
                Some(path)
            }
            Endpoint::Return | Endpoint::ReturnField(_) => return None,
        };
        let leftover = match path {
            None => fact.fields.clone(),
            Some(p) => {
                let elems = fact.fields.elements();
                let want = p.elements();
                if elems.len() < want.len() {
                    return None;
                }
                for (a, b) in elems.iter().zip(want.iter()) {
                    if let (FieldKey::Named(x), FieldKey::Named(y)) = (a, b)
                        && x != y
                    {
                        return None;
                    }
                }
                let mut rest = FieldChain::new();
                for &k in &elems[want.len()..] {
                    rest = rest.pushed(k, usize::MAX);
                }
                rest
            }
        };
        Some((leftover, true))
    }

    /// Substitute a sink endpoint at the call site.
    #[expect(
        clippy::too_many_arguments,
        reason = "each parameter is a distinct call-site substitution facet"
    )]
    fn substitute(
        &self,
        endpoint: &Endpoint,
        leftover: &FieldChain,
        args: &[ValueId],
        base: Option<ValueId>,
        result: Option<ValueId>,
        is_handler_site: bool,
        from_heap: bool,
        at: InstId,
        out: &mut Vec<Fact>,
    ) {
        let append = |path: &FieldChain| {
            let mut chain = path.clone();
            for &k in leftover.elements() {
                chain = chain.pushed(k, self.cap());
            }
            chain
        };
        // The target key for a value endpoint: a heap-sourced match
        // re-keys onto the target's site set (function-global state);
        // unknown-site targets stay local (rung-0 behavior).
        let value_key = |v: ValueId| {
            if from_heap {
                let sites = self.oracle.borrow().site_info_at(v, at).sites;
                if !sites.is_empty() {
                    return TaintBase::Heap(sites);
                }
            }
            TaintBase::Local(v)
        };
        match endpoint {
            Endpoint::Param(i) => {
                if let Some(&v) = args.get(*i as usize) {
                    out.push(Fact::of(TaintFact {
                        base: value_key(v),
                        fields: leftover.clone(),
                    }));
                }
            }
            Endpoint::AnyParamFrom(start) => {
                if let Some(slice) = args.get(*start as usize..) {
                    for &v in slice {
                        out.push(Fact::of(TaintFact {
                            base: value_key(v),
                            fields: leftover.clone(),
                        }));
                    }
                }
            }
            Endpoint::Base => {
                if let Some(b) = base {
                    out.push(Fact::of(TaintFact {
                        base: value_key(b),
                        fields: leftover.clone(),
                    }));
                }
            }
            Endpoint::Return => {
                // A return value exists only on the normal continuation.
                if !is_handler_site && let Some(r) = result {
                    out.push(Fact::of(TaintFact {
                        base: TaintBase::Local(r),
                        fields: leftover.clone(),
                    }));
                }
            }
            Endpoint::ReturnField(path) => {
                // A result-field sink (filter's base-elements →
                // result-elements flow): the result value with the
                // declared path ++ leftover.
                if !is_handler_site && let Some(r) = result {
                    out.push(Fact::of(TaintFact {
                        base: TaintBase::Local(r),
                        fields: append(path),
                    }));
                }
            }
            Endpoint::Field(path) => {
                if let Some(b) = base {
                    let sites = self.oracle.borrow().site_info_at(b, at).sites;
                    let chain = append(path);
                    let base_key = if sites.is_empty() {
                        TaintBase::Local(b)
                    } else {
                        TaintBase::Heap(sites)
                    };
                    out.push(Fact::of(TaintFact {
                        base: base_key,
                        fields: chain,
                    }));
                }
            }
        }
    }

    /// Callback-gap enter mapping ([`crate::gap`]): at a gap edge
    /// `(call → cb_func)`, each of the gap's `enter` rules whose source
    /// endpoint matches the incoming fact seeds the callback's formal
    /// (the N66 frame-slot binding — formal 0 of an es2abc closure is
    /// `params[formal_base]`, not `params[1]`). A heap-sourced match
    /// seeds a LOCAL formal fact: the element VALUE rides the formal —
    /// the heap key was about the receiver's storage, not the
    /// extracted element. `OverApproxAll` binding taints every formal
    /// (never silently drop a flow).
    #[expect(
        clippy::too_many_arguments,
        reason = "each parameter is a distinct gap-edge context facet"
    )]
    fn gap_enter(
        &self,
        call: InstId,
        cb_func: FuncId,
        gap: &CallbackGap,
        fact: &TaintFact,
        args: &[ValueId],
        base: Option<ValueId>,
        out: &mut Vec<Fact>,
    ) {
        let Some(fd) = self.module.func(cb_func) else {
            return;
        };
        let binding = param_binding(self.module, cb_func);
        for enter in &gap.enter {
            let Some((leftover, _from_heap)) =
                self.match_flow_endpoint(&enter.from, fact, args, base, call, true)
            else {
                continue;
            };
            match binding {
                ParamBinding::OverApproxAll => {
                    for &p in &fd.params {
                        out.push(Fact::of(TaintFact {
                            base: TaintBase::Local(p),
                            fields: leftover.clone(),
                        }));
                    }
                }
                ParamBinding::Precise { formal_base, .. } => {
                    if let Some(&p) = fd.params.get(formal_base + enter.formal as usize) {
                        out.push(Fact::of(TaintFact {
                            base: TaintBase::Local(p),
                            fields: leftover.clone(),
                        }));
                    }
                }
            }
        }
    }
}

impl IfdsProblem for TaintProblem<'_> {
    type Fact = Fact;

    fn zero(&self) -> Fact {
        Fact::Zero
    }

    fn initial_seeds(&self) -> Vec<(FuncId, Fact)> {
        let mut seeds = Vec::new();
        if self.config.seed_all_functions {
            for (fi, f) in self.module.functions.iter().enumerate() {
                if !f.blocks.is_empty() && self.zero_needed.get(fi).copied().unwrap_or(false) {
                    seeds.push((FuncId::new(fi as u32), Fact::Zero));
                }
            }
        }
        for (func, params) in &self.param_seeds {
            for &p in params {
                seeds.push((*func, Fact::of(TaintFact::local(p))));
            }
        }
        seeds
    }

    fn normal_flow(
        &self,
        module: &Module,
        curr: InstId,
        succ: InstId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let Some(curr_inst) = module.inst(curr) else {
            return;
        };
        let Some(succ_inst) = module.inst(succ) else {
            return;
        };

        // ── Unconditional IFDS `0 -> d` source generation fires ONLY on the
        // zero fact (`Λ`), anchoring every generated source fact at `(func, Zero)`
        // rather than cross-multiplying unrelated incoming procedure-entry facts.
        let Fact::Taint(fact) = source else {
            let global_hit_name = match &curr_inst.op {
                Op::TryGetGlobal { name, .. } if self.global_sources.contains(name) => Some(*name),
                Op::LoadProp { object, name }
                    if self.global_sources.contains(name) && is_global_object(module, *object) =>
                {
                    Some(*name)
                }
                _ => None,
            };
            if let Some(name) = global_hit_name
                && let Some(result) = curr_inst.result
            {
                out.push(Fact::of(TaintFact::local(result)));
                if self.config.ohos_lifecycle
                    && module.sym.resolve(name)
                        == Some(abcd_analysis::ohos_lifecycle::OHOS_WANT_GLOBAL)
                {
                    let d1 = TaintFact::local(result).pushed(FieldKey::AnyDynamic, self.cap());
                    let d2 = d1.pushed(FieldKey::AnyDynamic, self.cap());
                    out.push(Fact::of(d1));
                    out.push(Fact::of(d2));
                }
            }
            if let Op::LoadModuleVar { index, kind } = &curr_inst.op
                && !kind.is_local()
                && let Some(cid) = self.links.inst_class(module, curr)
                && let Some(field_spec) = self.module_import_sources.get(&(cid, *index))
                && let Some(result) = curr_inst.result
            {
                match field_spec {
                    None => out.push(Fact::of(TaintFact::local(result))),
                    Some(syms) => {
                        for &sym in syms {
                            out.push(Fact::of(
                                TaintFact::local(result).pushed(FieldKey::Named(sym), self.cap()),
                            ));
                        }
                    }
                }
            }
            self.apply_block_entry_phis(curr_inst.block, succ, out);
            return;
        };

        match &curr_inst.op {
            Op::Phi { .. } => {
                self.push_passthrough_at(source, succ, out);
            }
            // ── Exception dispatch: `throw v` taints the catch binding (T5).
            Op::Throw { value } => {
                self.push_passthrough_at(source, succ, out);
                if self.operand_matches_fact(*value, fact, curr)
                    && let Some(exc) = self.handler_exception_for(curr_inst.block, succ_inst.block)
                {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(exc))));
                }
            }
            // ── Global bindings ──────────────────────────────────────
            Op::TryGetGlobal { name, .. } => {
                if fact.base == TaintBase::Global(*name)
                    && let Some(result) = curr_inst.result
                {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
                self.generic_propagate(curr_inst, fact, out);
                self.push_passthrough_at(source, succ, out);
            }
            Op::StoreGlobal { name, value }
            | Op::StoreGlobalRecord { name, value, .. }
            | Op::TryStoreGlobal { name, value } => {
                if fact.base == TaintBase::Local(*value) {
                    out.push(Fact::of(fact.rebased(TaintBase::Global(*name))));
                }
                self.push_passthrough_at(source, succ, out);
            }
            // ── Module variables (per-record + cross-module ES linking) ──
            Op::LoadModuleVar { index, kind } => {
                let cid = self
                    .links
                    .inst_class(module, curr)
                    .unwrap_or(ClassId::new(0));
                if let Some(result) = curr_inst.result {
                    if kind.is_local() {
                        if fact.base == TaintBase::ModuleVar(cid, *index) {
                            out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                        }
                    } else if let Some(target) = self.links.external_load(cid, *index)
                        && target
                            .slots
                            .iter()
                            .any(|sr| fact.base == TaintBase::ModuleVar(sr.class_id, sr.slot))
                    {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::StoreModuleVar { index, value } => {
                let cid = self
                    .links
                    .inst_class(module, curr)
                    .unwrap_or(ClassId::new(0));
                if fact.base == TaintBase::Local(*value) {
                    out.push(Fact::of(fact.rebased(TaintBase::ModuleVar(cid, *index))));
                }
                self.push_passthrough_at(source, succ, out);
            }
            // ── Lexical environment slots ────────────────────────────
            Op::GetLexVar { level, slot, .. } => {
                if fact.base == TaintBase::LexVar(*level, *slot)
                    && let Some(result) = curr_inst.result
                {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
                if let Some(env) = self.oracle.borrow().lex_env_at(curr, *level)
                    && let TaintBase::Heap(sites) = &fact.base
                {
                    let precise = !env.has_unknown && !env.sites.is_empty();
                    let hits = if precise {
                        env.sites.intersects(sites)
                    } else {
                        let oracle = self.oracle.borrow();
                        sites.iter().any(|s| oracle.is_env_site(s))
                    };
                    if hits
                        && let Some(rest) = self.cut_first(&fact.fields, FieldKey::AnyIndex)
                        && let Some(result) = curr_inst.result
                    {
                        out.push(Fact::of(
                            fact.with_fields(rest).rebased(TaintBase::Local(result)),
                        ));
                    }
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::PutLexVar {
                level, slot, value, ..
            } => {
                if fact.base == TaintBase::Local(*value) {
                    let keyed_env = self
                        .oracle
                        .borrow()
                        .lex_env_at(curr, *level)
                        .and_then(|env| {
                            (!env.has_unknown && !env.sites.is_empty()).then_some(env.sites)
                        });
                    match keyed_env {
                        Some(sites) => {
                            let mut chain =
                                FieldChain::new().pushed(FieldKey::AnyIndex, self.cap());
                            for &k in fact.fields.elements() {
                                chain = chain.pushed(k, self.cap());
                            }
                            out.push(Fact::of(TaintFact {
                                base: TaintBase::Heap(sites),
                                fields: chain,
                            }));
                        }
                        None => out.push(Fact::of(fact.rebased(TaintBase::LexVar(*level, *slot)))),
                    }
                }
                self.push_passthrough_at(source, succ, out);
            }
            // ── Iterator protocol objects ───────────────────────────
            Op::GetIterator { obj } => {
                if let Some(result) = curr_inst.result
                    && let TaintBase::Heap(sites) = &fact.base
                    && self.heap_may_reach(sites, *obj, curr)
                {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
                self.generic_propagate(curr_inst, fact, out);
                self.push_passthrough_at(source, succ, out);
            }
            // ── Loads (access-path cut + namespace/globalThis lookup) ─
            Op::LoadProp { object, name } => {
                self.load_rule(fact, *object, FieldKey::Named(*name), curr, out);
                if let Some(result) = curr_inst.result {
                    if is_global_object(module, *object) && fact.base == TaintBase::Global(*name) {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                    if let Some(cid) = self.links.inst_class(module, curr)
                        && let Some(req_idx) = peel_ns_index(module, *object)
                        && let Some(slots) =
                            self.links.resolve_namespace_member(cid, req_idx, *name)
                        && slots
                            .iter()
                            .any(|sr| fact.base == TaintBase::ModuleVar(sr.class_id, sr.slot))
                    {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::LoadPropIdx { object, .. } => {
                self.load_rule(fact, *object, FieldKey::AnyIndex, curr, out);
                self.push_passthrough_at(source, succ, out);
            }
            Op::LoadPropDyn { object, .. } => {
                self.load_rule(fact, *object, FieldKey::AnyDynamic, curr, out);
                self.push_passthrough_at(source, succ, out);
            }
            Op::LoadSuper { key, this_value } => {
                let fk = match key {
                    SuperKey::Name(s) => FieldKey::Named(*s),
                    SuperKey::Dynamic(_) => FieldKey::AnyDynamic,
                };
                self.load_rule(fact, *this_value, fk, curr, out);
                self.push_passthrough_at(source, succ, out);
            }
            // ── Stores (heap re-keying + strong/weak kills) ──────────
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
                if is_global_object(module, *object) && fact.base == TaintBase::Local(*value) {
                    out.push(Fact::of(fact.rebased(TaintBase::Global(*name))));
                }
                if self.store_rule(fact, *object, FieldKey::Named(*name), *value, curr, out) {
                    self.push_passthrough_at(source, succ, out);
                }
            }
            Op::StorePropIdx { object, value, .. } | Op::StoreOwnPropIdx { object, value, .. } => {
                if self.store_rule(fact, *object, FieldKey::AnyIndex, *value, curr, out) {
                    self.push_passthrough_at(source, succ, out);
                }
            }
            Op::StorePropDyn { object, value, .. } | Op::StoreOwnPropDyn { object, value, .. } => {
                if self.store_rule(fact, *object, FieldKey::AnyDynamic, *value, curr, out) {
                    self.push_passthrough_at(source, succ, out);
                }
            }
            Op::StoreSuper {
                key,
                this_value,
                value,
            } => {
                let fk = match key {
                    SuperKey::Name(s) => FieldKey::Named(*s),
                    SuperKey::Dynamic(_) => FieldKey::AnyDynamic,
                };
                if self.store_rule(fact, *this_value, fk, *value, curr, out) {
                    self.push_passthrough_at(source, succ, out);
                }
            }
            // ── Object / array / variadic-args bespoke ops ───────────
            Op::ArraySpread { dst, src, .. } => {
                // `starrayspread` writes the updated integer index to `result`
                // and mutates `*dst`'s elements (`R4-H5`).
                let matches_src = match &fact.base {
                    TaintBase::Local(v) => self.local_alias_evidence(*v, *src, curr),
                    TaintBase::Heap(sites) => self.heap_may_reach(sites, *src, curr),
                    _ => false,
                };
                if matches_src {
                    let elem_tail = if fact.fields.is_empty() {
                        Some(&[][..])
                    } else if matches!(
                        fact.fields.elements()[0],
                        FieldKey::AnyIndex | FieldKey::AnyDynamic
                    ) {
                        Some(&fact.fields.elements()[1..])
                    } else {
                        None
                    };
                    if let Some(tail) = elem_tail {
                        let mut dst_chain =
                            FieldChain::new().pushed(FieldKey::AnyIndex, self.cap());
                        for &k in tail {
                            dst_chain = dst_chain.pushed(k, self.cap());
                        }
                        let dst_sites = self.oracle.borrow().site_info_at(*dst, curr).sites;
                        out.push(Fact::of(TaintFact {
                            base: TaintBase::Local(*dst),
                            fields: dst_chain.clone(),
                        }));
                        out.push(Fact::of(TaintFact {
                            base: TaintBase::Heap(dst_sites),
                            fields: dst_chain,
                        }));
                    }
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::CopyDataProps { dst, src } => {
                let matches_src = match &fact.base {
                    TaintBase::Local(v) => self.local_alias_evidence(*v, *src, curr),
                    TaintBase::Heap(sites) => self.heap_may_reach(sites, *src, curr),
                    _ => false,
                };
                if matches_src {
                    let dst_sites = self.oracle.borrow().site_info_at(*dst, curr).sites;
                    if dst_sites.is_empty() || fact.base == TaintBase::Local(*src) {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(*dst))));
                    }
                    out.push(Fact::of(fact.rebased(TaintBase::Heap(dst_sites))));
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::CreateObjectWithExcludedKeys { obj, keys } => {
                if let Some(result) = curr_inst.result {
                    let matches_obj = match &fact.base {
                        TaintBase::Local(v) => self.local_alias_evidence(*v, *obj, curr),
                        TaintBase::Heap(sites) => self.heap_may_reach(sites, *obj, curr),
                        _ => false,
                    };
                    if matches_obj {
                        let excluded = match fact.fields.elements().first() {
                            Some(&FieldKey::Named(prop)) => keys
                                .iter()
                                .any(|&kv| const_string_sym(module, kv) == Some(prop)),
                            _ => false,
                        };
                        if !excluded {
                            out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                            out.push(Fact::of(
                                fact.rebased(TaintBase::Heap(AllocSiteSet::one(curr))),
                            ));
                        }
                    }
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::GetUnmappedArgs | Op::CopyRestArgs { .. } => {
                let start_idx = match &curr_inst.op {
                    Op::CopyRestArgs { start_index } => *start_index as usize,
                    _ => 0,
                };
                if let Some(result) = curr_inst.result {
                    if let TaintBase::Heap(sites) = &fact.base
                        && sites.iter().any(|s| s == curr)
                    {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                    } else if let Some(v) = fact.local_base()
                        && let Some(fid) = self.links.inst_func(module, curr)
                        && let Some(fd) = module.func(fid)
                    {
                        let matched_param = match param_binding(module, fid) {
                            ParamBinding::Precise { formal_base, .. } => fd
                                .params
                                .get(formal_base + start_idx..)
                                .is_some_and(|slice| slice.contains(&v)),
                            ParamBinding::OverApproxAll => fd.params.contains(&v),
                        };
                        if matched_param {
                            let mut chain =
                                FieldChain::new().pushed(FieldKey::AnyIndex, self.cap());
                            for &k in fact.fields.elements() {
                                chain = chain.pushed(k, self.cap());
                            }
                            out.push(Fact::of(TaintFact {
                                base: TaintBase::Local(result),
                                fields: chain.clone(),
                            }));
                            out.push(Fact::of(TaintFact {
                                base: TaintBase::Heap(AllocSiteSet::one(curr)),
                                fields: chain,
                            }));
                        }
                    }
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::SetObjectWithProto { proto, obj } => {
                if fact.base == TaintBase::Local(*proto) {
                    out.push(Fact::of(
                        TaintFact::local(*obj).pushed(FieldKey::AnyDynamic, self.cap()),
                    ));
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::StorePrivate { obj, value, .. } | Op::DefinePrivate { obj, value, .. } => {
                if fact.base == TaintBase::Local(*value) {
                    let sites = self.oracle.borrow().resolve(*obj).sites;
                    if sites.is_empty() {
                        out.push(Fact::of(
                            TaintFact::local(*obj).pushed(FieldKey::AnyDynamic, self.cap()),
                        ));
                    } else {
                        out.push(Fact::of(
                            TaintFact {
                                base: TaintBase::Heap(sites),
                                fields: FieldChain::new(),
                            }
                            .pushed(FieldKey::AnyDynamic, self.cap()),
                        ));
                    }
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::DefineMethod { object, func, .. } => {
                if fact.base == TaintBase::Local(*func) {
                    let sites = self.oracle.borrow().resolve(*object).sites;
                    out.push(Fact::of(
                        TaintFact {
                            base: TaintBase::Heap(sites),
                            fields: FieldChain::new(),
                        }
                        .pushed(FieldKey::AnyDynamic, self.cap()),
                    ));
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::DefineFunc { .. } => {
                let is_capture = fact
                    .local_base()
                    .is_some_and(|v| curr_inst.op.has_operand(v));
                if is_capture && let Some(result) = curr_inst.result {
                    out.push(Fact::of(TaintFact::local(result)));
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::ResumeGenerator { .. } => {
                if let Some(awaited_vals) = self.await_resume.get(&curr)
                    && let Some(v) = fact.local_base()
                    && awaited_vals.contains(&v)
                    && let Some(result) = curr_inst.result
                {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
                self.generic_propagate(curr_inst, fact, out);
                self.push_passthrough_at(source, succ, out);
            }
            // ── Everything else: the generic operand→result rule ─────
            _ => {
                self.generic_propagate(curr_inst, fact, out);
                self.push_passthrough_at(source, succ, out);
            }
        }
        self.apply_block_entry_phis(curr_inst.block, succ, out);
    }

    fn call_flow(
        &self,
        module: &Module,
        call: InstId,
        callee: FuncId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let is_source_cb = self
            .source_cb_edges
            .get(&call)
            .is_some_and(|fs| fs.contains(&callee));
        if is_source_cb {
            if matches!(source, Fact::Zero)
                && let Some(fd) = module.func(callee)
            {
                match param_binding(module, callee) {
                    ParamBinding::Precise { formal_base, .. } => {
                        let formal_count = fd.params.len().saturating_sub(formal_base);
                        let data_idx = if formal_count >= 2 { 1 } else { 0 };
                        if let Some(&p) = fd.params.get(formal_base + data_idx) {
                            out.push(Fact::of(TaintFact::local(p)));
                        }
                    }
                    ParamBinding::OverApproxAll => {
                        for &p in &fd.params {
                            out.push(Fact::of(TaintFact::local(p)));
                        }
                    }
                }
                return;
            }
            if let Fact::Taint(fact) = source
                && fact.is_state_base()
                && self.allow_state_into_callee(call, callee, fact)
            {
                out.push(source.clone());
            }
            return;
        }
        let gap = self.gap_at(call, callee);
        if gap.is_none()
            && matches!(
                self.classify(call),
                SiteClass::Summary {
                    exclusive: true,
                    ..
                }
            )
        {
            return;
        }
        let Fact::Taint(fact) = source else { return };
        let Some(call_inst) = module.inst(call) else {
            return;
        };
        let Op::Call {
            callee: callee_val,
            this,
            args,
            kind,
        } = &call_inst.op
        else {
            return;
        };
        let Some(fd) = module.func(callee) else {
            return;
        };

        // ── Callback-gap edge ────────────────────────────────────────
        if let Some(gap) = &gap {
            if fact.is_state_base() && self.allow_state_into_callee(call, callee, fact) {
                out.push(source.clone());
            }
            let base = call_base_value(module, call_inst);
            self.gap_enter(call, callee, gap, fact, args, base, out);
            return;
        }

        match &fact.base {
            TaintBase::Local(v) => {
                let allow_this_prop = if !matches!(kind, CallKind::New | CallKind::NewSpread)
                    && !args.contains(v)
                    && let Some(&FieldKey::Named(prop)) = fact.fields.elements().first()
                {
                    self.can_callee_touch_this_prop(prop, callee)
                } else {
                    true
                };
                let binding = param_binding(module, callee);
                if binding == ParamBinding::OverApproxAll {
                    let on_operands = match kind {
                        CallKind::SuperForwardAllArgs => {
                            let in_caller_params = self
                                .links
                                .inst_func(module, call)
                                .and_then(|cf| module.func(cf))
                                .is_some_and(|cfd| cfd.params.contains(v));
                            (allow_this_prop && (this.is_some_and(|t| t == *v) || args.contains(v)))
                                || in_caller_params
                        }
                        _ => (allow_this_prop && this.is_some_and(|t| t == *v)) || args.contains(v),
                    };
                    if on_operands {
                        for &p in &fd.params {
                            out.push(Fact::of(fact.rebased(TaintBase::Local(p))));
                        }
                        self.emit_spread_variadic_arg(callee, &fact.fields, out);
                    }
                } else {
                    let (this_slot, formal_base) = match binding {
                        ParamBinding::Precise {
                            this_slot,
                            formal_base,
                        } => (this_slot, formal_base),
                        ParamBinding::OverApproxAll => unreachable!(),
                    };
                    if allow_this_prop
                        && let Some(slot) = this_slot
                        && let Some(&p) = fd.params.get(slot)
                    {
                        let matches_this = if *kind == CallKind::SuperForwardAllArgs {
                            let caller_this = self.links.inst_func(module, call).and_then(|cf| {
                                let cfd = module.func(cf)?;
                                match param_binding(module, cf) {
                                    ParamBinding::Precise {
                                        this_slot: Some(cs),
                                        ..
                                    } => cfd.params.get(cs).copied(),
                                    _ => None,
                                }
                            });
                            this.is_some_and(|t| t == *v)
                                || args.first() == Some(v)
                                || caller_this == Some(*v)
                        } else {
                            this.is_some_and(|t| t == *v)
                        };
                        if matches_this {
                            out.push(Fact::of(fact.rebased(TaintBase::Local(p))));
                        }
                    }
                    match kind {
                        CallKind::Direct
                        | CallKind::Dynamic
                        | CallKind::New
                        | CallKind::Super
                        | CallKind::SuperArrow
                        | CallKind::ClassInit => {
                            for (i, &a) in args.iter().enumerate() {
                                if a == *v {
                                    if let Some(&p) = fd.params.get(formal_base + i) {
                                        out.push(Fact::of(fact.rebased(TaintBase::Local(p))));
                                    } else {
                                        self.emit_excess_variadic_arg(callee, i, &fact.fields, out);
                                    }
                                }
                            }
                        }
                        CallKind::Apply | CallKind::SuperSpread | CallKind::NewSpread => {
                            if args.first() == Some(v) {
                                let elem_fields = if fact.fields.is_empty() {
                                    Some(FieldChain::new())
                                } else if matches!(
                                    fact.fields.elements()[0],
                                    FieldKey::AnyIndex | FieldKey::AnyDynamic
                                ) {
                                    let mut rest = FieldChain::new();
                                    for &k in &fact.fields.elements()[1..] {
                                        rest = rest.pushed(k, self.cap());
                                    }
                                    Some(rest)
                                } else {
                                    None
                                };
                                if let Some(ef) = elem_fields {
                                    for &p in fd.params.iter().skip(formal_base) {
                                        out.push(Fact::of(TaintFact {
                                            base: TaintBase::Local(p),
                                            fields: ef.clone(),
                                        }));
                                    }
                                    self.emit_spread_variadic_arg(callee, &ef, out);
                                }
                            }
                        }
                        CallKind::SuperForwardAllArgs => {
                            if let Some(caller_fid) = self.links.inst_func(module, call)
                                && let Some(caller_fd) = module.func(caller_fid)
                            {
                                match param_binding(module, caller_fid) {
                                    ParamBinding::Precise {
                                        formal_base: caller_fb,
                                        ..
                                    } => {
                                        for (i, &cp) in
                                            caller_fd.params.iter().skip(caller_fb).enumerate()
                                        {
                                            if cp == *v {
                                                if let Some(&p) = fd.params.get(formal_base + i) {
                                                    out.push(Fact::of(
                                                        fact.rebased(TaintBase::Local(p)),
                                                    ));
                                                } else {
                                                    self.emit_excess_variadic_arg(
                                                        callee,
                                                        i,
                                                        &fact.fields,
                                                        out,
                                                    );
                                                }
                                            }
                                        }
                                    }
                                    ParamBinding::OverApproxAll => {
                                        if caller_fd.params.contains(v) {
                                            for &p in fd.params.iter().skip(formal_base) {
                                                out.push(Fact::of(
                                                    fact.rebased(TaintBase::Local(p)),
                                                ));
                                            }
                                            self.emit_spread_variadic_arg(
                                                callee,
                                                &fact.fields,
                                                out,
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                // Mini-gap channel: `[AnyIndex, ...]` tag on direct callee calls.
                if *v == *callee_val
                    && !fact.fields.is_empty()
                    && fact.fields.elements()[0] == FieldKey::AnyIndex
                {
                    let mut rest = FieldChain::new();
                    for &k in &fact.fields.elements()[1..] {
                        rest = rest.pushed(k, self.cap());
                    }
                    match param_binding(module, callee) {
                        ParamBinding::Precise { formal_base, .. } => {
                            if let Some(&p1) = fd.params.get(formal_base) {
                                out.push(Fact::of(
                                    fact.with_fields(rest).rebased(TaintBase::Local(p1)),
                                ));
                            }
                        }
                        ParamBinding::OverApproxAll => {
                            for &p in &fd.params {
                                out.push(Fact::of(
                                    fact.with_fields(rest.clone()).rebased(TaintBase::Local(p)),
                                ));
                            }
                        }
                    }
                }
            }
            TaintBase::Heap(sites) => {
                if matches!(
                    kind,
                    CallKind::Apply | CallKind::SuperSpread | CallKind::NewSpread
                ) && let Some(&arr) = args.first()
                    && self.heap_may_reach(sites, arr, call)
                {
                    let elem_fields = if fact.fields.is_empty() {
                        Some(FieldChain::new())
                    } else if matches!(
                        fact.fields.elements()[0],
                        FieldKey::AnyIndex | FieldKey::AnyDynamic
                    ) {
                        let mut rest = FieldChain::new();
                        for &k in &fact.fields.elements()[1..] {
                            rest = rest.pushed(k, self.cap());
                        }
                        Some(rest)
                    } else {
                        None
                    };
                    if let Some(ef) = elem_fields {
                        match param_binding(module, callee) {
                            ParamBinding::Precise { formal_base, .. } => {
                                for &p in fd.params.iter().skip(formal_base) {
                                    out.push(Fact::of(TaintFact {
                                        base: TaintBase::Local(p),
                                        fields: ef.clone(),
                                    }));
                                }
                            }
                            ParamBinding::OverApproxAll => {
                                for &p in &fd.params {
                                    out.push(Fact::of(TaintFact {
                                        base: TaintBase::Local(p),
                                        fields: ef.clone(),
                                    }));
                                }
                            }
                        }
                        self.emit_spread_variadic_arg(callee, &ef, out);
                    }
                }
                if self.allow_state_into_callee(call, callee, fact) {
                    out.push(source.clone());
                }
            }
            _ => {
                if self.allow_state_into_callee(call, callee, fact) {
                    out.push(source.clone());
                }
            }
        }
    }

    fn return_flow(
        &self,
        module: &Module,
        call_site: Option<InstId>,
        callee: FuncId,
        exit: InstId,
        return_site: Option<InstId>,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let Fact::Taint(fact) = source else { return };
        let Some(exit_inst) = module.inst(exit) else {
            return;
        };
        let gap = call_site.and_then(|c| self.gap_at(c, callee));
        if gap.is_none()
            && call_site.is_some_and(|c| {
                matches!(
                    self.classify(c),
                    SiteClass::Summary {
                        exclusive: true,
                        ..
                    }
                )
            })
        {
            return;
        }

        if fact.is_state_base() {
            if call_site.is_none_or(|c| {
                !self.is_harness_call(c) || self.allow_state_across_harness(c, callee, fact, false)
            }) {
                out.push(source.clone());
            }
            if let Op::Throw { value } = &exit_inst.op
                && let (Some(call), Some(rs)) = (call_site, return_site)
                && self.operand_matches_fact(*value, fact, exit)
                && let Some(exc) = self.exceptional_handler_for_call(call, rs)
            {
                out.push(Fact::of(fact.rebased(TaintBase::Local(exc))));
            }
            if let (Some(call), Some(rs)) = (call_site, return_site)
                && let Some(call_inst) = module.inst(call)
            {
                self.apply_block_entry_phis(call_inst.block, rs, out);
            }
            return;
        }

        let Some(v) = fact.local_base() else { return };

        match &exit_inst.op {
            Op::Return { value } => {
                if let (Some(call), Some(rs)) = (call_site, return_site)
                    && self.exceptional_handler_for_call(call, rs).is_none()
                    && let Some(call_inst) = module.inst(call)
                {
                    let is_new_ctor_this = !fact.fields.is_empty()
                        && self.ctor_this_of(callee) == Some(v)
                        && matches!(
                            call_inst.op,
                            Op::Call {
                                kind: CallKind::New | CallKind::NewSpread,
                                ..
                            }
                        );
                    if is_new_ctor_this {
                        out.push(Fact::of(TaintFact {
                            base: TaintBase::Heap(AllocSiteSet::one(call)),
                            fields: fact.fields.clone(),
                        }));
                        if let Some(result) = call_inst.result {
                            out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                        }
                    } else if let Some(gap) = &gap {
                        if value == &Some(v)
                            && let Some(chain) = &gap.return_to_result
                            && let Some(result) = call_inst.result
                        {
                            let mut fields = FieldChain::new();
                            for &k in chain.elements() {
                                fields = fields.pushed(k, self.cap());
                            }
                            for &k in fact.fields.elements() {
                                fields = fields.pushed(k, self.cap());
                            }
                            out.push(Fact::of(TaintFact {
                                base: TaintBase::Local(result),
                                fields,
                            }));
                        }
                    } else {
                        // `R4-H3`: map surviving field-bearing `Local(param).fields`
                        // (and non-`New` `this_slot`) back to caller `Local(arg)` / `Local(this)`.
                        if !fact.fields.is_empty()
                            && let Op::Call {
                                this, args, kind, ..
                            } = &call_inst.op
                            && let Some(fd) = module.func(callee)
                        {
                            match param_binding(module, callee) {
                                ParamBinding::Precise {
                                    this_slot,
                                    formal_base,
                                } => {
                                    if !matches!(kind, CallKind::New | CallKind::NewSpread)
                                        && let Some(slot) = this_slot
                                        && fd.params.get(slot) == Some(&v)
                                    {
                                        if let Some(caller_this) = *this {
                                            out.push(Fact::of(
                                                fact.rebased(TaintBase::Local(caller_this)),
                                            ));
                                        } else if *kind == CallKind::SuperForwardAllArgs
                                            && let Some(&v_this) = args.first()
                                        {
                                            out.push(Fact::of(
                                                fact.rebased(TaintBase::Local(v_this)),
                                            ));
                                        }
                                    }
                                    for (i, &p) in fd.params.iter().skip(formal_base).enumerate() {
                                        if p != v {
                                            continue;
                                        }
                                        match kind {
                                            CallKind::Direct
                                            | CallKind::Dynamic
                                            | CallKind::New
                                            | CallKind::Super
                                            | CallKind::SuperArrow
                                            | CallKind::ClassInit => {
                                                if let Some(&caller_arg) = args.get(i) {
                                                    out.push(Fact::of(
                                                        fact.rebased(TaintBase::Local(caller_arg)),
                                                    ));
                                                }
                                            }
                                            CallKind::SuperForwardAllArgs => {
                                                if let Some(cf) = self.links.inst_func(module, call)
                                                    && let Some(cfd) = module.func(cf)
                                                    && let ParamBinding::Precise {
                                                        formal_base: cfb,
                                                        ..
                                                    } = param_binding(module, cf)
                                                    && let Some(&cp) = cfd.params.get(cfb + i)
                                                {
                                                    out.push(Fact::of(
                                                        fact.rebased(TaintBase::Local(cp)),
                                                    ));
                                                }
                                            }
                                            CallKind::Apply
                                            | CallKind::SuperSpread
                                            | CallKind::NewSpread => {}
                                        }
                                    }
                                }
                                ParamBinding::OverApproxAll => {
                                    if fd.params.contains(&v) {
                                        if !matches!(kind, CallKind::New | CallKind::NewSpread)
                                            && let Some(caller_this) = *this
                                        {
                                            out.push(Fact::of(
                                                fact.rebased(TaintBase::Local(caller_this)),
                                            ));
                                        }
                                        for &a in args {
                                            out.push(Fact::of(fact.rebased(TaintBase::Local(a))));
                                        }
                                    }
                                }
                            }
                        }
                        if value == &Some(v)
                            && let Some(result) = call_inst.result
                        {
                            out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                        }
                    }
                }
            }
            Op::Throw { value } => {
                if v == *value
                    && let (Some(call), Some(rs)) = (call_site, return_site)
                    && let Some(exc) = self.exceptional_handler_for_call(call, rs)
                {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(exc))));
                }
            }
            Op::Call { .. } => {
                if v == UNCAUGHT_EXCEPTION_VALUE
                    && let (Some(call), Some(rs)) = (call_site, return_site)
                    && let Some(exc) = self.exceptional_handler_for_call(call, rs)
                {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(exc))));
                }
            }
            _ => {}
        }

        if let (Some(call), Some(rs)) = (call_site, return_site)
            && let Some(call_inst) = module.inst(call)
        {
            self.apply_block_entry_phis(call_inst.block, rs, out);
        }
    }

    fn call_to_return_flow(
        &self,
        module: &Module,
        call: InstId,
        return_site: InstId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let Some(call_inst) = module.inst(call) else {
            return;
        };
        let Fact::Taint(fact) = source else {
            if self.call_return_sources.contains(&call)
                && self
                    .exceptional_handler_for_call(call, return_site)
                    .is_none()
                && let Some(result) = call_inst.result
            {
                out.push(Fact::of(TaintFact::local(result)));
            }
            self.apply_block_entry_phis(call_inst.block, return_site, out);
            return;
        };
        let Op::Call { args, kind, .. } = &call_inst.op else {
            return;
        };
        let is_handler_site = self
            .exceptional_handler_for_call(call, return_site)
            .is_some();
        let on_operand = fact
            .local_base()
            .is_some_and(|v| call_inst.op.has_operand(v));

        match self.classify(call) {
            SiteClass::Summary { name, exclusive } => {
                let base = call_base_value(module, call_inst);
                let result = call_inst.result;
                if let Some(summary) = self.registry.lookup(&name, args.len()) {
                    let cleared = summary
                        .clears
                        .iter()
                        .any(|c| Self::match_endpoint(c, fact, args, base).is_some());
                    if !cleared {
                        for flow in &summary.flows {
                            if let Some((leftover, from_heap)) =
                                self.match_flow_endpoint(&flow.from, fact, args, base, call, false)
                            {
                                self.substitute(
                                    &flow.to,
                                    &leftover,
                                    args,
                                    base,
                                    result,
                                    is_handler_site,
                                    from_heap,
                                    call,
                                    out,
                                );
                            }
                        }
                        if let Some(cb_gap) = &summary.callback
                            && Self::match_endpoint(&Endpoint::Base, fact, args, base).is_some()
                            && let Some(&cbv) = args.get(cb_gap.param as usize)
                        {
                            out.push(Fact::of(
                                TaintFact::local(cbv).pushed(FieldKey::AnyIndex, self.cap()),
                            ));
                        }
                    }
                    // Exclusive summaries kill field-bearing operand bypass taints
                    // (`!fact.fields.is_empty()`), while scalar pass-by-value caller
                    // locals survive unless explicitly listed in `clears` (`R4-H3`).
                    let retain = !(cleared || (exclusive && on_operand && !fact.fields.is_empty()));
                    if retain {
                        self.push_passthrough_at(source, return_site, out);
                    }
                    if self.applied_seen.borrow_mut().insert(call) {
                        self.applied.borrow_mut().push((call, name));
                    }
                }
            }
            SiteClass::BodyStep => {
                if self.call_resolution_incomplete(call) {
                    self.push_passthrough_at(source, return_site, out);
                    if self.config.native_identity
                        && on_operand
                        && !is_handler_site
                        && let Some(result) = call_inst.result
                    {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                } else {
                    let untouched_this_prop =
                        if !matches!(kind, CallKind::New | CallKind::NewSpread)
                            && let Some(v) = fact.local_base()
                            && !args.contains(&v)
                            && let Some(&FieldKey::Named(prop)) = fact.fields.elements().first()
                        {
                            self.callgraph
                                .callees_of_call_at(call)
                                .iter()
                                .any(|&c| !self.can_callee_touch_this_prop(prop, c))
                        } else {
                            false
                        };
                    let is_spread_arg = matches!(
                        kind,
                        CallKind::Apply | CallKind::NewSpread | CallKind::SuperSpread
                    ) && fact.local_base() == args.first().copied();
                    if !on_operand || fact.fields.is_empty() || untouched_this_prop || is_spread_arg
                    {
                        self.push_passthrough_at(source, return_site, out);
                    }
                }
            }
            SiteClass::NativeKeep | SiteClass::UnknownKeep => {
                self.push_passthrough_at(source, return_site, out);
                if self.config.native_identity
                    && on_operand
                    && !is_handler_site
                    && let Some(result) = call_inst.result
                {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
            }
        }
        self.apply_block_entry_phis(call_inst.block, return_site, out);
    }

    fn call_uncaught_exit_flow(
        &self,
        module: &Module,
        call_site: InstId,
        callee: FuncId,
        callee_exit: InstId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let Fact::Taint(fact) = source else { return };
        if self.gap_at(call_site, callee).is_none()
            && matches!(
                self.classify(call_site),
                SiteClass::Summary {
                    exclusive: true,
                    ..
                }
            )
        {
            return;
        }
        let Some(exit_inst) = module.inst(callee_exit) else {
            return;
        };
        if fact.is_state_base()
            && (!self.is_harness_call(call_site)
                || self.allow_state_across_harness(call_site, callee, fact, false))
        {
            out.push(source.clone());
        }
        match &exit_inst.op {
            Op::Throw { value } => {
                if self.operand_matches_fact(*value, fact, callee_exit) {
                    out.push(Fact::of(
                        fact.rebased(TaintBase::Local(UNCAUGHT_EXCEPTION_VALUE)),
                    ));
                }
            }
            Op::Call { .. } if fact.local_base() == Some(UNCAUGHT_EXCEPTION_VALUE) => {
                out.push(source.clone());
            }
            _ => {}
        }
    }

    fn propagate_zero_to_callee(&self, _call: InstId, callee: FuncId) -> bool {
        self.zero_needed
            .get(callee.index())
            .copied()
            .unwrap_or(false)
    }
}

#[derive(Default)]
struct HarnessGuard {
    fid: Option<FuncId>,
    calls: HashSet<InstId>,
    alloc_sites: HashSet<InstId>,
    call_allowed_sites: HashMap<InstId, HashSet<InstId>>,
}

fn build_harness_guard(module: &Module) -> HarnessGuard {
    let harness_fid = module.functions.iter().enumerate().find_map(|(fi, f)| {
        (module.sym.resolve(f.name) == Some(abcd_analysis::ohos_lifecycle::OHOS_HARNESS_FUNC))
            .then_some(FuncId::new(fi as u32))
    });
    let Some(hfid) = harness_fid else {
        return HarnessGuard::default();
    };
    let Some(hfd) = module.func(hfid) else {
        return HarnessGuard::default();
    };

    let mut calls = HashSet::new();
    let mut alloc_sites = HashSet::new();
    let mut val_sites: HashMap<ValueId, HashSet<InstId>> = HashMap::new();
    let mut call_allowed_sites: HashMap<InstId, HashSet<InstId>> = HashMap::new();

    // Pass 1: record `AllocObject` / `AllocArray` / `Call(New)` sites and `Mov` aliases.
    for &b in &hfd.blocks {
        let Some(bb) = module.block(b) else { continue };
        for &iid in &bb.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            match &inst.op {
                Op::AllocObject { .. }
                | Op::AllocArray { .. }
                | Op::Call {
                    kind: CallKind::New | CallKind::NewSpread,
                    ..
                } => {
                    alloc_sites.insert(iid);
                    if let Some(r) = inst.result {
                        val_sites.entry(r).or_default().insert(iid);
                    }
                }
                Op::Mov { src } => {
                    if let Some(r) = inst.result
                        && let Some(sites) = val_sites.get(src).cloned()
                    {
                        val_sites.entry(r).or_default().extend(sites);
                    }
                }
                _ => {}
            }
        }
    }

    // Pass 2: associate `this.context = ctx_v` sites with the owning component instance.
    for &b in &hfd.blocks {
        let Some(bb) = module.block(b) else { continue };
        for &iid in &bb.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            match &inst.op {
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
                } if module.sym.resolve(*name) == Some("context") => {
                    if let Some(sites) = val_sites.get(value).cloned() {
                        val_sites.entry(*object).or_default().extend(sites);
                    }
                }
                Op::Mov { src } => {
                    if let Some(r) = inst.result
                        && let Some(sites) = val_sites.get(src).cloned()
                    {
                        val_sites.entry(r).or_default().extend(sites);
                    }
                }
                _ => {}
            }
        }
    }

    // Pass 3: compute allowed harness allocation sites per call instruction.
    for &b in &hfd.blocks {
        let Some(bb) = module.block(b) else { continue };
        for &iid in &bb.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            if let Op::Call { this, .. } = &inst.op {
                calls.insert(iid);
                let mut allowed = HashSet::new();
                if let Some(t) = this
                    && let Some(sites) = val_sites.get(t)
                {
                    allowed.extend(sites.iter().copied());
                }
                if let Some(r) = inst.result
                    && let Some(sites) = val_sites.get(&r)
                {
                    allowed.extend(sites.iter().copied());
                }
                if !allowed.is_empty() {
                    call_allowed_sites.insert(iid, allowed);
                }
            }
        }
    }

    HarnessGuard {
        fid: Some(hfid),
        calls,
        alloc_sites,
        call_allowed_sites,
    }
}

pub(crate) fn resolve_global_sources(module: &Module, config: &TaintConfig) -> HashSet<Sym> {
    let global_names: HashSet<&str> = config
        .sources
        .iter()
        .filter_map(|s| match s {
            SourceSpec::GlobalLoad { name } => Some(name.as_str()),
            _ => None,
        })
        .collect();
    let mut global_sources = HashSet::new();
    if !global_names.is_empty() {
        for i in 0..module.sym.len() {
            let sym = Sym::new(i as u32);
            if let Some(s) = module.sym.resolve(sym)
                && global_names.contains(s)
            {
                global_sources.insert(sym);
            }
        }
    }
    global_sources
}

pub(crate) fn resolve_module_import_sources(
    module: &Module,
    links: &ModuleLinkTable,
    config: &TaintConfig,
) -> HashMap<(ClassId, u32), Option<Vec<Sym>>> {
    let mut module_import_sources: HashMap<(ClassId, u32), Option<Vec<Sym>>> = HashMap::new();
    let mut device_info_syms: Option<Vec<Sym>> = None;
    for spec in &config.sources {
        if let SourceSpec::ModuleImport {
            specifier,
            import_name,
        } = spec
        {
            let want_spec = normalize_sdk_specifier(specifier);
            for ci in 0..module.classes.len() {
                let cid = ClassId::new(ci as u32);
                let mut ext_idx = 0u32;
                while let Some(target) = links.external_load(cid, ext_idx) {
                    for &(s_sym, i_sym) in &target.external_imports {
                        let s_str = module.sym.resolve(s_sym).unwrap_or("");
                        let i_str = module.sym.resolve(i_sym).unwrap_or("");
                        let norm_s = normalize_sdk_specifier(s_str);
                        let matched = (s_str == specifier || norm_s == want_spec)
                            && import_name.as_deref().is_none_or(|w| w == i_str);
                        if !matched {
                            continue;
                        }
                        let canon_spec =
                            kit_canonical_alias(&norm_s, i_str).unwrap_or(norm_s.as_str());
                        let is_device_info_ns = canon_spec == "@ohos.deviceInfo"
                            && matches!(import_name.as_deref(), None | Some("deviceInfo"))
                            && matches!(i_str, "default" | "*" | "deviceInfo");
                        let entry_val = if is_device_info_ns {
                            let syms = device_info_syms.get_or_insert_with(|| {
                                let mut out = Vec::new();
                                for idx in 0..module.sym.len() {
                                    let sym = Sym::new(idx as u32);
                                    if let Some(name) = module.sym.resolve(sym)
                                        && matches!(name, "ODID" | "udid" | "serial" | "AAID")
                                    {
                                        out.push(sym);
                                    }
                                }
                                out
                            });
                            Some(syms.clone())
                        } else {
                            None
                        };
                        match module_import_sources.get_mut(&(cid, ext_idx)) {
                            Some(existing) => {
                                if entry_val.is_none() {
                                    *existing = None;
                                }
                            }
                            None => {
                                module_import_sources.insert((cid, ext_idx), entry_val);
                            }
                        }
                    }
                    ext_idx += 1;
                }
            }
        }
    }
    module_import_sources
}

fn ctor_this_of_module(module: &Module, fid: FuncId) -> Option<ValueId> {
    let fd = module.func(fid)?;
    if fd.kind != abcd_ir::FunctionKind::Constructor {
        return None;
    }
    let ParamBinding::Precise {
        this_slot: Some(slot),
        ..
    } = param_binding(module, fid)
    else {
        return None;
    };
    fd.params.get(slot).copied()
}

fn is_global_object(module: &Module, v: ValueId) -> bool {
    let root = abcd_analysis::dataflow::heap::peel_movs(module, v);
    let Some(ValueDef::Inst(iid)) = module.value(root).map(|val| val.def) else {
        return false;
    };
    matches!(module.inst(iid).map(|i| &i.op), Some(Op::LoadGlobalObject))
}

fn const_string_sym(module: &Module, v: ValueId) -> Option<Sym> {
    let root = abcd_analysis::dataflow::heap::peel_movs(module, v);
    let cid = match module.value(root)?.def {
        ValueDef::Const(c) => c,
        ValueDef::Inst(iid) => match &module.inst(iid)?.op {
            Op::LoadConst(c) => *c,
            _ => return None,
        },
        ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return None,
    };
    match module.consts.get(cid) {
        Some(Const::String(s)) => Some(*s),
        _ => None,
    }
}

fn build_variadic_ops_index(module: &Module) -> Vec<Vec<(InstId, Option<u16>)>> {
    let mut out = vec![Vec::new(); module.functions.len()];
    for (fi, f) in module.functions.iter().enumerate() {
        if f.blocks.is_empty() {
            continue;
        }
        let mut entries = Vec::new();
        for &b in &f.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if inst.result.is_none() {
                    continue;
                }
                match &inst.op {
                    Op::GetUnmappedArgs => entries.push((iid, None)),
                    Op::CopyRestArgs { start_index } => entries.push((iid, Some(*start_index))),
                    _ => {}
                }
            }
        }
        out[fi] = entries;
    }
    out
}

#[expect(
    clippy::type_complexity,
    reason = "internal one-shot tuple builder returning precomputed exception tables"
)]
fn build_exception_indexes(
    module: &Module,
) -> (Vec<Option<FuncId>>, HashMap<(FuncId, BlockId), ValueId>) {
    let mut block_to_func = vec![None; module.blocks.len()];
    let mut func_handler_exc = HashMap::new();
    for (fi, f) in module.functions.iter().enumerate() {
        let fid = FuncId::new(fi as u32);
        for &b in &f.blocks {
            if let Some(slot) = block_to_func.get_mut(b.index()) {
                slot.get_or_insert(fid);
            }
        }
        for region in &f.try_regions {
            for catch in &region.catches {
                func_handler_exc
                    .entry((fid, catch.handler))
                    .or_insert(catch.exception);
            }
        }
    }
    (block_to_func, func_handler_exc)
}

fn build_global_stores_map(module: &Module) -> HashMap<Sym, Vec<ValueId>> {
    let mut out: HashMap<Sym, Vec<ValueId>> = HashMap::new();
    for f in &module.functions {
        for &b in &f.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::StoreGlobal { name, value }
                    | Op::StoreGlobalRecord { name, value, .. }
                    | Op::TryStoreGlobal { name, value } => {
                        out.entry(*name).or_default().push(*value);
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
                    } if is_global_object(module, *object) => {
                        out.entry(*name).or_default().push(*value);
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

const UNSEEN_FUNC: u32 = u32::MAX;
const UNUSED_BLOCK: u32 = u32::MAX;
const MULTI_USE_BLOCK: u32 = u32::MAX - 1;

#[derive(Clone, Copy)]
struct InstLivenessLoc {
    func: u32,
    block_local: u32,
    pos: u32,
}

struct FuncLiveness {
    words_per_block: usize,
    aug_live_out_words: Vec<u64>,
    val_to_lidx: HashMap<ValueId, u32>,
    single_block_last_use: Vec<(u32, u32)>,
    multi_block_last_use: HashMap<(u32, u32), u32>,
}

impl FuncLiveness {
    fn empty() -> Self {
        Self {
            words_per_block: 0,
            aug_live_out_words: Vec::new(),
            val_to_lidx: HashMap::new(),
            single_block_last_use: Vec::new(),
            multi_block_last_use: HashMap::new(),
        }
    }

    fn build(module: &Module, fid: FuncId, await_resume: &HashMap<InstId, Vec<ValueId>>) -> Self {
        let Some(f) = module.func(fid) else {
            return Self::empty();
        };
        if f.blocks.is_empty() {
            return Self::empty();
        }

        let mut local_blocks: Vec<BlockId> = Vec::with_capacity(f.blocks.len());
        let mut block_to_local: HashMap<BlockId, usize> = HashMap::with_capacity(f.blocks.len());
        for &b in &f.blocks {
            if let std::collections::hash_map::Entry::Vacant(e) = block_to_local.entry(b) {
                e.insert(local_blocks.len());
                local_blocks.push(b);
            }
        }
        let num_blocks = local_blocks.len();
        let ctor_this = ctor_this_of_module(module, fid);

        let mut val_to_lidx: HashMap<ValueId, u32> = HashMap::new();
        let mut intern_val = |v: ValueId| {
            if v.index() >= module.values.len() {
                return;
            }
            let next_id = val_to_lidx.len() as u32;
            val_to_lidx.entry(v).or_insert(next_id);
        };

        for &p in &f.params {
            intern_val(p);
        }
        for region in &f.try_regions {
            for catch in &region.catches {
                intern_val(catch.exception);
            }
        }
        for &b in &local_blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if let Some(res) = inst.result {
                    intern_val(res);
                }
                inst.op.for_each_operand(&mut intern_val);
                if matches!(inst.op, Op::Call { .. })
                    && let Some(base_v) = call_base_value(module, inst)
                {
                    intern_val(base_v);
                }
                if matches!(inst.op, Op::ResumeGenerator { .. })
                    && let Some(aws) = await_resume.get(&iid)
                {
                    for &aw in aws {
                        intern_val(aw);
                    }
                }
                if matches!(inst.op, Op::Return { .. })
                    && let Some(ct) = ctor_this
                {
                    intern_val(ct);
                }
            }
        }

        let num_vals = val_to_lidx.len();
        let words = num_vals.div_ceil(64);
        if words == 0 {
            return Self::empty();
        }

        let mut single_block_last_use = vec![(UNUSED_BLOCK, 0u32); num_vals];
        let mut multi_block_last_use: HashMap<(u32, u32), u32> = HashMap::new();

        let mut norm_succs: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];
        let mut norm_preds: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];
        let mut exc_succs: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];
        let mut exc_preds: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];
        let mut entry_exc_kill = vec![0u64; num_blocks * words];

        for (b_local, &b) in local_blocks.iter().enumerate() {
            for s in abcd_analysis::control::block_succs(module, b) {
                if let Some(&sl) = block_to_local.get(&s)
                    && !norm_succs[b_local].contains(&sl)
                {
                    norm_succs[b_local].push(sl);
                    norm_preds[sl].push(b_local);
                }
            }
        }
        for region in &f.try_regions {
            let mut handlers = Vec::new();
            for catch in &region.catches {
                if let Some(&hl_usize) = block_to_local.get(&catch.handler) {
                    if !handlers.contains(&hl_usize) {
                        handlers.push(hl_usize);
                    }
                    if let Some(&lidx) = val_to_lidx.get(&catch.exception) {
                        let li = lidx as usize;
                        entry_exc_kill[hl_usize * words + li / 64] |= 1u64 << (li % 64);
                    }
                }
            }
            for &prot_b in &region.protected {
                if let Some(&pl_usize) = block_to_local.get(&prot_b) {
                    for &hl in &handlers {
                        if !exc_succs[pl_usize].contains(&hl) {
                            exc_succs[pl_usize].push(hl);
                            exc_preds[hl].push(pl_usize);
                        }
                    }
                }
            }
        }

        let mut gen_bits = vec![0u64; num_blocks * words];
        let mut kill_bits = vec![0u64; num_blocks * words];

        for (b_local, &b) in local_blocks.iter().enumerate() {
            let Some(bb) = module.block(b) else { continue };
            let b_u32 = b_local as u32;
            let base_w = b_local * words;

            let mut record_use =
                |v: ValueId, pos_u32: u32, gen_s: &mut [u64], kill_s: &mut [u64]| {
                    let Some(&lidx) = val_to_lidx.get(&v) else {
                        return;
                    };
                    let li = lidx as usize;
                    let w = li / 64;
                    let mask = 1u64 << (li % 64);
                    gen_s[w] |= mask;
                    kill_s[w] &= !mask;

                    let sb = &mut single_block_last_use[li];
                    if sb.0 == UNUSED_BLOCK {
                        *sb = (b_u32, pos_u32);
                    } else if sb.0 == b_u32 {
                        // Reverse iteration visits the maximum position first.
                    } else if sb.0 != MULTI_USE_BLOCK {
                        let (prev_b, prev_max) = *sb;
                        *sb = (MULTI_USE_BLOCK, 0);
                        multi_block_last_use.insert((prev_b, lidx), prev_max);
                        multi_block_last_use.insert((b_u32, lidx), pos_u32);
                    } else {
                        multi_block_last_use.entry((b_u32, lidx)).or_insert(pos_u32);
                    }
                };

            let gen_slice = &mut gen_bits[base_w..base_w + words];
            let kill_slice = &mut kill_bits[base_w..base_w + words];

            for (pos, &iid) in bb.insts.iter().enumerate().rev() {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if let Some(res) = inst.result
                    && let Some(&lidx) = val_to_lidx.get(&res)
                {
                    let li = lidx as usize;
                    let w = li / 64;
                    let mask = 1u64 << (li % 64);
                    gen_slice[w] &= !mask;
                    kill_slice[w] |= mask;
                }
                let pos_u32 = pos as u32;
                inst.op.for_each_operand(|u| {
                    record_use(u, pos_u32, gen_slice, kill_slice);
                });
                if matches!(inst.op, Op::Call { .. })
                    && let Some(base_v) = call_base_value(module, inst)
                {
                    record_use(base_v, pos_u32, gen_slice, kill_slice);
                }
                if matches!(inst.op, Op::ResumeGenerator { .. })
                    && let Some(aws) = await_resume.get(&iid)
                {
                    for &aw in aws {
                        record_use(aw, pos_u32, gen_slice, kill_slice);
                    }
                }
                if matches!(inst.op, Op::Return { .. })
                    && let Some(ct) = ctor_this
                {
                    record_use(ct, pos_u32, gen_slice, kill_slice);
                }
            }
        }

        let mut live_in = gen_bits.clone();
        let mut queue: VecDeque<usize> = (0..num_blocks).rev().collect();
        let mut in_queue = vec![true; num_blocks];

        while let Some(b_local) = queue.pop_front() {
            in_queue[b_local] = false;
            let base_w = b_local * words;
            let mut changed = false;
            for w in 0..words {
                let mut norm_out = 0u64;
                for &s in &norm_succs[b_local] {
                    norm_out |= live_in[s * words + w];
                }
                let mut exc_out = 0u64;
                for &h in &exc_succs[b_local] {
                    exc_out |= live_in[h * words + w] & !entry_exc_kill[h * words + w];
                }
                let new_in = (norm_out & !kill_bits[base_w + w]) | gen_bits[base_w + w] | exc_out;
                if new_in != live_in[base_w + w] {
                    live_in[base_w + w] = new_in;
                    changed = true;
                }
            }
            if changed {
                for &p in norm_preds[b_local].iter().chain(exc_preds[b_local].iter()) {
                    if !in_queue[p] {
                        in_queue[p] = true;
                        queue.push_back(p);
                    }
                }
            }
        }

        let mut aug_live_out_words = Vec::with_capacity(num_blocks * words);
        for b_local in 0..num_blocks {
            for w in 0..words {
                let mut aug_out = 0u64;
                for &s in &norm_succs[b_local] {
                    aug_out |= live_in[s * words + w];
                }
                for &h in &exc_succs[b_local] {
                    aug_out |= live_in[h * words + w] & !entry_exc_kill[h * words + w];
                }
                aug_live_out_words.push(aug_out);
            }
        }

        Self {
            words_per_block: words,
            aug_live_out_words,
            val_to_lidx,
            single_block_last_use,
            multi_block_last_use,
        }
    }

    fn is_live_at(&self, loc: InstLivenessLoc, v: ValueId) -> bool {
        if self.words_per_block == 0 {
            return false;
        }
        let Some(&lidx) = self.val_to_lidx.get(&v) else {
            return false;
        };
        let word_idx = (loc.block_local as usize) * self.words_per_block + (lidx as usize / 64);
        if self
            .aug_live_out_words
            .get(word_idx)
            .is_some_and(|&w| ((w >> (lidx % 64)) & 1) != 0)
        {
            return true;
        }
        let Some(&(ublk, max_pos)) = self.single_block_last_use.get(lidx as usize) else {
            return true;
        };
        if ublk == loc.block_local {
            max_pos >= loc.pos
        } else if ublk == MULTI_USE_BLOCK {
            self.multi_block_last_use
                .get(&(loc.block_local, lidx))
                .is_some_and(|&mp| mp >= loc.pos)
        } else {
            false
        }
    }
}

/// Compact lazy per-function backward SSA liveness index over [`Module`].
struct LocalLiveness {
    inst_loc: Vec<InstLivenessLoc>,
    funcs: RefCell<Vec<Option<FuncLiveness>>>,
}

impl LocalLiveness {
    fn build(module: &Module) -> Self {
        let mut inst_loc = vec![
            InstLivenessLoc {
                func: UNSEEN_FUNC,
                block_local: 0,
                pos: 0,
            };
            module.insts.len()
        ];
        let mut block_seen = vec![false; module.blocks.len()];
        let mut local_blocks: Vec<BlockId> = Vec::new();

        for (fi, f) in module.functions.iter().enumerate() {
            if f.blocks.is_empty() {
                continue;
            }
            let fid_u32 = fi as u32;
            local_blocks.clear();
            for &b in &f.blocks {
                if let Some(seen) = block_seen.get_mut(b.index())
                    && !*seen
                {
                    *seen = true;
                    local_blocks.push(b);
                }
            }
            for (b_local, &b) in local_blocks.iter().enumerate() {
                let Some(bb) = module.block(b) else { continue };
                for (pos, &iid) in bb.insts.iter().enumerate() {
                    if let Some(loc_slot) = inst_loc.get_mut(iid.index())
                        && loc_slot.func == UNSEEN_FUNC
                    {
                        *loc_slot = InstLivenessLoc {
                            func: fid_u32,
                            block_local: b_local as u32,
                            pos: pos as u32,
                        };
                    }
                }
            }
            for &b in &local_blocks {
                block_seen[b.index()] = false;
            }
        }

        let funcs = RefCell::new((0..module.functions.len()).map(|_| None).collect());
        Self { inst_loc, funcs }
    }

    fn is_live_at(
        &self,
        module: &Module,
        await_resume: &HashMap<InstId, Vec<ValueId>>,
        at_inst: InstId,
        v: ValueId,
    ) -> bool {
        let Some(&loc) = self.inst_loc.get(at_inst.index()) else {
            return true;
        };
        if loc.func == UNSEEN_FUNC || v.index() >= module.values.len() {
            return true;
        }
        let fidx = loc.func as usize;
        let has_built = self.funcs.borrow().get(fidx).is_some_and(Option::is_some);
        if !has_built {
            let built = FuncLiveness::build(module, FuncId::new(loc.func), await_resume);
            if let Some(slot) = self.funcs.borrow_mut().get_mut(fidx) {
                *slot = Some(built);
            }
        }
        let funcs_borrow = self.funcs.borrow();
        let Some(Some(fl)) = funcs_borrow.get(fidx) else {
            return true;
        };
        fl.is_live_at(loc, v)
    }
}

struct ValueAliasLoads {
    func: u32,
    load_ids: Box<[u32]>,
}

struct AliasLoadSite {
    block_local: u32,
    pos: u32,
    object: ValueId,
}

/// Per-function reachability index over property loads whose `object` has
/// non-empty `site_info_at` allocation sites (built lazily at most once per
/// function when a dead local taint fact is tested for pruning).
struct FuncAliasLoads {
    loads: Vec<AliasLoadSite>,
    words_per_block: usize,
    reach_out_words: Vec<u64>,
    site_to_loads: HashMap<InstId, Vec<u32>>,
}

impl FuncAliasLoads {
    fn empty() -> Self {
        Self {
            loads: Vec::new(),
            words_per_block: 0,
            reach_out_words: Vec::new(),
            site_to_loads: HashMap::new(),
        }
    }

    fn build(module: &Module, fid: FuncId, oracle: &Oracle) -> Self {
        let Some(f) = module.func(fid) else {
            return Self::empty();
        };
        if f.blocks.is_empty() {
            return Self::empty();
        }
        let mut local_blocks: Vec<BlockId> = Vec::with_capacity(f.blocks.len());
        let mut block_to_local: HashMap<BlockId, usize> = HashMap::with_capacity(f.blocks.len());
        for &b in &f.blocks {
            if let std::collections::hash_map::Entry::Vacant(e) = block_to_local.entry(b) {
                e.insert(local_blocks.len());
                local_blocks.push(b);
            }
        }

        let mut loads = Vec::new();
        let mut site_to_loads: HashMap<InstId, Vec<u32>> = HashMap::new();
        for (b_local, &b) in local_blocks.iter().enumerate() {
            let Some(bb) = module.block(b) else { continue };
            for (pos, &iid) in bb.insts.iter().enumerate() {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                let (Op::LoadProp { object, .. }
                | Op::LoadPropIdx { object, .. }
                | Op::LoadPropDyn { object, .. }) = &inst.op
                else {
                    continue;
                };
                let obj_sites = oracle.site_info_at(*object, iid).sites;
                if obj_sites.is_empty() {
                    continue;
                }
                let load_idx = loads.len() as u32;
                loads.push(AliasLoadSite {
                    block_local: b_local as u32,
                    pos: pos as u32,
                    object: *object,
                });
                for site in obj_sites.iter() {
                    site_to_loads.entry(site).or_default().push(load_idx);
                }
            }
        }

        if loads.is_empty() {
            return Self::empty();
        }

        let num_blocks = local_blocks.len();
        let words = loads.len().div_ceil(64);
        let mut succs: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];

        for (b_local, &b) in local_blocks.iter().enumerate() {
            for s in abcd_analysis::control::block_succs(module, b) {
                if let Some(&sl) = block_to_local.get(&s)
                    && !succs[b_local].contains(&sl)
                {
                    succs[b_local].push(sl);
                    preds[sl].push(b_local);
                }
            }
        }
        for region in &f.try_regions {
            let mut handlers = Vec::new();
            for catch in &region.catches {
                if let Some(&hl) = block_to_local.get(&catch.handler)
                    && !handlers.contains(&hl)
                {
                    handlers.push(hl);
                }
            }
            for &prot_b in &region.protected {
                if let Some(&pl) = block_to_local.get(&prot_b) {
                    for &hl in &handlers {
                        if !succs[pl].contains(&hl) {
                            succs[pl].push(hl);
                            preds[hl].push(pl);
                        }
                    }
                }
            }
        }

        let mut reach_in = vec![0u64; num_blocks * words];
        for (k, ld) in loads.iter().enumerate() {
            reach_in[(ld.block_local as usize) * words + k / 64] |= 1u64 << (k % 64);
        }
        let mut queue: VecDeque<usize> = (0..num_blocks).rev().collect();
        let mut in_queue = vec![true; num_blocks];
        while let Some(b_local) = queue.pop_front() {
            in_queue[b_local] = false;
            let base_w = b_local * words;
            let mut changed = false;
            for w in 0..words {
                let mut out_bits = reach_in[base_w + w];
                for &s in &succs[b_local] {
                    out_bits |= reach_in[s * words + w];
                }
                if out_bits != reach_in[base_w + w] {
                    reach_in[base_w + w] = out_bits;
                    changed = true;
                }
            }
            if changed {
                for &p in &preds[b_local] {
                    if !in_queue[p] {
                        in_queue[p] = true;
                        queue.push_back(p);
                    }
                }
            }
        }

        let mut reach_out_words = Vec::with_capacity(num_blocks * words);
        for succ_list in &succs {
            for w in 0..words {
                let mut out_bits = 0u64;
                for &s in succ_list {
                    out_bits |= reach_in[s * words + w];
                }
                reach_out_words.push(out_bits);
            }
        }

        Self {
            loads,
            words_per_block: words,
            reach_out_words,
            site_to_loads,
        }
    }

    fn matching_loads_for(&self, v: ValueId, v_sites: &AllocSiteSet) -> Vec<u32> {
        if self.loads.is_empty() {
            return Vec::new();
        }
        let mut out = Vec::new();
        for site in v_sites.iter() {
            let Some(cands) = self.site_to_loads.get(&site) else {
                continue;
            };
            for &k in cands {
                if let Some(ld) = self.loads.get(k as usize)
                    && ld.object != v
                    && !out.contains(&k)
                {
                    out.push(k);
                }
            }
        }
        out
    }

    fn any_reachable_at(&self, loc: InstLivenessLoc, load_ids: &[u32]) -> bool {
        if self.words_per_block == 0 {
            return false;
        }
        let b_base = (loc.block_local as usize) * self.words_per_block;
        for &k in load_ids {
            let ku = k as usize;
            let Some(ld) = self.loads.get(ku) else {
                continue;
            };
            if ld.block_local == loc.block_local && ld.pos >= loc.pos {
                return true;
            }
            if self
                .reach_out_words
                .get(b_base + ku / 64)
                .is_some_and(|&w| ((w >> (ku % 64)) & 1) != 0)
            {
                return true;
            }
        }
        false
    }
}

pub(crate) fn peel_ns_index(module: &Module, v: ValueId) -> Option<u32> {
    let root = abcd_analysis::dataflow::heap::peel_movs(module, v);
    let ValueDef::Inst(iid) = module.value(root)?.def else {
        return None;
    };
    match &module.inst(iid)?.op {
        Op::GetModuleNamespace { index } => Some(*index),
        _ => None,
    }
}

fn build_jsbridge_prop_index(module: &Module) -> JsBridgePropIndex {
    let mut index: JsBridgePropIndex = HashMap::new();
    for inst in &module.insts {
        match &inst.op {
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
                index.entry(*object).or_default().push((*name, *value));
            }
            Op::DefineMethod {
                object, name, func, ..
            } => {
                index.entry(*object).or_default().push((*name, *func));
            }
            _ => {}
        }
    }
    index
}

/// Discover methods exposed on `proxy_obj` via
/// `WebviewController.registerJavaScriptProxy(proxy_obj, name, methodList)`
/// and seed their formal parameters as untrusted JSBridge inputs.
fn collect_jsbridge_seeds(
    module: &Module,
    oracle: &Oracle,
    prop_index: &JsBridgePropIndex,
    proxy_obj: ValueId,
    method_list: Option<ValueId>,
    at: InstId,
    param_seeds: &mut Vec<(FuncId, Vec<ValueId>)>,
) {
    let allowed_names: Option<HashSet<String>> = method_list.and_then(|ml| {
        let ValueDef::Inst(iid) = module.value(ml)?.def else {
            return None;
        };
        let Op::AllocArray {
            shape: Some(arr_cid),
        } = &module.inst(iid)?.op
        else {
            return None;
        };
        let Const::ArrayLiteral(items) = module.consts.get(*arr_cid)? else {
            return None;
        };
        let mut set = HashSet::new();
        for &it_cid in items {
            if let Some(Const::String(s)) = module.consts.get(it_cid)
                && let Some(txt) = module.sym.resolve(*s)
            {
                set.insert(txt.to_owned());
            }
        }
        (!set.is_empty()).then_some(set)
    });

    let name_allowed = |mname: &str| -> bool {
        !mname.is_empty()
            && mname != "constructor"
            && !mname.starts_with("#~@")
            && allowed_names.as_ref().is_none_or(|s| s.contains(mname))
    };

    let mut candidate_funcs: Vec<FuncId> = Vec::new();
    let mut sites: Vec<InstId> = oracle.may_sites_at(proxy_obj, at).iter().collect();
    if let Some(ValueDef::Inst(def_iid)) = module.value(proxy_obj).map(|v| v.def)
        && !sites.contains(&def_iid)
    {
        sites.push(def_iid);
    }

    for site in sites {
        let Some(site_inst) = module.inst(site) else {
            continue;
        };
        match &site_inst.op {
            Op::AllocObject { shape } => {
                if let Some(Const::ObjectLiteral { keys, values }) = module.consts.get(*shape) {
                    for (&k_cid, &v_cid) in keys.iter().zip(values.iter()) {
                        if let (Some(Const::String(ks)), Some(Const::MethodRef { func: mfid, .. })) =
                            (module.consts.get(k_cid), module.consts.get(v_cid))
                            && let Some(mname) = module.sym.resolve(*ks)
                            && name_allowed(mname)
                        {
                            candidate_funcs.push(*mfid);
                        }
                    }
                }
                if let Some(obj_val) = site_inst.result
                    && let Some(props) = prop_index.get(&obj_val)
                {
                    for &(name, fn_val) in props {
                        if let Some(mname) = module.sym.resolve(name)
                            && name_allowed(mname)
                        {
                            for f in gap::resolve_callback_funcs(module, oracle, fn_val, at) {
                                candidate_funcs.push(f);
                            }
                        }
                    }
                }
            }
            Op::Call {
                callee,
                kind: CallKind::New | CallKind::NewSpread,
                ..
            } => {
                if let Some(ValueDef::Inst(cls_iid)) = module.value(*callee).map(|v| v.def)
                    && let Some(Op::DefineClass(data) | Op::DefineSendableClass(data)) =
                        module.inst(cls_iid).map(|i| &i.op)
                    && let Some(Const::ArrayLiteral(items)) = module.consts.get(data.members)
                {
                    let mut pending: Option<&str> = None;
                    for &it_cid in items {
                        match module.consts.get(it_cid) {
                            Some(Const::String(s)) => pending = module.sym.resolve(*s),
                            Some(Const::MethodRef { func: mfid, .. }) => {
                                if let Some(mname) = pending.take()
                                    && name_allowed(mname)
                                {
                                    candidate_funcs.push(*mfid);
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            _ => {}
        }
    }

    candidate_funcs.sort();
    candidate_funcs.dedup();
    for mfid in candidate_funcs {
        let Some(fd) = module.func(mfid) else {
            continue;
        };
        let formals: Vec<ValueId> = match param_binding(module, mfid) {
            ParamBinding::Precise { formal_base, .. } => {
                fd.params.iter().skip(formal_base).copied().collect()
            }
            ParamBinding::OverApproxAll => fd.params.clone(),
        };
        if !formals.is_empty() {
            param_seeds.push((mfid, formals));
        }
    }
}
