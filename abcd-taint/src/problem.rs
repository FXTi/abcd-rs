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
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::dataflow::heap::{AllocSiteSet, UpdateKind};
use abcd_analysis::dataflow::heap::{FieldChain, FieldKey, update_kind};
use abcd_analysis::dataflow::ifds::{CallGraphOracle, IfdsProblem};
use abcd_analysis::module_link::ModuleLinkTable;
use abcd_ir::op::{PropKey, SuperKey};
use abcd_ir::{
    BlockId, CallKind, ClassId, Const, FuncId, InstId, Module, Op, Sym, ValueDef, ValueId,
};

use crate::driver::{SourceSpec, TaintConfig};
use crate::fact::{Fact, TaintBase, TaintFact};
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

struct PropTouchIndex {
    by_prop: HashMap<Sym, Vec<FuncId>>,
    dyn_funcs: Vec<FuncId>,
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
    /// Dense `BlockId::index() -> Option<ValueId>` catch-handler exception parameter
    /// (first matching catch in function/region/catch order, matching `handler_exception_at`).
    handler_block_exc: Vec<Option<ValueId>>,
    /// Scoped `(FuncId, handler BlockId) -> exception ValueId` for intraprocedural throws.
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
    /// `(func, param indices)` seeds, resolved from the config's
    /// function-name source specs and JSBridge proxy registrations at construction.
    param_seeds: Vec<(FuncId, Vec<ValueId>)>,
    /// Module-interned names whose `TryGetGlobal` results are sources.
    global_sources: HashSet<Sym>,
    /// Call sites whose return values are tainted via `SourceSpec::CallReturn`.
    call_return_sources: HashSet<InstId>,
    /// Trailing `(err, data)` / `(data)` callback edges at `CallReturn` source sites.
    source_cb_edges: BTreeMap<InstId, Vec<FuncId>>,
    /// `(ClassId, ext_slot)` external imports tainted via `SourceSpec::ModuleImport`:
    /// `None` = whole-value taint, `Some(syms)` = field-sensitive namespace taint.
    module_import_sources: HashMap<(ClassId, u32), Option<Vec<Sym>>>,
    /// Async-machine `ResumeGenerator` instruction -> awaited `ValueId` from
    /// preceding `AwaitUncaught` in the same block.
    await_resume: HashMap<InstId, ValueId>,
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
    /// Fresh-result memo (rung 2; [`TaintProblem::fresh_result_site`]).
    fresh_memo: RefCell<HashMap<ValueId, Option<InstId>>>,
    /// Callback-gap counters: call
    /// sites whose callback summary applied AND the callback value
    /// resolved to at least one user body.
    gap_resolved: usize,
    /// Callback-summary sites whose callback value did NOT resolve —
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
    /// One-time lazy index `site_iid -> Vec<FuncId>` of functions holding or
    /// lexically reading `site_iid` on large (`> 512`-function) Rung-2 bundles.
    heap_site_users: RefCell<Option<HashMap<InstId, Vec<FuncId>>>>,
    /// Lazily memoized `site_iid -> Vec<bool>` backward caller cone of `heap_site_users`.
    heap_site_cone: RefCell<HashMap<InstId, Vec<bool>>>,
    /// Lazily memoized `Vec<bool>` backward caller cone of `Op::GetLexVar` readers.
    lex_var_readers: RefCell<Option<Vec<bool>>>,
    /// One-time lazy index of functions touching named/dynamic properties (`> 512`-function bundles).
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
        let (block_to_func, handler_block_exc, func_handler_exc) = build_exception_indexes(module);
        let module_import_sources = resolve_module_import_sources(module, &links, config);

        let call_source_names: HashSet<&str> = config
            .sources
            .iter()
            .filter_map(|s| match s {
                SourceSpec::CallReturn { name } => Some(name.as_str()),
                _ => None,
            })
            .collect();

        let mut call_return_sources = HashSet::new();
        let mut source_cb_edges: BTreeMap<InstId, Vec<FuncId>> = BTreeMap::new();
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
                    collect_jsbridge_seeds(
                        module,
                        &oracle,
                        proxy_obj,
                        args.get(2).copied(),
                        call,
                        &mut param_seeds,
                    );
                }
            }
        }

        let await_resume = build_await_resume_map(module);
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
            handler_block_exc,
            func_handler_exc,
            liveness,
            value_keep_flag,
            func_alias_loads,
            value_alias_loads,
            oracle: RefCell::new(oracle),
            registry,
            config,
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
            heap_site_users: RefCell::new(None),
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

    fn func_derefs_site_rung0(&self, fid: FuncId, site: InstId) -> bool {
        let Some(f) = self.module.func(fid) else {
            return false;
        };
        if matches!(
            self.module.inst(site).map(|i| &i.op),
            Some(Op::NewLexEnv { .. } | Op::NewLexEnvWithName { .. })
        ) {
            for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    if matches!(
                        self.module.inst(iid).map(|i| &i.op),
                        Some(Op::GetLexVar { .. } | Op::PutLexVar { .. })
                    ) {
                        return true;
                    }
                }
            }
            return false;
        }
        let oracle = self.oracle.borrow();
        let has_site = |v: ValueId| oracle.resolve(v).sites.iter().any(|s| s == site);
        for &b in &f.blocks {
            let Some(bb) = self.module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                let Some(inst) = self.module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::LoadProp { object, .. }
                    | Op::LoadPropIdx { object, .. }
                    | Op::LoadPropDyn { object, .. }
                    | Op::StoreProp { object, .. }
                    | Op::StoreOwnPropName { object, .. }
                    | Op::StorePropIdx { object, .. }
                    | Op::StoreOwnPropIdx { object, .. }
                    | Op::StorePropDyn { object, .. }
                    | Op::StoreOwnPropDyn { object, .. }
                    | Op::GetIterator { obj: object } => {
                        if has_site(*object) {
                            return true;
                        }
                    }
                    Op::Call { args, .. }
                        if !self.call_has_body_callee(iid)
                            && (call_base_value(self.module, inst).is_some_and(has_site)
                                || args.iter().copied().any(has_site)) =>
                    {
                        return true;
                    }
                    _ => {}
                }
            }
        }
        false
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
                            | Op::StoreOwnPropName { name, .. } => {
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
                            | Op::GetIterator { .. }
                            | Op::CopyDataProps { .. } => {
                                has_dyn = true;
                            }
                            Op::Call { .. } => {
                                if let Some(leaf) = call_method_leaf(self.module, inst)
                                    && matches!(
                                        self.module.sym.resolve(leaf),
                                        Some(
                                            "assign" | "stringify" | "keys" | "values" | "entries"
                                        )
                                    )
                                {
                                    has_dyn = true;
                                }
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

    fn can_callee_use_heap_site(&self, site: InstId, callee: FuncId) -> bool {
        if let Some(reach) = self.heap_site_cone.borrow().get(&site) {
            return reach.get(callee.index()).copied().unwrap_or(false);
        }
        if self.heap_site_users.borrow().is_none() {
            let mut site_to_funcs: HashMap<InstId, Vec<FuncId>> = HashMap::new();
            {
                let oracle_ref = self.oracle.borrow();
                if let Oracle::Rung2(o) = &*oracle_ref {
                    let mut push_fn = |s: InstId, fid: FuncId| {
                        let list = site_to_funcs.entry(s).or_default();
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
                                    Op::LoadProp { object, .. }
                                    | Op::LoadPropIdx { object, .. }
                                    | Op::LoadPropDyn { object, .. }
                                    | Op::StoreProp { object, .. }
                                    | Op::StoreOwnPropName { object, .. }
                                    | Op::StorePropIdx { object, .. }
                                    | Op::StoreOwnPropIdx { object, .. }
                                    | Op::StorePropDyn { object, .. }
                                    | Op::StoreOwnPropDyn { object, .. }
                                    | Op::GetIterator { obj: object } => {
                                        for s in o.query(*object, iid).sites.iter() {
                                            push_fn(s, fid);
                                        }
                                    }
                                    Op::Call { args, .. } if !self.call_has_body_callee(iid) => {
                                        if let Some(bv) = call_base_value(self.module, inst) {
                                            for s in o.query(bv, iid).sites.iter() {
                                                push_fn(s, fid);
                                            }
                                        }
                                        for &a in args {
                                            for s in o.query(a, iid).sites.iter() {
                                                push_fn(s, fid);
                                            }
                                        }
                                    }
                                    Op::GetLexVar { level, .. } | Op::PutLexVar { level, .. } => {
                                        for s in o.lex_env_at(iid, *level).sites.iter() {
                                            push_fn(s, fid);
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }
                }
            }
            *self.heap_site_users.borrow_mut() = Some(site_to_funcs);
        }

        let n_funcs = self.module.functions.len();
        let mut reach = vec![false; n_funcs];
        let mut fn_queue = VecDeque::new();
        let is_rung2 = matches!(*self.oracle.borrow(), Oracle::Rung2(_));
        if let Some(owner_fid) = self.links.inst_func(self.module, site)
            && Some(owner_fid) != self.harness.fid
            && (!is_rung2 || self.func_derefs_site_rung0(owner_fid, site))
            && let Some(slot) = reach.get_mut(owner_fid.index())
            && !*slot
        {
            *slot = true;
            fn_queue.push_back(owner_fid);
        }
        {
            let users_borrow = self.heap_site_users.borrow();
            if let Some(funcs) = users_borrow.as_ref().and_then(|m| m.get(&site)) {
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
    /// pruning for monotone `ModuleVar`, `Global`, `LexVar`, and large-bundle
    /// `Heap` state, plus synthetic `__abcd_ohos_harness__` component isolation).
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
            TaintBase::LexVar(_, _)
                if self.module.functions.len() > 512 && !self.can_callee_read_lex_var(callee) =>
            {
                return false;
            }
            TaintBase::Heap(sites) if !sites.is_empty() && self.module.functions.len() > 512 => {
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
        if self.module.functions.len() > 512 {
            self.config.max_field_chain.min(1)
        } else {
            self.config.max_field_chain
        }
    }

    /// Classify a call site on the fallback ladder (memoized; counters
    /// fire exactly once per site).
    ///
    /// The lookup precedence (`design/analysis.md`):
    ///
    /// 1. **direct name match** — a summary registered under one of
    ///    the callee's def-chain name candidates wins (exclusive
    ///    summaries also win over resolved bodies — never merged);
    /// 2. **resolved user body** — a callee the call graph resolved to
    ///    a function with a body is stepped into (USER CODE beats the
    ///    builtin assumption of the prototype path — the receiver
    ///    type is a may-answer, the body is evidence);
    /// 3. **prototype-resolution path** — the receiver's alloc-kind /
    ///    constant / global-provenance family qualifies the method
    ///    leaf (`a.pop` + Array ⇒ `Array.prototype.pop`);
    ///    prototype-applied summaries are ALWAYS applied
    ///    non-exclusively (additive: flows are added, incoming taint
    ///    is retained — a may-typed receiver must never kill);
    /// 4. **native keep** (named) / **unknown keep** (no name).
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
        // Resolved callees contribute their FunctionData names (directly
        // resolved internal functions named like a builtin match too).
        let callees = self.callgraph.callees_of_call_at(call);
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
                let has_body = callees.iter().any(|f| {
                    self.module
                        .func(*f)
                        .is_some_and(|fd| !fd.is_external && !fd.blocks.is_empty())
                });
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

    /// Whether `return_site` is the entry instruction of a catch handler
    /// of the calling function (then the callee's RETURN value does not
    /// flow there — only thrown values do). Returns the handler's
    /// exception binding when it is one (`O(1)` pre-indexed lookup).
    fn handler_exception_at(&self, return_site: InstId) -> Option<ValueId> {
        let rs_inst = self.module.inst(return_site)?;
        self.handler_block_exc
            .get(rs_inst.block.index())
            .copied()
            .flatten()
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
    ///
    /// - If `v` has at least one direct or implicit SSA use at or after `target_inst`
    ///   in `target_inst`'s function, it stays live (`true`).
    /// - Entry `ValueDef::Param` and `ValueDef::Const` values (`O(1)` per function)
    ///   stay live so parameter-seeded functions continue classifying reachable calls.
    /// - Dead instruction-defined temporaries (`ValueDef::Inst`) and handler
    ///   `ExceptionParam`s can only ever match downstream via `load_rule`'s
    ///   `local_alias_evidence(v, object, at)` (`object != v`). Unless `v`'s
    ///   allocation sites positively intersect `site_info_at(object).sites` at
    ///   some `LoadProp*` instruction reachable at or after `target_inst`, `v`
    ///   is soundly pruned (`false`).
    fn should_retain_local_at(&self, v: ValueId, target_inst: InstId) -> bool {
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

    /// Whether a load through `object` may pick up a heap fact keyed by
    /// `sites` (positive intersection, or either side unknown — the
    /// conservative may-alias answer for unknown bases; the refined
    /// rungs sharpen `object`'s sites through their engines).
    ///
    /// Rung 2 addition (probe e13 mechanism): when `object`'s sites
    /// are unknown BUT it is the result of a summary call whose result
    /// no static flow reaches (a FRESH container — [`TaintProblem`]'s
    /// `fresh_result_site`), the load base keys by the call site: a
    /// VM-allocated `map` result no longer may-aliases the source
    /// array's heap fact through the wildcard.
    fn heap_may_reach(&self, sites: &AllocSiteSet, object: ValueId, at: InstId) -> bool {
        if self.module.functions.len() > 512 {
            if sites.is_empty() {
                return false;
            }
            let known = self.oracle.borrow().known_sites_at(object, at);
            if !known.is_empty() {
                return sites.intersects(&known);
            }
            return match self.fresh_result_site(object) {
                Some(site) => sites.iter().any(|s| s == site),
                None => false,
            };
        }
        if sites.is_empty() {
            return true;
        }
        let obj = self.oracle.borrow().site_info_at(object, at);
        if !obj.sites.is_empty() {
            return sites.intersects(&obj.sites);
        }
        match self.fresh_result_site(object) {
            Some(site) => sites.iter().any(|s| s == site),
            None => true, // the unknown-base wildcard
        }
    }

    /// Fresh summary-result keying (probe e13): the call instruction of
    /// a summary application whose
    /// result NO static flow reaches (`Param/Base/Field → Return*`
    /// would mean the result derives from — may alias — an input, and
    /// gap return channels key their facts precisely on the local
    /// result, so they do not count as aliasing either). Rung-2-gated:
    /// the wildcard discipline of rungs 0/1 is unchanged. Memoized;
    /// classification is peeked (counter-free).
    fn fresh_result_site(&self, value: ValueId) -> Option<InstId> {
        if self.config.alias_rung < 2 {
            return None;
        }
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

    /// Access-path leading-field cut: what
    /// remains of `fields` after reading `key`. An empty chain means the
    /// base itself was tainted — any property read is tainted one step.
    fn cut_first(&self, fields: &FieldChain, key: FieldKey) -> Option<FieldChain> {
        if fields.is_empty() {
            if self.module.functions.len() > 512 {
                return Some(FieldChain::new());
            }
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
    /// false for the killed fact).
    ///
    /// Rung 1 changes BOTH decisions through the engine's memoized query
    /// ([`Oracle::site_info_at`] / [`Oracle::aliases_of_store`]): the
    /// strong-kill proof may come from an interprocedural def chain (the
    /// a5 case — a sanitizing store through a call-result alias), and the
    /// stored taint's heap key may be refined from an unknown base to
    /// precise sites (the a4 case). Any imprecise answer falls back to
    /// the rung-0 local walk — never silently wrong.
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
        // Strong kill: the old value at exactly this location is dead.
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
                let same_key = match (first, key) {
                    (FieldKey::Named(a), FieldKey::Named(b)) => a == b,
                    _ => true,
                };
                if same_key {
                    survive = false;
                }
            }
        }
        // The stored value's taint is re-keyed into the heap: store-base
        // alias resolution (`Oracle::aliases_of_store`) — rung 1/2 injects
        // the REFINED key and the baseline is skipped; otherwise the
        // rung-0 keying stands (empty-site unknown-base wildcard
        // included — sound by construction).
        if fact.base == TaintBase::Local(value) {
            let mut chain = FieldChain::new().pushed(key, self.cap());
            for &k in fact.fields.elements() {
                chain = chain.pushed(k, self.cap());
            }
            if let Some(this_param) = self.new_ctor_this_param(object, at) {
                // Keep constructor `this.field = v` local to `this_param`
                // until `return_flow` binds it to the specific `CallKind::New`
                // call site via IFDS's context-sensitive summary replay.
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
                    let base = if sites.is_empty() && self.module.functions.len() > 512 {
                        let known = self.oracle.borrow().known_sites_at(object, at);
                        if known.is_empty() {
                            TaintBase::Local(object)
                        } else {
                            TaintBase::Heap(known)
                        }
                    } else {
                        TaintBase::Heap(sites)
                    };
                    out.push(Fact::of(TaintFact {
                        base,
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
                    kind: CallKind::New,
                    ..
                })
            )
        });
        all_new.then_some(this_param)
    }

    fn ctor_this_of(&self, fid: FuncId) -> Option<ValueId> {
        ctor_this_of_module(self.module, fid)
    }

    /// The generic operand→result rule (Mov/binop/unop/compare/
    /// coercion/iterator families — everything with a result that is not
    /// in an explicitly handled family).
    fn generic_propagate(&self, inst: &abcd_ir::Inst, fact: &TaintFact, out: &mut Vec<Fact>) {
        let Some(result) = inst.result else { return };
        let Some(v) = fact.local_base() else { return };
        if !op_uses_value(&inst.op, v) {
            return;
        }
        match &inst.op {
            Op::Compare { .. } | Op::UnaryOp { .. } => {
                if fact.fields.is_empty() {
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
        let (value, path) = match endpoint {
            Endpoint::Param(i) => (*args.get(*i as usize)?, None),
            Endpoint::Base => (base?, None),
            Endpoint::Return | Endpoint::ReturnField(_) => return None,
            Endpoint::Field(path) => (base?, Some(path)),
        };
        if local != value {
            return None;
        }
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
        let (value, path) = match endpoint {
            Endpoint::Param(i) => (*args.get(*i as usize)?, None),
            Endpoint::Base => (base?, None),
            Endpoint::Field(path) => (base?, Some(path)),
            Endpoint::Return | Endpoint::ReturnField(_) => return None,
        };
        let pts = if may {
            self.oracle.borrow().may_sites_at(value, at)
        } else {
            self.oracle.borrow().site_info_at(value, at).sites
        };
        if pts.is_empty() || !pts.intersects(sites) {
            return None;
        }
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
    // Each parameter is a distinct facet of the call-site context;
    // grouping them would obscure the flow logic.
    #[allow(clippy::too_many_arguments)]
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
    #[allow(clippy::too_many_arguments)] // gap-edge context facets; see substitute()
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
            if let Op::TryGetGlobal { name, .. } = &curr_inst.op
                && self.global_sources.contains(name)
                && let Some(result) = curr_inst.result
            {
                out.push(Fact::of(TaintFact::local(result)));
                if self.config.ohos_lifecycle
                    && module.sym.resolve(*name)
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
            return;
        };

        // ── Phi-entry edges: an incoming value listed for THIS edge
        // additionally maps to the phi result (phi merges union sites via
        // the heap oracle; the SSA value mapping is exact per edge).
        // Non-matching locals PASS THROUGH — a phi edge is a block
        // boundary, not a kill: the value's taint is path-insensitively
        // true wherever the value is in scope.
        if let Op::Phi { entries } = &succ_inst.op {
            if let Some(v) = fact.local_base() {
                for (edge, val) in entries {
                    if *val == v
                        && edge.from == curr_inst.block
                        && let Some(result) = succ_inst.result
                    {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                }
            }
            self.push_passthrough_at(source, succ, out);
            return;
        }

        // ── Exception dispatch: `throw v` taints the catch binding (T5).
        if let Op::Throw { value } = &curr_inst.op {
            self.push_passthrough_at(source, succ, out);
            if fact.base == TaintBase::Local(*value)
                && let Some(exc) = self.handler_exception_for(curr_inst.block, succ_inst.block)
            {
                out.push(Fact::of(fact.rebased(TaintBase::Local(exc))));
            }
            return;
        }

        match &curr_inst.op {
            // ── Global bindings ──────────────────────────────────────
            Op::TryGetGlobal { name, .. } => {
                // Pick up a previously stored global taint.
                if fact.base == TaintBase::Global(*name)
                    && let Some(result) = curr_inst.result
                {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
                self.generic_propagate(curr_inst, fact, out); // the `default` operand
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
            Op::GetLexVar { level, slot } => {
                if fact.base == TaintBase::LexVar(*level, *slot)
                    && let Some(result) = curr_inst.result
                {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
                // The rung-2 environment-identity channel (b2): a
                // PRECISE writer keys the slot by its NewLexEnv site's
                // abstract object (`Heap(env).[AnyIndex]`), so two
                // functions' colliding (level, slot) captures no longer
                // merge. A precise reader matches by env-site
                // intersection; an imprecise reader (env unknown) falls
                // back to matching ANY env-keyed fact — the
                // may-direction rule that keeps the channel sound when
                // the env analysis gives up (the rung-1 unbalanced
                // discipline's analogue).
                if let Some(env) = self.oracle.borrow().lex_env_at(curr, *level)
                    && let TaintBase::Heap(sites) = &fact.base
                {
                    let precise = !env.has_unknown && !env.sites.is_empty();
                    let hits = if precise || self.module.functions.len() > 512 {
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
            Op::PutLexVar { level, slot, value } => {
                if fact.base == TaintBase::Local(*value) {
                    // Rung 2 keys the slot by the environment's
                    // abstract object when the env analysis is precise
                    // (b2 — see the GetLexVar arm); the legacy
                    // function-agnostic `(level, slot)` keying stands
                    // otherwise and on rungs 0/1. Slots within one
                    // environment merge under `AnyIndex` (the b2
                    // collision is ACROSS environments — documented).
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
                // `it = getiterator(obj)`: the iterator yields obj's
                // elements, so obj's taint state transfers to it.
                // LOCAL facts ride the generic rule below with their
                // chain intact (empty = whole-source taint;
                // `[AnyIndex]` = the "elements of" tag the
                // `Iterator.prototype.next` summary consumes). HEAP
                // facts re-key onto the result by positive site
                // intersection (heap reads are otherwise opaque —
                // this is the one builtin op whose element channel is
                // static): `Heap(site(a)).[AnyIndex]` ⇒
                // `Local(it).[AnyIndex]`.
                if let Some(result) = curr_inst.result
                    && let TaintBase::Heap(sites) = &fact.base
                    && self.heap_may_reach(sites, *obj, curr)
                {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
                self.generic_propagate(curr_inst, fact, out);
                self.push_passthrough_at(source, succ, out);
            }
            // ── Loads (access-path cut + namespace export lookup) ────
            Op::LoadProp { object, name } => {
                self.load_rule(fact, *object, FieldKey::Named(*name), curr, out);
                if let Some(result) = curr_inst.result
                    && let Some(cid) = self.links.inst_class(module, curr)
                    && let Some(req_idx) = peel_ns_index(module, *object)
                    && let Some(slots) = self.links.resolve_namespace_member(cid, req_idx, *name)
                    && slots
                        .iter()
                        .any(|sr| fact.base == TaintBase::ModuleVar(sr.class_id, sr.slot))
                {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
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
            } => {
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
            // ── Object-family ops with bespoke taint semantics ───────
            Op::CopyDataProps { dst, src } => {
                // Object spread: src's taint (object + fields) copies to dst.
                if fact.base == TaintBase::Local(*src) {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(*dst))));
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::SetObjectWithProto { proto, obj } => {
                // obj's prototype chain now reads through proto.
                if fact.base == TaintBase::Local(*proto) {
                    out.push(Fact::of(
                        TaintFact::local(*obj).pushed(FieldKey::AnyDynamic, self.cap()),
                    ));
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::StorePrivate { obj, value, .. } | Op::DefinePrivate { obj, value, .. } => {
                // No FieldKey for private names at rung 0: record "some
                // property of obj is tainted".
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
                    let base = if sites.is_empty() && self.module.functions.len() > 512 {
                        TaintBase::Local(*object)
                    } else {
                        TaintBase::Heap(sites)
                    };
                    out.push(Fact::of(
                        TaintFact {
                            base,
                            fields: FieldChain::new(),
                        }
                        .pushed(FieldKey::AnyDynamic, self.cap()),
                    ));
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::DefineFunc { .. } => {
                // Captured taint marks the closure value with an EMPTY
                // chain ("this function closes over tainted data").
                // Lexical captures propagate into the body via
                // `GetLexVar`/`PutLexVar` (and `NewLexEnv` sites at rung 2;
                // `design/analysis.md`), not via the function-object value.
                let is_capture = fact
                    .local_base()
                    .is_some_and(|v| op_uses_value(&curr_inst.op, v));
                if is_capture && let Some(result) = curr_inst.result {
                    out.push(Fact::of(TaintFact::local(result)));
                }
                self.push_passthrough_at(source, succ, out);
            }
            Op::ResumeGenerator { .. } => {
                if let Some(&awaited_val) = self.await_resume.get(&curr)
                    && fact.base == TaintBase::Local(awaited_val)
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
        // Exclusive summaries kill the call edge into the callee body —
        // never merged (`design/analysis.md`). The GAP edge into the user
        // callback is NOT killed (gap.rs §"Interaction with exclusive":
        // exclusive-with-callback still runs the callback).
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
        // The summary call site virtually invokes the callback with
        // (element, index, array) — the summary call's operands are NOT
        // the callback's arguments, so the normal arg→param binding does
        // not run here; only the gap's `enter` rules bind. Function-
        // global state crosses unchanged (same as a normal edge). The
        // oracle's calling-context injection is deliberately skipped:
        // the rung-1 engine reads the BASE call graph, which has no gap
        // edges — a query inside the callback that tries to hop through
        // the gap call finds no recorded caller and falls back to the
        // rung-0 floor (sound; documented in gap.rs).
        if let Some(gap) = &gap {
            if fact.is_state_base() && self.allow_state_into_callee(call, callee, fact) {
                out.push(source.clone());
            }
            let base = call_base_value(module, call_inst);
            self.gap_enter(call, callee, gap, fact, args, base, out);
            return;
        }

        // The oracle learns the calling context (rung 0: no-op; `design/analysis.md`).
        abcd_analysis::dataflow::heap::AliasOracle::inject_calling_context(
            &mut *self.oracle.borrow_mut(),
            call,
            callee,
            fact,
        );

        match &fact.base {
            TaintBase::Local(v) => {
                // N66: bind through the vendored frame-slot model
                // ([func][newTarget][this][formals…], per the callee's
                // callType annotation or the 0xF static default) —
                // args[i] → params[formal_base + i], NOT params[i + 1]
                // (the pre-N66 table was written for a normalized ABI
                // the lift never produced).
                let allow_this_prop = if self.module.functions.len() > 512
                    && *kind != CallKind::New
                    && !args.contains(v)
                    && let Some(&FieldKey::Named(prop)) = fact.fields.elements().first()
                {
                    self.can_callee_touch_prop(prop, callee)
                } else {
                    true
                };
                let binding = param_binding(module, callee);
                if binding == ParamBinding::OverApproxAll {
                    // Conservative: a tainted this/arg taints EVERY
                    // param (never silently drop a flow).
                    let on_operands =
                        (allow_this_prop && this.is_some_and(|t| t == *v)) || args.contains(v);
                    if on_operands {
                        for &p in &fd.params {
                            out.push(Fact::of(fact.rebased(TaintBase::Local(p))));
                        }
                    }
                } else {
                    // `this` → the this slot (T4 binding convention).
                    if allow_this_prop
                        && let ParamBinding::Precise {
                            this_slot: Some(slot),
                            ..
                        } = binding
                        && this.is_some_and(|t| t == *v)
                        && let Some(&p) = fd.params.get(slot)
                    {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(p))));
                    }
                    let formal_base = match binding {
                        ParamBinding::Precise { formal_base, .. } => formal_base,
                        // unreachable: the else branch guarantees Precise
                        // (OverApproxAll was handled and returned above).
                        ParamBinding::OverApproxAll => unreachable!(),
                    };
                    match kind {
                        CallKind::Direct | CallKind::Dynamic | CallKind::New | CallKind::Super => {
                            for (i, &a) in args.iter().enumerate() {
                                if a == *v
                                    && let Some(&p) = fd.params.get(formal_base + i)
                                {
                                    out.push(Fact::of(fact.rebased(TaintBase::Local(p))));
                                }
                            }
                        }
                        CallKind::Apply | CallKind::SuperSpread => {
                            // args[0] is an ARRAY spread over the formals: a
                            // tainted array conservatively taints every formal.
                            if args.first() == Some(v) {
                                for &p in fd.params.iter().skip(formal_base) {
                                    out.push(Fact::of(fact.rebased(TaintBase::Local(p))));
                                }
                            }
                        }
                        CallKind::SuperForwardAllArgs => {
                            // The forwarded arguments are the caller's own
                            // formals — not operands of this call. Rung 0
                            // models nothing here (documented gap).
                        }
                    }
                }
                // The mini-gap channel: a callback value tagged
                // `[AnyIndex, ...]` by a summary (forEach-style) seeds
                // its first formal when user code calls it directly.
                // N66: the first FORMAL is `params[formal_base]` (the
                // implicit frame slots lead), not `params[1]`;
                // OverApproxAll taints every formal (never silently
                // drop).
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
                // A tainted callee value with an EMPTY chain (function-
                // object taint, e.g. a closure over tainted captures) is
                // dropped at the boundary — function-object taint is not
                // data taint (documented rung-0 gap).
            }
            // Heap/global/module/lexical state flows into the callee.
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

        // State bases are function-global: they cross returns unchanged
        // (also for unbalanced returns with `None` endpoints — and
        // across gap edges: the callback's side effects on heap/global
        // state persist at the summary call's continuation).
        if fact.is_state_base() {
            if call_site.is_none_or(|c| {
                !self.is_harness_call(c) || self.allow_state_across_harness(c, callee, fact, false)
            }) {
                out.push(source.clone());
            }
            return;
        }
        let Some(v) = fact.local_base() else { return };
        // Callback-gap return channel (gap.rs): at a gap edge the
        // callback's RETURN value maps per the summary's
        // `return_to_result` instead of the normal value→result
        // rebasing (map: the result array's `[AnyIndex]` elements;
        // forEach: `None` — the callback return dies with the undefined
        // result).
        let gap = call_site.and_then(|c| self.gap_at(c, callee));

        match &exit_inst.op {
            Op::Return { value } => {
                // Context-sensitive `CallKind::New` constructor `this.field`
                // exit wiring: re-key `Local(this_param).fields` onto THIS
                // specific `New` call site (`Heap({call})` + `Local(result)`).
                if !fact.fields.is_empty()
                    && self.ctor_this_of(callee) == Some(v)
                    && let (Some(call), Some(rs)) = (call_site, return_site)
                    && self.handler_exception_at(rs).is_none()
                    && matches!(
                        module.inst(call).map(|i| &i.op),
                        Some(Op::Call {
                            kind: CallKind::New,
                            ..
                        })
                    )
                {
                    out.push(Fact::of(TaintFact {
                        base: TaintBase::Heap(AllocSiteSet::one(call)),
                        fields: fact.fields.clone(),
                    }));
                    if let Some(Some(result)) = module.inst(call).map(|i| i.result) {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                    return;
                }
                if value != &Some(v) {
                    return; // callee-local taint that is not returned dies here
                }
                let (Some(call), Some(rs)) = (call_site, return_site) else {
                    return; // unbalanced: no result value to rebase onto
                };
                // The return VALUE flows only to the normal continuation,
                // never to handler entries.
                if self.handler_exception_at(rs).is_some() {
                    return;
                }
                if let Some(gap) = &gap {
                    if let Some(chain) = &gap.return_to_result
                        && let Some(Some(result)) = module.inst(call).map(|i| i.result)
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
                    return;
                }
                if let Some(Some(result)) = module.inst(call).map(|i| i.result) {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
            }
            Op::Throw { value } => {
                if value != &v {
                    return;
                }
                let Some(rs) = return_site else { return };
                // Thrown taint lands on the catch binding of whichever
                // handler entry this return site is (T5/T10).
                if let Some(exc) = self.handler_exception_at(rs) {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(exc))));
                }
            }
            _ => {}
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
        let Fact::Taint(fact) = source else {
            if self.call_return_sources.contains(&call)
                && self.handler_exception_at(return_site).is_none()
                && let Some(result) = module.inst(call).and_then(|i| i.result)
            {
                out.push(Fact::of(TaintFact::local(result)));
            }
            return;
        };
        let Some(call_inst) = module.inst(call) else {
            return;
        };
        let Op::Call { args, kind, .. } = &call_inst.op else {
            return;
        };
        let is_handler_site = self.handler_exception_at(return_site).is_some();
        let on_operand = fact
            .local_base()
            .is_some_and(|v| op_uses_value(&call_inst.op, v));

        match self.classify(call) {
            SiteClass::Summary { name, exclusive } => {
                let base = call_base_value(module, call_inst);
                let result = call_inst.result;
                let Some(summary) = self.registry.lookup(&name, args.len()) else {
                    return;
                };
                // Clears are evaluated before flows.
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
                    // Mini-gap: tag the callback value with `[AnyIndex]`
                    // (the may-call-user-code marker). The FULL gap
                    // propagator's enter/return channels live on the
                    // gap call/return edges (gap.rs); this tag remains
                    // the channel for DIRECT user calls of the callback
                    // value and the unresolved-callback fallback.
                    if let Some(cb_gap) = &summary.callback
                        && Self::match_endpoint(&Endpoint::Base, fact, args, base).is_some()
                        && let Some(&cbv) = args.get(cb_gap.param as usize)
                    {
                        out.push(Fact::of(
                            TaintFact::local(cbv).pushed(FieldKey::AnyIndex, self.cap()),
                        ));
                    }
                }
                // The incoming taint is RETAINED unless cleared; exclusive
                // summaries additionally kill incoming operand taints the
                // flows did not re-add: the summary is the complete model
                // of the operands' fate.
                let retain = !(cleared || exclusive && on_operand);
                if retain {
                    self.push_passthrough_at(source, return_site, out);
                }
                // Log once per (site, fact-free) application (`O(1)` dedup).
                if self.applied_seen.borrow_mut().insert(call) {
                    self.applied.borrow_mut().push((call, name));
                }
            }
            SiteClass::BodyStep => {
                // The callee body carries operand taints through the
                // call/return edges; caller SSA values with empty field
                // chains also survive (JS/ArkTS passes arguments by value,
                // so a callee cannot rebind or sanitize the caller's SSA
                // register, while non-empty `Local(v).f` chains defer to
                // the callee body for Rung-0 field strong-kills unless no
                // callee touches `f` on large bundles).
                let untouched_this_prop = if self.module.functions.len() > 512
                    && *kind != CallKind::New
                    && let Some(v) = fact.local_base()
                    && !args.contains(&v)
                    && let Some(&FieldKey::Named(prop)) = fact.fields.elements().first()
                {
                    self.callgraph
                        .callees_of_call_at(call)
                        .iter()
                        .all(|&c| !self.can_callee_touch_prop(prop, c))
                } else {
                    false
                };
                if !on_operand || fact.fields.is_empty() || untouched_this_prop {
                    self.push_passthrough_at(source, return_site, out);
                }
            }
            SiteClass::NativeKeep | SiteClass::UnknownKeep => {
                // Conservative keep: taint passes through untouched —
                // never sanitizes. Plus the optional identity heuristic:
                // tainted operand ⇒ tainted return.
                self.push_passthrough_at(source, return_site, out);
                if self.config.native_identity
                    && on_operand
                    && !is_handler_site
                    && let Some(result) = call_inst.result
                {
                    if self.module.functions.len() > 512 {
                        if fact
                            .local_base()
                            .is_some_and(|v| fact.fields.is_empty() || args.contains(&v))
                        {
                            out.push(Fact::of(TaintFact::local(result)));
                        }
                    } else {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                }
            }
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
                    kind: CallKind::New,
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

/// Visit every SSA [`ValueId`] operand of `op` in [`Op::operands`] order
/// without heap allocation.
pub(crate) fn for_each_op_operand(op: &Op, mut f: impl FnMut(ValueId)) {
    use Op::*;
    match op {
        BinaryOp { left, right, .. } | Compare { left, right, .. } => {
            f(*left);
            f(*right);
        }
        UnaryOp { operand, .. } => f(*operand),
        Mov { src } => f(*src),
        LoadConst(_) | AllocObject { .. } | AllocArray { .. } | AllocRegExp { .. } => {}
        AllocClosure { func } => f(*func),
        LoadProp { object, .. } => f(*object),
        StoreProp { object, value, .. } | StoreOwnPropName { object, value, .. } => {
            f(*object);
            f(*value);
        }
        LoadPropIdx { object, index } | LoadPropDyn { object, key: index } => {
            f(*object);
            f(*index);
        }
        StorePropIdx {
            object,
            index,
            value,
        }
        | StorePropDyn {
            object,
            key: index,
            value,
        }
        | StoreOwnPropDyn {
            object,
            key: index,
            value,
        }
        | StoreOwnPropIdx {
            object,
            index,
            value,
        } => {
            f(*object);
            f(*index);
            f(*value);
        }
        DefineMethod { object, func, .. } => {
            f(*object);
            f(*func);
        }
        DeleteProp { object, key } => {
            f(*object);
            f(*key);
        }
        TestProp { object, key } => {
            f(*object);
            match key {
                PropKey::Name(_) => {}
                PropKey::Index(k) | PropKey::Dynamic(k) => f(*k),
            }
        }
        CopyDataProps { dst, src } => {
            f(*dst);
            f(*src);
        }
        SetObjectWithProto { proto, obj } => {
            f(*proto);
            f(*obj);
        }
        ArraySpread { dst, index, src } => {
            f(*dst);
            f(*index);
            f(*src);
        }
        CreateObjectWithExcludedKeys { obj, keys } => {
            f(*obj);
            for &k in keys {
                f(k);
            }
        }
        DefineGetterSetterByValue {
            obj,
            key,
            getter,
            setter,
        } => {
            f(*obj);
            f(*key);
            f(*getter);
            f(*setter);
        }
        GetTemplateObject { literal } => f(*literal),
        CreateIterResultObj { value, done } => {
            f(*value);
            f(*done);
        }
        GetIterator { obj } | GetPropIterator { obj } | GetAsyncIterator { obj } => f(*obj),
        IteratorNext { iterator }
        | IteratorReturn { iterator }
        | IteratorThrow { iterator }
        | NextPropName { iterator } => f(*iterator),
        NewLexEnv { .. }
        | NewLexEnvWithName { .. }
        | PopLexEnv
        | GetLexVar { .. }
        | CreatePrivateNames { .. }
        | LoadNewTarget
        | LoadGlobalObject
        | LoadFunction
        | GetUnmappedArgs
        | CopyRestArgs { .. }
        | AsyncFunctionEnter
        | ThrowNotExists
        | ThrowPatternNonCoercible
        | ThrowDeleteSuperProperty
        | Debugger
        | LoadModuleVar { .. }
        | GetModuleNamespace { .. }
        | Branch { .. }
        | Unreachable => {}
        PutLexVar { value, .. }
        | StoreGlobal { value, .. }
        | StoreGlobalRecord { value, .. }
        | TryStoreGlobal { value, .. }
        | StoreModuleVar { value, .. } => f(*value),
        TryGetGlobal { default, .. } => {
            if let Some(d) = default {
                f(*d);
            }
        }
        DynamicImport { specifier } => f(*specifier),
        Call {
            callee, this, args, ..
        } => {
            f(*callee);
            if let Some(t) = this {
                f(*t);
            }
            for &a in args {
                f(a);
            }
        }
        DefineFunc { captures, .. } => {
            for &(_, v) in captures {
                f(v);
            }
        }
        DefineClass { heritage, .. } | DefineSendableClass { heritage, .. } => {
            if let Some(h) = heritage {
                f(*h);
            }
        }
        LoadPrivate { obj, .. } | TestPrivate { obj, .. } => f(*obj),
        StorePrivate { obj, value, .. } | DefinePrivate { obj, value, .. } => {
            f(*obj);
            f(*value);
        }
        Throw { value }
        | ThrowIfSuperNotCalled { value, .. }
        | ThrowConstAssignment { name: value }
        | ThrowIfNotObject { value }
        | ThrowUndefinedIfHoleWithName { value, .. }
        | Await { value } => f(*value),
        AwaitUncaught { funcobj, value }
        | AsyncResolve { funcobj, value }
        | AsyncReject { funcobj, value } => {
            f(*funcobj);
            f(*value);
        }
        ThrowUndefinedIfHole { name, value } => {
            f(*name);
            f(*value);
        }
        CreateGenerator { func } => f(*func),
        SuspendGenerator { genobj, value } => {
            f(*genobj);
            f(*value);
        }
        ResumeGenerator { genobj } | GetResumeMode { genobj } => f(*genobj),
        LoadSuper { key, this_value } => {
            if let SuperKey::Dynamic(k) = key {
                f(*k);
            }
            f(*this_value);
        }
        StoreSuper {
            key,
            this_value,
            value,
        } => {
            f(*value);
            f(*this_value);
            if let SuperKey::Dynamic(k) = key {
                f(*k);
            }
        }
        CondBranch { cond, .. } => f(*cond),
        Return { value } => {
            if let Some(v) = value {
                f(*v);
            }
        }
        Phi { entries } => {
            for &(_, v) in entries {
                f(v);
            }
        }
    }
}

/// Zero-allocation check equivalent to `op.operands().contains(&target)`.
pub(crate) fn op_uses_value(op: &Op, target: ValueId) -> bool {
    let mut found = false;
    for_each_op_operand(op, |v| {
        if v == target {
            found = true;
        }
    });
    found
}

#[allow(clippy::type_complexity)]
fn build_exception_indexes(
    module: &Module,
) -> (
    Vec<Option<FuncId>>,
    Vec<Option<ValueId>>,
    HashMap<(FuncId, BlockId), ValueId>,
) {
    let mut block_to_func = vec![None; module.blocks.len()];
    let mut handler_block_exc = vec![None; module.blocks.len()];
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
                if let Some(slot) = handler_block_exc.get_mut(catch.handler.index()) {
                    slot.get_or_insert(catch.exception);
                }
                func_handler_exc
                    .entry((fid, catch.handler))
                    .or_insert(catch.exception);
            }
        }
    }
    (block_to_func, handler_block_exc, func_handler_exc)
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

    fn build(module: &Module, fid: FuncId, await_resume: &HashMap<InstId, ValueId>) -> Self {
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
                for_each_op_operand(&inst.op, &mut intern_val);
                if matches!(inst.op, Op::Call { .. })
                    && let Some(base_v) = call_base_value(module, inst)
                {
                    intern_val(base_v);
                }
                if matches!(inst.op, Op::ResumeGenerator { .. })
                    && let Some(&aw) = await_resume.get(&iid)
                {
                    intern_val(aw);
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
                for_each_op_operand(&inst.op, |u| {
                    record_use(u, pos_u32, gen_slice, kill_slice);
                });
                if matches!(inst.op, Op::Call { .. })
                    && let Some(base_v) = call_base_value(module, inst)
                {
                    record_use(base_v, pos_u32, gen_slice, kill_slice);
                }
                if matches!(inst.op, Op::ResumeGenerator { .. })
                    && let Some(&aw) = await_resume.get(&iid)
                {
                    record_use(aw, pos_u32, gen_slice, kill_slice);
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
        await_resume: &HashMap<InstId, ValueId>,
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

pub(crate) fn peel_ns_index(module: &Module, mut v: ValueId) -> Option<u32> {
    for _ in 0..8 {
        let ValueDef::Inst(iid) = module.value(v)?.def else {
            return None;
        };
        match &module.inst(iid)?.op {
            Op::Mov { src } => v = *src,
            Op::GetModuleNamespace { index } => return Some(*index),
            _ => return None,
        }
    }
    None
}

fn build_await_resume_map(module: &Module) -> HashMap<InstId, ValueId> {
    let mut out = HashMap::new();
    for bb in &module.blocks {
        let mut last_await: HashMap<ValueId, ValueId> = HashMap::new();
        for &iid in &bb.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            match &inst.op {
                Op::AwaitUncaught { funcobj, value } => {
                    last_await.insert(*funcobj, *value);
                }
                Op::ResumeGenerator { genobj } => {
                    if let Some(&val) = last_await.get(genobj) {
                        out.insert(iid, val);
                    }
                }
                _ => {}
            }
        }
    }
    out
}

/// Discover methods exposed on `proxy_obj` via
/// `WebviewController.registerJavaScriptProxy(proxy_obj, name, methodList)`
/// and seed their formal parameters as untrusted JSBridge inputs.
fn collect_jsbridge_seeds(
    module: &Module,
    oracle: &Oracle,
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
        for it in items {
            if let Const::String(s) = it
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
                    for (k, v) in keys.iter().zip(values.iter()) {
                        if let (Const::String(ks), Const::MethodRef(mfid)) = (k, v)
                            && let Some(mname) = module.sym.resolve(*ks)
                            && name_allowed(mname)
                        {
                            candidate_funcs.push(*mfid);
                        }
                    }
                }
                if let Some(obj_val) = site_inst.result {
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
                            } if *object == obj_val => {
                                if let Some(mname) = module.sym.resolve(*name)
                                    && name_allowed(mname)
                                {
                                    for f in gap::resolve_callback_funcs(module, oracle, *value, at)
                                    {
                                        candidate_funcs.push(f);
                                    }
                                }
                            }
                            Op::DefineMethod {
                                object, name, func, ..
                            } if *object == obj_val => {
                                if let Some(mname) = module.sym.resolve(*name)
                                    && name_allowed(mname)
                                {
                                    for f in gap::resolve_callback_funcs(module, oracle, *func, at)
                                    {
                                        candidate_funcs.push(f);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            Op::Call {
                callee,
                kind: CallKind::New,
                ..
            } => {
                if let Some(ValueDef::Inst(cls_iid)) = module.value(*callee).map(|v| v.def)
                    && let Some(
                        Op::DefineClass { members, .. } | Op::DefineSendableClass { members, .. },
                    ) = module.inst(cls_iid).map(|i| &i.op)
                    && let Some(Const::ArrayLiteral(items)) = module.consts.get(*members)
                {
                    let mut pending: Option<&str> = None;
                    for it in items {
                        match it {
                            Const::String(s) => pending = module.sym.resolve(*s),
                            Const::MethodRef(mfid) => {
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

#[cfg(test)]
mod tests {
    use super::*;
    use abcd_ir::op::{BinOp, CmpOp, ModuleVarKind, SuperCheck, UnOp};
    use abcd_ir::{ConstId, Edge, EdgeKind};

    #[test]
    fn op_uses_value_and_visitor_match_operands_table() {
        let v0 = ValueId::new(10);
        let v1 = ValueId::new(11);
        let v2 = ValueId::new(12);
        let v3 = ValueId::new(13);
        let absent = ValueId::new(99);
        let s = Sym::new(0);
        let c = ConstId::new(0);
        let b = BlockId::new(0);
        let f = FuncId::new(0);
        let edge = Edge {
            from: b,
            kind: EdgeKind::Normal,
        };

        let ops = vec![
            Op::BinaryOp {
                op: BinOp::Add,
                left: v0,
                right: v1,
            },
            Op::UnaryOp {
                op: UnOp::Minus,
                operand: v0,
            },
            Op::Compare {
                op: CmpOp::Eq,
                left: v0,
                right: v1,
            },
            Op::Mov { src: v0 },
            Op::LoadConst(c),
            Op::AllocObject { shape: c },
            Op::AllocArray { shape: Some(c) },
            Op::AllocRegExp {
                pattern: s,
                flags: 0,
            },
            Op::AllocClosure { func: v0 },
            Op::LoadProp {
                object: v0,
                name: s,
            },
            Op::StoreProp {
                object: v0,
                name: s,
                value: v1,
            },
            Op::LoadPropIdx {
                object: v0,
                index: v1,
            },
            Op::StorePropIdx {
                object: v0,
                index: v1,
                value: v2,
            },
            Op::LoadPropDyn {
                object: v0,
                key: v1,
            },
            Op::StorePropDyn {
                object: v0,
                key: v1,
                value: v2,
            },
            Op::StoreOwnPropName {
                object: v0,
                name: s,
                value: v1,
            },
            Op::StoreOwnPropDyn {
                object: v0,
                key: v1,
                value: v2,
            },
            Op::StoreOwnPropIdx {
                object: v0,
                index: v1,
                value: v2,
            },
            Op::DefineMethod {
                object: v0,
                name: s,
                func: v1,
                length: 1,
            },
            Op::DeleteProp {
                object: v0,
                key: v1,
            },
            Op::TestProp {
                object: v0,
                key: PropKey::Name(s),
            },
            Op::TestProp {
                object: v0,
                key: PropKey::Index(v1),
            },
            Op::TestProp {
                object: v0,
                key: PropKey::Dynamic(v1),
            },
            Op::CopyDataProps { dst: v0, src: v1 },
            Op::SetObjectWithProto { proto: v0, obj: v1 },
            Op::ArraySpread {
                dst: v0,
                index: v1,
                src: v2,
            },
            Op::CreateObjectWithExcludedKeys {
                obj: v0,
                keys: vec![v1, v2],
            },
            Op::DefineGetterSetterByValue {
                obj: v0,
                key: v1,
                getter: v2,
                setter: v3,
            },
            Op::GetTemplateObject { literal: v0 },
            Op::CreateIterResultObj {
                value: v0,
                done: v1,
            },
            Op::GetIterator { obj: v0 },
            Op::GetAsyncIterator { obj: v0 },
            Op::IteratorNext { iterator: v0 },
            Op::IteratorReturn { iterator: v0 },
            Op::IteratorThrow { iterator: v0 },
            Op::GetPropIterator { obj: v0 },
            Op::NextPropName { iterator: v0 },
            Op::NewLexEnv { num_vars: 2 },
            Op::NewLexEnvWithName {
                num_vars: 2,
                scope_names: c,
            },
            Op::PopLexEnv,
            Op::GetLexVar { level: 0, slot: 1 },
            Op::PutLexVar {
                level: 0,
                slot: 1,
                value: v0,
            },
            Op::TryGetGlobal {
                name: s,
                default: None,
            },
            Op::TryGetGlobal {
                name: s,
                default: Some(v0),
            },
            Op::StoreGlobal { name: s, value: v0 },
            Op::StoreGlobalRecord {
                name: s,
                value: v0,
                is_const: true,
            },
            Op::TryStoreGlobal { name: s, value: v0 },
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::Local,
            },
            Op::StoreModuleVar {
                index: 0,
                value: v0,
            },
            Op::GetModuleNamespace { index: 0 },
            Op::DynamicImport { specifier: v0 },
            Op::Call {
                callee: v0,
                this: Some(v1),
                args: vec![v2, v3],
                kind: CallKind::Dynamic,
            },
            Op::Call {
                callee: v0,
                this: None,
                args: vec![],
                kind: CallKind::Direct,
            },
            Op::DefineFunc {
                body: f,
                captures: vec![(s, v0), (s, v1)],
                length: 0,
            },
            Op::DefineClass {
                ctor: f,
                heritage: Some(v0),
                members: c,
                member_attrs: Vec::new(),
                count: 0,
            },
            Op::DefineSendableClass {
                ctor: f,
                heritage: None,
                members: c,
                member_attrs: Vec::new(),
                count: 0,
            },
            Op::LoadPrivate {
                level: 0,
                slot: 0,
                obj: v0,
            },
            Op::StorePrivate {
                level: 0,
                slot: 0,
                obj: v0,
                value: v1,
            },
            Op::DefinePrivate {
                level: 0,
                slot: 0,
                obj: v0,
                value: v1,
            },
            Op::TestPrivate {
                level: 0,
                slot: 0,
                obj: v0,
            },
            Op::CreatePrivateNames { count: 1, names: c },
            Op::Throw { value: v0 },
            Op::ThrowIfSuperNotCalled {
                value: v0,
                kind: SuperCheck::NotCalled,
            },
            Op::ThrowUndefinedIfHole {
                name: v0,
                value: v1,
            },
            Op::ThrowUndefinedIfHoleWithName { name: s, value: v0 },
            Op::ThrowNotExists,
            Op::ThrowPatternNonCoercible,
            Op::ThrowDeleteSuperProperty,
            Op::ThrowConstAssignment { name: v0 },
            Op::ThrowIfNotObject { value: v0 },
            Op::CreateGenerator { func: v0 },
            Op::SuspendGenerator {
                genobj: v0,
                value: v1,
            },
            Op::ResumeGenerator { genobj: v0 },
            Op::GetResumeMode { genobj: v0 },
            Op::Await { value: v0 },
            Op::AwaitUncaught {
                funcobj: v0,
                value: v1,
            },
            Op::AsyncFunctionEnter,
            Op::AsyncResolve {
                funcobj: v0,
                value: v1,
            },
            Op::AsyncReject {
                funcobj: v0,
                value: v1,
            },
            Op::LoadNewTarget,
            Op::LoadGlobalObject,
            Op::LoadFunction,
            Op::GetUnmappedArgs,
            Op::CopyRestArgs { start_index: 0 },
            Op::LoadSuper {
                key: SuperKey::Name(s),
                this_value: v0,
            },
            Op::LoadSuper {
                key: SuperKey::Dynamic(v1),
                this_value: v0,
            },
            Op::StoreSuper {
                key: SuperKey::Name(s),
                this_value: v0,
                value: v1,
            },
            Op::StoreSuper {
                key: SuperKey::Dynamic(v2),
                this_value: v0,
                value: v1,
            },
            Op::Branch { dest: b },
            Op::CondBranch {
                cond: v0,
                true_dest: b,
                false_dest: b,
            },
            Op::Return { value: Some(v0) },
            Op::Return { value: None },
            Op::Phi {
                entries: vec![(edge, v0), (edge, v1)],
            },
            Op::Unreachable,
            Op::Debugger,
        ];

        for op in &ops {
            let expected = op.operands();
            let mut visited = Vec::new();
            for_each_op_operand(op, |v| visited.push(v));
            assert_eq!(visited, expected, "visitor mismatch on {op:?}");
            for cand in [v0, v1, v2, v3, absent] {
                assert_eq!(
                    op_uses_value(op, cand),
                    expected.contains(&cand),
                    "op_uses_value mismatch on {op:?} for {cand:?}"
                );
            }
        }
    }
}
