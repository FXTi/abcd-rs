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
//! - **Calls** ([`abcd_analysis::dataflow::ifds::IfdsProblem::call_flow`] /
//!   [`abcd_analysis::dataflow::ifds::IfdsProblem::call_to_return_flow`]): N66 frame-slot arg→param
//!   mapping, summary application on the call-to-return edge, exclusive-kill
//!   of the call edge into the callee, and the fallback ladder.
//! - **Return wiring** ([`abcd_analysis::dataflow::ifds::IfdsProblem::return_flow`]): return value →
//!   call result on the normal continuation; thrown value → the catch
//!   handler's `ExceptionParam` binding on handler return sites (T5).
//! - **Exception edges**: intraprocedural `Throw` → handler entry maps
//!   the thrown value's taint onto the catch binding
//!   ([`abcd_ir::ValueDef::ExceptionParam`]) — "ExceptionParam taints the catch
//!   binding".
//!
//! Everything else is pass-through (facts survive) plus the generic
//! operand→result rule.

mod classify;
mod cones;
mod escape;
mod ifds;
mod indexes;
mod lex_env;
mod liveness;
#[cfg(test)]
mod tests;
mod transfer;

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::dataflow::heap::{AllocSiteSet, Rung0AliasOracle, SingletonSiteClassifier};
use abcd_analysis::dataflow::ifds::CallGraphOracle;
use abcd_analysis::module_link::ModuleLinkTable;
use abcd_ir::{BlockId, ClassId, FuncId, InstId, Module, Op, Sym, ValueId};

use crate::driver::{SinkSpec, SourceSpec, TaintConfig};
use crate::fact::Fact;
use crate::gap;
use crate::names::{ClassPropStores, callee_name_candidates_indexed, quick_callee_leaf_sym};
use crate::oracle::Oracle;
use crate::prototype::FamilyAnswer;
use crate::summary::SummaryRegistry;

use self::cones::{GlobalReaderIndex, HeapSiteIndex, PropTouchIndex};
use self::escape::{HarnessHeapEscape, LocalSiteEscape};
use self::indexes::{
    HarnessGuard, build_exception_indexes, build_func_has_return, build_global_stores_map,
    build_harness_guard, build_variadic_ops_index, const_string_sym,
};
pub(crate) use self::indexes::{
    classify_dyn_prop_key, is_any_index_compatible_prop_str, is_global_object,
    resolve_global_sources, resolve_module_import_sources, resolve_namespace_import_sources,
};
use self::lex_env::PrivateFieldIndex;
pub(crate) use self::lex_env::StaticLexEnvTable;
use self::liveness::{
    FuncAliasLoads, LocalLiveness, ValueAliasLoads, build_jsbridge_prop_index,
    collect_jsbridge_seeds,
};
use crate::closed_dispatch::ClosedDispatchIndex;

/// How a call site is handled — the fallback ladder, memoized per site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum SiteClass {
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
pub(crate) enum ParamBinding {
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
pub(crate) fn param_binding(module: &Module, callee: FuncId) -> ParamBinding {
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
type VariadicOpsMap = HashMap<FuncId, Box<[(InstId, Option<u16>)]>>;

/// Compact `[u64]` bitset indexed by `FuncId::index()` (`8x` denser than `Vec<bool>`; `#78`).
#[derive(Clone, Debug, Default)]
pub(crate) struct FuncBitSet(Box<[u64]>);

impl FuncBitSet {
    #[inline]
    pub(crate) fn new(n_funcs: usize) -> Self {
        Self(vec![0u64; n_funcs.div_ceil(64)].into_boxed_slice())
    }

    #[inline]
    pub(crate) fn new_all_set(n_funcs: usize) -> Self {
        let mut words = vec![!0u64; n_funcs.div_ceil(64)];
        let rem = n_funcs % 64;
        if rem != 0
            && let Some(last) = words.last_mut()
        {
            *last = (1u64 << rem) - 1;
        }
        Self(words.into_boxed_slice())
    }

    #[inline]
    pub(crate) fn get(&self, fi: usize) -> bool {
        self.0
            .get(fi / 64)
            .is_some_and(|&w| ((w >> (fi % 64)) & 1) != 0)
    }

    /// Set bit `fi` if within allocated words; returns `true` iff bit `fi` transitioned `0 -> 1`.
    #[inline]
    pub(crate) fn set(&mut self, fi: usize) -> bool {
        let Some(w) = self.0.get_mut(fi / 64) else {
            return false;
        };
        let mask = 1u64 << (fi % 64);
        if (*w & mask) != 0 {
            false
        } else {
            *w |= mask;
            true
        }
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.0.iter().all(|&w| w == 0)
    }

    #[inline]
    pub(crate) fn intersects(&self, other: &Self) -> bool {
        self.0
            .iter()
            .zip(other.0.iter())
            .any(|(&a, &b)| (a & b) != 0)
    }
}

/// The taint problem over a module + call graph + the rung-selected
/// alias oracle ([`Oracle`]: rung-0 baseline, rung-1 demand-driven
/// engine, or rung-2 whole-module PTA) + summary registry + source/sink config.
pub struct TaintProblem<'m> {
    module: &'m Module,
    callgraph: &'m CallGraph,
    links: Cow<'m, ModuleLinkTable>,
    prop_stores: ClassPropStores,
    global_stores: HashMap<Sym, Vec<ValueId>>,
    has_dyn_global_store: bool,
    /// Scoped `(FuncId, handler BlockId) -> exception ValueId` for intraprocedural
    /// and per-call exceptional dispatch.
    func_handler_exc: HashMap<(FuncId, BlockId), ValueId>,
    /// Protected-block -> handler-block pairs `(prot_block, handler_block)` (`T1`).
    protected_handler_edges: HashSet<(BlockId, BlockId)>,
    /// Concrete runtime singleton allocation-site classifier (`D5`); `None` when
    /// delegating directly to `Oracle::Rung2::singletons()`.
    singletons: Option<SingletonSiteClassifier>,
    /// Static lexical-environment scope table for Rung 0/1 `LexVar` `level` shift (`R10`).
    static_lex_env: StaticLexEnvTable,
    /// Pre-indexed synthetic symbols for `#private` class fields (`LoadPrivate`/`StorePrivate`/`DefinePrivate`).
    private_fields: PrivateFieldIndex,
    /// Packed `FuncId::index() -> bool` bitset of functions containing at least one `Op::Return`.
    func_has_return: FuncBitSet,
    /// Per-function backward SSA local liveness for pruning dead `TaintBase::Local` facts.
    liveness: LocalLiveness,
    /// Lazy memo per `ValueId::index()`: `0 = unknown`, `1 = dead-prunable`,
    /// `2 = has aliasing property loads in its owning function`.
    value_keep_flag: RefCell<Vec<u8>>,
    /// Per-function lazy index of property loads with non-empty `site_info_at(object).sites`.
    func_alias_loads: RefCell<Vec<Option<Box<FuncAliasLoads>>>>,
    /// Cached `(func_idx, matching_load_indices)` for locals with `value_keep_flag == 2`.
    value_alias_loads: RefCell<HashMap<ValueId, ValueAliasLoads>>,
    oracle: RefCell<Oracle<'m>>,
    /// Compact `Op::Throw` operand site cache retained when `oracle` is dropped before path replay.
    throw_replay_sites: HashMap<(InstId, ValueId), AllocSiteSet>,
    registry: &'m SummaryRegistry,
    config: &'m TaintConfig,
    /// Final `.`-segment leaves of configured [`SinkSpec::Call`] targets.
    sink_leaves: HashSet<String>,
    /// Per-function `(InstId, Option<start_index>)` of `GetUnmappedArgs` (`None`)
    /// and `CopyRestArgs` (`Some(start_index)`) instructions.
    variadic_ops: VariadicOpsMap,
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
    /// `(ClassId, req_idx)` `GetModuleNamespace` external imports tainted via `SourceSpec::ModuleImport`.
    namespace_import_sources: HashMap<(ClassId, u32), Option<Vec<Sym>>>,
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
    /// Packed `FuncId::index() -> bool` backward caller cone of functions that
    /// can generate `0 -> d` taint facts across `callgraph ∪ gap_edges`.
    zero_needed: FuncBitSet,
    /// Precomputed synthetic `__abcd_ohos_harness__` call and allocation-site guard.
    harness: HarnessGuard,
    /// Reverse callback-gap caller index (`callee FuncId -> caller FuncIds`).
    rev_gap_callers: HashMap<FuncId, Vec<FuncId>>,
    /// One-time lazy index `(src_cid, src_slot) -> Vec<FuncId>` of functions
    /// reading `TaintBase::ModuleVar(src_cid, src_slot)` directly or via ES links.
    module_slot_users: RefCell<Option<ModuleSlotUsers>>,
    /// Lazily memoized `(src_cid, src_slot) -> FuncBitSet` of functions that can
    /// transitively reach a module-variable reader of `(src_cid, src_slot)`.
    module_var_readers: RefCell<HashMap<(ClassId, u32), FuncBitSet>>,
    /// One-time lazy index of functions reading named or dynamic globals (`#78`).
    global_reader_index: RefCell<Option<GlobalReaderIndex>>,
    /// Lazily memoized `sym -> FuncBitSet` of functions that can transitively
    /// reach a global reader of `sym`.
    global_readers: RefCell<HashMap<Sym, FuncBitSet>>,
    /// One-time lazy heap-site dereference index across all rungs (`0`/`1`/`2`),
    /// with precomputed `O(1)` `unknown_deref_cone` and `imprecise_lex_cone`.
    heap_site_index: RefCell<Option<HeapSiteIndex>>,
    /// Lazily memoized `site_iid -> FuncBitSet` backward caller cone of `HeapSiteIndex::by_site`.
    heap_site_cone: RefCell<HashMap<InstId, FuncBitSet>>,
    /// Lazily memoized `site_iid -> FuncBitSet` backward caller cone stopping at `inst_func(site)`.
    outside_site_cone: RefCell<HashMap<InstId, FuncBitSet>>,
    /// One-time lazy escape index for non-harness `Heap(sites)` facts crossing `__abcd_ohos_harness__`.
    harness_heap_escape: RefCell<Option<HarnessHeapEscape>>,
    /// Lazily memoized `FuncBitSet` backward caller cone of `Op::GetLexVar` readers.
    lex_var_readers: RefCell<Option<FuncBitSet>>,
    /// Per-record `ClassId -> FuncBitSet` backward caller cone of `Op::GetLexVar` readers in that record.
    env_class_cone: RefCell<HashMap<ClassId, FuncBitSet>>,
    /// One-time lazy index of functions touching named/dynamic properties.
    prop_touch_index: RefCell<Option<PropTouchIndex>>,
    /// Lazily memoized `prop_sym -> FuncBitSet` backward caller cone of `prop_touch_index`.
    prop_touch_cone: RefCell<HashMap<Sym, FuncBitSet>>,
    /// Lazily memoized `prop_sym -> FuncBitSet` backward caller cone of unknown-receiver named readers.
    prop_unknown_cone: RefCell<HashMap<Sym, FuncBitSet>>,
    /// Lazily memoized `prop_sym -> FuncBitSet` backward caller cone of named property writers.
    prop_write_cone: RefCell<HashMap<Sym, FuncBitSet>>,
    /// One-time lazy `FuncId::index() -> bool` bitset of callees whose `this` may return or escape.
    this_ret_or_esc: RefCell<Option<FuncBitSet>>,
    /// Lazily memoized `caller_fid -> (backward_caller_ancestors, reaches_harness)`.
    caller_ancestors: RefCell<HashMap<FuncId, (FuncBitSet, bool)>>,
    /// Memoized `(caller_fid, owner_callee_or_max, source_fact_id) -> observable` answers.
    caller_obs_memo: RefCell<HashMap<(FuncId, u32, u32), bool>>,
    /// Lazily memoized intraprocedural SSA escape classification per heap site.
    site_local_escape_memo: RefCell<HashMap<InstId, LocalSiteEscape>>,
    /// Lazily memoized upward/global escape classification per heap site (`#78`, `#84`).
    site_upward_escape_memo: RefCell<HashMap<InstId, bool>>,
    /// One-time lazy map `param_vid -> (owning FuncId, param_index)`.
    param_owner: RefCell<Option<HashMap<ValueId, (FuncId, usize)>>>,
    /// Memoized closed caller-argument site set for formal parameters (`#78`, `#84`).
    closed_param_memo: RefCell<HashMap<ValueId, Option<AllocSiteSet>>>,
    /// Lazy whole-module closed class/method/singleton dispatch index (`#84`).
    closed_dispatch: RefCell<Option<ClosedDispatchIndex>>,
    /// `true` after [`Self::shrink_for_path_replay`] drops heavy cone indexes.
    in_path_replay: bool,
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
        Self::new_with_harness(module, links, callgraph, oracle, registry, config, None)
    }

    /// Build the problem reusing a precomputed [`ModuleLinkTable`] and an explicit
    /// [`abcd_analysis::ohos_lifecycle::EntryModel::harness_func`] (`D3`).
    pub fn new_with_harness(
        module: &'m Module,
        links: ModuleLinkTable,
        callgraph: &'m CallGraph,
        oracle: Oracle<'m>,
        registry: &'m SummaryRegistry,
        config: &'m TaintConfig,
        harness_func: Option<FuncId>,
    ) -> Self {
        let prop_stores = ClassPropStores::build(module);
        Self::new_with_indexed(
            module,
            Cow::Owned(links),
            prop_stores,
            callgraph,
            oracle,
            registry,
            config,
            harness_func,
        )
    }

    /// Build the problem reusing [`ModuleLinkTable`], [`ClassPropStores`], and
    /// explicit `harness_func` (`D3`).
    #[expect(
        clippy::too_many_arguments,
        reason = "internal constructor accepting prebuilt module indexes and harness handle"
    )]
    pub(crate) fn new_with_indexed(
        module: &'m Module,
        links: Cow<'m, ModuleLinkTable>,
        prop_stores: ClassPropStores,
        callgraph: &'m CallGraph,
        oracle: Oracle<'m>,
        registry: &'m SummaryRegistry,
        config: &'m TaintConfig,
        harness_func: Option<FuncId>,
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
        let (global_stores, has_dyn_global_store) = build_global_stores_map(module);
        let (func_handler_exc, protected_handler_edges) = build_exception_indexes(module);
        let singletons = match &oracle {
            Oracle::Rung2(..) => None,
            Oracle::Rung0(_) | Oracle::Rung1(..) => Some(
                SingletonSiteClassifier::build_with_links(module, &links, callgraph, harness_func),
            ),
        };
        let static_lex_env = StaticLexEnvTable::build(module, &links);
        let private_fields = PrivateFieldIndex::build(module, &links, &static_lex_env);
        let func_has_return = build_func_has_return(module);
        let module_import_sources = resolve_module_import_sources(module, &links, config);
        let namespace_import_sources = resolve_namespace_import_sources(module, &links, config);
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
        let liveness = LocalLiveness::new(module.functions.len());
        let value_keep_flag = RefCell::new(vec![0u8; module.values.len()]);
        let mut alias_loads_init = Vec::with_capacity(module.functions.len());
        alias_loads_init.resize_with(module.functions.len(), || None);
        let func_alias_loads = RefCell::new(alias_loads_init);
        let value_alias_loads = RefCell::new(HashMap::new());

        let mut problem = TaintProblem {
            module,
            callgraph,
            links,
            prop_stores,
            global_stores,
            has_dyn_global_store,
            func_handler_exc,
            protected_handler_edges,
            singletons,
            static_lex_env,
            private_fields,
            func_has_return,
            liveness,
            value_keep_flag,
            func_alias_loads,
            value_alias_loads,
            oracle: RefCell::new(oracle),
            throw_replay_sites: HashMap::new(),
            registry,
            config,
            sink_leaves,
            variadic_ops,
            param_seeds,
            global_sources,
            call_return_sources,
            source_cb_edges: source_cb_edges.clone(),
            module_import_sources,
            namespace_import_sources,
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
            zero_needed: FuncBitSet::default(),
            harness: build_harness_guard(module, harness_func),
            rev_gap_callers: HashMap::new(),
            module_slot_users: RefCell::new(None),
            module_var_readers: RefCell::new(HashMap::new()),
            global_reader_index: RefCell::new(None),
            global_readers: RefCell::new(HashMap::new()),
            heap_site_index: RefCell::new(None),
            heap_site_cone: RefCell::new(HashMap::new()),
            outside_site_cone: RefCell::new(HashMap::new()),
            harness_heap_escape: RefCell::new(None),
            lex_var_readers: RefCell::new(None),
            env_class_cone: RefCell::new(HashMap::new()),
            prop_touch_index: RefCell::new(None),
            prop_touch_cone: RefCell::new(HashMap::new()),
            prop_unknown_cone: RefCell::new(HashMap::new()),
            prop_write_cone: RefCell::new(HashMap::new()),
            this_ret_or_esc: RefCell::new(None),
            caller_ancestors: RefCell::new(HashMap::new()),
            caller_obs_memo: RefCell::new(HashMap::new()),
            site_local_escape_memo: RefCell::new(HashMap::new()),
            site_upward_escape_memo: RefCell::new(HashMap::new()),
            param_owner: RefCell::new(None),
            closed_param_memo: RefCell::new(HashMap::new()),
            closed_dispatch: RefCell::new(None),
            in_path_replay: false,
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
        let mut rev_gap_callers: HashMap<FuncId, Vec<FuncId>> = HashMap::new();
        for (&call_iid, callees) in &edges {
            if let Some(inst) = module.inst(call_iid)
                && let Some(caller_fid) = problem.links.func_of_block(inst.block)
            {
                for &cb in callees {
                    rev_gap_callers.entry(cb).or_default().push(caller_fid);
                }
            }
        }
        let mut harness_callee_set = FuncBitSet::new(module.functions.len());
        for &call_iid in &problem.harness.calls {
            for &c in callgraph.callees_of_call_at(call_iid) {
                let _ = harness_callee_set.set(c.index());
            }
            if let Some(cbs) = edges.get(&call_iid) {
                for &cb in cbs {
                    let _ = harness_callee_set.set(cb.index());
                }
            }
        }
        problem.harness.callee_set = harness_callee_set;
        problem.gap_edges = edges;
        problem.rev_gap_callers = rev_gap_callers;
        problem.gap_resolved = resolved;
        problem.gap_unresolved = unresolved;
        problem.zero_needed = problem.compute_zero_needed();
        problem
    }

    /// Release heavy points-to tables, liveness arrays, and cone caches prior to
    /// witness-path index construction (`#78`), retaining only compact replay state
    /// needed by [`Self::return_flow`] and [`Self::call_uncaught_exit_flow`].
    pub(crate) fn shrink_for_path_replay(
        &mut self,
        result: &abcd_analysis::dataflow::ifds::IfdsResult<Fact>,
    ) {
        let mut reached = FuncBitSet::new(self.module.functions.len());
        let mut reached_list = Vec::new();
        for &(_, target_node, _) in result.raw_path_edges() {
            if let Some(inst) = self.module.inst(target_node)
                && let Some(fid) = self.links.func_of_block(inst.block)
                && reached.set(fid.index())
            {
                reached_list.push(fid);
            }
        }
        let zero = Fact::Zero;
        for fid in reached_list {
            let Some(fd) = self.module.func(fid) else {
                continue;
            };
            for &b in &fd.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    let Some(inst) = self.module.inst(iid) else {
                        continue;
                    };
                    match &inst.op {
                        Op::Call { .. } => {
                            if !self.site_class.borrow().contains_key(&iid) {
                                let (cls, _) = self.compute_class(iid, true);
                                self.site_class.borrow_mut().insert(iid, cls);
                            }
                        }
                        Op::Throw { value } if result.has_non_zero_fact_at(iid, &zero) => {
                            let mut union_sites = {
                                let oracle = self.oracle.borrow();
                                let mut s = oracle.known_sites_at(*value, iid);
                                s.union_with(&oracle.may_sites_at(*value, iid));
                                s.union_with(&oracle.site_info_at(*value, iid).sites);
                                s
                            };
                            if let Some(fs) = self.fresh_result_site(*value) {
                                union_sites.insert(fs);
                            }
                            self.throw_replay_sites.insert((iid, *value), union_sites);
                        }
                        _ => {}
                    }
                }
            }
        }

        *self.oracle.borrow_mut() = Oracle::Rung0(Rung0AliasOracle::with_links_and_graph(
            self.module,
            &self.links,
            self.callgraph,
            self.harness.fid,
        ));
        self.singletons = None;
        self.prop_stores = ClassPropStores::default();
        self.global_stores = HashMap::new();
        self.static_lex_env = StaticLexEnvTable::empty();
        self.private_fields = PrivateFieldIndex::empty();
        self.variadic_ops = HashMap::new();
        self.liveness.clear();
        *self.value_keep_flag.borrow_mut() = Vec::new();
        *self.func_alias_loads.borrow_mut() = Vec::new();
        *self.value_alias_loads.borrow_mut() = HashMap::new();
        *self.module_slot_users.borrow_mut() = None;
        *self.module_var_readers.borrow_mut() = HashMap::new();
        *self.global_reader_index.borrow_mut() = None;
        *self.global_readers.borrow_mut() = HashMap::new();
        *self.heap_site_index.borrow_mut() = None;
        *self.heap_site_cone.borrow_mut() = HashMap::new();
        *self.outside_site_cone.borrow_mut() = HashMap::new();
        *self.harness_heap_escape.borrow_mut() = None;
        *self.lex_var_readers.borrow_mut() = None;
        *self.env_class_cone.borrow_mut() = HashMap::new();
        *self.prop_touch_index.borrow_mut() = None;
        *self.prop_touch_cone.borrow_mut() = HashMap::new();
        *self.prop_unknown_cone.borrow_mut() = HashMap::new();
        *self.prop_write_cone.borrow_mut() = HashMap::new();
        *self.this_ret_or_esc.borrow_mut() = None;
        *self.caller_ancestors.borrow_mut() = HashMap::new();
        *self.caller_obs_memo.borrow_mut() = HashMap::new();
        *self.site_local_escape_memo.borrow_mut() = HashMap::new();
        *self.site_upward_escape_memo.borrow_mut() = HashMap::new();
        *self.param_owner.borrow_mut() = None;
        *self.closed_param_memo.borrow_mut() = HashMap::new();
        *self.closed_dispatch.borrow_mut() = None;
        self.in_path_replay = true;
        *self.proto_memo.borrow_mut() = HashMap::new();
        *self.fresh_memo.borrow_mut() = HashMap::new();
        *self.counted.borrow_mut() = HashSet::new();
        *self.applied.borrow_mut() = Vec::new();
        *self.applied_seen.borrow_mut() = HashSet::new();
        self.rev_gap_callers = HashMap::new();
        self.zero_needed = FuncBitSet::default();
    }

    /// Compute the packed backward caller cone (`callgraph ∪ gap_edges`) of
    /// functions capable of generating `0 -> d` taint facts.
    fn compute_zero_needed(&self) -> FuncBitSet {
        let n_funcs = self.module.functions.len();
        if !self.config.seed_all_functions {
            return FuncBitSet::new_all_set(n_funcs);
        }
        let mut zero_needed = FuncBitSet::new(n_funcs);
        let mut queue: VecDeque<FuncId> = VecDeque::new();
        let mark = |fid: FuncId, zn: &mut FuncBitSet, q: &mut VecDeque<FuncId>| {
            if let Some(f) = self.module.func(fid)
                && !f.blocks.is_empty()
                && zn.set(fid.index())
            {
                q.push_back(fid);
            }
        };

        for &(fid, _) in &self.param_seeds {
            mark(fid, &mut zero_needed, &mut queue);
        }
        for &call_iid in &self.call_return_sources {
            if let Some(inst) = self.module.inst(call_iid)
                && let Some(fid) = self.links.func_of_block(inst.block)
            {
                mark(fid, &mut zero_needed, &mut queue);
            }
        }
        if !self.global_sources.is_empty()
            || !self.module_import_sources.is_empty()
            || !self.namespace_import_sources.is_empty()
        {
            for (fi, f) in self.module.functions.iter().enumerate() {
                if f.blocks.is_empty() || zero_needed.get(fi) {
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
                            Op::LoadPropDyn { object, key } => {
                                inst.result.is_some()
                                    && is_global_object(self.module, *object)
                                    && const_string_sym(self.module, *key)
                                        .is_some_and(|s| self.global_sources.contains(&s))
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
                            Op::GetModuleNamespace { index } => {
                                inst.result.is_some()
                                    && self.links.inst_class(self.module, iid).is_some_and(|cid| {
                                        self.namespace_import_sources
                                            .get(&(cid, *index))
                                            .is_some_and(|opt| {
                                                opt.as_ref().is_none_or(|syms| !syms.is_empty())
                                            })
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

        while let Some(curr) = queue.pop_front() {
            for &call_iid in self.callgraph.callers_of(curr) {
                if let Some(inst) = self.module.inst(call_iid)
                    && let Some(caller_fid) = self.links.func_of_block(inst.block)
                {
                    mark(caller_fid, &mut zero_needed, &mut queue);
                }
            }
            if let Some(gap_callers) = self.rev_gap_callers.get(&curr) {
                for &caller_fid in gap_callers {
                    mark(caller_fid, &mut zero_needed, &mut queue);
                }
            }
        }

        zero_needed
    }
}
