//! The taint driver: source/sink configuration, the IFDS run over the
//! call graph + rung-selected alias oracle (default rung-2 PTA), and the taint-path report.
//!
//! ## Configuration
//!
//! Sources and sinks are NAME-keyed (`design/analysis.md`: the
//! registry and the config key on `Sym`; the driver interns spec strings
//! per module so one config serves every module — corpus reality is that
//! ~97% of call sites are `UnknownCallees`, so name matching through
//! the global-load chain, [`crate::names`], is the mechanism that makes
//! sinks like `print` fire at all):
//!
//! - [`SourceSpec::FunctionParams`] — parameters of a named function
//!   (the smoke seeds all params of `func_main_0`, the abc module entry
//!   point: every module has one and its params are the classic
//!   "environment input" stand-in).
//! - [`SourceSpec::GlobalLoad`] — every `TryGetGlobal(name)` result is a
//!   source (e.g. a host-provided global).
//! - [`SinkSpec::Call`] — calls whose callee names resolve to `name`
//!   (through the global-load chain OR a resolved callee's
//!   [`abcd_ir::FunctionData::name`]).
//!
//! ## The report
//!
//! [`TaintReport`] carries every sink hit with: the sink site + its
//! `Inst.loc` line/column (T8), the tainted argument position, the fact,
//! the seed it derived from, a best-effort propagation path (backward
//! BFS over the solver's path-edge set — deterministic; documented as
//! approximate across call/return anchor switches), the applied-summary
//! log, and the registry miss counters.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::dataflow::Rung1AliasOracle;
use abcd_analysis::dataflow::heap::{DEFAULT_MAX_FIELD_CHAIN, Rung0AliasOracle};
use abcd_analysis::dataflow::ifds::{
    CallGraphOracle, IfdsConfig, IfdsProblem, IfdsResult, IfdsSolver,
};
use abcd_analysis::dataflow::pta::{PtaConfig, Rung2AliasOracle};
use abcd_analysis::module_link::{ModuleLinkTable, ModuleSlotRef};
use abcd_analysis::ohos_lifecycle::EntryModel;
use abcd_ir::{FuncId, InstId, Loc, Module, Op};

use crate::fact::{Fact, TaintFact, UNCAUGHT_EXCEPTION_VALUE};
use crate::gap::GapCallGraph;
use crate::names::{
    ClassPropStores, call_base_value, callee_name_candidates_indexed, quick_callee_leaf_sym,
    resolve_namespace_classes,
};
use crate::oracle::Oracle;
use crate::problem::{
    TaintProblem, is_global_object, resolve_global_sources, resolve_module_import_sources,
    resolve_namespace_import_sources,
};
use crate::summary::{RegistryStats, Summary, SummaryRegistry};

/// A taint source specification (name-keyed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceSpec {
    /// Parameters of every function with this name are tainted.
    /// `params: None` = all parameter slots (including the leading implicit
    /// `[func][new.target][this]` frame slots when present; see [`abcd_ir::frame`]).
    FunctionParams {
        /// The function name (`func_main_0` for module entry points).
        name: String,
        /// Specific parameter indices; `None` = all.
        params: Option<Vec<u16>>,
    },
    /// Every `TryGetGlobal(name)` result is tainted.
    GlobalLoad {
        /// The global's name.
        name: String,
    },
    /// Every call whose callee-name candidates match `name` taints its return
    /// value (and, when invoked with a trailing `(err, data)` / `(data)`
    /// callback closure, enters taint onto the callback's data parameter).
    CallReturn {
        /// Canonical or qualified callee name (e.g.
        /// `"@ohos.pasteboard.SystemPasteboard.getData"`).
        name: String,
    },
    /// Every ES module import binding from `specifier` (optionally restricted
    /// to `import_name`) is tainted at load.
    ModuleImport {
        /// Module specifier (e.g. `"@ohos.deviceInfo"` or `"./secret"`).
        specifier: String,
        /// Exported binding name; `None` matches all bindings from `specifier`.
        import_name: Option<String>,
    },
}

/// A taint sink specification (name-keyed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SinkSpec {
    /// A call whose callee-name candidates include `name`.
    Call {
        /// The callee name (bare global like `print`, or qualified like
        /// `console.log`).
        name: String,
    },
}

/// Driver configuration.
#[derive(Clone, Debug)]
pub struct TaintConfig {
    /// Sources.
    pub sources: Vec<SourceSpec>,
    /// Sinks.
    pub sinks: Vec<SinkSpec>,
    /// Register the top-20 corpus builtins (default true).
    pub builtin_summaries: bool,
    /// Additional user summaries `(name, arity, summary)`.
    pub extra_summaries: Vec<(String, Option<usize>, Summary)>,
    /// Seed every function with the zero fact (dummy-main coverage:
    /// functions unreachable from the sources through the call graph are
    /// still analyzed for global-source tagging). Default true.
    pub seed_all_functions: bool,
    /// Propagate return flows past initial seeds (unbalanced returns). Default true.
    pub follow_returns_past_seeds: bool,
    /// The native/unknown fallback's identity heuristic: tainted
    /// operand ⇒ tainted return. Default true.
    pub native_identity: bool,
    /// The access-path k-limit (default
    /// [`DEFAULT_MAX_FIELD_CHAIN`] = 5).
    pub max_field_chain: usize,
    /// The alias-oracle rung (`design/analysis.md`): 0 = local
    /// def chains; 1 = the on-demand backward `points_to` engine
    /// (memoized, depth-capped, rung-0 fallback) plus the points_to-fed
    /// call-graph refinement; 2 = the whole-module context-sensitive
    /// PTA (1-call-site contexts, field-sensitive, on-the-fly
    /// call-graph co-evolution — the call graph the solver runs against
    /// is the PTA's own). Default 2; 0/1 stay selectable for A/B/C
    /// measurement in the probe runner.
    pub alias_rung: u8,
    /// Override for the rung-2 PTA's propagation-step budget
    /// ([`abcd_analysis::dataflow::pta::PtaConfig::step_budget`]);
    /// `None` (the default) uses the engine default. A budget cut
    /// degrades the run to the rung-1 pipeline, recorded loudly in
    /// [`TaintReport::alias_rung_used`] — the knob exists so operators
    /// facing a pathological module (and tests pinning the degrade arm)
    /// can exercise it without a 25M-step module.
    pub pta_step_budget: Option<usize>,
    /// Synthesize OpenHarmony Stage/FA Ability, ExtensionAbility, ArkUI `ViewPU`,
    /// and multi-record `func_main_0` lifecycle harness when applicable
    /// (default `true`; no-op on plain single-module JS inputs).
    pub ohos_lifecycle: bool,
    /// Optional `module.json` / `config.json` text for `srcEntry` discovery.
    pub manifest_json: Option<String>,
}

impl Default for TaintConfig {
    fn default() -> Self {
        TaintConfig {
            sources: Vec::new(),
            sinks: Vec::new(),
            builtin_summaries: true,
            extra_summaries: Vec::new(),
            seed_all_functions: true,
            follow_returns_past_seeds: true,
            native_identity: true,
            max_field_chain: DEFAULT_MAX_FIELD_CHAIN,
            alias_rung: 2,
            pta_step_budget: None,
            ohos_lifecycle: true,
            manifest_json: None,
        }
    }
}

/// One step of a reported taint path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathStep {
    /// The instruction.
    pub inst: InstId,
    /// Its source location (T8), when the source carried line info.
    pub loc: Option<Loc>,
    /// A short op-kind tag (the `Op` variant name).
    pub op: String,
}

/// One source→sink hit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SinkHit {
    /// The sink name that matched.
    pub sink: String,
    /// The sink call instruction.
    pub call: InstId,
    /// Its source location (T8).
    pub loc: Option<Loc>,
    /// Which call operand carried the taint (`arg N`, `this`, `base`,
    /// `callee`).
    pub position: String,
    /// The taint fact at the sink.
    pub fact: TaintFact,
    /// The seed the flow derived from `(anchor function, seed fact)`.
    pub seed: (FuncId, Fact),
    /// The propagation path, seed-first (best-effort; see module docs).
    pub path: Vec<PathStep>,
}

/// The analysis result.
#[derive(Clone, Debug)]
pub struct TaintReport {
    /// Sink hits, in deterministic order (`InstId`, position, fact).
    pub hits: Vec<SinkHit>,
    /// The summary/fallback counters.
    pub stats: RegistryStats,
    /// `(call site, summary name)` in application order.
    pub summaries_applied: Vec<(InstId, String)>,
    /// Summary hits by NAME (resolved; aggregation-safe across modules).
    pub summary_hits: std::collections::BTreeMap<String, usize>,
    /// Named misses by NAME — the "report missing" backlog
    /// (aggregation-safe across modules).
    pub summary_misses: std::collections::BTreeMap<String, usize>,
    /// Total propagated path edges (solver work).
    pub path_edges: usize,
    /// Callback-gap counters: callback-summary call sites whose
    /// callback value resolved to user bodies (the full gap propagator
    /// entered them).
    pub gap_sites_resolved: usize,
    /// Callback-summary sites whose callback value did NOT resolve —
    /// the honest fallback (mini-gap tag only; `gap.rs` module docs).
    pub gap_sites_unresolved: usize,
    /// The alias rung the analysis actually ran at (rung 2 degrades to
    /// rung 1 when the PTA's step budget cuts — loud, never silent).
    pub alias_rung_used: u8,
    /// Whether the rung-2 PTA ran in demand-driven root-sliced mode (`false`
    /// unless rung 2 ran without budget degradation and `pta_stats.root_sliced`
    /// was set).
    pub pta_root_sliced: bool,
}

/// Run the taint analysis over `module`.
pub fn run_taint(module: &Module, config: &TaintConfig) -> TaintReport {
    run_taint_full(module, config).0
}

const PTA_SLICE_FUNC_THRESHOLD: usize = 512;

fn is_const_operand(module: &Module, val: abcd_ir::ValueId) -> bool {
    let peeled = abcd_analysis::dataflow::heap::peel_movs(module, val);
    match module.value(peeled).map(|v| v.def) {
        Some(abcd_ir::ValueDef::Const(_)) => true,
        Some(abcd_ir::ValueDef::Inst(iid)) => {
            matches!(module.inst(iid).map(|i| &i.op), Some(Op::LoadConst(_)))
        }
        _ => false,
    }
}

/// Compute demand-driven PTA entry roots on large bundles (`> 512` functions),
/// or `None` when whole-module PTA should run.
fn compute_pta_roots(
    module: &Module,
    links: &ModuleLinkTable,
    prop_stores: &ClassPropStores,
    base_graph: &CallGraph,
    config: &TaintConfig,
    harness_fid: Option<FuncId>,
) -> Option<Vec<FuncId>> {
    if module.functions.len() <= PTA_SLICE_FUNC_THRESHOLD {
        return None;
    }
    let has_wildcard_params = config
        .sources
        .iter()
        .any(|s| matches!(s, SourceSpec::FunctionParams { name, .. } if name == "*"));
    if has_wildcard_params {
        return None;
    }

    let n_funcs = module.functions.len();
    let mut is_gen = vec![false; n_funcs];

    for spec in &config.sources {
        if let SourceSpec::FunctionParams { name, params } = spec {
            for (fi, f) in module.functions.iter().enumerate() {
                if module.sym.resolve(f.name) == Some(name.as_str()) {
                    let has_param = match params {
                        Some(indices) => indices.iter().any(|&i| (i as usize) < f.params.len()),
                        None => !f.params.is_empty(),
                    };
                    if has_param {
                        is_gen[fi] = true;
                    }
                }
            }
        }
    }

    let global_sources = resolve_global_sources(module, config);
    let module_import_sources = resolve_module_import_sources(module, links, config);
    let namespace_import_sources = resolve_namespace_import_sources(module, links, config);
    if !global_sources.is_empty()
        || !module_import_sources.is_empty()
        || !namespace_import_sources.is_empty()
    {
        for (fi, f) in module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if is_gen[fi] || f.blocks.is_empty() || Some(fid) == harness_fid {
                continue;
            }
            'scan_fn: for &b in &f.blocks {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    let hit =
                        match &inst.op {
                            Op::TryGetGlobal { name, .. } => {
                                inst.result.is_some() && global_sources.contains(name)
                            }
                            Op::LoadProp { object, name } => {
                                inst.result.is_some()
                                    && global_sources.contains(name)
                                    && is_global_object(module, *object)
                            }
                            Op::LoadModuleVar { index, kind } => {
                                inst.result.is_some()
                                    && !kind.is_local()
                                    && links.inst_class(module, iid).is_some_and(|cid| {
                                        module_import_sources.get(&(cid, *index)).is_some_and(
                                            |opt| opt.as_ref().is_none_or(|syms| !syms.is_empty()),
                                        )
                                    })
                            }
                            Op::GetModuleNamespace { index } => {
                                inst.result.is_some()
                                    && links.inst_class(module, iid).is_some_and(|cid| {
                                        namespace_import_sources.get(&(cid, *index)).is_some_and(
                                            |opt| opt.as_ref().is_none_or(|syms| !syms.is_empty()),
                                        )
                                    })
                            }
                            _ => false,
                        };
                    if hit {
                        is_gen[fi] = true;
                        break 'scan_fn;
                    }
                }
            }
        }
    }

    let call_source_names: HashSet<&str> = config
        .sources
        .iter()
        .filter_map(|s| match s {
            SourceSpec::CallReturn { name } => Some(name.as_str()),
            _ => None,
        })
        .collect();

    let mut proxy_classes = vec![false; module.classes.len()];
    let mut any_proxy_class = false;

    if !call_source_names.is_empty() || config.ohos_lifecycle {
        let mut wanted_leaves: HashSet<&str> = call_source_names
            .iter()
            .map(|s| s.rsplit('.').next().unwrap_or(s))
            .collect();
        if config.ohos_lifecycle {
            wanted_leaves.insert("registerJavaScriptProxy");
        }
        let rung0 = Oracle::Rung0(Rung0AliasOracle::new(module));
        for (call, edge) in base_graph.sites() {
            if Some(edge.caller) == harness_fid {
                continue;
            }
            let Some(inst) = module.inst(call) else {
                continue;
            };
            let Op::Call { callee, args, .. } = &inst.op else {
                continue;
            };
            if let Some(leaf_sym) =
                quick_callee_leaf_sym(module, links, prop_stores, edge.caller, *callee)
            {
                let direct_match = module
                    .sym
                    .resolve(leaf_sym)
                    .map(|s| s.rsplit('.').next().unwrap_or(s))
                    .is_some_and(|l| wanted_leaves.contains(l));
                let resolved_match = !direct_match
                    && base_graph.callees_of_call_at(call).iter().any(|f| {
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
                links,
                Some(prop_stores),
                edge.caller,
                *callee,
            );
            for f in base_graph.callees_of_call_at(call) {
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
                if let Some(slot) = is_gen.get_mut(edge.caller.index()) {
                    *slot = true;
                }
                if let Some(&last_arg) = args.last() {
                    for cb in crate::gap::resolve_callback_funcs(module, &rung0, last_arg, call) {
                        if let Some(slot) = is_gen.get_mut(cb.index()) {
                            *slot = true;
                        }
                    }
                }
            }
            if config.ohos_lifecycle
                && cands
                    .iter()
                    .any(|c| c == "@ohos.web.webview.WebviewController.registerJavaScriptProxy")
            {
                if let Some(slot) = is_gen.get_mut(edge.caller.index()) {
                    *slot = true;
                }
                if let Some(cid) = links.func_class(edge.caller)
                    && let Some(cslot) = proxy_classes.get_mut(cid.index())
                {
                    *cslot = true;
                    any_proxy_class = true;
                }
            }
        }
    }

    if any_proxy_class {
        for (fi, f) in module.functions.iter().enumerate() {
            if proxy_classes
                .get(f.class_id.index())
                .copied()
                .unwrap_or(false)
            {
                is_gen[fi] = true;
            }
        }
    }

    // Mark Ability / ExtensionAbility lifecycle methods invoked with non-const
    // `want` inside `harness_fid` (plus sibling lifecycle calls sharing `this`).
    if let Some(hfid) = harness_fid
        && let Some(hfd) = module.func(hfid)
    {
        let mut active_this: HashSet<abcd_ir::ValueId> = HashSet::new();
        for &b in &hfd.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                if let Some(Op::Call { this, args, .. }) = module.inst(iid).map(|i| &i.op)
                    && args.iter().any(|&a| !is_const_operand(module, a))
                    && let Some(t) = this
                {
                    active_this.insert(*t);
                }
            }
        }
        for &b in &hfd.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                if let Some(Op::Call { this, args, .. }) = module.inst(iid).map(|i| &i.op) {
                    let has_non_const = args.iter().any(|&a| !is_const_operand(module, a));
                    let shares_this = this.is_some_and(|t| active_this.contains(&t));
                    if has_non_const || shares_this {
                        for &callee in base_graph.callees_of_call_at(iid) {
                            if let Some(slot) = is_gen.get_mut(callee.index()) {
                                *slot = true;
                            }
                        }
                    }
                }
            }
        }
    }

    const MAX_PTA_BACKWARD_HOPS: u8 = 2;
    const MAX_PTA_FAN_IN: usize = 64;
    let backward_closure = |seeds: &[bool]| -> Vec<bool> {
        let mut visited = vec![false; n_funcs];
        let mut queue: VecDeque<(FuncId, u8)> = VecDeque::new();
        for (fi, &seeded) in seeds.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if seeded && Some(fid) != harness_fid {
                visited[fi] = true;
                queue.push_back((fid, 0));
            }
        }
        while let Some((curr, hops)) = queue.pop_front() {
            if hops >= MAX_PTA_BACKWARD_HOPS {
                continue;
            }
            let callers = base_graph.callers_of(curr);
            if callers.len() > MAX_PTA_FAN_IN {
                continue;
            }
            for &call_iid in callers {
                if let Some(caller) = links.inst_func(module, call_iid)
                    && Some(caller) != harness_fid
                    && let Some(slot) = visited.get_mut(caller.index())
                    && !*slot
                {
                    *slot = true;
                    queue.push_back((caller, hops + 1));
                }
            }
        }
        visited
    };

    let b_cone_gen = backward_closure(&is_gen);
    let mut keep_func = b_cone_gen.clone();

    let n_classes = module.classes.len();
    let mut gen_cls = vec![false; n_classes];
    for (fi, &g) in is_gen.iter().enumerate() {
        let fid = FuncId::new(fi as u32);
        if g && Some(fid) != harness_fid
            && let Some(cid) = links.func_class(fid)
            && let Some(slot) = gen_cls.get_mut(cid.index())
        {
            *slot = true;
        }
    }

    let b_cone_count = b_cone_gen.iter().filter(|&&b| b).count();
    let mut init_main_cls = gen_cls.clone();
    if b_cone_count <= 128 {
        for (fi, &in_gen_cone) in b_cone_gen.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if in_gen_cone
                && Some(fid) != harness_fid
                && let Some(cid) = links.func_class(fid)
                && let Some(slot) = init_main_cls.get_mut(cid.index())
            {
                *slot = true;
            }
        }
    }

    let mut gen_export_funcs = is_gen.clone();
    for (fi, f) in module.functions.iter().enumerate() {
        if !f.is_external
            && !f.blocks.is_empty()
            && module.sym.resolve(f.name) == Some("func_main_0")
        {
            if init_main_cls
                .get(f.class_id.index())
                .copied()
                .unwrap_or(false)
            {
                keep_func[fi] = true;
            }
            if gen_cls.get(f.class_id.index()).copied().unwrap_or(false) {
                gen_export_funcs[fi] = true;
            }
        }
    }

    let mut exported_slots: HashSet<ModuleSlotRef> = HashSet::new();
    for (fi, &src_fn) in gen_export_funcs.iter().enumerate() {
        let fid = FuncId::new(fi as u32);
        if !src_fn || Some(fid) == harness_fid {
            continue;
        }
        let Some(f) = module.func(fid) else {
            continue;
        };
        for &b in &f.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                if let Some(Op::StoreModuleVar { index, .. }) = module.inst(iid).map(|i| &i.op) {
                    exported_slots.insert(ModuleSlotRef {
                        class_id: f.class_id,
                        slot: *index,
                    });
                }
            }
        }
    }

    let mut viewpu_cls = gen_cls.clone();
    if !exported_slots.is_empty() {
        let mut slot_to_readers: BTreeMap<ModuleSlotRef, Vec<FuncId>> = BTreeMap::new();
        let mut push_reader = |sr: ModuleSlotRef, fid: FuncId| {
            let list = slot_to_readers.entry(sr).or_default();
            if list.last() != Some(&fid) {
                list.push(fid);
            }
        };
        for (fi, f) in module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if f.blocks.is_empty() || Some(fid) == harness_fid {
                continue;
            }
            for &b in &f.blocks {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    match &inst.op {
                        Op::LoadModuleVar { index, kind } => {
                            if kind.is_local() {
                                let sr = ModuleSlotRef {
                                    class_id: f.class_id,
                                    slot: *index,
                                };
                                if exported_slots.contains(&sr) {
                                    push_reader(sr, fid);
                                }
                            } else if let Some(t) = links.external_load(f.class_id, *index) {
                                for &sr in &t.slots {
                                    if exported_slots.contains(&sr) {
                                        push_reader(sr, fid);
                                    }
                                }
                            }
                        }
                        Op::LoadProp { object, name } => {
                            for ns_cid in resolve_namespace_classes(module, links, fid, *object) {
                                if let Some(slots) =
                                    links.namespace_exports(ns_cid).and_then(|m| m.get(name))
                                {
                                    for &sr in slots {
                                        if exported_slots.contains(&sr) {
                                            push_reader(sr, fid);
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
        let mut slot_readers = vec![false; n_funcs];
        let mut any_slot_reader = false;
        for readers in slot_to_readers.values() {
            if readers.len() <= MAX_PTA_FAN_IN {
                for &fid in readers {
                    slot_readers[fid.index()] = true;
                    any_slot_reader = true;
                    if let Some(cid) = links.func_class(fid)
                        && let Some(cslot) = viewpu_cls.get_mut(cid.index())
                    {
                        *cslot = true;
                    }
                }
            }
        }
        if any_slot_reader {
            let reader_cone = backward_closure(&slot_readers);
            let mut reader_cls = vec![false; n_classes];
            for (fi, &in_rcone) in reader_cone.iter().enumerate() {
                if in_rcone {
                    keep_func[fi] = true;
                    if let Some(cid) = links.func_class(FuncId::new(fi as u32))
                        && let Some(cslot) = reader_cls.get_mut(cid.index())
                    {
                        *cslot = true;
                    }
                }
            }
            for (fi, f) in module.functions.iter().enumerate() {
                if !f.is_external
                    && !f.blocks.is_empty()
                    && reader_cls.get(f.class_id.index()).copied().unwrap_or(false)
                    && module.sym.resolve(f.name) == Some("func_main_0")
                {
                    keep_func[fi] = true;
                }
            }
        }
    }

    // Include `ViewPU` / component lifecycle & `@Builder` methods called by
    // `harness_fid` when their owning class is in `gen_cls` or reads a low-fan-in
    // exported slot from `gen_cls`.
    if let Some(hfid) = harness_fid
        && let Some(hfd) = module.func(hfid)
    {
        for &b in &hfd.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                if matches!(module.inst(iid).map(|i| &i.op), Some(Op::Call { .. })) {
                    for &callee in base_graph.callees_of_call_at(iid) {
                        if links.func_class(callee).is_some_and(|cid| {
                            viewpu_cls.get(cid.index()).copied().unwrap_or(false)
                        }) && let Some(slot) = keep_func.get_mut(callee.index())
                        {
                            *slot = true;
                        }
                    }
                }
            }
        }
    }

    // Global-store bridge: if any `is_gen` or `gen_cls` `func_main_0` writes
    // symbol `g` with `<= 64` readers, include those readers (plus their bounded
    // caller cone and owning `func_main_0`) in `keep_func`.
    let mut stored_globals: HashSet<abcd_ir::Sym> = HashSet::new();
    for (fi, &src_fn) in gen_export_funcs.iter().enumerate() {
        let fid = FuncId::new(fi as u32);
        if !src_fn || Some(fid) == harness_fid {
            continue;
        }
        let Some(f) = module.func(fid) else {
            continue;
        };
        for &b in &f.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                match module.inst(iid).map(|i| &i.op) {
                    Some(
                        Op::StoreGlobal { name, .. }
                        | Op::StoreGlobalRecord { name, .. }
                        | Op::TryStoreGlobal { name, .. },
                    ) => {
                        stored_globals.insert(*name);
                    }
                    Some(
                        Op::StoreProp { object, name, .. }
                        | Op::StoreOwnPropName { object, name, .. },
                    ) if is_global_object(module, *object) => {
                        stored_globals.insert(*name);
                    }
                    _ => {}
                }
            }
        }
    }
    if !stored_globals.is_empty() {
        let mut glob_to_readers: BTreeMap<abcd_ir::Sym, Vec<FuncId>> = BTreeMap::new();
        for (fi, f) in module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if f.blocks.is_empty() || Some(fid) == harness_fid {
                continue;
            }
            for &b in &f.blocks {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    match module.inst(iid).map(|i| &i.op) {
                        Some(Op::TryGetGlobal { name, .. }) if stored_globals.contains(name) => {
                            let list = glob_to_readers.entry(*name).or_default();
                            if list.last() != Some(&fid) {
                                list.push(fid);
                            }
                        }
                        Some(Op::LoadProp { object, name })
                            if stored_globals.contains(name)
                                && is_global_object(module, *object) =>
                        {
                            let list = glob_to_readers.entry(*name).or_default();
                            if list.last() != Some(&fid) {
                                list.push(fid);
                            }
                        }
                        Some(
                            Op::LoadPropDyn { object, .. }
                            | Op::LoadPropIdx { object, .. }
                            | Op::CopyDataProps { src: object, .. }
                            | Op::CreateObjectWithExcludedKeys { obj: object, .. },
                        ) if is_global_object(module, *object) => {
                            for &g in &stored_globals {
                                let list = glob_to_readers.entry(g).or_default();
                                if list.last() != Some(&fid) {
                                    list.push(fid);
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        let mut global_readers = vec![false; n_funcs];
        let mut any_reader = false;
        for readers in glob_to_readers.values() {
            if readers.len() <= MAX_PTA_FAN_IN {
                for &fid in readers {
                    if !keep_func[fid.index()] {
                        global_readers[fid.index()] = true;
                        any_reader = true;
                    }
                }
            }
        }
        if any_reader {
            let reader_cone = backward_closure(&global_readers);
            let mut reader_cls = vec![false; n_classes];
            for (fi, &in_rcone) in reader_cone.iter().enumerate() {
                if in_rcone {
                    keep_func[fi] = true;
                    if let Some(cid) = links.func_class(FuncId::new(fi as u32))
                        && let Some(cslot) = reader_cls.get_mut(cid.index())
                    {
                        *cslot = true;
                    }
                }
            }
            for (fi, f) in module.functions.iter().enumerate() {
                if !f.is_external
                    && !f.blocks.is_empty()
                    && reader_cls.get(f.class_id.index()).copied().unwrap_or(false)
                    && module.sym.resolve(f.name) == Some("func_main_0")
                {
                    keep_func[fi] = true;
                }
            }
        }
    }

    if let Some(hfid) = harness_fid
        && let Some(slot) = keep_func.get_mut(hfid.index())
    {
        *slot = true;
    }

    let roots: Vec<FuncId> = keep_func
        .iter()
        .enumerate()
        .filter_map(|(fi, &keep)| keep.then_some(FuncId::new(fi as u32)))
        .collect();
    Some(roots)
}

/// Run the analysis, also returning the raw solver result (for tests
/// that assert on facts at arbitrary program points).
pub fn run_taint_full(module: &Module, config: &TaintConfig) -> (TaintReport, IfdsResult<Fact>) {
    let orig_func_len = module.functions.len();
    let orig_inst_len = module.insts.len();
    let entry_model = config
        .ohos_lifecycle
        .then(|| EntryModel::build(module, config.manifest_json.as_deref()));
    let harness_fid = entry_model.as_ref().and_then(|em| em.harness_func);
    let has_augmented = entry_model
        .as_ref()
        .is_some_and(|em| em.augmented_module.is_some());
    let work_mod: &Module = entry_model
        .as_ref()
        .map_or(module, |em| em.active_module(module));

    let links = ModuleLinkTable::build(work_mod);
    let prop_stores = ClassPropStores::build(work_mod);
    let base_graph = CallGraph::build_with_links(work_mod, &links);
    // The alias ladder (`design/analysis.md`):
    // - rung 0 solves against the base graph with def-chain answers;
    // - rung 1 builds the on-demand engine over the BASE graph and
    //   refines the graph once with the engine's points_to (one
    //   engine, two consumers; one pass, no fixed point);
    // - rung 2 runs the k=1 PTA (root-sliced on large >512-function
    //   bundles): its co-evolution fixed point IS the call graph the
    //   solver runs against, and its fixed-point tables are the oracle.
    //   A step-budget cut degrades to the rung-1 pipeline, recorded in
    //   `alias_rung_used` (loud, never silent).
    let rung1_pipeline = || {
        let engine = Rung1AliasOracle::new(work_mod, &base_graph);
        let refined = CallGraph::refine_with_points_to(work_mod, &base_graph, &engine);
        (refined, Oracle::Rung1(engine), 1u8)
    };
    let (refined, oracle, rung_used, pta_root_sliced) = match config.alias_rung {
        0 => (
            None,
            Oracle::Rung0(Rung0AliasOracle::new(work_mod)),
            0u8,
            false,
        ),
        2 => {
            let pta_config = PtaConfig {
                step_budget: config
                    .pta_step_budget
                    .unwrap_or(abcd_analysis::dataflow::pta::DEFAULT_STEP_BUDGET),
                harness_func: harness_fid,
                ..PtaConfig::default()
            };
            let pta_roots = compute_pta_roots(
                work_mod,
                &links,
                &prop_stores,
                &base_graph,
                config,
                harness_fid,
            );
            let outcome = abcd_analysis::dataflow::pta::analyze_with_links_and_roots(
                work_mod,
                &links,
                &base_graph,
                &pta_config,
                pta_roots.as_deref(),
            );
            if outcome.stats().capped {
                let (g, o, u) = rung1_pipeline();
                (Some(g), o, u, false)
            } else {
                let (graph, tables, stats) = outcome.into_parts();
                let root_sliced = stats.root_sliced;
                (
                    Some(graph),
                    Oracle::Rung2(Rung2AliasOracle::new(work_mod, tables, stats)),
                    2u8,
                    root_sliced,
                )
            }
        }
        _ => {
            let (g, o, u) = rung1_pipeline();
            (Some(g), o, u, false)
        }
    };
    let callgraph: &CallGraph = refined.as_ref().unwrap_or(&base_graph);
    let mut registry = if config.builtin_summaries {
        SummaryRegistry::with_builtins()
    } else {
        SummaryRegistry::new()
    };
    for (name, arity, summary) in &config.extra_summaries {
        registry.register(name, *arity, summary.clone());
    }

    let problem = TaintProblem::new_with_indexed(
        work_mod,
        links,
        prop_stores,
        callgraph,
        oracle,
        &registry,
        config,
        harness_fid,
    );
    // Callback-gap layer: the eager scan's callback edges ride the
    // solver's call-graph oracle (the base graph itself is untouched —
    // sink collection and path reconstruction keep consuming it).
    let gap_graph = GapCallGraph::new(callgraph, problem.gap_edges());
    let solver = IfdsSolver::new(
        work_mod,
        &problem,
        &gap_graph,
        IfdsConfig {
            follow_returns_past_seeds: config.follow_returns_past_seeds,
        },
    );
    let result = solver.solve();

    let hits = collect_hits(work_mod, &problem, config, callgraph, &result);
    let applied = problem
        .applied_summaries()
        .into_iter()
        .filter(|(iid, _)| iid.index() < orig_inst_len)
        .collect();
    let (gap_sites_resolved, gap_sites_unresolved) = problem.gap_counts();
    let stats = registry.stats();
    let resolve_map = |m: &std::collections::BTreeMap<abcd_ir::Sym, usize>| {
        m.iter()
            .map(|(s, n)| (registry.resolve(*s).unwrap_or_default(), *n))
            .collect()
    };
    let mut report = TaintReport {
        hits,
        summary_hits: resolve_map(&stats.hits),
        summary_misses: resolve_map(&stats.misses_named),
        stats,
        summaries_applied: applied,
        path_edges: result.path_edge_count(),
        gap_sites_resolved,
        gap_sites_unresolved,
        alias_rung_used: rung_used,
        pta_root_sliced,
    };
    report.hits.retain(|h| h.call.index() < orig_inst_len);
    if !report.hits.is_empty() {
        let path_index = PathIndex::build(work_mod, &result);
        for hit in &mut report.hits {
            let (mut seed, mut path) =
                reconstruct_path(work_mod, &problem, &gap_graph, &result, &path_index, hit);
            if has_augmented {
                path.retain(|step| step.inst.index() < orig_inst_len);
                if path.is_empty()
                    && let Some(inst) = module.inst(hit.call)
                {
                    path.push(PathStep {
                        inst: hit.call,
                        loc: inst.loc,
                        op: op_tag(&inst.op),
                    });
                }
                if seed.0.index() >= orig_func_len {
                    let first_inst = path.first().map(|s| s.inst).unwrap_or(hit.call);
                    let user_func = path_index
                        .func_of_inst(module, first_inst)
                        .filter(|f| f.index() < orig_func_len)
                        .unwrap_or(FuncId::new(0));
                    seed = (user_func, Fact::Zero);
                }
            }
            hit.seed = seed;
            hit.path = path;
        }
        report.hits.sort_by(|a, b| {
            (a.call, &a.position, &a.fact, &a.sink).cmp(&(b.call, &b.position, &a.fact, &b.sink))
        });
    }
    (report, result)
}

/// Scan call sites for sink matches with tainted operands.
fn collect_hits(
    module: &Module,
    problem: &TaintProblem<'_>,
    config: &TaintConfig,
    callgraph: &CallGraph,
    result: &IfdsResult<Fact>,
) -> Vec<SinkHit> {
    if config.sinks.is_empty() {
        return Vec::new();
    }
    let zero = Fact::Zero;
    let mut hits = Vec::new();
    for (iid, edge) in callgraph.sites() {
        let facts = result.facts_at(iid, &zero);
        if facts.is_empty() {
            continue;
        }
        let Some(inst) = module.inst(iid) else {
            continue;
        };
        let Op::Call {
            callee, this, args, ..
        } = &inst.op
        else {
            continue;
        };
        let mut names = callee_name_candidates_indexed(
            module,
            problem.links(),
            Some(problem.prop_stores()),
            edge.caller,
            *callee,
        );
        for f in callgraph.callees_of_call_at(iid) {
            if let Some(fd) = module.func(*f)
                && let Some(n) = module.sym.resolve(fd.name)
                && !names.iter().any(|x| x == n)
            {
                names.push(n.to_owned());
            }
        }
        for sink in &config.sinks {
            let SinkSpec::Call { name } = sink;
            if !names.iter().any(|n| n == name) {
                continue;
            }
            let base = call_base_value(module, inst);
            for fact in &facts {
                let Fact::Taint(tf) = &fact else { continue };
                let position = if let Some(pos) = args
                    .iter()
                    .position(|&a| problem.operand_matches_fact(a, tf, iid))
                {
                    format!("arg {pos}")
                } else if this.is_some_and(|t| problem.operand_matches_fact(t, tf, iid)) {
                    "this".to_owned()
                } else if base.is_some_and(|b| problem.operand_matches_fact(b, tf, iid)) {
                    "base".to_owned()
                } else if problem.operand_matches_fact(*callee, tf, iid) {
                    "callee".to_owned()
                } else {
                    continue; // unrelated fact at the call node
                };
                hits.push(SinkHit {
                    sink: name.clone(),
                    call: iid,
                    loc: inst.loc,
                    position,
                    fact: tf.clone(),
                    seed: (FuncId::new(0), Fact::Zero), // filled by reconstruct
                    path: Vec::new(),                   // filled by reconstruct
                });
            }
        }
    }
    hits
}

/// Instruction predecessors for path reconstruction: the previous
/// instruction in the block, the last instruction of each normal predecessor
/// block, or the throwing instructions of each exceptional predecessor block.
fn inst_preds(module: &Module, index: &PathIndex, inst: InstId) -> Vec<InstId> {
    let Some(i) = module.inst(inst) else {
        return Vec::new();
    };
    let Some(block) = module.block(i.block) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let pos = index
        .inst_pos_in_block
        .get(inst.index())
        .copied()
        .filter(|&p| {
            p != u32::MAX && (p as usize) < block.insts.len() && block.insts[p as usize] == inst
        })
        .map(|p| p as usize)
        .or_else(|| block.insts.iter().position(|&x| x == inst));
    if let Some(pos) = pos
        && pos > 0
    {
        out.push(block.insts[pos - 1]);
        return out;
    }
    for pred in &block.preds {
        let Some(pb) = module.block(pred.from) else {
            continue;
        };
        match pred.kind {
            abcd_ir::EdgeKind::Normal => {
                if let Some(&last) = pb.insts.last() {
                    out.push(last);
                }
            }
            abcd_ir::EdgeKind::Exceptional => {
                let before = out.len();
                for &iid in &pb.insts {
                    if module
                        .inst(iid)
                        .is_some_and(|pi| pi.op.effects_in(module).may_throw)
                    {
                        out.push(iid);
                    }
                }
                if out.len() == before
                    && let Some(&last) = pb.insts.last()
                {
                    out.push(last);
                }
            }
        }
    }
    out
}

const NO_EDGE: u32 = u32::MAX;

/// Indices over the path-edge set for backward reconstruction.
struct PathIndex {
    /// Dense `BlockId::index() -> Option<FuncId>` owning-function index.
    block_to_func: Vec<Option<FuncId>>,
    /// Dense `InstId::index() -> u32` instruction position in its block (`u32::MAX` if unplaced).
    inst_pos_in_block: Vec<u32>,
    /// `InstId::index() -> first edge index` (`NO_EDGE` when empty).
    head_by_node: Vec<u32>,
    /// `edge_idx -> next edge index` sharing the same `target_node` (`NO_EDGE` at tail).
    next_edge: Vec<u32>,
    /// start point → function.
    func_of_sp: HashMap<InstId, FuncId>,
    /// handler entry block's first instruction → catch `ExceptionParam` value.
    handler_entry_exc: HashMap<InstId, abcd_ir::ValueId>,
    /// function → exit instructions (Return/Throw).
    exits_of: HashMap<FuncId, Vec<InstId>>,
    /// function → unprotected call sites (`!has_catch_all`) that may propagate uncaught exceptions.
    uncaught_calls_of: HashMap<FuncId, Vec<InstId>>,
    /// return site → call instructions it is a return site of.
    calls_at_return_site: HashMap<InstId, Vec<InstId>>,
}

impl PathIndex {
    fn build(module: &Module, result: &IfdsResult<Fact>) -> Self {
        let mut inst_pos_in_block = vec![u32::MAX; module.insts.len()];
        for bb in &module.blocks {
            for (pos, &iid) in bb.insts.iter().enumerate() {
                if let Some(slot) = inst_pos_in_block.get_mut(iid.index()) {
                    *slot = pos as u32;
                }
            }
        }

        let mut block_to_func = vec![None; module.blocks.len()];
        for (fi, f) in module.functions.iter().enumerate() {
            let func = FuncId::new(fi as u32);
            for &b in &f.blocks {
                if let Some(slot) = block_to_func.get_mut(b.index()) {
                    slot.get_or_insert(func);
                }
            }
        }

        let edges = result.raw_path_edges();
        let mut head_by_node = vec![NO_EDGE; module.insts.len()];
        let mut next_edge = vec![NO_EDGE; edges.len()];
        let mut reached_funcs = vec![false; module.functions.len()];
        for i in (0..edges.len()).rev() {
            let target_node = edges[i].1;
            if let Some(head) = head_by_node.get_mut(target_node.index()) {
                next_edge[i] = *head;
                *head = i as u32;
            }
            if let Some(inst) = module.inst(target_node)
                && let Some(fid) = block_to_func.get(inst.block.index()).copied().flatten()
                && let Some(rf) = reached_funcs.get_mut(fid.index())
            {
                *rf = true;
            }
        }

        // Pre-index exceptional handler entry instructions per protected block
        // for reached functions only.
        let mut block_exc_handlers: Vec<Vec<InstId>> = vec![Vec::new(); module.blocks.len()];
        let mut block_has_catch_all: Vec<bool> = vec![false; module.blocks.len()];
        let mut handler_entry_exc: HashMap<InstId, abcd_ir::ValueId> = HashMap::new();
        for (fi, f) in module.functions.iter().enumerate() {
            if !reached_funcs[fi] {
                continue;
            }
            let func = FuncId::new(fi as u32);
            for region in &f.try_regions {
                let mut catch_entries = Vec::new();
                let mut region_catch_all = false;
                for catch in &region.catches {
                    if catch.type_class.is_none() {
                        region_catch_all = true;
                    }
                    if let Some(&first) =
                        module.block(catch.handler).and_then(|bb| bb.insts.first())
                    {
                        handler_entry_exc.entry(first).or_insert(catch.exception);
                        if !catch_entries.contains(&first) {
                            catch_entries.push(first);
                        }
                    }
                }
                if catch_entries.is_empty() && !region_catch_all {
                    continue;
                }
                for &prot_b in &region.protected {
                    if block_to_func.get(prot_b.index()).copied().flatten() != Some(func) {
                        continue;
                    }
                    if region_catch_all
                        && let Some(ca) = block_has_catch_all.get_mut(prot_b.index())
                    {
                        *ca = true;
                    }
                    let slot = &mut block_exc_handlers[prot_b.index()];
                    for &first in &catch_entries {
                        if !slot.contains(&first) {
                            slot.push(first);
                        }
                    }
                }
            }
        }

        let mut func_of_sp = HashMap::new();
        let mut exits_of: HashMap<FuncId, Vec<InstId>> = HashMap::new();
        let mut uncaught_calls_of: HashMap<FuncId, Vec<InstId>> = HashMap::new();
        let mut calls_at_return_site: HashMap<InstId, Vec<InstId>> = HashMap::new();
        let mut rs_buf: Vec<InstId> = Vec::new();
        for (fi, f) in module.functions.iter().enumerate() {
            let func = FuncId::new(fi as u32);
            if let Some(sp) = f
                .entry()
                .and_then(|b| module.block(b))
                .and_then(|bb| bb.insts.first())
            {
                func_of_sp.insert(*sp, func);
            }
            if !reached_funcs[fi] {
                continue;
            }
            let mut exits = Vec::new();
            let mut uncaught_calls = Vec::new();
            for &b in &f.blocks {
                let Some(bb) = module.block(b) else { continue };
                for (pos, &iid) in bb.insts.iter().enumerate() {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    if matches!(inst.op, Op::Return { .. } | Op::Throw { .. }) {
                        exits.push(iid);
                    }
                    if matches!(inst.op, Op::Call { .. }) {
                        if !block_has_catch_all
                            .get(inst.block.index())
                            .copied()
                            .unwrap_or(false)
                        {
                            uncaught_calls.push(iid);
                        }
                        rs_buf.clear();
                        if inst.block == b {
                            if pos + 1 < bb.insts.len() {
                                rs_buf.push(bb.insts[pos + 1]);
                            } else {
                                for s in abcd_analysis::control::block_succs(module, b) {
                                    if let Some(&first) =
                                        module.block(s).and_then(|sb| sb.insts.first())
                                    {
                                        rs_buf.push(first);
                                    }
                                }
                            }
                        } else if let Some(actual_bb) = module.block(inst.block)
                            && let Some(&raw_pos) = inst_pos_in_block.get(iid.index())
                            && raw_pos != u32::MAX
                        {
                            let actual_pos = raw_pos as usize;
                            if actual_pos + 1 < actual_bb.insts.len() {
                                rs_buf.push(actual_bb.insts[actual_pos + 1]);
                            } else {
                                for s in abcd_analysis::control::block_succs(module, inst.block) {
                                    if let Some(&first) =
                                        module.block(s).and_then(|sb| sb.insts.first())
                                    {
                                        rs_buf.push(first);
                                    }
                                }
                            }
                        }
                        if inst.op.effects_in(module).may_throw
                            && let Some(exc_list) = block_exc_handlers.get(inst.block.index())
                        {
                            for &first in exc_list {
                                if !rs_buf.contains(&first) {
                                    rs_buf.push(first);
                                }
                            }
                        }
                        for &rs in &rs_buf {
                            calls_at_return_site.entry(rs).or_default().push(iid);
                        }
                    }
                }
            }
            exits_of.insert(func, exits);
            if !uncaught_calls.is_empty() {
                uncaught_calls_of.insert(func, uncaught_calls);
            }
        }
        PathIndex {
            block_to_func,
            inst_pos_in_block,
            head_by_node,
            next_edge,
            func_of_sp,
            handler_entry_exc,
            exits_of,
            uncaught_calls_of,
            calls_at_return_site,
        }
    }

    fn edges_at(&self, node: InstId) -> impl Iterator<Item = usize> + '_ {
        let mut cur = self
            .head_by_node
            .get(node.index())
            .copied()
            .unwrap_or(NO_EDGE);
        std::iter::from_fn(move || {
            if cur == NO_EDGE {
                None
            } else {
                let idx = cur as usize;
                cur = self.next_edge[idx];
                Some(idx)
            }
        })
    }

    fn func_of_inst(&self, module: &Module, inst: InstId) -> Option<FuncId> {
        let block = module.inst(inst)?.block;
        self.block_to_func.get(block.index()).copied().flatten()
    }
}

/// Best-effort backward-BFS path from the sink edge back to the seed,
/// over the solver's path-edge set — and the seed itself.
///
/// Path-edge anchoring: intraprocedural
/// edges keep the ORIGINAL anchor, which for the seed's own function is
/// the ZERO fact (seeds are `(Zero, sp, fact)` edges); the anchor
/// switches to the callee-entry fact at call boundaries. Predecessors
/// of an edge `(d1, n, d2)`:
///
/// 1. `n` a start point, `d1 == Zero` → terminal seed edge
///    (seed = `(func(n), d2)`);
/// 2. `n` a start point, `d1 == d2 != Zero` → callee-anchor self-loop:
///    predecessors are the call edges into `func(n)`;
/// 3. otherwise → same-anchor edges at instruction predecessors, plus —
///    when `n` is a return site of call `c` — the call edge `(d1, c, *)`
///    and the callee exit edges (any anchor; the exact producing exit
///    is not recoverable from the edge set alone — documented
///    approximation, deterministic via BFS order and insertion-ordered
///    indices).
fn reconstruct_path(
    module: &Module,
    problem: &TaintProblem<'_>,
    callgraph: &impl CallGraphOracle,
    result: &IfdsResult<Fact>,
    index: &PathIndex,
    hit: &SinkHit,
) -> ((FuncId, Fact), Vec<PathStep>) {
    let edges = result.raw_path_edges();

    let step_of = |inst: InstId| -> PathStep {
        let i = module.inst(inst);
        PathStep {
            inst,
            loc: i.and_then(|x| x.loc),
            op: i.map(|x| op_tag(&x.op)).unwrap_or_default(),
        }
    };

    let fallback = || {
        (
            (
                index
                    .func_of_inst(module, hit.call)
                    .unwrap_or(FuncId::new(0)),
                Fact::Zero,
            ),
            vec![step_of(hit.call)],
        )
    };

    let zero_id = result.id_of_fact(&Fact::Zero);
    let Some(hit_fact_id) = result.id_of_fact(&Fact::Taint(hit.fact.clone())) else {
        return fallback();
    };
    let Some(start_edge) = index
        .edges_at(hit.call)
        .find(|&ei| edges[ei].2 == hit_fact_id)
    else {
        return fallback();
    };

    let fact_local_base = |fact_id: u32| -> Option<abcd_ir::ValueId> {
        result
            .fact_by_id(fact_id)
            .and_then(Fact::taint)
            .and_then(TaintFact::local_base)
    };

    let mut visited: HashSet<usize> = HashSet::new();
    let mut parent: HashMap<usize, usize> = HashMap::new();
    let mut queue: VecDeque<usize> = VecDeque::new();
    let mut replay_buf: Vec<Fact> = Vec::new();
    queue.push_back(start_edge);
    visited.insert(start_edge);
    let mut seed_edge = None;

    'bfs: while let Some(ei) = queue.pop_front() {
        let (src_id, n, dst_id) = edges[ei];
        // Terminal: a seed edge (Zero, sp, non-zero fact).
        if Some(src_id) == zero_id
            && let Some(&func) = index.func_of_sp.get(&n)
        {
            if Some(dst_id) != zero_id {
                seed_edge = Some((ei, func));
                break;
            }
            continue; // the zero self-loop root: do not expand
        }
        if parent.len() > 4096 {
            break; // cap: report the partial path
        }
        let mut preds: Vec<usize> = Vec::new();
        if src_id == dst_id && Some(src_id) != zero_id && index.func_of_sp.contains_key(&n) {
            // Callee-anchor self-loop: call edges into this function,
            // restricted to caller facts on the call's operands or matching
            // non-local state facts passed across the call edge.
            let func = index.func_of_sp[&n];
            for call in callgraph.callers_of(func) {
                let Some(call_inst) = module.inst(*call) else {
                    continue;
                };
                preds.extend(index.edges_at(*call).filter(|&pi| {
                    edges[pi].2 == src_id
                        || fact_local_base(edges[pi].2).is_some_and(|v| call_inst.op.has_operand(v))
                }));
            }
        } else {
            let dst_fact = result.fact_by_id(dst_id);
            let dst_local = fact_local_base(dst_id);

            // Uncaught-exit disambiguation at a throwing `Op::Call` site (`!has_catch_all`):
            // replay `call_uncaught_exit_flow` across callee `Return`/`Throw` exits and
            // nested uncaught `Op::Call` sites so multi-frame exception paths reconstruct
            // every callee frame back to the originating `Throw`.
            let mut via_uncaught_call = false;
            if matches!(module.inst(n).map(|i| &i.op), Some(Op::Call { .. }))
                && Some(dst_id) != zero_id
            {
                let is_uncaught_sentinel = dst_local == Some(UNCAUGHT_EXCEPTION_VALUE);
                let is_uncaught_state = !is_uncaught_sentinel
                    && dst_local.is_none()
                    && !inst_preds(module, index, n).into_iter().any(|p| {
                        index
                            .edges_at(p)
                            .any(|pi| edges[pi].0 == src_id && edges[pi].2 == dst_id)
                    });
                if (is_uncaught_sentinel || is_uncaught_state)
                    && let Some(dst_f) = dst_fact
                {
                    let mut uncaught_preds: Vec<usize> = Vec::new();
                    for &callee in callgraph.callees_of_call_at(n) {
                        let exit_iter = index
                            .exits_of
                            .get(&callee)
                            .into_iter()
                            .flatten()
                            .chain(index.uncaught_calls_of.get(&callee).into_iter().flatten());
                        for &callee_exit in exit_iter {
                            for pi in index.edges_at(callee_exit) {
                                let Some(src_f) = result.fact_by_id(edges[pi].2) else {
                                    continue;
                                };
                                replay_buf.clear();
                                problem.call_uncaught_exit_flow(
                                    module,
                                    n,
                                    callee,
                                    callee_exit,
                                    src_f,
                                    &mut replay_buf,
                                );
                                if replay_buf.contains(dst_f) {
                                    uncaught_preds.push(pi);
                                }
                            }
                        }
                    }
                    if !uncaught_preds.is_empty() {
                        preds.extend(uncaught_preds);
                        via_uncaught_call = true;
                    }
                }
            }

            if !via_uncaught_call {
                // Return-site disambiguation: if this edge's fact is on the
                // call's RESULT value (or catch handler ExceptionParam, or a heap
                // fact produced by the callee), the taint arrived through the
                // callee (return flow), so the path detours via the callee exit —
                // not the intraprocedural bypass.
                let mut via_exit: Option<Vec<usize>> = None;
                if let Some(calls) = index.calls_at_return_site.get(&n) {
                    let handler_exc = index.handler_entry_exc.get(&n).copied();
                    'calls: for c in calls {
                        let result_val = module.inst(*c).and_then(|i| i.result);
                        let is_handler_exc = dst_local.is_some() && dst_local == handler_exc;
                        let on_result =
                            (dst_local == result_val && result_val.is_some()) || is_handler_exc;
                        let is_heap_return = dst_local.is_none()
                            && Some(dst_id) != zero_id
                            && !index
                                .edges_at(*c)
                                .any(|pi| edges[pi].0 == src_id && edges[pi].2 == dst_id);
                        if !on_result && !is_heap_return {
                            continue;
                        }
                        let mut exit_preds: Vec<usize> = Vec::new();
                        if let Some(dst_f) = dst_fact {
                            for &callee in callgraph.callees_of_call_at(*c) {
                                let uncaught_slice: &[InstId] = if is_handler_exc {
                                    index
                                        .uncaught_calls_of
                                        .get(&callee)
                                        .map_or(&[], Vec::as_slice)
                                } else {
                                    &[]
                                };
                                let exit_iter = index
                                    .exits_of
                                    .get(&callee)
                                    .map_or(&[][..], Vec::as_slice)
                                    .iter()
                                    .chain(uncaught_slice.iter());
                                for &exit in exit_iter {
                                    for pi in index.edges_at(exit) {
                                        let Some(src_f) = result.fact_by_id(edges[pi].2) else {
                                            continue;
                                        };
                                        replay_buf.clear();
                                        problem.return_flow(
                                            module,
                                            Some(*c),
                                            callee,
                                            exit,
                                            Some(n),
                                            src_f,
                                            &mut replay_buf,
                                        );
                                        if replay_buf.contains(dst_f) {
                                            exit_preds.push(pi);
                                        }
                                    }
                                }
                            }
                        }
                        if !exit_preds.is_empty() {
                            via_exit = Some(exit_preds);
                            break 'calls;
                        }
                    }
                }
                if let Some(exit_preds) = via_exit {
                    preds.extend(exit_preds);
                } else {
                    let mut zero_preds: Vec<usize> = Vec::new();
                    for p in inst_preds(module, index, n) {
                        // Prefer the exact-fact (pass-through) predecessor;
                        // widen only at transforming instructions, preferring
                        // non-zero incoming taint before the Zero-minting fallback.
                        let mut any_exact = false;
                        for pi in index.edges_at(p) {
                            if edges[pi].0 == src_id && edges[pi].2 == dst_id {
                                preds.push(pi);
                                any_exact = true;
                            }
                        }
                        if !any_exact {
                            for pi in index.edges_at(p) {
                                if edges[pi].0 == src_id {
                                    if Some(edges[pi].2) != zero_id {
                                        preds.push(pi);
                                    } else {
                                        zero_preds.push(pi);
                                    }
                                }
                            }
                        }
                    }
                    if let Some(calls) = index.calls_at_return_site.get(&n) {
                        for c in calls {
                            // The call edge with the same anchor (bypass).
                            for pi in index.edges_at(*c) {
                                if edges[pi].0 == src_id {
                                    if Some(edges[pi].2) != zero_id {
                                        preds.push(pi);
                                    } else {
                                        zero_preds.push(pi);
                                    }
                                }
                            }
                        }
                    }
                    if preds.is_empty() {
                        preds.extend(zero_preds);
                    }
                }
            }
        }
        for pi in preds {
            if pi != ei && visited.insert(pi) {
                parent.insert(pi, ei);
                if Some(dst_id) != zero_id && Some(edges[pi].2) == zero_id {
                    seed_edge = Some((
                        pi,
                        index
                            .func_of_inst(module, edges[pi].1)
                            .unwrap_or(FuncId::new(0)),
                    ));
                    break 'bfs;
                }
                queue.push_back(pi);
            }
        }
        if queue.len() > 8192 {
            break;
        }
    }

    let Some((seed_ei, seed_func)) = seed_edge else {
        return fallback();
    };
    let Some(seed_fact) = result.fact_by_id(edges[seed_ei].2).cloned() else {
        return fallback();
    };
    let seed = (seed_func, seed_fact);

    // Rebuild seed → sink along the child links.
    let mut chain = vec![seed_ei];
    let mut cur = seed_ei;
    while let Some(&next) = parent.get(&cur) {
        chain.push(next);
        cur = next;
        if chain.len() > 4096 {
            break;
        }
    }
    let path = chain.into_iter().map(|ei| step_of(edges[ei].1)).collect();
    (seed, path)
}

/// The `Op` variant name for reporting (Debug-prefix; no per-variant
/// list to maintain — reporting only, never semantics).
fn op_tag(op: &Op) -> String {
    let s = format!("{op:?}");
    let end = s.find([' ', '{', '(']).unwrap_or(s.len());
    s[..end].to_owned()
}
