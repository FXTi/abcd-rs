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

use std::collections::{HashMap, HashSet, VecDeque};

use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::dataflow::Rung1AliasOracle;
use abcd_analysis::dataflow::heap::{DEFAULT_MAX_FIELD_CHAIN, Rung0AliasOracle};
use abcd_analysis::dataflow::ifds::CallGraphOracle;
use abcd_analysis::dataflow::ifds::{IfdsConfig, IfdsResult, IfdsSolver};
use abcd_analysis::dataflow::pta::{PtaConfig, Rung2AliasOracle};
use abcd_analysis::module_link::ModuleLinkTable;
use abcd_analysis::ohos_lifecycle::synthesize_ohos_harness;
use abcd_ir::{FuncId, InstId, Loc, Module, Op};

use crate::fact::{Fact, TaintFact};
use crate::gap::GapCallGraph;
use crate::names::{ClassPropStores, call_base_value, callee_name_candidates_indexed};
use crate::oracle::Oracle;
use crate::problem::{TaintProblem, op_uses_value};
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
}

/// Run the taint analysis over `module`.
pub fn run_taint(module: &Module, config: &TaintConfig) -> TaintReport {
    run_taint_full(module, config).0
}

/// Run the analysis, also returning the raw solver result (for tests
/// that assert on facts at arbitrary program points).
pub fn run_taint_full(module: &Module, config: &TaintConfig) -> (TaintReport, IfdsResult<Fact>) {
    let orig_func_len = module.functions.len();
    let orig_inst_len = module.insts.len();
    let augmented = if config.ohos_lifecycle {
        synthesize_ohos_harness(module, config.manifest_json.as_deref()).map(|(m, _)| m)
    } else {
        None
    };
    let work_mod: &Module = augmented.as_ref().unwrap_or(module);

    let base_graph = CallGraph::build(work_mod);
    // The alias ladder (`design/analysis.md`):
    // - rung 0 solves against the base graph with def-chain answers;
    // - rung 1 builds the on-demand engine over the BASE graph and
    //   refines the graph once with the engine's points_to (one
    //   engine, two consumers; one pass, no fixed point);
    // - rung 2 runs the whole-module PTA: its co-evolution fixed point
    //   IS the call graph the solver runs against, and its fixed-point
    //   tables are the oracle. A step-budget cut degrades to the rung-1
    //   pipeline, recorded in `alias_rung_used` (loud, never silent).
    let rung1_pipeline = || {
        let engine = Rung1AliasOracle::new(work_mod, &base_graph);
        let refined = CallGraph::refine_with_points_to(work_mod, &base_graph, &engine);
        (refined, Oracle::Rung1(engine), 1u8)
    };
    let (refined, oracle, rung_used) = match config.alias_rung {
        0 => (None, Oracle::Rung0(Rung0AliasOracle::new(work_mod)), 0u8),
        2 => {
            let pta_config = PtaConfig {
                step_budget: config
                    .pta_step_budget
                    .unwrap_or(abcd_analysis::dataflow::pta::DEFAULT_STEP_BUDGET),
                ..PtaConfig::default()
            };
            let outcome = abcd_analysis::dataflow::pta::analyze(work_mod, &base_graph, &pta_config);
            if outcome.stats().capped {
                let (g, o, u) = rung1_pipeline();
                (Some(g), o, u)
            } else {
                let (graph, tables, stats) = outcome.into_parts();
                (
                    Some(graph),
                    Oracle::Rung2(Rung2AliasOracle::new(work_mod, tables, stats)),
                    2u8,
                )
            }
        }
        _ => {
            let (g, o, u) = rung1_pipeline();
            (Some(g), o, u)
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

    let problem = TaintProblem::new(work_mod, callgraph, oracle, &registry, config);
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

    let hits = collect_hits(
        work_mod,
        problem.links(),
        problem.prop_stores(),
        config,
        callgraph,
        &result,
    );
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
    };
    report.hits.retain(|h| h.call.index() < orig_inst_len);
    if !report.hits.is_empty() {
        let path_index = PathIndex::build(work_mod, &result);
        for hit in &mut report.hits {
            let (mut seed, mut path) =
                reconstruct_path(work_mod, &gap_graph, &result, &path_index, hit);
            if augmented.is_some() {
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
    links: &ModuleLinkTable,
    prop_stores: &ClassPropStores,
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
        let Some(inst) = module.inst(iid) else {
            continue;
        };
        let Op::Call {
            callee, this, args, ..
        } = &inst.op
        else {
            continue;
        };
        let mut names =
            callee_name_candidates_indexed(module, links, Some(prop_stores), edge.caller, *callee);
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
            for fact in result.facts_at(iid, &zero) {
                let Fact::Taint(tf) = &fact else { continue };
                let Some(v) = tf.local_base() else { continue };
                let position = if let Some(pos) = args.iter().position(|&a| a == v) {
                    format!("arg {pos}")
                } else if this == &Some(v) {
                    "this".to_owned()
                } else if base == Some(v) {
                    "base".to_owned()
                } else if v == *callee {
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
/// instruction in the block, or the last instruction of each predecessor
/// block (Normal and Exceptional edges alike).
fn inst_preds(module: &Module, inst: InstId) -> Vec<InstId> {
    let Some(i) = module.inst(inst) else {
        return Vec::new();
    };
    let Some(block) = module.block(i.block) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    if let Some(pos) = block.insts.iter().position(|&x| x == inst)
        && pos > 0
    {
        out.push(block.insts[pos - 1]);
        return out;
    }
    for pred in &block.preds {
        if let Some(pb) = module.block(pred.from)
            && let Some(&last) = pb.insts.last()
        {
            out.push(last);
        }
    }
    out
}

/// Indices over the path-edge set for backward reconstruction.
struct PathIndex {
    /// Dense `BlockId::index() -> Option<FuncId>` owning-function index.
    block_to_func: Vec<Option<FuncId>>,
    /// `(anchor fact ID, target node)` → edge indices.
    by_anchor_node: HashMap<(u32, InstId), Vec<usize>>,
    /// target node → edge indices (any anchor).
    by_node: HashMap<InstId, Vec<usize>>,
    /// start point → function.
    func_of_sp: HashMap<InstId, FuncId>,
    /// function → exit instructions (Return/Throw).
    exits_of: HashMap<FuncId, Vec<InstId>>,
    /// return site → call instructions it is a return site of.
    calls_at_return_site: HashMap<InstId, Vec<InstId>>,
}

impl PathIndex {
    fn build(module: &Module, result: &IfdsResult<Fact>) -> Self {
        let mut block_to_func = vec![None; module.blocks.len()];
        for (fi, f) in module.functions.iter().enumerate() {
            let func = FuncId::new(fi as u32);
            for &b in &f.blocks {
                if let Some(slot) = block_to_func.get_mut(b.index()) {
                    slot.get_or_insert(func);
                }
            }
        }

        // Pre-index exceptional handler entry instructions per protected block
        // once (`O(|try_regions|)`) so call return-site indexing never scans
        // `module.functions`.
        let mut block_exc_handlers: Vec<Vec<InstId>> = vec![Vec::new(); module.blocks.len()];
        for (fi, f) in module.functions.iter().enumerate() {
            let func = FuncId::new(fi as u32);
            for region in &f.try_regions {
                let mut catch_entries = Vec::new();
                for catch in &region.catches {
                    if let Some(&first) =
                        module.block(catch.handler).and_then(|bb| bb.insts.first())
                        && !catch_entries.contains(&first)
                    {
                        catch_entries.push(first);
                    }
                }
                if catch_entries.is_empty() {
                    continue;
                }
                for &prot_b in &region.protected {
                    if block_to_func.get(prot_b.index()).copied().flatten() != Some(func) {
                        continue;
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

        let mut by_anchor_node: HashMap<(u32, InstId), Vec<usize>> = HashMap::new();
        let mut by_node: HashMap<InstId, Vec<usize>> = HashMap::new();
        for (i, &(src_id, target_node, _dst_id)) in result.raw_path_edges().iter().enumerate() {
            by_anchor_node
                .entry((src_id, target_node))
                .or_default()
                .push(i);
            by_node.entry(target_node).or_default().push(i);
        }
        let mut func_of_sp = HashMap::new();
        let mut exits_of: HashMap<FuncId, Vec<InstId>> = HashMap::new();
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
            let mut exits = Vec::new();
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
                            && let Some(actual_pos) = actual_bb.insts.iter().position(|&x| x == iid)
                        {
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
                        if inst.op.effects().may_throw
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
        }
        PathIndex {
            block_to_func,
            by_anchor_node,
            by_node,
            func_of_sp,
            exits_of,
            calls_at_return_site,
        }
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
        .by_node
        .get(&hit.call)
        .and_then(|cands| cands.iter().copied().find(|&ei| edges[ei].2 == hit_fact_id))
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
    queue.push_back(start_edge);
    visited.insert(start_edge);
    let mut seed_edge = None;

    while let Some(ei) = queue.pop_front() {
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
            // restricted to caller facts on the call's operands (the
            // only facts call_flow can map).
            let func = index.func_of_sp[&n];
            for call in callgraph.callers_of(func) {
                let Some(call_inst) = module.inst(*call) else {
                    continue;
                };
                if let Some(cands) = index.by_node.get(call) {
                    preds.extend(cands.iter().copied().filter(|&pi| {
                        fact_local_base(edges[pi].2)
                            .is_some_and(|v| op_uses_value(&call_inst.op, v))
                    }));
                }
            }
        } else {
            // Return-site disambiguation: if this edge's fact is on the
            // call's RESULT value, the taint arrived through the callee
            // (return flow), so the path detours via the callee exit —
            // not the intraprocedural bypass.
            let mut via_exit: Option<Vec<usize>> = None;
            if let Some(calls) = index.calls_at_return_site.get(&n) {
                let dst_local = fact_local_base(dst_id);
                'calls: for c in calls {
                    let result_val = module.inst(*c).and_then(|i| i.result);
                    let on_result = dst_local.is_some_and(|v| Some(v) == result_val);
                    if !on_result {
                        continue;
                    }
                    let mut exit_preds: Vec<usize> = Vec::new();
                    for callee in callgraph.callees_of_call_at(*c) {
                        if let Some(exits) = index.exits_of.get(callee) {
                            for exit in exits {
                                let exit_val = module.inst(*exit).and_then(|i| match &i.op {
                                    Op::Return { value } => *value,
                                    Op::Throw { value } => Some(*value),
                                    _ => None,
                                });
                                if let Some(cands) = index.by_node.get(exit) {
                                    exit_preds.extend(
                                        cands
                                            .iter()
                                            .copied()
                                            .filter(|&pi| fact_local_base(edges[pi].2) == exit_val),
                                    );
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
                for p in inst_preds(module, n) {
                    if let Some(cands) = index.by_anchor_node.get(&(src_id, p)) {
                        // Prefer the exact-fact (pass-through) predecessor;
                        // widen only at transforming instructions.
                        let exact: Vec<usize> = cands
                            .iter()
                            .copied()
                            .filter(|&pi| edges[pi].2 == dst_id)
                            .collect();
                        if exact.is_empty() {
                            preds.extend(cands.iter().copied());
                        } else {
                            preds.extend(exact);
                        }
                    }
                }
                if let Some(calls) = index.calls_at_return_site.get(&n) {
                    for c in calls {
                        // The call edge with the same anchor (bypass).
                        if let Some(cands) = index.by_anchor_node.get(&(src_id, *c)) {
                            preds.extend(cands.iter().copied());
                        }
                    }
                }
            }
        }
        for pi in preds {
            if pi != ei && visited.insert(pi) {
                parent.insert(pi, ei);
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
