//! The taint driver: source/sink configuration, the IFDS run over the
//! call graph + rung-0 alias oracle, and the taint-path report.
//!
//! ## Configuration
//!
//! Sources and sinks are NAME-keyed (analysis-strategy §5.3: the
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
use abcd_analysis::dataflow::heap::DEFAULT_MAX_FIELD_CHAIN;
use abcd_analysis::dataflow::ifds::CallGraphOracle;
use abcd_analysis::dataflow::ifds::{IfdsConfig, IfdsResult, IfdsSolver};
use abcd_ir::{FuncId, InstId, Loc, Module, Op, ValueId};

use crate::fact::{Fact, TaintFact};
use crate::names::{call_base_value, callee_name_candidates};
use crate::problem::TaintProblem;
use crate::summary::{RegistryStats, Summary, SummaryRegistry};

/// A taint source specification (name-keyed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceSpec {
    /// Parameters of every function with this name are tainted.
    /// `params: None` = all parameters (including `params[0]` = `this`).
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
    /// heros `followReturnsPastSeeds` (unbalanced returns). Default true.
    pub follow_returns_past_seeds: bool,
    /// The native/unknown fallback's identity heuristic: tainted
    /// operand ⇒ tainted return (reader D ladder rung 3). Default true.
    pub native_identity: bool,
    /// The access-path k-limit (default
    /// [`DEFAULT_MAX_FIELD_CHAIN`] = 5, FlowDroid's conventional bound).
    pub max_field_chain: usize,
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
}

impl TaintReport {
    /// The smoke-summary lines (verbatim format pinned by the corpus
    /// smoke test): flows, counters, determinism-friendly.
    pub fn summary_lines(&self) -> Vec<String> {
        let mut lines = vec![
            format!("TAINT-FLOWS hits={}", self.hits.len()),
            format!(
                "TAINT-COUNTERS lookups={} neg_cache_hits={} body_step={} native_keep={} unknown={}",
                self.stats.lookups,
                self.stats.negative_cache_hits,
                self.stats.sites_body_step,
                self.stats.sites_native_keep,
                self.stats.sites_unknown,
            ),
        ];
        let hits: Vec<String> = self
            .summary_hits
            .iter()
            .map(|(s, n)| format!("{s}={n}"))
            .collect();
        lines.push(format!("TAINT-SUMMARY-HITS {}", hits.join(" ")));
        let misses: Vec<String> = self
            .summary_misses
            .iter()
            .map(|(s, n)| format!("{s}={n}"))
            .collect();
        lines.push(format!("TAINT-SUMMARY-MISSES {}", misses.join(" ")));
        lines
    }
}

/// Run the taint analysis over `module`.
pub fn run_taint(module: &Module, config: &TaintConfig) -> TaintReport {
    run_taint_full(module, config).0
}

/// Run the analysis, also returning the raw solver result (for tests
/// that assert on facts at arbitrary program points).
pub fn run_taint_full(module: &Module, config: &TaintConfig) -> (TaintReport, IfdsResult<Fact>) {
    let callgraph = CallGraph::build(module);
    let mut registry = if config.builtin_summaries {
        SummaryRegistry::with_builtins()
    } else {
        SummaryRegistry::new()
    };
    for (name, arity, summary) in &config.extra_summaries {
        registry.register(name, *arity, summary.clone());
    }

    let problem = TaintProblem::new(module, &callgraph, &registry, config);
    let solver = IfdsSolver::new(
        module,
        &problem,
        &callgraph,
        IfdsConfig {
            follow_returns_past_seeds: config.follow_returns_past_seeds,
        },
    );
    let result = solver.solve();

    let hits = collect_hits(module, config, &callgraph, &result);
    let applied = problem.applied_summaries();
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
        path_edges: result.path_edges().len(),
    };
    let path_index = PathIndex::build(module, &result);
    for hit in &mut report.hits {
        let (seed, path) = reconstruct_path(module, &callgraph, &result, &path_index, hit);
        hit.seed = seed;
        hit.path = path;
    }
    report.hits.sort_by(|a, b| {
        (a.call, &a.position, &a.fact, &a.sink).cmp(&(b.call, &b.position, &b.fact, &b.sink))
    });
    (report, result)
}

/// Scan call sites for sink matches with tainted operands.
fn collect_hits(
    module: &Module,
    config: &TaintConfig,
    callgraph: &CallGraph,
    result: &IfdsResult<Fact>,
) -> Vec<SinkHit> {
    let zero = Fact::Zero;
    let mut hits = Vec::new();
    for (iid, _edge) in callgraph.sites() {
        let Some(inst) = module.inst(iid) else {
            continue;
        };
        let Op::Call {
            callee, this, args, ..
        } = &inst.op
        else {
            continue;
        };
        let mut names = callee_name_candidates(module, *callee);
        for f in callgraph.callees_of_call_at(iid) {
            if let Some(fd) = module.func(*f) {
                if let Some(n) = module.sym.resolve(fd.name) {
                    if !names.iter().any(|x| x == n) {
                        names.push(n.to_owned());
                    }
                }
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
                let position = if args.iter().position(|&a| a == v).is_some() {
                    format!("arg {}", args.iter().position(|&a| a == v).unwrap())
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

/// The function owning an instruction.
fn func_of_inst(module: &Module, inst: InstId) -> Option<FuncId> {
    let block = module.inst(inst)?.block;
    module
        .functions
        .iter()
        .position(|f| f.blocks.contains(&block))
        .map(|i| FuncId::new(i as u32))
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
    if let Some(pos) = block.insts.iter().position(|&x| x == inst) {
        if pos > 0 {
            out.push(block.insts[pos - 1]);
            return out;
        }
    }
    for pred in &block.preds {
        if let Some(pb) = module.block(pred.from) {
            if let Some(&last) = pb.insts.last() {
                out.push(last);
            }
        }
    }
    out
}

/// The solver's return-site computation for a call, replicated for path
/// reconstruction (the supergraph is solver-internal): the normal
/// continuation plus handler entries when the call may throw.
fn return_sites_of(module: &Module, call: InstId) -> Vec<InstId> {
    let Some(inst) = module.inst(call) else {
        return Vec::new();
    };
    let Some(block) = module.block(inst.block) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    if let Some(pos) = block.insts.iter().position(|&x| x == call) {
        if pos + 1 < block.insts.len() {
            out.push(block.insts[pos + 1]);
        } else {
            for s in abcd_analysis::control::block_succs(module, inst.block) {
                if let Some(first) = module.block(s).and_then(|b| b.insts.first()) {
                    out.push(*first);
                }
            }
        }
    }
    if inst.op.effects().may_throw {
        if let Some(f) = module
            .functions
            .iter()
            .find(|f| f.blocks.contains(&inst.block))
        {
            for region in &f.try_regions {
                if !region.protected.contains(&inst.block) {
                    continue;
                }
                for catch in &region.catches {
                    if let Some(first) = module.block(catch.handler).and_then(|b| b.insts.first()) {
                        if !out.contains(first) {
                            out.push(*first);
                        }
                    }
                }
            }
        }
    }
    out
}

/// Indices over the path-edge set for backward reconstruction.
struct PathIndex {
    /// `(anchor, target node)` → edge indices.
    by_anchor_node: HashMap<(Fact, InstId), Vec<usize>>,
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
        let mut by_anchor_node: HashMap<(Fact, InstId), Vec<usize>> = HashMap::new();
        let mut by_node: HashMap<InstId, Vec<usize>> = HashMap::new();
        for (i, e) in result.path_edges().iter().enumerate() {
            by_anchor_node
                .entry((e.source_fact.clone(), e.target_node))
                .or_default()
                .push(i);
            by_node.entry(e.target_node).or_default().push(i);
        }
        let mut func_of_sp = HashMap::new();
        let mut exits_of: HashMap<FuncId, Vec<InstId>> = HashMap::new();
        let mut calls_at_return_site: HashMap<InstId, Vec<InstId>> = HashMap::new();
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
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    if matches!(inst.op, Op::Return { .. } | Op::Throw { .. }) {
                        exits.push(iid);
                    }
                    if matches!(inst.op, Op::Call { .. }) {
                        for rs in return_sites_of(module, iid) {
                            calls_at_return_site.entry(rs).or_default().push(iid);
                        }
                    }
                }
            }
            exits_of.insert(func, exits);
        }
        PathIndex {
            by_anchor_node,
            by_node,
            func_of_sp,
            exits_of,
            calls_at_return_site,
        }
    }
}

/// Best-effort backward-BFS path from the sink edge back to the seed,
/// over the solver's path-edge set — and the seed itself.
///
/// Heros anchoring (the subtlety this implements): intraprocedural
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
    callgraph: &CallGraph,
    result: &IfdsResult<Fact>,
    index: &PathIndex,
    hit: &SinkHit,
) -> ((FuncId, Fact), Vec<PathStep>) {
    let edges = result.path_edges();

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
                func_of_inst(module, hit.call).unwrap_or(FuncId::new(0)),
                Fact::Zero,
            ),
            vec![step_of(hit.call)],
        )
    };

    let Some(start_edge) = edges
        .iter()
        .position(|e| e.target_node == hit.call && e.target_fact == Fact::Taint(hit.fact.clone()))
    else {
        return fallback();
    };

    let mut visited: HashSet<usize> = HashSet::new();
    let mut parent: HashMap<usize, usize> = HashMap::new();
    let mut queue: VecDeque<usize> = VecDeque::new();
    queue.push_back(start_edge);
    visited.insert(start_edge);
    let mut seed_edge = None;

    while let Some(ei) = queue.pop_front() {
        let e = &edges[ei];
        let n = e.target_node;
        // Terminal: a seed edge (Zero, sp, non-zero fact).
        if e.source_fact == Fact::Zero {
            if let Some(&func) = index.func_of_sp.get(&n) {
                if e.target_fact != Fact::Zero {
                    seed_edge = Some((ei, func));
                    break;
                }
                continue; // the zero self-loop root: do not expand
            }
        }
        if parent.len() > 4096 {
            break; // cap: report the partial path
        }
        let mut preds: Vec<usize> = Vec::new();
        if e.source_fact == e.target_fact
            && e.source_fact != Fact::Zero
            && index.func_of_sp.contains_key(&n)
        {
            // Callee-anchor self-loop: call edges into this function,
            // restricted to caller facts on the call's operands (the
            // only facts call_flow can map).
            let func = index.func_of_sp[&n];
            for call in callgraph.callers_of(func) {
                let operands: Vec<ValueId> = module
                    .inst(*call)
                    .map(|i| i.op.operands())
                    .unwrap_or_default();
                if let Some(cands) = index.by_node.get(call) {
                    preds.extend(cands.iter().copied().filter(|&pi| {
                        edges[pi]
                            .target_fact
                            .taint()
                            .and_then(|t| t.local_base())
                            .is_some_and(|v| operands.contains(&v))
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
                'calls: for c in calls {
                    let result_val = module.inst(*c).and_then(|i| i.result);
                    let on_result = e
                        .target_fact
                        .taint()
                        .and_then(|t| t.local_base())
                        .is_some_and(|v| Some(v) == result_val);
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
                                    exit_preds.extend(cands.iter().copied().filter(|&pi| {
                                        edges[pi].target_fact.taint().and_then(|t| t.local_base())
                                            == exit_val
                                    }));
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
                    if let Some(cands) = index.by_anchor_node.get(&(e.source_fact.clone(), p)) {
                        // Prefer the exact-fact (pass-through) predecessor;
                        // widen only at transforming instructions.
                        let exact: Vec<usize> = cands
                            .iter()
                            .copied()
                            .filter(|&pi| edges[pi].target_fact == e.target_fact)
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
                        if let Some(cands) = index.by_anchor_node.get(&(e.source_fact.clone(), *c))
                        {
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
    let seed = (seed_func, edges[seed_ei].target_fact.clone());

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
    let path = chain
        .into_iter()
        .map(|ei| step_of(edges[ei].target_node))
        .collect();
    (seed, path)
}

/// The `Op` variant name for reporting (Debug-prefix; no per-variant
/// list to maintain — reporting only, never semantics).
fn op_tag(op: &Op) -> String {
    let s = format!("{op:?}");
    let end = s
        .find(|c: char| c == ' ' || c == '{' || c == '(')
        .unwrap_or(s.len());
    s[..end].to_owned()
}
