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
use abcd_analysis::dataflow::ifds::CallGraphOracle;
use abcd_analysis::dataflow::heap::DEFAULT_MAX_FIELD_CHAIN;
use abcd_analysis::dataflow::ifds::{IfdsConfig, IfdsResult, IfdsSolver};
use abcd_ir::{FuncId, InstId, Loc, Module, Op};

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
    /// Total propagated path edges (solver work).
    pub path_edges: usize,
}

impl TaintReport {
    /// The smoke-summary lines (verbatim format pinned by the corpus
    /// smoke test): flows, counters, determinism-friendly.
    pub fn summary_lines(&self, registry: &SummaryRegistry) -> Vec<String> {
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
        let mut hits: Vec<String> = self
            .stats
            .hits
            .iter()
            .map(|(s, n)| format!("{}={}", registry.resolve(*s).unwrap_or_default(), n))
            .collect();
        hits.sort();
        lines.push(format!("TAINT-SUMMARY-HITS {}", hits.join(" ")));
        let mut misses: Vec<String> = self
            .stats
            .misses_named
            .iter()
            .map(|(s, n)| format!("{}={}", registry.resolve(*s).unwrap_or_default(), n))
            .collect();
        misses.sort();
        lines.push(format!("TAINT-SUMMARY-MISSES {}", misses.join(" ")));
        lines
    }
}

/// Run the taint analysis over `module`.
pub fn run_taint(module: &Module, config: &TaintConfig) -> TaintReport {
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
    let mut report = TaintReport {
        hits,
        stats,
        summaries_applied: applied,
        path_edges: result.path_edges().len(),
    };
    for hit in &mut report.hits {
        hit.path = reconstruct_path(module, &callgraph, &result, hit);
    }
    report.hits.sort_by(|a, b| {
        (a.call, &a.position, &a.fact, &a.sink).cmp(&(b.call, &b.position, &b.fact, &b.sink))
    });
    report
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
        let Some(inst) = module.inst(iid) else { continue };
        let Op::Call {
            callee,
            this,
            args,
            ..
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
                let seed = seed_of(module, result, iid, &fact).unwrap_or((FuncId::new(0), fact.clone()));
                hits.push(SinkHit {
                    sink: name.clone(),
                    call: iid,
                    loc: inst.loc,
                    position,
                    fact: tf.clone(),
                    seed,
                    path: Vec::new(), // filled by reconstruct_path
                });
            }
        }
    }
    hits
}

/// Find the seed (anchor function + seed fact) a reached fact derives
/// from: the path edge that first introduced a fact with the same
/// anchor. The anchor of an edge at the sink IS the seed fact for
/// caller-side edges; for callee-internal edges the anchor is the
/// callee-entry fact — follow the anchor chain back to a seed.
fn seed_of(
    module: &Module,
    result: &IfdsResult<Fact>,
    node: InstId,
    fact: &Fact,
) -> Option<(FuncId, Fact)> {
    let edges = result.path_edges();
    let mut anchor = edges
        .iter()
        .find(|e| e.target_node == node && &e.target_fact == fact)
        .map(|e| e.source_fact.clone())?;
    // Walk anchor switches backwards: an anchor that was itself produced
    // as a target fact at some function's start point by a call edge has
    // a parent anchor (the caller-side edge's source).
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(anchor.clone()) {
            return None;
        }
        if anchor == Fact::Zero {
            return None;
        }
        // Is `anchor` a seed? Seeds are edges (Zero, sp, anchor) where sp
        // is the start point.
        if let Some(e) = edges
            .iter()
            .find(|e| e.source_fact == Fact::Zero && e.target_fact == anchor)
        {
            let func = func_of_inst(module, e.target_node)?;
            return Some((func, anchor));
        }
        // Otherwise the anchor was produced by a call edge: find an edge
        // whose target fact equals the anchor at some start point and
        // continue from ITS source.
        let parent = edges
            .iter()
            .find(|e| e.target_fact == anchor && e.source_fact != Fact::Zero)?;
        anchor = parent.source_fact.clone();
    }
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
    let Some(i) = module.inst(inst) else { return Vec::new() };
    let Some(block) = module.block(i.block) else { return Vec::new() };
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

/// Best-effort backward-BFS path from the sink node back to the seed,
/// over the solver's path-edge set. Links: intraprocedural predecessor
/// edges with the same anchor; call-entry anchor switches (an edge into
/// a function's start point follows the caller's call-site edge);
/// return-site edges follow the callee's exit edges. Deterministic
/// (BFS over insertion-ordered edges, first path wins, depth-capped).
fn reconstruct_path(
    module: &Module,
    callgraph: &CallGraph,
    result: &IfdsResult<Fact>,
    hit: &SinkHit,
) -> Vec<PathStep> {
    let edges = result.path_edges();
    // Index: (anchor, node) → edge indices.
    let mut by_anchor_node: HashMap<(Fact, InstId), Vec<usize>> = HashMap::new();
    // Start-point edges by function for anchor switching.
    let mut start_point_of: HashMap<FuncId, InstId> = HashMap::new();
    for (fi, f) in module.functions.iter().enumerate() {
        if let Some(sp) = f
            .entry()
            .and_then(|b| module.block(b))
            .and_then(|bb| bb.insts.first())
        {
            start_point_of.insert(FuncId::new(fi as u32), *sp);
        }
    }
    for (i, e) in edges.iter().enumerate() {
        by_anchor_node
            .entry((e.source_fact.clone(), e.target_node))
            .or_default()
            .push(i);
    }

    let step_of = |inst: InstId| -> PathStep {
        let i = module.inst(inst);
        PathStep {
            inst,
            loc: i.and_then(|x| x.loc),
            op: i.map(|x| op_tag(&x.op)).unwrap_or_default(),
        }
    };

    // Backward BFS from (sink node, hit fact, anchor = hit.seed.1).
    // A state in the search is an edge index; parents are computed per
    // pop. Stop when we reach an edge whose source is Zero at a start
    // point (the seed edge).
    let target = edges
        .iter()
        .position(|e| e.target_node == hit.call && e.target_fact == Fact::Taint(hit.fact.clone()));
    let Some(start_edge) = target else {
        return vec![step_of(hit.call)];
    };

    let mut visited: HashSet<usize> = HashSet::new();
    let mut parent: HashMap<usize, usize> = HashMap::new();
    let mut queue: VecDeque<usize> = VecDeque::new();
    queue.push_back(start_edge);
    visited.insert(start_edge);
    let mut seed_edge = None;

    'bfs: while let Some(ei) = queue.pop_front() {
        let e = &edges[ei];
        if e.source_fact == Fact::Zero {
            seed_edge = Some(ei);
            break;
        }
        if parent.len() > 4096 {
            break; // depth cap: report the partial path
        }
        let push_parent = |pi: usize,
                               queue: &mut VecDeque<usize>,
                               visited: &mut HashSet<usize>,
                               parent: &mut HashMap<usize, usize>| {
            if visited.insert(pi) {
                parent.insert(pi, ei);
                queue.push_back(pi);
            }
        };
        // 1. Intraprocedural predecessors with the same anchor.
        for pred in inst_preds(module, e.target_node) {
            if let Some(cands) = by_anchor_node.get(&(e.source_fact.clone(), pred)) {
                for &pi in cands {
                    push_parent(pi, &mut queue, &mut visited, &mut parent);
                }
            }
        }
        // 2. Anchor switch at a callee start point: this edge's anchor
        // was produced by a call edge into this function.
        let is_start = start_point_of.values().any(|sp| *sp == e.target_node);
        if is_start && e.source_fact == e.target_fact {
            if let Some(func) = func_of_inst(module, e.target_node) {
                for caller_call in callgraph.callers_of(func) {
                    if let Some(cands) = by_anchor_node
                        .iter()
                        .find(|((_, n), _)| *n == *caller_call)
                        .map(|(_, v)| v.clone())
                    {
                        for pi in cands {
                            // The caller edge whose target fact maps to
                            // our anchor (any anchor — over-approximate
                            // but deterministic).
                            push_parent(pi, &mut queue, &mut visited, &mut parent);
                        }
                    }
                }
            }
        }
        if queue.len() > 8192 {
            break 'bfs;
        }
    }

    // Rebuild seed → sink.
    let mut chain = Vec::new();
    let mut cur = seed_edge.unwrap_or(start_edge);
    chain.push(cur);
    while let Some(&p) = parent.get(&cur) {
        chain.push(p);
        cur = p;
        if chain.len() > 4096 {
            break;
        }
    }
    chain.reverse();
    chain.into_iter().map(|ei| step_of(edges[ei].target_node)).collect()
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
