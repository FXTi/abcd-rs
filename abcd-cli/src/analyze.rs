//! `abcd analyze` — structural analysis report over the lifted IR
//! (design/cli.md §2, design/analysis.md §2).
//!
//! Pipeline: `.abc` → [`abcd_file::decode`] → [`abcd_lift::lift_file`] →
//! abcd-analysis. Every reported field traces to a public abcd-analysis /
//! abcd-ir API — nothing is invented:
//!
//! - the module summary counts IR arenas and the [`CallGraph`] resolution
//!   histogram; `entry` is the `func_main_0` naming convention every
//!   es2abc module carries (the IR itself has no entry concept);
//! - `--callgraph` lists, per function, every call site with its
//!   [`abcd_analysis::callgraph::CallEdge`] classification and resolved targets (unresolved sites
//!   are explicit `unknown_callees`, never dropped);
//! - `--dominators` runs [`Dominators::normal`] per function and reports
//!   the immediate-dominator tree in reverse post-order.
//!
//! Output conventions (design/cli.md §3): aligned text by default, `--json`
//! for the machine-readable form; both render from the same report data.

use abcd_analysis::callgraph::{CallEdgeKind, CallGraph, CallTargets};
use abcd_analysis::control::Dominators;
use abcd_analysis::dataflow::alias::Rung1AliasOracle;
use abcd_analysis::dataflow::pta::{self, DEFAULT_STEP_BUDGET, PtaConfig};
use abcd_ir::{CallKind, FuncId, Module};
use rayon::prelude::*;
use serde::Serialize;

use crate::CliError;
use crate::input::InputModule;

/// Which optional sections and alias rung the report computes (wired to
/// `--callgraph`, `--dominators`, `--pta`, `--alias-rung`, and `--pta-budget`
/// by the CLI layer).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AnalyzeOptions {
    /// Per-function call-site listing with resolved targets.
    pub callgraph: bool,
    /// Per-function immediate-dominator tree.
    pub dominators: bool,
    /// Call-graph / alias rung (`0` = base `CallGraph::build`, `1` =
    /// `Rung1AliasOracle` + `CallGraph::refine_with_points_to`, `2` = Rung-2
    /// `pta::analyze`).
    pub alias_rung: u8,
    /// Optional Rung-2 pointer-analysis step budget override.
    pub pta_budget: Option<usize>,
}

/// Machine-readable analysis report of one module (serialized by `--json`).
#[derive(Clone, Debug, Serialize)]
pub struct AnalyzeReport {
    /// Module name (container provenance or file stem).
    pub module: String,
    /// Where the bytes came from.
    pub provenance: String,
    /// Input `.abc` size in bytes.
    pub input_bytes: usize,
    /// Module-level counts and the call-graph resolution histogram.
    pub summary: SummaryReport,
    /// Present only when Rung-2 pointer analysis (`--pta` / `--alias-rung 2`)
    /// ran.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub pta: Option<PtaReport>,
    /// Present only under `--callgraph`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub callgraph: Option<CallgraphReport>,
    /// Present only under `--dominators`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub dominators: Option<Vec<DominatorTree>>,
}

/// Rung-2 pointer-analysis telemetry (`--pta` / `--alias-rung 2`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct PtaReport {
    /// Effective alias rung used for the reported call graph (`2` when PTA
    /// converged within budget; `1` when `capped` triggered Rung-1 fallback).
    pub alias_rung_used: u8,
    /// Worklist activations executed.
    pub activations: usize,
    /// Total abstract heap/value facts materialized.
    pub facts: usize,
    /// Constraint-graph flow edges added.
    pub flow_edges: usize,
    /// Indirect call edges newly resolved by PTA.
    pub call_edges_resolved: usize,
    /// Call sites whose points-to set remained incomplete.
    pub call_sites_partial: usize,
    /// Lexical/module environment rounds executed.
    pub env_rounds: usize,
    /// Whether the step budget was exhausted before fixed point.
    pub capped: bool,
    /// Whether PTA ran in demand-driven root-sliced mode (`roots` excluded at
    /// least one internal function).
    pub root_sliced: bool,
}

/// Module-level counts (IR arena sizes) and resolution histogram.
#[derive(Clone, Debug, Serialize)]
pub struct SummaryReport {
    /// Functions in the IR function table.
    pub functions: usize,
    /// External (bodiless, native attachment point) functions.
    pub external_functions: usize,
    /// Basic blocks across all functions.
    pub blocks: usize,
    /// Instructions across all functions.
    pub instructions: usize,
    /// Call sites the graph recorded (including unresolved ones).
    pub call_sites: usize,
    /// Call-site resolution histogram.
    pub resolution: ResolutionReport,
    /// The module entry function, when the es2abc `func_main_0`
    /// convention is present.
    pub entry: Option<String>,
}

/// Call-site resolution histogram (abcd-analysis `ResolutionHistogram`).
#[derive(Clone, Debug, Serialize)]
pub struct ResolutionReport {
    /// Sites resolved to at least one internal (has-body) function.
    pub resolved_internal: usize,
    /// Sites whose targets are ALL external declarations.
    pub resolved_external: usize,
    /// Sites with mixed internal+external targets.
    pub resolved_mixed: usize,
    /// Sites explicitly unresolved (`UnknownCallees`).
    pub unknown: usize,
}

/// The `--callgraph` section: one entry per function, in `FuncId` order.
#[derive(Clone, Debug, Serialize)]
pub struct CallgraphReport {
    /// Per-function call-site lists (functions with no sites have an
    /// empty `sites` array).
    pub functions: Vec<FunctionCallgraph>,
}

/// Call sites of one function.
#[derive(Clone, Debug, Serialize)]
pub struct FunctionCallgraph {
    /// The function's `FuncId` arena index.
    pub function_index: u32,
    /// Resolved function name.
    pub function: String,
    /// Call sites in instruction order.
    pub sites: Vec<CallSiteReport>,
}

/// One call site.
#[derive(Clone, Debug, Serialize)]
pub struct CallSiteReport {
    /// The call instruction's `InstId` arena index.
    pub inst: u32,
    /// The IR `CallKind`, snake_case (`direct`, `dynamic`, `apply`,
    /// `new`, `new_spread`, `super`, `super_arrow`, `super_spread`,
    /// `super_forward_all_args`, `class_init`).
    pub kind: String,
    /// Edge classification: `direct` / `resolved_value_flow` /
    /// `unknown_callees`.
    pub edge_kind: String,
    /// Whether the callee trace was complete; `false` on a resolved
    /// edge means "these callees AND possibly others".
    pub resolution_complete: bool,
    /// Resolved callees (empty iff `edge_kind == "unknown_callees"`).
    pub targets: Vec<CallTarget>,
}

/// One resolved call target.
#[derive(Clone, Debug, Serialize)]
pub struct CallTarget {
    /// The callee's `FuncId` arena index.
    pub index: u32,
    /// Resolved callee name.
    pub name: String,
    /// Whether the callee is an external (bodiless) declaration.
    pub external: bool,
}

/// One function's immediate-dominator tree (`--dominators`).
#[derive(Clone, Debug, Serialize)]
pub struct DominatorTree {
    /// The function's `FuncId` arena index.
    pub function_index: u32,
    /// Resolved function name.
    pub function: String,
    /// Blocks owned by the function (including unreachable ones).
    pub blocks: usize,
    /// Blocks reachable from the entry block.
    pub reachable: usize,
    /// Reachable nodes in reverse post-order; `depth` is the dominator
    /// tree depth (0 = entry).
    pub nodes: Vec<DomNode>,
}

/// One dominator-tree node.
#[derive(Clone, Debug, Serialize)]
pub struct DomNode {
    /// The block's `BlockId` arena index.
    pub block: u32,
    /// Immediate dominator (`None` on the entry block).
    pub idom: Option<u32>,
    /// Dominator-tree depth (entry = 0).
    pub depth: usize,
}

/// The es2abc module entry-point naming convention.
const ENTRY_NAME: &str = "func_main_0";

/// Decode, lift, and analyze one module.
pub fn report(module: &InputModule, opts: AnalyzeOptions) -> Result<AnalyzeReport, CliError> {
    if opts.alias_rung > 2 {
        return Err(CliError::User(format!(
            "invalid alias_rung {} (expected 0, 1, or 2)",
            opts.alias_rung
        )));
    }
    if opts.pta_budget.is_some() && opts.alias_rung < 2 {
        return Err(CliError::User(format!(
            "--pta-budget requires --alias-rung 2 (or --pta), got alias rung {}",
            opts.alias_rung
        )));
    }
    let ir = {
        let file = abcd_file::decode(&module.abc).map_err(|e| {
            CliError::Tool(format!(
                "failed to decode {} ({}): {e}",
                module.name, module.provenance
            ))
        })?;
        abcd_lift::lift_file(&file).map_err(|e| {
            CliError::Tool(format!(
                "failed to lift {} ({}): {e}",
                module.name, module.provenance
            ))
        })?
    };

    let (graph, pta_report) = match opts.alias_rung {
        0 => (CallGraph::build(&ir), None),
        1 => {
            let base = CallGraph::build(&ir);
            let oracle = Rung1AliasOracle::new(&ir, &base);
            (CallGraph::refine_with_points_to(&ir, &base, &oracle), None)
        }
        2 => {
            let base = CallGraph::build(&ir);
            let cfg = PtaConfig {
                step_budget: opts.pta_budget.unwrap_or(DEFAULT_STEP_BUDGET),
                ..PtaConfig::default()
            };
            let outcome = pta::analyze(&ir, &base, &cfg);
            let stats = *outcome.stats();
            let (cg, alias_rung_used) = if stats.capped {
                let oracle = Rung1AliasOracle::new(&ir, &base);
                (CallGraph::refine_with_points_to(&ir, &base, &oracle), 1)
            } else {
                (outcome.into_parts().0, 2)
            };
            let rep = PtaReport {
                alias_rung_used,
                activations: stats.activations,
                facts: stats.facts,
                flow_edges: stats.flow_edges,
                call_edges_resolved: stats.call_edges_resolved,
                call_sites_partial: stats.call_sites_partial,
                env_rounds: stats.env_rounds,
                capped: stats.capped,
                root_sliced: stats.root_sliced,
            };
            (cg, Some(rep))
        }
        other => {
            return Err(CliError::User(format!(
                "invalid alias_rung {other} (expected 0, 1, or 2)"
            )));
        }
    };
    let histogram = graph.histogram(&ir);

    let entry = ir
        .functions
        .iter()
        .find(|f| ir.sym.resolve(f.name) == Some(ENTRY_NAME))
        .map(|f| ir.sym.resolve(f.name).unwrap_or(ENTRY_NAME).to_string());

    let callgraph = opts.callgraph.then(|| callgraph_section(&ir, &graph));
    let dominators = opts.dominators.then(|| dominator_sections(&ir));

    Ok(AnalyzeReport {
        module: module.name.clone(),
        provenance: module.provenance.clone(),
        input_bytes: module.abc.len(),
        summary: SummaryReport {
            functions: ir.functions.len(),
            external_functions: ir.functions.iter().filter(|f| f.is_external).count(),
            blocks: ir.blocks.len(),
            instructions: ir.insts.len(),
            call_sites: graph.site_count(),
            resolution: ResolutionReport {
                resolved_internal: histogram.resolved_internal,
                resolved_external: histogram.resolved_external,
                resolved_mixed: histogram.resolved_mixed,
                unknown: histogram.unknown,
            },
            entry,
        },
        pta: pta_report,
        callgraph,
        dominators,
    })
}

/// Resolve a function's display name (names are display-only in the IR;
/// identity is the `FuncId`).
fn func_name(ir: &Module, f: FuncId) -> String {
    ir.func(f)
        .and_then(|fd| ir.sym.resolve(fd.name))
        .unwrap_or("<unnamed>")
        .to_string()
}

/// Build the `--callgraph` section: every function (in `FuncId` order)
/// with its call sites.
fn callgraph_section(ir: &Module, graph: &CallGraph) -> CallgraphReport {
    let mut functions: Vec<FunctionCallgraph> = ir
        .functions
        .iter()
        .enumerate()
        .map(|(fi, _)| FunctionCallgraph {
            function_index: fi as u32,
            function: func_name(ir, FuncId::new(fi as u32)),
            sites: Vec::new(),
        })
        .collect();
    for (iid, edge) in graph.sites() {
        let kind = match edge.kind {
            CallKind::Direct => "direct",
            CallKind::Dynamic => "dynamic",
            CallKind::Apply => "apply",
            CallKind::Super => "super",
            CallKind::SuperArrow => "super_arrow",
            CallKind::SuperSpread => "super_spread",
            CallKind::SuperForwardAllArgs => "super_forward_all_args",
            CallKind::New => "new",
            CallKind::NewSpread => "new_spread",
            CallKind::ClassInit => "class_init",
        };
        let edge_kind = match edge.edge_kind {
            CallEdgeKind::Direct => "direct",
            CallEdgeKind::ResolvedValueFlow => "resolved_value_flow",
            CallEdgeKind::UnknownCallees => "unknown_callees",
        };
        let targets = match &edge.targets {
            CallTargets::Resolved(ts) => ts
                .iter()
                .map(|t| CallTarget {
                    index: t.index() as u32,
                    name: func_name(ir, *t),
                    external: ir.func(*t).is_some_and(|f| f.is_external),
                })
                .collect(),
            CallTargets::UnknownCallees => Vec::new(),
        };
        let site = CallSiteReport {
            inst: iid.index() as u32,
            kind: kind.to_string(),
            edge_kind: edge_kind.to_string(),
            resolution_complete: edge.resolution_complete,
            targets,
        };
        if let Some(f) = functions.get_mut(edge.caller.index()) {
            f.sites.push(site);
        }
    }
    CallgraphReport { functions }
}

/// Build the `--dominators` section: one tree per function (parallelized across functions).
fn dominator_sections(ir: &Module) -> Vec<DominatorTree> {
    ir.functions
        .par_iter()
        .enumerate()
        .map(|(fi, f)| {
            let func = FuncId::new(fi as u32);
            let dom = Dominators::normal(ir, func);
            let nodes = dom
                .rpo()
                .iter()
                .map(|b| DomNode {
                    block: b.index() as u32,
                    idom: dom.idom(*b).map(|i| i.index() as u32),
                    depth: dom.depth(*b).unwrap_or(0) as usize,
                })
                .collect();
            DominatorTree {
                function_index: fi as u32,
                function: func_name(ir, func),
                blocks: f.blocks.len(),
                reachable: dom.rpo().len(),
                nodes,
            }
        })
        .collect()
}

/// Human-readable rendering of one report (goes to stdout).
pub fn render_text(report: &AnalyzeReport) -> String {
    let s = &report.summary;
    let mut out = format!(
        "module:          {} ({})\n\
         input bytes:     {}\n\
         functions:       {} ({} external)\n\
         blocks:          {}\n\
         instructions:    {}\n\
         call sites:      {}\n\
         resolution:      {} internal, {} external, {} mixed, {} unknown\n",
        report.module,
        report.provenance,
        report.input_bytes,
        s.functions,
        s.external_functions,
        s.blocks,
        s.instructions,
        s.call_sites,
        s.resolution.resolved_internal,
        s.resolution.resolved_external,
        s.resolution.resolved_mixed,
        s.resolution.unknown,
    );
    match &s.entry {
        Some(name) => out.push_str(&format!("entry:           {name}\n")),
        None => out.push_str("entry:           (none)\n"),
    }
    if let Some(pta) = &report.pta {
        let capped_tag = if pta.capped { ", capped" } else { "" };
        out.push_str(&format!(
            "pta:             rung {}, {} activations, {} facts, {} flow edges, {} call edges, {} partial, {} env rounds{}\n\
             pta root sliced: {}\n",
            pta.alias_rung_used,
            pta.activations,
            pta.facts,
            pta.flow_edges,
            pta.call_edges_resolved,
            pta.call_sites_partial,
            pta.env_rounds,
            capped_tag,
            pta.root_sliced,
        ));
    }

    if let Some(cg) = &report.callgraph {
        out.push_str("\ncall graph:\n");
        for f in &cg.functions {
            out.push_str(&format!("  fn {} {}:\n", f.function_index, f.function));
            for site in &f.sites {
                let targets = if site.targets.is_empty() {
                    "<unknown callees>".to_string()
                } else {
                    site.targets
                        .iter()
                        .map(|t| {
                            if t.external {
                                format!("fn {} {} (external)", t.index, t.name)
                            } else {
                                format!("fn {} {}", t.index, t.name)
                            }
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                };
                let incomplete = if site.resolution_complete {
                    ""
                } else {
                    " (incomplete)"
                };
                out.push_str(&format!(
                    "    i{}: {} call [{}]{} -> {}\n",
                    site.inst, site.kind, site.edge_kind, incomplete, targets
                ));
            }
        }
    }

    if let Some(trees) = &report.dominators {
        out.push_str("\ndominators:\n");
        for t in trees {
            out.push_str(&format!(
                "  fn {} {} ({} blocks, {} reachable):\n",
                t.function_index, t.function, t.blocks, t.reachable
            ));
            for n in &t.nodes {
                let indent = "    ".repeat(n.depth + 1);
                match n.idom {
                    Some(idom) => out.push_str(&format!("{indent}b{} <- b{idom}\n", n.block)),
                    None => out.push_str(&format!("{indent}b{}\n", n.block)),
                }
            }
        }
    }
    out
}

/// Render reports per `--json`: a single module yields one object,
/// several modules yield an array.
pub fn render(reports: &[AnalyzeReport], json: bool) -> Result<String, CliError> {
    if json {
        let value = if reports.len() == 1 {
            serde_json::to_value(&reports[0])
        } else {
            serde_json::to_value(reports)
        }
        .map_err(|e| CliError::Tool(format!("failed to serialize report: {e}")))?;
        serde_json::to_string_pretty(&value)
            .map_err(|e| CliError::Tool(format!("failed to serialize report: {e}")))
    } else {
        Ok(reports
            .iter()
            .map(render_text)
            .collect::<Vec<_>>()
            .join("\n"))
    }
}
