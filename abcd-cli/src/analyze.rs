//! `abcd analyze` — structural analysis report over the lifted IR
//! (design/cli-plan.md §2, P3).
//!
//! Pipeline: `.abc` → [`abcd_file::decode`] → [`abcd_lift::lift_file`] →
//! abcd-analysis. Every reported field traces to a public abcd-analysis /
//! abcd-ir API — nothing is invented:
//!
//! - the module summary counts IR arenas and the [`CallGraph`] resolution
//!   histogram; `entry` is the `func_main_0` naming convention every
//!   es2abc module carries (the IR itself has no entry concept);
//! - `--callgraph` lists, per function, every call site with its
//!   [`CallEdge`] classification and resolved targets (unresolved sites
//!   are explicit `unknown_callees`, never dropped);
//! - `--dominators` runs [`Dominators::normal`] per function and reports
//!   the immediate-dominator tree in reverse post-order.
//!
//! Output conventions (§3.4): aligned text by default, `--json` for the
//! machine-readable form; both render from the same report data.

use abcd_analysis::callgraph::{CallEdgeKind, CallGraph, CallTargets};
use abcd_analysis::control::Dominators;
use abcd_ir::{CallKind, FuncId, Module};
use serde::Serialize;

use crate::CliError;
use crate::input::InputModule;

/// Which optional sections the report computes (wired to `--callgraph` /
/// `--dominators` by the CLI layer).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AnalyzeOptions {
    /// Per-function call-site listing with resolved targets.
    pub callgraph: bool,
    /// Per-function immediate-dominator tree.
    pub dominators: bool,
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
    /// Present only under `--callgraph`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub callgraph: Option<CallgraphReport>,
    /// Present only under `--dominators`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub dominators: Option<Vec<DominatorTree>>,
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
    /// `new`, `super`, `super_spread`, `super_forward_all_args`).
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
    let file = abcd_file::decode(&module.abc).map_err(|e| {
        CliError::Tool(format!(
            "failed to decode {} ({}): {e}",
            module.name, module.provenance
        ))
    })?;
    let ir = abcd_lift::lift_file(&file).map_err(|e| {
        CliError::Tool(format!(
            "failed to lift {} ({}): {e}",
            module.name, module.provenance
        ))
    })?;

    let graph = CallGraph::build(&ir);
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
            CallKind::SuperSpread => "super_spread",
            CallKind::SuperForwardAllArgs => "super_forward_all_args",
            CallKind::New => "new",
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

/// Build the `--dominators` section: one tree per function.
fn dominator_sections(ir: &Module) -> Vec<DominatorTree> {
    let mut out = Vec::with_capacity(ir.functions.len());
    for (fi, f) in ir.functions.iter().enumerate() {
        let func = FuncId::new(fi as u32);
        let dom = Dominators::normal(ir, func);
        let nodes = dom
            .rpo()
            .iter()
            .map(|b| DomNode {
                block: b.index() as u32,
                idom: dom.idom(*b).map(|i| i.index() as u32),
                depth: dom.dominator_chain(*b).len().saturating_sub(1),
            })
            .collect();
        out.push(DominatorTree {
            function_index: fi as u32,
            function: func_name(ir, func),
            blocks: f.blocks.len(),
            reachable: dom.rpo().len(),
            nodes,
        });
    }
    out
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
