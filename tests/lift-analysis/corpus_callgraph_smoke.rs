//! Corpus check for base `CallGraph` + Rung-2 `pta::analyze` completeness and
//! N20 determinism.

use abcd_analysis::callgraph::{CallGraph, CallTargets, ResolutionHistogram};
use abcd_analysis::dataflow::pta::{PtaConfig, PtaStats};
use abcd_ir::Module;

#[derive(Default)]
pub(crate) struct FixtureStats {
    pub functions: usize,
    pub histogram: ResolutionHistogram,
    pub rung2_histogram: ResolutionHistogram,
    pub pta_stats: PtaStats,
    pub pta_capped: usize,
}

impl FixtureStats {
    pub fn merge(&mut self, b: Self) {
        self.functions += b.functions;
        self.histogram.resolved_internal += b.histogram.resolved_internal;
        self.histogram.resolved_external += b.histogram.resolved_external;
        self.histogram.resolved_mixed += b.histogram.resolved_mixed;
        self.histogram.unknown += b.histogram.unknown;
        self.rung2_histogram.resolved_internal += b.rung2_histogram.resolved_internal;
        self.rung2_histogram.resolved_external += b.rung2_histogram.resolved_external;
        self.rung2_histogram.resolved_mixed += b.rung2_histogram.resolved_mixed;
        self.rung2_histogram.unknown += b.rung2_histogram.unknown;
        self.pta_stats.activations += b.pta_stats.activations;
        self.pta_stats.facts += b.pta_stats.facts;
        self.pta_stats.flow_edges += b.pta_stats.flow_edges;
        self.pta_stats.call_edges_resolved += b.pta_stats.call_edges_resolved;
        self.pta_stats.call_sites_partial += b.pta_stats.call_sites_partial;
        self.pta_stats.env_rounds += b.pta_stats.env_rounds;
        self.pta_capped += b.pta_capped;
    }
}

pub(crate) fn check_fixture(module: &Module, relative: &str) -> FixtureStats {
    let mut out = FixtureStats {
        functions: module.functions.len(),
        ..FixtureStats::default()
    };

    let g1 = CallGraph::build(module);
    let g2 = CallGraph::build(module);
    assert_eq!(
        g1, g2,
        "call graph construction must be deterministic: {relative}"
    );

    for (fi, f) in module.functions.iter().enumerate() {
        for &b in &f.blocks {
            for &iid in &module.blocks[b.index()].insts {
                if matches!(module.insts[iid.index()].op, abcd_ir::Op::Call { .. }) {
                    let edge = g1.edge_at(iid).unwrap_or_else(|| {
                        panic!("call site {iid} in function {fi} of {relative} has no edge")
                    });
                    match &edge.targets {
                        CallTargets::Resolved(targets) => {
                            assert!(!targets.is_empty());
                            for t in targets {
                                assert!(module.func(*t).is_some());
                            }
                        }
                        CallTargets::UnknownCallees => {}
                    }
                }
            }
        }
    }

    let h = g1.histogram(module);
    out.histogram.resolved_internal += h.resolved_internal;
    out.histogram.resolved_external += h.resolved_external;
    out.histogram.resolved_mixed += h.resolved_mixed;
    out.histogram.unknown += h.unknown;

    let out1 = abcd_analysis::dataflow::pta::analyze(module, &g1, &PtaConfig::default());
    let out2 = abcd_analysis::dataflow::pta::analyze(module, &g1, &PtaConfig::default());
    assert_eq!(
        out1.graph(),
        out2.graph(),
        "rung-2 PTA must be deterministic: {relative}"
    );
    let s = out1.stats();
    out.pta_stats.activations += s.activations;
    out.pta_stats.facts += s.facts;
    out.pta_stats.flow_edges += s.flow_edges;
    out.pta_stats.call_edges_resolved += s.call_edges_resolved;
    out.pta_stats.call_sites_partial += s.call_sites_partial;
    out.pta_stats.env_rounds += s.env_rounds;
    if s.capped {
        out.pta_capped += 1;
    }
    let h2 = out1.graph().histogram(module);
    out.rung2_histogram.resolved_internal += h2.resolved_internal;
    out.rung2_histogram.resolved_external += h2.resolved_external;
    out.rung2_histogram.resolved_mixed += h2.resolved_mixed;
    out.rung2_histogram.unknown += h2.unknown;
    assert_eq!(
        out1.graph().site_count(),
        g1.site_count(),
        "rung-2 graph covers every call site: {relative}"
    );
    out
}

pub(crate) fn report_and_assert(fixtures: usize, total: FixtureStats) {
    let functions = total.functions;
    let total_histogram = total.histogram;
    let rung2_histogram = total.rung2_histogram;
    let pta_stats = total.pta_stats;
    let pta_capped = total.pta_capped;

    eprintln!("CALLGRAPH-SMOKE fixtures={fixtures} functions={functions}");
    eprintln!(
        "CALLGRAPH-HISTOGRAM sites={} resolved_internal={} resolved_external={} resolved_mixed={} unknown={}",
        total_histogram.total(),
        total_histogram.resolved_internal,
        total_histogram.resolved_external,
        total_histogram.resolved_mixed,
        total_histogram.unknown,
    );
    eprintln!(
        "RUNG2-HISTOGRAM sites={} resolved_internal={} resolved_external={} resolved_mixed={} unknown={}",
        rung2_histogram.total(),
        rung2_histogram.resolved_internal,
        rung2_histogram.resolved_external,
        rung2_histogram.resolved_mixed,
        rung2_histogram.unknown,
    );
    eprintln!(
        "RUNG2-PTA activations={} facts={} flow_edges={} call_edges_resolved={} call_sites_partial={} env_rounds={} capped={}",
        pta_stats.activations,
        pta_stats.facts,
        pta_stats.flow_edges,
        pta_stats.call_edges_resolved,
        pta_stats.call_sites_partial,
        pta_stats.env_rounds,
        pta_capped,
    );
    eprintln!("RUNG2-DETERMINISM runs=2 identical=true");
    assert!(
        total_histogram.total() > 0,
        "the corpus contains call sites"
    );
    assert_eq!(
        total_histogram.total(),
        rung2_histogram.total(),
        "the rung-2 graph covers the same sites"
    );
    assert!(
        rung2_histogram.unknown <= total_histogram.unknown,
        "rung 2 never resolves FEWER sites than the base graph"
    );
}
