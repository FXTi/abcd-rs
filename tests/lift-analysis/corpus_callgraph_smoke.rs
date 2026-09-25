//! Opt-in corpus smoke test for the on-the-fly call graph
//! (design/analysis-strategy.md §5.4; gate 3 of v2-P5a):
//!
//! 1. build the call graph for every fixture (all 2787 rows) — no panics,
//!    and every call site is recorded (resolved OR explicitly unknown);
//! 2. build it TWICE per module and assert the graphs are equal
//!    (deterministic construction);
//! 3. print the aggregated resolution-rate histogram
//!    (resolved internal / resolved external / mixed / unknown).
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-analysis --release -- --ignored corpus_callgraph_smoke
//! ```
//!
//! Migrated from `abcd-analysis/tests/corpus_callgraph_smoke.rs` to the
//! root package's `tests/lift-analysis/` target; the shared helpers
//! moved to the root package's `tests/common/`.

use crate::common;

use abcd_analysis::callgraph::{CallGraph, CallTargets};
use abcd_analysis::dataflow::pta::PtaConfig;
use abcd_lift::lift_file;

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn callgraph_smoke_all_fixtures() {
    let root = common::corpus_root();
    let paths = common::manifest_paths(&root);
    assert_eq!(paths.len(), 2787, "expected the full 2787-fixture corpus");

    let mut fixtures = 0usize;
    let mut functions = 0usize;
    let mut total_histogram = abcd_analysis::callgraph::ResolutionHistogram::default();
    let mut rung2_histogram = abcd_analysis::callgraph::ResolutionHistogram::default();
    let mut pta_stats = abcd_analysis::dataflow::pta::PtaStats::default();
    let mut pta_capped = 0usize;

    for relative in &paths {
        let data = std::fs::read(root.join(relative)).expect("read fixture");
        let file = abcd_file::decode(&data).expect("decode fixture");
        let module = lift_file(&file).expect("lift fixture");
        fixtures += 1;
        functions += module.functions.len();

        let g1 = CallGraph::build(&module);
        let g2 = CallGraph::build(&module);
        assert_eq!(
            g1, g2,
            "call graph construction must be deterministic: {relative}"
        );

        // Every Op::Call in the module has an edge record — resolved or
        // explicitly unknown (never silently dropped).
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

        let h = g1.histogram(&module);
        total_histogram.resolved_internal += h.resolved_internal;
        total_histogram.resolved_external += h.resolved_external;
        total_histogram.resolved_mixed += h.resolved_mixed;
        total_histogram.unknown += h.unknown;

        // ── Rung 2 (t-P6): the whole-module PTA over the same module —
        // its co-evolved graph is the rung-2 call graph. Two runs must
        // be byte-identical (N20 determinism), the resolution histogram
        // is reported against the base (the rung-2 upgrade IS the
        // unknown-bucket shrink), and budget cuts are counted (loud).
        let out1 = abcd_analysis::dataflow::pta::analyze(&module, &g1, &PtaConfig::default());
        let out2 = abcd_analysis::dataflow::pta::analyze(&module, &g1, &PtaConfig::default());
        assert_eq!(
            out1.graph(),
            out2.graph(),
            "rung-2 PTA must be deterministic: {relative}"
        );
        let s = out1.stats();
        pta_stats.activations += s.activations;
        pta_stats.facts += s.facts;
        pta_stats.flow_edges += s.flow_edges;
        pta_stats.call_edges_resolved += s.call_edges_resolved;
        pta_stats.call_sites_partial += s.call_sites_partial;
        pta_stats.env_rounds += s.env_rounds;
        if s.capped {
            pta_capped += 1;
        }
        let h2 = out1.graph().histogram(&module);
        rung2_histogram.resolved_internal += h2.resolved_internal;
        rung2_histogram.resolved_external += h2.resolved_external;
        rung2_histogram.resolved_mixed += h2.resolved_mixed;
        rung2_histogram.unknown += h2.unknown;
        // The rung-2 graph records every call site too (resolved or
        // explicitly unknown — never dropped).
        assert_eq!(
            out1.graph().site_count(),
            g1.site_count(),
            "rung-2 graph covers every call site: {relative}"
        );
    }

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
