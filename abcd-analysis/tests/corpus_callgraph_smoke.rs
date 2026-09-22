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
//! cargo test -p abcd-analysis --test corpus_callgraph_smoke --release -- --ignored
//! ```

mod common;

use abcd_analysis::callgraph::{CallGraph, CallTargets};
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
    assert!(
        total_histogram.total() > 0,
        "the corpus contains call sites"
    );
}
