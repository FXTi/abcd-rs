//! lift → analysis fused corpus gate (#37).
//!
//! Reads, decodes, and lifts each of the 5,517 corpus fixtures ONCE in a
//! single parallel pass (`rayon`), driving all three static-analysis gates on
//! the lifted [`abcd_ir::Module`]:
//! 1. `corpus_dom_agreement`: `Dominators` agreement with `abcd_ir::verify`;
//! 2. `corpus_regions`: pattern-independent region structuring totality,
//!    determinism, and `TryRegion` containment;
//! 3. `corpus_callgraph_smoke`: base `CallGraph` + Rung-2 `pta::analyze`
//!    completeness and N20 byte-identical determinism.

#[path = "../common/mod.rs"]
mod common;

mod corpus_callgraph_smoke;
mod corpus_dom_agreement;
mod corpus_regions;

use abcd_lift::lift_file;
use rayon::prelude::*;

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn corpus_analysis_gates() {
    let root = common::corpus_root();
    let paths = common::manifest_paths(&root);
    assert_eq!(paths.len(), 5517, "expected the full 5517-fixture corpus");

    let per_fixture: Vec<(
        corpus_dom_agreement::DomCounts,
        corpus_regions::RegionStats,
        corpus_callgraph_smoke::FixtureStats,
    )> = paths
        .par_iter()
        .map(|relative| {
            let data = std::fs::read(root.join(relative)).expect("read fixture");
            let file = abcd_file::decode(&data).expect("decode fixture");
            let module = lift_file(&file).expect("lift fixture");

            let dom = corpus_dom_agreement::check_fixture(&module, relative);
            let reg = corpus_regions::check_fixture(&module, relative);
            let cg = corpus_callgraph_smoke::check_fixture(&module, relative);
            (dom, reg, cg)
        })
        .collect();

    let mut dom_total = corpus_dom_agreement::DomCounts::default();
    let mut reg_total = corpus_regions::RegionStats::default();
    let mut cg_total = corpus_callgraph_smoke::FixtureStats::default();
    for (d, r, c) in per_fixture {
        dom_total.merge(d);
        reg_total.merge(r);
        cg_total.merge(c);
    }

    corpus_dom_agreement::report_and_assert(paths.len(), dom_total);
    corpus_regions::report_and_assert(paths.len(), reg_total);
    corpus_callgraph_smoke::report_and_assert(paths.len(), cg_total);
}
