//! Opt-in corpus gate for region structuring (d-P1, design/decompile.md
//! §4.2/§7): run `abcd_analysis::control::structure_regions` over every
//! function of every corpus fixture.
//!
//! Assertions:
//!
//! - **Totality**: every function with blocks produces a root region;
//!   shapes that resist structuring are counted in the escape-hatch
//!   histogram, never panicked on.
//! - **Determinism**: two independent runs over the same module produce
//!   identical trees (`RegionTree: PartialEq`).
//! - **Zero interleaving TryRegions**: no [`RegionError`] of any kind
//!   (the lift guarantees containment; any interleaving is a bug).
//! - **Irreducible count**: printed verbatim; expected ≈0 on es2abc
//!   output (the corpus is compiler-generated).
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-analysis --release -- --ignored --nocapture corpus_regions
//! ```
//!
//! Migrated from `abcd-analysis/tests/corpus_regions.rs` to the root
//! package's `tests/lift-analysis/` target; the shared helpers moved to
//! the root package's `tests/common/`.

use crate::common;

use std::collections::BTreeMap;

use abcd_analysis::control::{
    reachable_blocks, structure_regions, EdgeClass, EscapeHatch, LoopKind, RegionNode, RegionTree,
};
use abcd_ir::FuncId;
use abcd_lift::lift_file;
use rayon::prelude::*;

/// Per-fixture (aggregatable) gate counters. Every field merges by
/// addition / map-merge, so the parallel fold is order-independent; the
/// REGION-ERROR lines travel as per-fixture ordered strings and are
/// replayed in fixture order below, byte-identical to the serial loop.
#[derive(Default)]
struct RegionStats {
    functions: usize,
    functions_empty: usize,
    functions_structured: usize,
    blocks_reachable: usize,
    blocks_dead: usize,
    region_nodes: usize,
    loops_total: usize,
    loops_while: usize,
    loops_do_while: usize,
    edges_internal: usize,
    edges_continue: usize,
    edges_continue_labeled: usize,
    edges_break: usize,
    edges_break_labeled: usize,
    irreducible_cores: usize,
    functions_with_irreducible: usize,
    escape_hist: BTreeMap<&'static str, usize>,
    functions_with_escape: usize,
    cross_arm_edges: usize,
    functions_with_cross_arm: usize,
    try_cuts: usize,
    try_regions: usize,
    /// Formatted REGION-ERROR payloads (sans the counter guard), in
    /// per-fixture function order.
    errors: Vec<String>,
}

impl RegionStats {
    fn merge(&mut self, other: RegionStats) {
        self.functions += other.functions;
        self.functions_empty += other.functions_empty;
        self.functions_structured += other.functions_structured;
        self.blocks_reachable += other.blocks_reachable;
        self.blocks_dead += other.blocks_dead;
        self.region_nodes += other.region_nodes;
        self.loops_total += other.loops_total;
        self.loops_while += other.loops_while;
        self.loops_do_while += other.loops_do_while;
        self.edges_internal += other.edges_internal;
        self.edges_continue += other.edges_continue;
        self.edges_continue_labeled += other.edges_continue_labeled;
        self.edges_break += other.edges_break;
        self.edges_break_labeled += other.edges_break_labeled;
        self.irreducible_cores += other.irreducible_cores;
        self.functions_with_irreducible += other.functions_with_irreducible;
        for (k, n) in other.escape_hist {
            *self.escape_hist.entry(k).or_insert(0) += n;
        }
        self.functions_with_escape += other.functions_with_escape;
        self.cross_arm_edges += other.cross_arm_edges;
        self.functions_with_cross_arm += other.functions_with_cross_arm;
        self.try_cuts += other.try_cuts;
        self.try_regions += other.try_regions;
        self.errors.extend(other.errors);
    }
}

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn corpus_region_gate() {
    let root = common::corpus_root();
    let paths = common::manifest_paths(&root);
    assert_eq!(paths.len(), 5517, "expected the full 5517-fixture corpus");

    // Parallel per-fixture structuring (rayon); each fixture's stats are
    // collected in manifest order and folded serially below.
    let per_fixture: Vec<RegionStats> = paths
        .par_iter()
        .map(|relative| {
            let data = std::fs::read(root.join(relative)).expect("read fixture");
            let file = abcd_file::decode(&data).expect("decode fixture");
            let module = lift_file(&file).expect("lift fixture");
            let mut stats = RegionStats::default();
            for fi in 0..module.functions.len() {
                let func = FuncId::new(fi as u32);
                let tree = structure_regions(&module, func);
                // Determinism: a fresh second run must be identical.
                let again = structure_regions(&module, func);
                assert_eq!(
                    tree, again,
                    "non-deterministic region tree in {relative} {func:?}"
                );

                stats.functions += 1;
                if module.func(func).expect("func").blocks.is_empty() {
                    stats.functions_empty += 1;
                    assert!(tree.root.is_none());
                    continue;
                }
                assert!(
                    tree.root.is_some(),
                    "function with blocks must structure in {relative} {func:?}"
                );
                stats.functions_structured += 1;

                // Totality: the tree covers every Normal-reachable block
                // exactly once (If heads and Block/Irreducible members are
                // the block-carrying nodes).
                let mut covered = 0usize;
                for n in tree.nodes() {
                    match n {
                        RegionNode::Block(_) => covered += 1,
                        RegionNode::If { .. } => covered += 1,
                        RegionNode::Irreducible { blocks, .. } => covered += blocks.len(),
                        _ => {}
                    }
                }
                let universe = reachable_blocks(&module, func, &|b| {
                    abcd_analysis::control::block_succs(&module, b)
                })
                .len();
                assert_eq!(
                    covered, universe,
                    "tree does not cover the reachable universe in {relative} {func:?}"
                );

                collect_stats(&tree, &mut stats);

                for e in &tree.errors {
                    stats.errors.push(format!("{relative} {func:?}: {e:?}"));
                }
            }
            stats
        })
        .collect();

    let fixtures = paths.len();
    let mut stats = RegionStats::default();
    for s in per_fixture {
        stats.merge(s);
    }
    // Replay the error lines in fixture order with the serial loop's
    // first-10 guard.
    let mut try_errors = 0usize;
    for line in &stats.errors {
        try_errors += 1;
        if try_errors <= 10 {
            eprintln!("REGION-ERROR {line}");
        }
    }

    let functions = stats.functions;
    let functions_empty = stats.functions_empty;
    let functions_structured = stats.functions_structured;
    let blocks_reachable = stats.blocks_reachable;
    let blocks_dead = stats.blocks_dead;
    let region_nodes = stats.region_nodes;
    let loops_total = stats.loops_total;
    let loops_while = stats.loops_while;
    let loops_do_while = stats.loops_do_while;
    let edges_internal = stats.edges_internal;
    let edges_continue = stats.edges_continue;
    let edges_continue_labeled = stats.edges_continue_labeled;
    let edges_break = stats.edges_break;
    let edges_break_labeled = stats.edges_break_labeled;
    let irreducible_cores = stats.irreducible_cores;
    let functions_with_irreducible = stats.functions_with_irreducible;
    let escape_hist = &stats.escape_hist;
    let functions_with_escape = stats.functions_with_escape;
    let cross_arm_edges = stats.cross_arm_edges;
    let functions_with_cross_arm = stats.functions_with_cross_arm;
    let try_cuts = stats.try_cuts;
    let try_regions = stats.try_regions;

    eprintln!(
        "REGION-GATE fixtures={fixtures} functions={functions} \
         empty={functions_empty} structured={functions_structured} \
         blocks_reachable={blocks_reachable} blocks_dead={blocks_dead} \
         region_nodes={region_nodes}"
    );
    eprintln!(
        "REGION-GATE loops total={loops_total} while={loops_while} do_while={loops_do_while}"
    );
    eprintln!(
        "REGION-GATE edges internal={edges_internal} \
         continue={edges_continue}(labeled={edges_continue_labeled}) \
         break={edges_break}(labeled={edges_break_labeled})"
    );
    eprintln!(
        "REGION-GATE irreducible cores={irreducible_cores} \
         functions_with_irreducible={functions_with_irreducible}"
    );
    eprintln!(
        "REGION-GATE escape_hatches functions_with_escape={functions_with_escape} \
         histogram={escape_hist:?}"
    );
    eprintln!(
        "REGION-GATE cross_arm_edges={cross_arm_edges} \
         functions_with_cross_arm={functions_with_cross_arm} \
         try_cuts_structured_region={try_cuts}"
    );
    eprintln!("REGION-GATE try_regions={try_regions} try_errors={try_errors}");

    // Hard gates: every non-empty function structured, zero hard errors
    // (in particular: zero interleaving TryRegions).
    assert_eq!(functions_structured + functions_empty, functions);
    assert_eq!(
        try_errors, 0,
        "region errors on the corpus (see REGION-ERROR lines above)"
    );
}

fn collect_stats(tree: &RegionTree, stats: &mut RegionStats) {
    stats.region_nodes += tree.nodes().len();
    stats.blocks_dead += tree.dead_blocks.len();
    stats.try_regions += tree.try_plans.len();
    stats.try_cuts += tree
        .try_plans
        .iter()
        .filter(|p| p.cuts_structured_region)
        .count();
    stats.cross_arm_edges += tree.cross_arm_edges.len();
    if !tree.cross_arm_edges.is_empty() {
        stats.functions_with_cross_arm += 1;
    }
    stats.loops_total += tree.loops.len();
    for l in &tree.loops {
        match l.kind {
            LoopKind::While => stats.loops_while += 1,
            LoopKind::DoWhile => stats.loops_do_while += 1,
        }
    }
    let mut reachable = 0usize;
    for n in tree.nodes() {
        match n {
            RegionNode::Block(_) => reachable += 1,
            RegionNode::If { .. } => reachable += 1,
            RegionNode::Irreducible { blocks, .. } => reachable += blocks.len(),
            _ => {}
        }
    }
    stats.blocks_reachable += reachable;
    for e in &tree.edges {
        match e.class {
            EdgeClass::Internal => stats.edges_internal += 1,
            EdgeClass::Continue { labeled, .. } => {
                stats.edges_continue += 1;
                if labeled {
                    stats.edges_continue_labeled += 1;
                }
            }
            EdgeClass::Break { labeled, .. } => {
                stats.edges_break += 1;
                if labeled {
                    stats.edges_break_labeled += 1;
                }
            }
        }
    }
    stats.irreducible_cores += tree.irreducible.len();
    if !tree.irreducible.is_empty() {
        stats.functions_with_irreducible += 1;
    }
    if !tree.escape_hatches.is_empty() {
        stats.functions_with_escape += 1;
    }
    for h in &tree.escape_hatches {
        let key = match h {
            EscapeHatch::MultiEntry { .. } => "multi_entry",
            EscapeHatch::Stranded { .. } => "stranded",
            EscapeHatch::CrossEdge { .. } => "cross_edge",
        };
        *stats.escape_hist.entry(key).or_insert(0) += 1;
    }
}
