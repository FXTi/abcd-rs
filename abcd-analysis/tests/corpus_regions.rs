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
//! cargo test -p abcd-analysis --test corpus_regions --release -- --ignored --nocapture
//! ```

mod common;

use std::collections::BTreeMap;

use abcd_analysis::control::{
    EdgeClass, EscapeHatch, LoopKind, RegionNode, RegionTree, reachable_blocks, structure_regions,
};
use abcd_ir::FuncId;
use abcd_lift::lift_file;

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn corpus_region_gate() {
    let root = common::corpus_root();
    let paths = common::manifest_paths(&root);
    assert_eq!(paths.len(), 2787, "expected the full 2787-fixture corpus");

    let mut fixtures = 0usize;
    let mut functions = 0usize;
    let mut functions_empty = 0usize;
    let mut functions_structured = 0usize;
    let mut blocks_reachable = 0usize;
    let mut blocks_dead = 0usize;
    let mut region_nodes = 0usize;
    let mut loops_total = 0usize;
    let mut loops_while = 0usize;
    let mut loops_do_while = 0usize;
    let mut edges_internal = 0usize;
    let mut edges_continue = 0usize;
    let mut edges_continue_labeled = 0usize;
    let mut edges_break = 0usize;
    let mut edges_break_labeled = 0usize;
    let mut irreducible_cores = 0usize;
    let mut functions_with_irreducible = 0usize;
    let mut escape_hist: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut functions_with_escape = 0usize;
    let mut cross_arm_edges = 0usize;
    let mut functions_with_cross_arm = 0usize;
    let mut try_cuts = 0usize;
    let mut try_regions = 0usize;
    let mut try_errors = 0usize;

    for relative in &paths {
        let data = std::fs::read(root.join(relative)).expect("read fixture");
        let file = abcd_file::decode(&data).expect("decode fixture");
        let module = lift_file(&file).expect("lift fixture");
        fixtures += 1;
        for fi in 0..module.functions.len() {
            let func = FuncId::new(fi as u32);
            let tree = structure_regions(&module, func);
            // Determinism: a fresh second run must be identical.
            let again = structure_regions(&module, func);
            assert_eq!(
                tree, again,
                "non-deterministic region tree in {relative} {func:?}"
            );

            functions += 1;
            if module.func(func).expect("func").blocks.is_empty() {
                functions_empty += 1;
                assert!(tree.root.is_none());
                continue;
            }
            assert!(
                tree.root.is_some(),
                "function with blocks must structure in {relative} {func:?}"
            );
            functions_structured += 1;

            // Totality: the tree covers every Normal-reachable block
            // exactly once (If heads and Block/Irreducible members are the
            // block-carrying nodes).
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

            collect_stats(
                &tree,
                &mut blocks_reachable,
                &mut blocks_dead,
                &mut region_nodes,
                &mut loops_total,
                &mut loops_while,
                &mut loops_do_while,
                &mut edges_internal,
                &mut edges_continue,
                &mut edges_continue_labeled,
                &mut edges_break,
                &mut edges_break_labeled,
                &mut irreducible_cores,
                &mut functions_with_irreducible,
                &mut escape_hist,
                &mut functions_with_escape,
                &mut cross_arm_edges,
                &mut functions_with_cross_arm,
                &mut try_cuts,
                &mut try_regions,
            );

            for e in &tree.errors {
                try_errors += 1;
                if try_errors <= 10 {
                    eprintln!("REGION-ERROR {relative} {func:?}: {e:?}");
                }
            }
        }
    }

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

#[allow(clippy::too_many_arguments)]
fn collect_stats(
    tree: &RegionTree,
    blocks_reachable: &mut usize,
    blocks_dead: &mut usize,
    region_nodes: &mut usize,
    loops_total: &mut usize,
    loops_while: &mut usize,
    loops_do_while: &mut usize,
    edges_internal: &mut usize,
    edges_continue: &mut usize,
    edges_continue_labeled: &mut usize,
    edges_break: &mut usize,
    edges_break_labeled: &mut usize,
    irreducible_cores: &mut usize,
    functions_with_irreducible: &mut usize,
    escape_hist: &mut BTreeMap<&'static str, usize>,
    functions_with_escape: &mut usize,
    cross_arm_edges: &mut usize,
    functions_with_cross_arm: &mut usize,
    try_cuts: &mut usize,
    try_regions: &mut usize,
) {
    *region_nodes += tree.nodes().len();
    *blocks_dead += tree.dead_blocks.len();
    *try_regions += tree.try_plans.len();
    *try_cuts += tree
        .try_plans
        .iter()
        .filter(|p| p.cuts_structured_region)
        .count();
    *cross_arm_edges += tree.cross_arm_edges.len();
    if !tree.cross_arm_edges.is_empty() {
        *functions_with_cross_arm += 1;
    }
    *loops_total += tree.loops.len();
    for l in &tree.loops {
        match l.kind {
            LoopKind::While => *loops_while += 1,
            LoopKind::DoWhile => *loops_do_while += 1,
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
    *blocks_reachable += reachable;
    for e in &tree.edges {
        match e.class {
            EdgeClass::Internal => *edges_internal += 1,
            EdgeClass::Continue { labeled, .. } => {
                *edges_continue += 1;
                if labeled {
                    *edges_continue_labeled += 1;
                }
            }
            EdgeClass::Break { labeled, .. } => {
                *edges_break += 1;
                if labeled {
                    *edges_break_labeled += 1;
                }
            }
        }
    }
    *irreducible_cores += tree.irreducible.len();
    if !tree.irreducible.is_empty() {
        *functions_with_irreducible += 1;
    }
    if !tree.escape_hatches.is_empty() {
        *functions_with_escape += 1;
    }
    for h in &tree.escape_hatches {
        let key = match h {
            EscapeHatch::MultiEntry { .. } => "multi_entry",
            EscapeHatch::Stranded { .. } => "stranded",
            EscapeHatch::CrossEdge { .. } => "cross_edge",
        };
        *escape_hist.entry(key).or_insert(0) += 1;
    }
}
