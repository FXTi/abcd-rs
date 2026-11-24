//! Corpus check for pattern-independent region structuring (`structure_regions`).

use std::collections::BTreeMap;

use abcd_analysis::control::{
    EdgeClass, EscapeHatch, LoopKind, RegionNode, RegionTree, reachable_blocks, structure_regions,
};
use abcd_ir::{FuncId, Module};

#[derive(Default)]
pub(crate) struct RegionStats {
    pub functions: usize,
    pub functions_empty: usize,
    pub functions_structured: usize,
    pub blocks_reachable: usize,
    pub blocks_dead: usize,
    pub region_nodes: usize,
    pub loops_total: usize,
    pub loops_while: usize,
    pub loops_do_while: usize,
    pub edges_internal: usize,
    pub edges_continue: usize,
    pub edges_continue_labeled: usize,
    pub edges_break: usize,
    pub edges_break_labeled: usize,
    pub irreducible_cores: usize,
    pub functions_with_irreducible: usize,
    pub escape_hist: BTreeMap<&'static str, usize>,
    pub functions_with_escape: usize,
    pub cross_arm_edges: usize,
    pub functions_with_cross_arm: usize,
    pub try_cuts: usize,
    pub try_regions: usize,
    pub errors: Vec<String>,
}

impl RegionStats {
    pub fn merge(&mut self, other: RegionStats) {
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

pub(crate) fn check_fixture(module: &Module, relative: &str) -> RegionStats {
    let mut stats = RegionStats::default();
    for fi in 0..module.functions.len() {
        let func = FuncId::new(fi as u32);
        let tree = structure_regions(module, func);
        let again = structure_regions(module, func);
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

        let mut covered = 0usize;
        for n in tree.nodes() {
            match n {
                RegionNode::Block(_) | RegionNode::If { .. } => covered += 1,
                RegionNode::Irreducible { blocks, .. } => covered += blocks.len(),
                _ => {}
            }
        }
        let universe = reachable_blocks(module, func, &|b| {
            abcd_analysis::control::block_succs(module, b)
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
}

pub(crate) fn report_and_assert(fixtures: usize, stats: RegionStats) {
    let mut try_errors = 0usize;
    for line in &stats.errors {
        try_errors += 1;
        if try_errors <= 10 {
            eprintln!("REGION-ERROR {line}");
        }
    }

    eprintln!(
        "REGION-GATE fixtures={fixtures} functions={} \
         empty={} structured={} blocks_reachable={} blocks_dead={} region_nodes={}",
        stats.functions,
        stats.functions_empty,
        stats.functions_structured,
        stats.blocks_reachable,
        stats.blocks_dead,
        stats.region_nodes
    );
    eprintln!(
        "REGION-GATE loops total={} while={} do_while={}",
        stats.loops_total, stats.loops_while, stats.loops_do_while
    );
    eprintln!(
        "REGION-GATE edges internal={} continue={}(labeled={}) break={}(labeled={})",
        stats.edges_internal,
        stats.edges_continue,
        stats.edges_continue_labeled,
        stats.edges_break,
        stats.edges_break_labeled
    );
    eprintln!(
        "REGION-GATE irreducible cores={} functions_with_irreducible={}",
        stats.irreducible_cores, stats.functions_with_irreducible
    );
    eprintln!(
        "REGION-GATE escape_hatches functions_with_escape={} histogram={:?}",
        stats.functions_with_escape, stats.escape_hist
    );
    eprintln!(
        "REGION-GATE cross_arm_edges={} functions_with_cross_arm={} try_cuts_structured_region={}",
        stats.cross_arm_edges, stats.functions_with_cross_arm, stats.try_cuts
    );
    eprintln!(
        "REGION-GATE try_regions={} try_errors={try_errors}",
        stats.try_regions
    );

    assert_eq!(
        stats.functions_structured + stats.functions_empty,
        stats.functions
    );
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
            RegionNode::Block(_) | RegionNode::If { .. } => reachable += 1,
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
