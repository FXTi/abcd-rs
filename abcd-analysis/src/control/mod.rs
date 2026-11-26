//! Control-flow analyses over the SSA IR (`design/ir.md`,
//! `design/analysis.md`).
//!
//! Successor relations come in two flavors, and choosing the right one is
//! the whole game:
//!
//! - **Normal** ([`block_succs`], [`inst_succs`]): terminator successors
//!   only. This is the layout/lowering relation.
//! - **Augmented** ([`augmented_succs`]): terminator successors ∪
//!   try→handler dispatch. Any analysis reasoning about reachability or
//!   value flow must use the augmented relation — a try body may end in
//!   `Throw`/`Unreachable` while the handler still reads values defined
//!   there. The IR materializes the same relation as first-class
//!   [`EdgeKind::Exceptional`](abcd_ir::EdgeKind) predecessors.
//!
//! On top of these sit the graph algorithms: reverse post-order
//! ([`compute_rpo`]), reachability ([`reachable_blocks`]),
//! Cooper–Harvey–Kennedy dominators ([`Dominators`]) and post-dominators
//! ([`PostDominators`]), back-edge / natural-loop detection ([`back_edges`],
//! [`natural_loop`]), and pattern-independent region structuring
//! ([`structure_regions`] — `design/decompile.md` §4.2).
//!
//! ## Dominance delegation and verifier agreement
//!
//! [`Dominators`] and [`PostDominators`] delegate directly to
//! [`abcd_ir::cfg::DomTree`] and [`abcd_ir::cfg::IndexedDom`] (iterative
//! Cooper–Harvey–Kennedy dominance with `O(1)` Euler-interval ancestry
//! queries), sharing the exact engine that `abcd-ir::verify` uses for SSA
//! dominance verification (`N45`, `N64`).
//!
//! The agreement suites (`tests/lift-analysis/corpus_dom_agreement.rs`
//! corpus-wide and `dom_agreement_crafted.rs` on hand-built shapes) cross-check
//! [`Dominators::normal`] against textbook iterative set-intersection dataflow:
//! over all blocks both algorithms consider Normal-reachable (excluding
//! unreachable cycles and blocks polluted by dead-predecessor all-set
//! initialization in textbook set intersection), both compute identical
//! dominator sets.

mod dom;
mod loops;
mod reach;
mod regions;
mod rpo;
mod succs;

pub use dom::{Dominators, PostDominators};
pub use loops::{back_edges, natural_loop};
pub use reach::reachable_blocks;
pub use regions::{
    CfgSubgraph, ClassifiedEdge, EdgeClass, EscapeHatch, IrreducibleCore, LoopInfo, LoopKind,
    RegionError, RegionId, RegionNode, RegionTree, TryPlan, structure_regions, structure_subgraph,
};
pub use rpo::compute_rpo;
pub use succs::{
    augmented_succs, augmented_succs_with_map, awaited_values_for_resume, block_succs,
    build_await_resume_map, inst_succs,
};
