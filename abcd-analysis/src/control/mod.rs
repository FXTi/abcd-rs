//! Control-flow analyses over the v0.2 IR (design/ir-v0.2.md §2 T5,
//! design/analysis-strategy.md §5.1).
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
//!   there. v0.2 materializes the same relation as first-class
//!   [`EdgeKind::Exceptional`](abcd_ir::EdgeKind) predecessors.
//!
//! On top of these sit the graph algorithms: reverse post-order
//! ([`compute_rpo`], migrated from `abcd-lower`), reachability
//! ([`reachable_blocks`]), Cooper–Harvey–Kennedy dominators
//! ([`Dominators`]) and post-dominators ([`PostDominators`]),
//! back-edge / natural-loop detection ([`back_edges`],
//! [`natural_loop`]), and region structuring ([`structure_regions`] —
//! the d-P1 region layer for the decompile track).
//!
//! ## The dominance contract with `abcd-ir`'s verifier
//!
//! `abcd-ir::verify` keeps its own private, minimal iterative dominator
//! computation (the N45 use-def check) because the layering is one-way:
//! `abcd-ir` must never depend on `abcd-analysis`. The two implementations
//! are pinned to agree by the agreement tests (`abcd-analysis/tests/
//! corpus_dom_agreement.rs` corpus-wide and `dom_agreement_crafted.rs` on
//! hand-built shapes), which re-implement the verifier's set-based
//! algorithm verbatim as the reference. The contract:
//!
//! > Over all blocks BOTH implementations consider Normal-reachable —
//! > reachable from the entry in the [`Dominators`] tree AND containing
//! > the entry in the verifier's `dom[b]` — the two compute the same
//! > dominator SETS.
//!
//! Two divergence classes are documented and excluded (both dead-code
//! shapes the verifier's N45 check exempts anyway): (1) unreachable
//! Normal-edge cycles keep the verifier's initial "everything" set while
//! the tree reports them unreachable; (2) a reachable block with an
//! unreachable Normal predecessor is *polluted* by the verifier's all-set
//! initialization (the intersection with the dead predecessor's set
//! empties it, so the verifier treats the block as unreachable) while the
//! CHK tree computes dominators on the reachable subgraph — the
//! graph-theoretic answer. The divergence always weakens the verifier's
//! check, never strengthens it.

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
    ClassifiedEdge, EdgeClass, EscapeHatch, IrreducibleCore, LoopInfo, LoopKind, RegionError,
    RegionId, RegionNode, RegionTree, TryPlan, structure_regions,
};
pub use rpo::compute_rpo;
pub use succs::{augmented_succs, block_succs, inst_succs};
