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
//! ([`compute_rpo`], migrated verbatim from `abcd-lower`), reachability
//! ([`reachable_blocks`]), Cooper–Harvey–Kennedy dominators
//! ([`Dominators`]) and post-dominators ([`PostDominators`]), and
//! back-edge / natural-loop detection ([`back_edges`],
//! [`natural_loop`]).
//!
//! ## The dominance contract with `abcd-ir`'s verifier
//!
//! `abcd-ir::verify` keeps its own private, minimal iterative dominator
//! computation (the N45 use-def check) because the layering is one-way:
//! `abcd-ir` must never depend on `abcd-analysis`. The two implementations
//! are pinned to agree by the corpus agreement test
//! (`abcd-analysis/tests/corpus_dom_agreement.rs`, which re-implements the
//! verifier's set-based algorithm verbatim as the reference) over **all
//! Normal-edge-reachable blocks** of every corpus function: for any such
//! block pair `(a, b)`, `a` dominates `b` under [`Dominators`] iff `a ∈
//! dom[b]` under the verifier's algorithm. Blocks with no Normal-edge path
//! from the entry are outside the contract (the verifier's iterative sets
//! degenerate there: an unreachable block with no Normal predecessors is
//! dominated only by itself, and an unreachable Normal-edge cycle keeps the
//! initial "everything" set — both are dead-code cases the verifier exempts
//! from N45 anyway).

mod dom;
mod loops;
mod reach;
mod rpo;
mod succs;

pub use dom::{Dominators, PostDominators};
pub use loops::{back_edges, natural_loop};
pub use reach::reachable_blocks;
pub use rpo::compute_rpo;
pub use succs::{augmented_succs, block_succs, inst_succs};
