//! Control-flow analyses over the SSA IR (`design/ir.md`,
//! `design/analysis.md`, `D1`).
//!
//! Successor relations and Reverse Post-Order delegate directly to
//! [`abcd_ir::cfg`]:
//!
//! - **Normal** ([`block_succs`], [`inst_succs`]): terminator successors
//!   only. This is the layout/lowering relation.
//! - **Augmented** ([`augmented_succs`], [`augmented_succs_with_map`]):
//!   terminator successors ∪ try→handler dispatch via [`ExceptionHandlerMap`].
//!   Any analysis reasoning about reachability or value flow must use the
//!   augmented relation — a try body may end in `Throw`/`Unreachable` while
//!   the handler still reads values defined there.
//!
//! On top of these sit the graph algorithms: reverse post-order
//! ([`compute_rpo`], [`compute_rpo_with`]), reachability ([`reachable_blocks`],
//! [`reachable_from`]), Georgiadis Semi-NCA dominators ([`Dominators`]) and
//! post-dominators ([`PostDominators`]), and back-edge / natural-loop detection
//! ([`back_edges`], [`back_edges_in_blocks`], [`natural_loop`]). Region-tree
//! structuring lives downstream in `abcd-decompile::structure::regions` (`D1`).
//!
//! ## Dominance delegation and verifier agreement
//!
//! [`Dominators`] and [`PostDominators`] delegate directly to
//! [`abcd_ir::cfg::DomTree`] and [`abcd_ir::cfg::IndexedDom`] (iterative
//! Georgiadis–Tarjan–Werneck Semi-NCA dominance over flat CSR adjacency buffers
//! with `O(1)` Euler-interval ancestry queries), sharing the exact engine that
//! `abcd-ir::verify` uses for SSA dominance verification (`N45`, `N64`).
//! Unreachable blocks satisfy `dominates(dead, dead) == false`, agreeing
//! workspace-wide with [`DomTree::dominates`].

mod dom;
mod loops;
mod reach;
mod rpo;
mod succs;

pub use abcd_ir::cfg::{DomTree, ExceptionHandlerMap, IndexedDom};
pub use dom::{Dominators, PostDominators};
pub use loops::{back_edges, back_edges_in_blocks, natural_loop};
pub use reach::{reachable_blocks, reachable_from};
pub use rpo::{compute_rpo, compute_rpo_with};
pub use succs::{
    augmented_succs, augmented_succs_with_map, awaited_values_for_resume, block_succs,
    build_await_resume_map, inst_succs,
};
