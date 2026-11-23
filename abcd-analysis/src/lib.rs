//! # abcd-analysis — analysis infrastructure on the v0.2 IR
//!
//! The format-independent analysis crate (design/analysis-strategy.md §5):
//! everything here consumes only [`abcd_ir`], never the container, ISA,
//! lift, lower, or optimizer crates (the crate graph is the enforcement —
//! see the `Cargo.toml` invariant comment).
//!
//! Four module families:
//!
//! - [`control`] — control-flow analyses: successor relations (Normal and
//!   exception-augmented), reverse post-order, reachability,
//!   Cooper–Harvey–Kennedy dominators/post-dominators, back-edge and
//!   natural-loop detection, and pattern-independent region trees
//!   ([`control::structure_regions`]). `abcd-lower`'s CFG helpers
//!   live here (migrated at v2-P5a; the lowering corpus byte-identity gate
//!   pins the move).
//! - [`dataflow`] — a generic monotone forward/backward framework, use-def
//!   chains as a cached commodity, the IFDS solver skeleton (path-edge
//!   worklist, `incoming`/`endSummary` tables, deterministic iteration —
//!   heros.md §1/§5), heap v0 ([`dataflow::heap`], rung 0), the on-demand
//!   backward alias engine ([`dataflow::alias`], rung 1), and the
//!   whole-module `k=1` context-sensitive PTA ([`dataflow::pta`], rung 2,
//!   co-evolving with the call graph).
//! - [`frame`] — the vendored frame-slot model (N66): which leading
//!   `params` slots are the implicit `[func][newTarget][this]` slots,
//!   shared by every interprocedural arg↔param binding.
//! - [`callgraph`] — the on-the-fly call graph: direct calls resolve
//!   statically; dynamic callees are traced backward through
//!   `Mov`/`Phi`/`LoadConst`/`AllocClosure` def chains; unresolved sites
//!   get an explicit [`callgraph::CallTargets::UnknownCallees`] marker,
//!   never silently dropped. Rung 1 adds
//!   [`callgraph::CallGraph::refine_with_points_to`]; rung 2 produces its
//!   co-evolved call graph directly in [`dataflow::pta`].
//!
//! What is deliberately NOT here: IDE value computation (heros phase II)
//! and any taint-specific fact type or source/sink configuration (that is
//! `abcd-taint`, v2-P5b). See `abcd-analysis/README.md` for the module map
//! and the precision ladder.

#![deny(missing_docs)]

pub mod callgraph;
pub mod control;
pub mod dataflow;
pub mod frame;

#[cfg(test)]
mod testutil;
