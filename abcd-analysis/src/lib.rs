//! # abcd-analysis — analysis infrastructure on the v0.2 IR
//!
//! The format-independent analysis crate (design/analysis-strategy.md §5):
//! everything here consumes only [`abcd_ir`], never the container, ISA,
//! lift, lower, or optimizer crates (the crate graph is the enforcement —
//! see the `Cargo.toml` invariant comment).
//!
//! Three module families:
//!
//! - [`control`] — control-flow analyses: successor relations (Normal and
//!   exception-augmented), reverse post-order, reachability,
//!   Cooper–Harvey–Kennedy dominators/post-dominators, back-edge and
//!   natural-loop detection. `abcd-lower`'s CFG helpers live here (migrated
//!   at v2-P5a; the lowering corpus byte-identity gate pins the move).
//! - [`dataflow`] — a generic monotone forward/backward framework, use-def
//!   chains as a cached commodity, the IFDS solver skeleton (path-edge
//!   worklist, `incoming`/`endSummary` tables, deterministic iteration —
//!   heros.md §1/§5), and heap v0: alloc-site-keyed heap facts with
//!   strong/weak updates behind the [`dataflow::heap::AliasOracle`] trait
//!   seam (analysis-strategy §4.4 rung 0, §5.2).
//! - [`callgraph`] — the on-the-fly call graph: direct calls resolve
//!   statically; dynamic callees are traced backward through
//!   `Mov`/`Phi`/`LoadConst`/`AllocClosure` def chains; unresolved sites
//!   get an explicit [`callgraph::CallTargets::UnknownCallees`] marker,
//!   never silently dropped.
//!
//! What is deliberately NOT here: the points-to engine (rung 1 of the
//! precision ladder — the `AliasOracle` seam is sized for it), IDE value
//! computation (heros phase II), and any taint-specific fact type or
//! source/sink configuration (that is `abcd-taint`, v2-P5b). See
//! `abcd-analysis/README.md` for the module map and the precision ladder.

#![deny(missing_docs)]

pub mod callgraph;
pub mod control;
pub mod dataflow;

#[cfg(test)]
mod testutil;
