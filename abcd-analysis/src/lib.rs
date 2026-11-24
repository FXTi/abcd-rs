//! # abcd-analysis — static analysis infrastructure on `abcd-ir`
//!
//! Format-independent static analysis library (`design/analysis.md`,
//! `design/ir.md`): everything here consumes only [`abcd_ir`], never the
//! container, ISA, lift, lower, or optimizer crates.
//!
//! Four module families:
//!
//! - [`control`] — control-flow analyses: successor relations (`Normal` and
//!   exception-augmented), reverse post-order, reachability,
//!   Cooper–Harvey–Kennedy dominators/post-dominators, back-edge and
//!   natural-loop detection, and pattern-independent region trees
//!   ([`control::structure_regions`]).
//! - [`dataflow`] — a generic monotone forward/backward framework, cached
//!   use-def chains, the deterministic IFDS tabulation solver
//!   ([`dataflow::ifds`]), alloc-site heap keying ([`dataflow::heap`], rung 0),
//!   the on-demand backward alias engine ([`dataflow::alias`], rung 1), and the
//!   whole-module `k=1` context-sensitive pointer analysis ([`dataflow::pta`],
//!   rung 2, co-evolving with the call graph).
//! - [`frame`] — the ArkCompiler frame-slot model: identifies which leading
//!   `params` slots hold the implicit `[func][new.target][this]` values for
//!   interprocedural argument↔parameter binding.
//! - [`callgraph`] — the on-the-fly call graph: direct calls resolve
//!   statically; dynamic callees trace backward through
//!   `Mov`/`Phi`/`LoadConst`/`AllocClosure` definition chains; unresolved sites
//!   record an explicit [`callgraph::CallTargets::UnknownCallees`] marker
//!   (never silently dropped). Rung 1 adds
//!   [`callgraph::CallGraph::refine_with_points_to`]; rung 2 produces its
//!   co-evolved call graph directly in [`dataflow::pta`].
//!
//! Taint-specific fact lattices, summaries, and source/sink configuration live
//! in `abcd-taint`. See `abcd-analysis/README.md` for the module map and
//! precision ladder.

#![deny(missing_docs)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]

pub mod callgraph;
pub mod control;
pub mod dataflow;
pub mod frame;
pub mod module_link;
pub mod ohos_lifecycle;

#[cfg(test)]
mod testutil;
