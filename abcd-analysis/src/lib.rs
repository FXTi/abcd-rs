//! # abcd-analysis — static analysis infrastructure on `abcd-ir`
//!
//! Format-independent static analysis library (`design/analysis.md`,
//! `design/ir.md`): everything here consumes only [`abcd_ir`] (and `hashbrown`
//! for compact index-only deduplication), never the container, ISA, lift,
//! lower, or optimizer crates.
//!
//! Four module families plus cross-module & OpenHarmony support:
//!
//! - [`control`] — control-flow analyses: successor relations (`Normal` and
//!   exception-augmented) and reverse post-order delegated to [`abcd_ir::cfg`],
//!   reachability, Georgiadis Semi-NCA dominators/post-dominators, and back-edge
//!   / natural-loop detection.
//! - [`dataflow`] — use-def chains, the deterministic IFDS tabulation solver
//!   ([`dataflow::ifds`], with separated uncaught-exception edges and zero-copy
//!   [`dataflow::ifds::FlowSink::pass_through`]), alloc-site heap keying and
//!   concrete-singleton classification ([`dataflow::heap`], rung 0), the
//!   on-demand backward alias engine ([`dataflow::alias`], rung 1), and the
//!   whole-module `k=1` context-sensitive pointer analysis ([`dataflow::pta`],
//!   rung 2, co-evolving with the call graph).
//! - [`frame`] — the ArkCompiler frame-slot model: identifies which leading
//!   `params` slots hold the implicit `[func][new.target][this]` values (or
//!   static ArkTS receiver slots) for interprocedural argument↔parameter binding.
//! - [`callgraph`] — the on-the-fly call graph: direct calls resolve
//!   statically; dynamic callees trace backward through
//!   `Mov`/`Phi`/`LoadConst`/`AllocClosure` definition chains and dynamic/static
//!   class hierarchies; unresolved sites record an explicit
//!   [`callgraph::CallTargets::UnknownCallees`] marker (never silently dropped).
//!   Rung 1 adds [`callgraph::CallGraph::refine_with_points_to`]; rung 2 produces
//!   its co-evolved call graph directly in [`dataflow::pta`].
//! - [`ohmurl`], [`module_link`], [`ohos_lifecycle`] — canonical OpenHarmony
//!   [`OhmUrl`] parsing, multi-record ES module linking, and steady-state
//!   `while (*)` OpenHarmony component lifecycle [`ohos_lifecycle::EntryModel`]
//!   synthesis.
//!
//! Taint-specific fact lattices, summaries, and source/sink configuration live
//! in `abcd-taint`. See `abcd-analysis/README.md` for the module map and
//! precision ladder.

#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]

pub mod callgraph;
pub mod control;
pub mod dataflow;
pub mod frame;
pub mod module_link;
pub mod ohmurl;
pub mod ohos_lifecycle;

pub use dataflow::heap;
pub use ohmurl::{OhmUrl, OhmUrlKind};

#[cfg(test)]
mod testutil;
