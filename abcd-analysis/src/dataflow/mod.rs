//! Dataflow infrastructure (design/analysis-strategy.md §5.1–§5.2).
//!
//! - [`framework`] — a generic monotone forward/backward block-level
//!   framework over any successor relation. Future `abcd-opt` refactors
//!   are intended consumers; nothing here is taint-specific.
//! - [`usedef`] — use-def chains as a commodity, cached per function with
//!   explicit invalidation.
//! - [`ifds`] — the IFDS solver skeleton (heros.md §1: path-edge worklist,
//!   `incoming`/`endSummary` tables with second-arriver replay, sparse
//!   jump-function table, TOP-as-absent, deterministic iteration).
//! - [`heap`] — heap v0 (analysis-strategy §4.4 rung 0): heap facts keyed
//!   by `(AllocSite, field chain, k-capped)`, strong/weak updates, and the
//!   [`heap::AliasOracle`] trait seam sized for a Boomerang-shaped rung-1
//!   engine (§5.2).
//! - [`alias`] — the rung-1 on-demand alias engine (§4.4 rung 1): a
//!   memoized, demand-driven backward `points_to(base, at)` query with
//!   the balanced-parentheses interprocedural discipline, a depth cap
//!   with rung-0 fallback, and the full [`heap::AliasOracle`] impl
//!   ([`alias::Rung1AliasOracle`]).

pub mod alias;
pub mod framework;
pub mod heap;
pub mod ifds;
pub mod usedef;

pub use alias::{AliasEngineStats, QueryAnswer, Rung1AliasOracle};
pub use framework::{DataflowResult, Direction, MonotoneFramework, SolveConfig, solve};
pub use heap::{
    AliasOracle, AllocSiteSet, FieldChain, FieldKey, HeapRef, Rung0AliasOracle, Tribool,
};
pub use usedef::{AnalysisStore, UseDefChains};
