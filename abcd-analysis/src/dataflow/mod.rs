//! Dataflow and pointer-analysis infrastructure (`design/analysis.md`).
//!
//! - [`framework`] — a generic monotone forward/backward block-level
//!   framework over any successor relation.
//! - [`usedef`] — use-def chains as a commodity, cached per function with
//!   explicit invalidation.
//! - [`ifds`] — the Reps–Horwitz–Sagiv IFDS tabulation solver (start-anchored
//!   path-edge worklist, `incoming`/`end_summary` tables with second-arriver
//!   replay, sparse TOP-as-absent jump-function set, deterministic iteration).
//! - [`heap`] — rung-0 allocation-site keying: heap facts keyed by
//!   `(AllocSite, field chain, k-capped)`, strong/weak updates, and the
//!   [`heap::AliasOracle`] interprocedural calling-context seam.
//! - [`alias`] — rung-1 demand-driven alias engine: memoized backward
//!   `points_to(base, at)` queries with Boomerang-style balanced-parentheses
//!   call-stack CFL-reachability, depth cap with rung-0 fallback, and
//!   [`alias::Rung1AliasOracle`].
//! - [`pta`] — rung-2 whole-module `k=1` context-sensitive Andersen-style
//!   subset pointer analysis: abstract objects keyed by
//!   `(alloc InstId, 1-call-site context)`, per-object field sensitivity,
//!   two-half delta worklist propagation, on-the-fly call-graph
//!   co-evolution, and lexical-environment stack identity
//!   ([`pta::Rung2AliasOracle`]).

pub mod alias;
pub mod framework;
pub mod heap;
pub mod ifds;
pub mod pta;
pub mod usedef;

pub use alias::{AliasEngineStats, QueryAnswer, Rung1AliasOracle};
pub use framework::{DataflowResult, Direction, MonotoneFramework, SolveConfig, solve};
pub use heap::{
    AliasOracle, AllocSiteSet, FieldChain, FieldKey, HeapRef, Rung0AliasOracle, Tribool,
};
pub use pta::{EnvAnswer, PtaConfig, PtaOutcome, PtaStats, Rung2AliasOracle, Rung2Tables};
pub use usedef::{AnalysisStore, UseDefChains};
