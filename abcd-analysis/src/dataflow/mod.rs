//! Dataflow and pointer-analysis infrastructure (`design/analysis.md`).
//!
//! - [`usedef`] — per-function use-def chains in deterministic program order.
//! - [`ifds`] — the Reps–Horwitz–Sagiv IFDS tabulation solver (start-anchored
//!   path-edge worklist, `incoming`/`end_summary` tables with second-arriver
//!   replay, sparse TOP-as-absent jump-function set, deterministic iteration).
//! - [`heap`] — rung-0 allocation-site keying: heap facts keyed by
//!   `(AllocSite, field chain, k-capped)`, strong/weak updates, `Mov` peeling,
//!   and the [`heap::AliasOracle`] marker seam.
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
pub mod heap;
pub mod ifds;
pub mod pta;
pub mod usedef;

pub use alias::{AliasEngineStats, QueryAnswer, Rung1AliasOracle};
pub use heap::{
    AliasOracle, AllocSiteSet, FieldChain, FieldKey, HeapRef, Rung0AliasOracle,
    SingletonSiteClassifier, SiteInfo, Tribool, UpdateKind, is_concrete_singleton_site,
    is_keyed_alloc, key_may_alias, peel_movs, resolve_alloc_sites, update_kind, update_kind_for,
};
pub use ifds::{FactId, FlowOut, FlowSink};
pub use pta::{EnvAnswer, PtaConfig, PtaOutcome, PtaStats, Rung2AliasOracle, Rung2Tables};
pub use usedef::UseDefChains;
