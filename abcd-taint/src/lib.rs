//! # abcd-taint — taint analysis on the v0.2 IR
//!
//! The taint-analysis application crate (design/analysis-strategy.md
//! §5.2–§5.5 is the spec; this crate is its v2-P5b deliverable). It plugs
//! into `abcd-analysis`'s IFDS solver skeleton as a client
//! ([`abcd_analysis::dataflow::ifds::IfdsProblem`]) and never touches the
//! solver's internals:
//!
//! - [`fact`] — the fact model: [`fact::Fact`] = Λ or a
//!   [`fact::TaintFact`] access path (`base` + k-capped field chain),
//!   following soot-infoflow's access-path discipline with weak updates
//!   via the rung-0 heap model.
//! - [`names`] — callee-name resolution through the global-load def
//!   chain (`TryGetGlobal`/`LoadProp` → name candidates). This is what
//!   makes name-keyed summaries and sinks fire on the corpus' ~97%
//!   `UnknownCallees` call sites.
//! - [`summary`] — the minimal summary registry (summaries.md §"A
//!   minimal summary registry for a JS bytecode analyzer"):
//!   `Map<(Sym, Arity), Summary>` with flows over
//!   `{param(i), base, return, field(path)}`, clears, `is_alias`,
//!   a mini-gap `callback` flag, an `exclusive` bit, negative caching,
//!   and miss counters from day one.
//! - [`problem`] — the [`problem::TaintProblem`]: the four flow
//!   functions, driven by `Op::operands()`/`Op::has_result()` plus
//!   explicit per-family rules only where semantics demand (property
//!   loads/stores, calls + the summary wrapper, return wiring,
//!   exception edges).
//! - [`driver`] — source/sink configuration, the analysis run, and the
//!   taint-path report (line/column from `Inst.loc`, T8).
//!
//! The crate graph is the enforcement of the format-independence
//! invariant: the library depends on `abcd-ir` + `abcd-analysis` only;
//! `abcd-file`/`abcd-lift` are dev-dependencies for the corpus smoke
//! test (see the `Cargo.toml` invariant comment).

#![deny(missing_docs)]

pub mod driver;
pub mod fact;
pub mod names;
pub mod problem;
pub mod summary;

pub use driver::{
    PathStep, SinkHit, SinkSpec, SourceSpec, TaintConfig, TaintReport, run_taint,
};
pub use fact::{Fact, TaintBase, TaintFact};
pub use problem::TaintProblem;
pub use summary::{Endpoint, Flow, RegistryStats, Summary, SummaryRegistry, builtin_summaries};
