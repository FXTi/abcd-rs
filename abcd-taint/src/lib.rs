//! # abcd-taint — interprocedural IFDS taint analysis on `abcd-ir`
//!
//! Taint-analysis engine (`design/analysis.md`, `design/decisions.md`) built as
//! a client of `abcd-analysis`'s [`abcd_analysis::dataflow::ifds::IfdsProblem`]
//! tabulation solver:
//!
//! - [`fact`] — the fact domain: [`fact::Fact`] = `Λ` (zero fact) or a
//!   [`fact::TaintFact`] access path (`base` + `k`-capped field chain),
//!   applying strong or weak updates via the rungs 0–2 alias oracle ladder
//!   ([`oracle`]).
//! - [`names`] — callee-name resolution through global and property load
//!   definition chains (`TryGetGlobal`/`LoadProp` → qualified name candidates),
//!   enabling name-keyed summaries and sinks on dynamic JS/ArkTS call sites.
//! - [`summary`] — builtin and library summary registry (`Map<(Sym, Arity), Summary>`):
//!   endpoint flows over `{param(i), any-param-from(start), base, return, field(path), return-field(path)}`,
//!   clears, `is_alias`, callback gap specifications, `exclusive` dispatch,
//!   negative caching, and hit/miss telemetry.
//! - [`gap`] — callback-gap propagation: summary call sites taking higher-order
//!   callbacks (`Array.prototype.map`, `forEach`, `Promise.prototype.then`, …)
//!   materialize synthetic call edges into resolved callback bodies and wire
//!   tainted formals and return values back to the summary result.
//! - [`problem`] — [`problem::TaintProblem`]: normal, call, return, and
//!   call-to-return flow functions driven by `Op::operands()`/`Op::has_result()`,
//!   explicit property/global/module/lexical transfer rules, and exception-edge
//!   propagation.
//! - [`driver`] — source/sink configuration, solver execution, and witness-path
//!   reconstruction with source line/column attribution (`Inst.loc`).
//! - [`prototype`] — receiver prototype-family inference from allocation kinds,
//!   constant definition chains, and global-store provenance, resolving
//!   instance method calls (e.g. `arr.pop()` → `Array.prototype.pop`).
//!
//! Library `[dependencies]` reference only `abcd-ir` and `abcd-analysis`,
//! preserving strict format independence.

#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]

mod closed_dispatch;
pub mod driver;
pub mod fact;
pub mod gap;
pub mod names;
pub mod ohos;
pub mod oracle;
pub mod problem;
pub mod prototype;
pub mod summary;

pub use driver::{
    PathStep, PreparedModule, SinkHit, SinkSpec, SourceSpec, TaintConfig, TaintReport, run_taint,
    run_taint_full, run_taint_prepared, run_taint_prepared_full,
};
pub use fact::{Fact, TaintBase, TaintFact, UNCAUGHT_EXCEPTION_VALUE};
pub use gap::GapCallGraph;
pub use ohos::{OHOS_PRESET_VERSION, apply_ohos_preset, ohos_preset};
pub use oracle::Oracle;
pub use problem::TaintProblem;
pub use prototype::{FamilyAnswer, ProtoFamily, PrototypeResolver};
pub use summary::{
    CallbackGap, Endpoint, Flow, GapEnter, RegistryStats, Summary, SummaryRegistry,
    builtin_summaries,
};
