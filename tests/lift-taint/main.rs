//! lift → taint integration suites, migrated from `abcd-taint/tests/`
//! (the crate-local mechanism tests stay in `abcd-taint/tests/`).
//!
//! Layout choice: one Cargo target per data-flow chain
//! (`tests/lift-taint/main.rs` + one module per former standalone test
//! file) instead of per-file `tests/lift-taint_<name>.rs` targets — the
//! target name stays `lift-taint` and each suite is selected by its
//! module path, e.g.:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-taint --release -- --ignored --nocapture probes
//! ```
//!
//! The shared corpus helpers live in the root package's
//! `tests/common/`; the hand-built IR scaffolding the probe suite uses
//! is `tests/common/taint_scaffold.rs` (verbatim from abcd-taint's
//! crate-local common).

#[path = "../common/mod.rs"]
mod common;

mod corpus_callee_names;
mod corpus_taint_smoke;
mod probes;
