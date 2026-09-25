//! lift → analysis integration suites, migrated from
//! `abcd-analysis/tests/` (the crate-local crafted tests stay in
//! `abcd-analysis/tests/`).
//!
//! Layout choice: one Cargo target per data-flow chain
//! (`tests/lift-analysis/main.rs` + one module per former standalone
//! test file) instead of per-file `tests/lift-analysis_<name>.rs`
//! targets — the target name stays `lift-analysis` and each suite is
//! selected by its module path, e.g.:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-analysis --release -- --ignored --nocapture corpus_regions
//! ```
//!
//! The shared corpus/dominator helpers live in the root package's
//! `tests/common/` (deduplicated from the crate-local commons).

#[path = "../common/mod.rs"]
mod common;

mod corpus_callgraph_smoke;
mod corpus_dom_agreement;
mod corpus_regions;
