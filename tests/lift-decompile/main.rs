//! lift → decompile integration suites, migrated from
//! `abcd-decompile/tests/` (the crate-local golden tests stay in
//! `abcd-decompile/tests/`).
//!
//! Layout choice: one Cargo target per data-flow chain
//! (`tests/lift-decompile/main.rs` + one module per former standalone
//! test file) instead of per-file `tests/lift-decompile_<name>.rs`
//! targets — the target name stays `lift-decompile` and each suite is
//! selected by its module path, e.g.:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-decompile --release -- --ignored --nocapture dream_gate
//! ```
//!
//! The shared corpus helpers live in the root package's
//! `tests/common/`; the hand-built IR scaffolding the node-evidence
//! suites use is `tests/common/decompile_scaffold.rs` (verbatim from
//! abcd-decompile's crate-local common).

#[path = "../common/mod.rs"]
mod common;

mod async_node;
mod corpus_decompile;
mod corpus_stage_a;
mod dream_gate;
mod textual_oracle;
mod yield_star_node;
