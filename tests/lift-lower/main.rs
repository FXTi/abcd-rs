//! lift → lower integration suites, migrated from `abcd-lower/tests/`
//! (the cross-crate corpus gates; the crate-local L1 lowering tests stay
//! in `abcd-lower/tests/`).
//!
//! Layout choice: one Cargo target per data-flow chain
//! (`tests/lift-lower/main.rs` + one module per former standalone test
//! file) instead of per-file `tests/lift-lower_<name>.rs` targets — the
//! target name stays `lift-lower` and each suite is selected by its
//! module path, e.g.:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-lower --release -- --ignored --nocapture corpus_lower_oracle
//! ```

mod corpus_lower_async;
mod corpus_lower_oracle;
mod lower_determinism;
mod lower_sendable_class;
mod n71_ic_slots;
mod regalloc_pressure;
mod rewrite_pipeline;
mod test262_vm;
