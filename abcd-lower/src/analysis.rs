//! CFG traversal and successor relations — MIGRATED to
//! `abcd_analysis::control` at v2-P5a (design/analysis-strategy.md §5;
//! the corpus byte-identity gate pinned the move). This module is a
//! re-export shim so existing lowering code and tests keep their paths.

pub use abcd_analysis::control::{augmented_succs, block_succs, compute_rpo, inst_succs};
