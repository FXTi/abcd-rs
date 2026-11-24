//! CFG traversal and successor relations — re-exported from
//! `abcd_analysis::control` (`design/analysis.md`). This module provides a
//! crate-local path for lowering passes and integration tests.

pub use abcd_analysis::control::{augmented_succs, block_succs, compute_rpo, inst_succs};
