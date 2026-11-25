//! Consolidated integration test suite for `abcd-opt`.

mod common;

mod opt_adce_observable_loads;
mod opt_dce_cfg_edges;
mod opt_empty_jump_phi_guard;
mod opt_fold_int_conversion;
mod opt_fold_operand_order;
mod opt_inline;
mod opt_inline_e2e;
mod opt_inline_red;
mod opt_inline_skip_reasons;
mod opt_merge_empty_phi;
mod opt_round3_soundness;
mod opt_sccp_exception_soundness;
mod opt_sccp_folds;
mod opt_try_handler_survives;
mod opt_v02_ops;
