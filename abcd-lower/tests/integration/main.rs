//! Consolidated integration test suite for `abcd-lower`.

mod common;

mod lower_acc_cache;
mod lower_async_acc_value;
mod lower_cmp_branch_fusion;
mod lower_copydataproperties;
mod lower_delobjprop_roles;
mod lower_errors;
mod lower_exception_edges;
mod lower_excluded_keys_window;
mod lower_frame_init_orphan;
mod lower_frame_init_prune;
mod lower_fusion_bails;
mod lower_handler_phi;
mod lower_isel_acc_spill;
mod lower_isel_construct;
mod lower_isel_wide_calls;
mod lower_layout_defensive;
mod lower_literal_negative_zero;
mod lower_method_body;
mod lower_op_arms;
mod lower_overflow_errors;
mod lower_parallel_copy_slots;
mod lower_phi_copy_cond_branch;
mod lower_phi_swap_loop;
mod lower_rpo_entry_first;
mod lower_try_range_contiguity;
mod lower_zero_extent_block;
