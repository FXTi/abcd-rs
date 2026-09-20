//! N49 regression (v0.2 port of `abcd-ir/tests/lower_zero_extent_block.rs`):
//! a block that emits zero bytecodes must be a hard
//! `LowerError::ZeroExtentBlock`, never a silent layout.
//!
//! `reconstruct_try_blocks` computes each block's flat extent as
//! `[own offset, next greater offset)`. That formula is only sound when
//! block offsets strictly increase. On verified IR they do — every block
//! ends in a terminator and every terminator arm of `select_inst` emits
//! >= 1 bytecode. But `lower_function` also accepts UNVERIFIED input (the
//! `UnallocatedOperand` precedent), and a terminator-less block emits
//! nothing: its offset aliases the next block's, and its extent would
//! swallow the following block into this one's try/handler range —
//! silent exception misdispatch at runtime.

mod common;

use abcd_ir2::{FunctionKind, Module, Op};
use abcd_lower::{LowerError, lower_function};

use common::V2Builder;

#[test]
fn zero_emission_block_is_a_hard_error() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let dead;
    {
        let mut builder = V2Builder::new(&mut module, func);
        // A block with no instructions and no terminator: emits zero
        // bytecodes at isel. Unreachable in the terminator-successor model
        // but still laid out (compute_rpo appends unreachable blocks).
        dead = builder.create_block();
        let cid = builder.konst(abcd_ir2::Const::number(1.0));
        let x = builder.emit_val(abcd_ir2::Op::LoadConst(cid));
        builder.emit_void(Op::Return { value: Some(x) });
    }
    let err =
        lower_function(&module, func).expect_err("a zero-emission block must not lower silently");
    assert!(
        matches!(err, LowerError::ZeroExtentBlock { block, .. } if block == dead),
        "expected ZeroExtentBlock for the terminator-less block, got {err:?}"
    );
}
