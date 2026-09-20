//! N49 regression (Phase 5): a block that emits zero bytecodes must be a
//! hard `LowerError::ZeroExtentBlock`, never a silent layout.
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

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::inst::InstData;
use abcd_ir::lower::{LowerError, lower_function};
use abcd_ir::module::Module;
use abcd_ir::types::IrType;

#[test]
fn zero_emission_block_is_a_hard_error() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let dead;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        // A block with no instructions and no terminator: emits zero
        // bytecodes at isel. Unreachable in the terminator-successor model
        // but still laid out (compute_rpo appends unreachable blocks).
        dead = builder.create_block();
        let x = builder.emit_val(InstData::LiteralNumber(1.0), IrType::default());
        builder.emit_void(InstData::Return { value: Some(x) });
    }
    let err =
        lower_function(&module, func).expect_err("a zero-emission block must not lower silently");
    assert!(
        matches!(err, LowerError::ZeroExtentBlock { block, .. } if block == dead),
        "expected ZeroExtentBlock for the terminator-less block, got {err:?}"
    );
}
