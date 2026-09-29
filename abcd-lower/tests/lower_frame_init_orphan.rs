//! Frame-initial const attribution regression: `frame_init_consts`
//! attributes `ValueDef::Const` values to functions by id range, using
//! each function's anchor minimum (params / handler exception values /
//! instruction results). A DEGENERATE function — no params, no
//! result-carrying instructions, no try regions — has no anchor at all,
//! so its frame-initial constants found no owner: register allocation
//! never colored them and lowering died with
//! `LowerError::UnallocatedOperand`.
//!
//! The degenerate shape is real: a 0-argument static method whose only
//! bytecode is a bare `return` never writes the accumulator, so the
//! lift resolves the `Return` operand to the frame-initial constant
//! (design/ir-v0.2.md §5.1). es2abc's real output never produces it
//! (every method carries the [func][newtarget][this] implicit frame
//! slots as params, anchoring the range), which is why the corpus never
//! tripped it.
//!
//! The fix attributes a USED frame-initial const to the function(s)
//! using it (use-based attribution, exactly v0.1's owning-function
//! placement); the id-range rule remains the fallback for unused consts.

mod common;

use abcd_ir::{Const, FuncId, FunctionKind, Module, Op};
use abcd_isa::Bytecode;
use abcd_lower::{LowerOptions, lower_function, lower_function_with_options};

use common::V2Builder;

/// The degenerate shape: one function, no params, a single
/// `Return { value: Some(frame_init_undefined) }`. The const is the
/// module's very first value — no anchor exists anywhere.
fn build_degenerate_only() -> (Module, FuncId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "g", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let undef = b.create_const_value(Const::Undefined);
        b.emit_void(Op::Return { value: Some(undef) });
    }
    (module, func)
}

/// The degenerate shape AFTER an anchored function: `f` has a param
/// (anchor minimum 0); `g` is degenerate and its frame-initial const
/// (a higher id) positionally sorts into `f`'s id range — the
/// wrong-owner case of the attribution hole.
fn build_degenerate_after_anchored() -> (Module, FuncId, FuncId) {
    let mut module = Module::new();
    let anchored = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, anchored);
        let _param_anchor = b.create_param();
        b.emit_void(Op::Return { value: None });
    }
    let degenerate = V2Builder::create_function(&mut module, "g", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, degenerate);
        let undef = b.create_const_value(Const::Undefined);
        b.emit_void(Op::Return { value: Some(undef) });
    }
    (module, anchored, degenerate)
}

#[test]
fn anchorless_function_frame_init_const_lowers() {
    let (module, func) = build_degenerate_only();
    let result = lower_function(&module, func)
        .expect("the frame-init const used by Return must be colored and materialized");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldundefined)),
        "the seed load materializes at the entry top: {:?}",
        result.bytecodes
    );
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Return)),
        "the return uses the seeded value: {:?}",
        result.bytecodes
    );
}

#[test]
fn anchorless_function_frame_init_const_lowers_under_prune_option() {
    let (module, func) = build_degenerate_only();
    // v0.1-opt parity: the used gate must not drop the seed either —
    // the const IS used (by the Return).
    let result = lower_function_with_options(
        &module,
        func,
        LowerOptions {
            prune_unused_frame_init_consts: true,
        },
    )
    .expect("the used frame-init const survives the opt-parity use gate");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldundefined)),
        "the used seed's load is emitted: {:?}",
        result.bytecodes
    );
}

#[test]
fn degenerate_function_after_anchored_function_owns_its_const() {
    let (module, anchored, degenerate) = build_degenerate_after_anchored();
    let result = lower_function(&module, degenerate)
        .expect("the degenerate function's const must not sort into the previous function's range");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldundefined)),
        "the degenerate function materializes its own seed: {:?}",
        result.bytecodes
    );
    // The anchored function must NOT absorb the degenerate function's
    // seed: its stream stays `returnundefined` only.
    let anchored_result = lower_function(&module, anchored).expect("the anchored function lowers");
    assert!(
        !anchored_result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldundefined)),
        "no foreign seed leaks into the anchored function: {:?}",
        anchored_result.bytecodes
    );
}

#[test]
fn unused_const_in_anchorless_function_stays_unowned() {
    // Residual boundary (documented in `frame_init_consts`): an UNUSED
    // frame-initial const of a degenerate function carries no use to
    // reverse-lookup and no anchor range to sort into, so it finds no
    // owner. Nothing references it, so lowering still succeeds; the
    // seed load is not materialized (the lift never produces this
    // shape — its lazily created frame-initial consts are wired into
    // the instruction whose read created them).
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "g", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let _unused = b.create_const_value(Const::Undefined);
        b.emit_void(Op::Return { value: None });
    }
    let result = lower_function(&module, func).expect("no live operand references the const");
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldundefined)),
        "an unused, unowned seed is not materialized: {:?}",
        result.bytecodes
    );
}
