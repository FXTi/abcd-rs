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
//! (`design/ir.md` §3). es2abc's real output never produces it
//! (every method carries the `[func][new.target][this]` implicit frame
//! slots as params, anchoring the range), which is why the corpus never
//! tripped it.
//!
//! `frame_init_consts` reads `FunctionData::frame_init_consts` and appends
//! any unrecorded `ValueDef::Const` operand referenced in `func.blocks`.

use crate::common;
use abcd_ir::{Const, FuncId, FunctionKind, Module, Op, Ty, Value, ValueDef, ValueId};
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
fn anchorless_function_frame_init_const_lowers_with_options() {
    let (module, func) = build_degenerate_only();
    let result = lower_function_with_options(&module, func, LowerOptions::default())
        .expect("the used frame-init const lowers cleanly");
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
fn unowned_unused_arena_const_is_not_materialized() {
    // An unreferenced `ValueDef::Const` pushed directly into `module.values`
    // without being registered in `func.frame_init_consts` is not owned by
    // `func` and must not be materialized (#30).
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "g", FunctionKind::Function);
    let cid = module.consts.push(Const::Undefined);
    let _orphan = ValueId::new(module.values.len() as u32);
    module.values.push(Value {
        def: ValueDef::Const(cid),
        ty: Ty::Any,
    });
    {
        let mut b = V2Builder::new(&mut module, func);
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
