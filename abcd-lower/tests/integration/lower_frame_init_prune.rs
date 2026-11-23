//! Frame-initial constant ownership & ADCE pruning regression (#30):
//! `FunctionData::frame_init_consts` owns each function's seeded
//! `ValueDef::Const` values directly. Unoptimized lowering materializes all
//! owned seeds (`v2lift` parity); running ADCE (`abcd-opt`) sweeps unused
//! entries from `func.frame_init_consts`, so lowering skips unused seed loads
//! automatically without any `LowerOptions` flag (`v2opt` parity).

use crate::common;
use abcd_ir::verify_module;
use abcd_ir::{Const, Module, Op};
use abcd_isa::Bytecode;
use abcd_lower::lower_function;

use common::V2Builder;

/// One function `f()` ending in `return undefined`, with two
/// frame-initial-style const values attributed to it: one UNUSED (the
/// discarded-read seed shape), one used by a store.
fn build() -> (Module, abcd_ir::FuncId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", abcd_ir::FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let _param_anchor = b.create_param();
        let _unused = b.create_const_value(Const::Undefined);
        let used = b.create_const_value(Const::Hole);
        let obj = b.emit_val(Op::LoadNewTarget);
        let name = b.sym("x");
        b.emit_void(Op::StoreProp {
            object: obj,
            name,
            value: used,
        });
        b.emit_void(Op::Return { value: None });
    }
    (module, func)
}

#[test]
fn unoptimized_lowering_materializes_owned_unused_seed() {
    let (module, func) = build();
    let report = verify_module(&module);
    assert!(report.is_ok(), "{:?}", report.errors);
    let result = lower_function(&module, func).expect("lowers");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldundefined)),
        "owned unused seed load is emitted: {:?}",
        result.bytecodes
    );
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldhole)),
        "used seed load is emitted: {:?}",
        result.bytecodes
    );
}

#[test]
fn swept_frame_init_consts_skips_unused_seed_keeps_used() {
    let (mut module, func) = build();
    // Simulate ADCE sweeping the unused `Undefined` entry while retaining the
    // live `Hole` entry (`abcd-opt`'s `Adce` performs this sweep).
    module.functions[func.index()].frame_init_consts.remove(0);
    let result = lower_function(&module, func).expect("lowers");
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldundefined)),
        "swept unused seed is not materialized: {:?}",
        result.bytecodes
    );
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldhole)),
        "used seed still materializes: {:?}",
        result.bytecodes
    );
}
