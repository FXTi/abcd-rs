//! `LowerOptions::prune_unused_frame_init_consts` regression: the v0.2
//! frame-initial constants are instruction-less `ValueDef::Const` values
//! (design/ir-v0.2.md §5.1), so an optimizer cannot sweep the seed the
//! way v0.1's ADCE sweeps the seed INSTRUCTION. The lower's default
//! (v0.1-lift parity) materializes even unused seeds' loads; the option
//! (v0.1-opt parity) skips unused ones entirely.

mod common;

use abcd_ir::verify_module;
use abcd_ir::{Const, Module, Op};
use abcd_isa::Bytecode;
use abcd_lower::{LowerOptions, lower_function, lower_function_with_options};

use common::V2Builder;

/// One function `f()` ending in `return undefined`, with two
/// frame-initial-style const values attributed to it: one UNUSED (the
/// discarded-read seed shape), one used by a store.
fn build() -> (Module, abcd_ir::FuncId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", abcd_ir::FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let _param_anchor = b.create_param(); // anchors the function's value-id range
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
fn default_lowering_materializes_unused_seed() {
    let (module, func) = build();
    let report = verify_module(&module);
    assert!(report.is_ok(), "{:?}", report.errors);
    let result = lower_function(&module, func).expect("lowers");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldundefined)),
        "v0.1-lift parity: the unused seed's load is emitted: {:?}",
        result.bytecodes
    );
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldhole)),
        "the used seed's load is emitted: {:?}",
        result.bytecodes
    );
}

#[test]
fn prune_option_skips_unused_seed_keeps_used() {
    let (module, func) = build();
    let result = lower_function_with_options(
        &module,
        func,
        LowerOptions {
            prune_unused_frame_init_consts: true,
        },
    )
    .expect("lowers");
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldundefined)),
        "v0.1-opt parity: ADCE swept the unused seed instruction, so no \
         load is materialized: {:?}",
        result.bytecodes
    );
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldhole)),
        "the used seed still materializes: {:?}",
        result.bytecodes
    );
}
