//! N68/G6 pin (v0.2 lower): `Op::AwaitUncaught`/`Op::AsyncResolve`/
//! `Op::AsyncReject` lower with the async FUNCTION OBJECT in the v0
//! register operand and the VALUE in the accumulator (vendor
//! `asyncfunctionawaituncaught v:in:top, acc: inout:top`,
//! isa.yaml:1311-1314; interpreter-inl.cpp:5357-5366; resolve
//! :6577-6589; reject :6605-6617). The pre-N68 lower read the IR's
//! single operand into the register — self-consistent with the mis-lift
//! (double inversion) but semantically the funcobj rode the IR `value`
//! slot and the acc was dropped.

mod common;

use abcd_ir::{FunctionKind, Module, Op};
use abcd_lower::lower_function;

use common::{Halt, Machine, V2Builder};

const FUNCOBJ: i64 = 4242;
const VALUE: i64 = 777;

/// Build `funcobj = param0; value = ldai 777; <async op>; return acc`
/// and run it with param0 seeded to FUNCOBJ. Returns the halt record.
fn run_async(op: impl Fn(abcd_ir::ValueId, abcd_ir::ValueId) -> Op) -> Halt {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "af", FunctionKind::Async);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let funcobj = builder.create_param();
        let cid = builder.konst(abcd_ir::Const::number(VALUE as f64));
        let value = builder.emit_val(Op::LoadConst(cid));
        let res = builder.emit_val(op(funcobj, value));
        builder.emit_void(Op::Return { value: Some(res) });
    }

    let result = lower_function(&module, func).expect("async shape must lower");
    // Seed the ABI top slot (num_regs = frame; param0 sits above it).
    Machine::new()
        .with_reg(result.num_regs, FUNCOBJ)
        .run(&result.bytecodes)
}

#[test]
fn awaituncaught_lowers_funcobj_to_v0_and_value_to_acc() {
    let halt = run_async(|funcobj, value| Op::AwaitUncaught { funcobj, value });
    let Halt::AsyncAwaitUncaught { funcobj, value } = halt else {
        panic!("expected AsyncAwaitUncaught halt, got {halt:?}");
    };
    assert_eq!(funcobj, FUNCOBJ, "v0 register operand = the funcobj");
    assert_eq!(value, VALUE, "the acc carries the awaited value");
}

#[test]
fn async_resolve_lowers_funcobj_to_v0_and_value_to_acc() {
    let halt = run_async(|funcobj, value| Op::AsyncResolve { funcobj, value });
    let Halt::AsyncResolve { funcobj, value } = halt else {
        panic!("expected AsyncResolve halt, got {halt:?}");
    };
    assert_eq!(funcobj, FUNCOBJ, "v0 register operand = the funcobj");
    assert_eq!(value, VALUE, "the acc carries the resolution value");
}

#[test]
fn async_reject_lowers_funcobj_to_v0_and_value_to_acc() {
    let halt = run_async(|funcobj, value| Op::AsyncReject { funcobj, value });
    let Halt::AsyncReject { funcobj, value } = halt else {
        panic!("expected AsyncReject halt, got {halt:?}");
    };
    assert_eq!(funcobj, FUNCOBJ, "v0 register operand = the funcobj");
    assert_eq!(value, VALUE, "the acc carries the rejection reason");
}

/// The acc-carried value must survive an intervening acc-clobbering
/// instruction (the B4 acc-cache contract): the tracker reloads the
/// value's home rather than trusting a stale acc.
#[test]
fn acc_held_async_value_survives_clobber_before_resolve() {
    const OBJ: i64 = 7777;

    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "af", FunctionKind::Async);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let funcobj = builder.create_param();
        let obj = builder.create_param();
        let cid = builder.konst(abcd_ir::Const::number(VALUE as f64));
        let value = builder.emit_val(Op::LoadConst(cid));
        let fcid = builder.konst(abcd_ir::Const::Bool(false));
        let f = builder.emit_val(Op::LoadConst(fcid));
        let name = builder.sym("x");
        // Clobbers the acc between the value's definition and the op.
        builder.emit_void(Op::StoreProp {
            object: obj,
            name,
            value: f,
        });
        let res = builder.emit_val(Op::AsyncResolve { funcobj, value });
        builder.emit_void(Op::Return { value: Some(res) });
    }

    let result = lower_function(&module, func).expect("clobber shape must lower");
    let halt = Machine::new()
        .with_reg(result.num_regs, FUNCOBJ)
        .with_reg(result.num_regs + 1, OBJ)
        .run(&result.bytecodes);
    let Halt::AsyncResolve { funcobj, value } = halt else {
        panic!(
            "expected AsyncResolve halt, got {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(funcobj, FUNCOBJ, "v0 register operand = the funcobj");
    assert_eq!(
        value, VALUE,
        "the acc at asyncfunctionresolve must be the resolution value \
         (bytecodes: {:?})",
        result.bytecodes
    );
}
