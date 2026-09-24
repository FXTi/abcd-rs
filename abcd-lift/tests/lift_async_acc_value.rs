//! N68/G6 regression (v0.2 lifter): the modern
//! `asyncfunctionawaituncaught`/`asyncfunctionresolve`/
//! `asyncfunctionreject` bytecodes carry the awaited/resolved/rejected
//! VALUE in the ACCUMULATOR and the async function object in the v0
//! register operand.
//!
//! Vendor grounding (arkcompiler_ets_runtime-master,
//! ecmascript/interpreter/interpreter-inl.cpp):
//!
//! - `HANDLE_OPCODE(ASYNCFUNCTIONAWAITUNCAUGHT_V8)` (:5357-5366):
//!   `asyncFuncObj = GET_VREG_VALUE(v0)`, `value = GET_ACC()`,
//!   `SET_ACC(res)`. isa.yaml:1311-1314 `asyncfunctionawaituncaught
//!   v:in:top, acc: inout:top`.
//! - `HANDLE_OPCODE(ASYNCFUNCTIONRESOLVE_V8)` (:6577-6589): same shape —
//!   `value = GET_ACC()`, `asyncFuncObj = GET_VREG_VALUE(v0)`.
//!   isa.yaml:1413-1416 `acc: inout:top`.
//! - `HANDLE_OPCODE(ASYNCFUNCTIONREJECT_V8)` (:6605-6617): same shape.
//!   isa.yaml:1422-1425 `acc: inout:top`.
//! - The DEPRECATED explicit-register forms
//!   (`DEPRECATED_ASYNCFUNCTIONAWAITUNCAUGHT_PREF_V8_V8` :5369-5381,
//!   `DEPRECATED_ASYNCFUNCTIONRESOLVE_PREF_V8_V8_V8` :6590-6603,
//!   `DEPRECATED_ASYNCFUNCTIONREJECT_PREF_V8_V8_V8` :6618-6631) read
//!   funcobj from the FIRST register and the value from the LAST
//!   register (`GET_VREG_VALUE(v2)` — the middle register of the
//!   resolve/reject form is read only for the log line).
//!
//! The pre-N68 lift read the REGISTER operand as the value and dropped
//! the accumulator — the value never reached the IR (and the lower's
//! matching inversion kept bytes identical, hiding the gap). The
//! deprecated resolve/reject arms additionally read the MIDDLE register
//! as the value where the vendor reads the LAST.

use abcd_file::{AccessFlags, Builder, Type, decode};
use abcd_ir::{Const, Op, ValueDef, ValueId};
use abcd_isa::{Bytecode, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;

/// Build a 12.x file whose global class carries one static method `f`
/// with the given bytecodes.
fn build_file(bytecodes: &[Bytecode], num_vregs: u32) -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _offsets) = encode_bytecodes(bytecodes).unwrap();
    b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, num_vregs, 0);
    decode(&b.finalize().unwrap()).unwrap()
}

/// The `Op` payload of the single instruction in `f` matching `pred`.
fn find_op(module: &abcd_ir::Module, pred: impl Fn(&Op) -> bool) -> Op {
    assert_eq!(module.functions.len(), 1, "one method in the built file");
    let f = &module.functions[0];
    let mut found = None;
    for &b in &f.blocks {
        for &iid in &module.blocks[b.index()].insts {
            let op = &module.insts[iid.index()].op;
            if pred(op) {
                assert!(found.is_none(), "single match expected");
                found = Some(op.clone());
            }
        }
    }
    found.expect("the async op must be present in the lifted body")
}

/// The f64 bits of the `LoadConst` definition behind `v` (the synthetic
/// bodies feed the async ops `ldai` immediates, so the defining op must
/// be a numeric `LoadConst`).
fn const_of(module: &abcd_ir::Module, v: ValueId) -> f64 {
    let ValueDef::Inst(iid) = module.values[v.index()].def else {
        panic!("expected an instruction-defined value, got {:?}", module.values[v.index()].def)
    };
    let Op::LoadConst(cid) = &module.inst(iid).expect("inst").op else {
        panic!("expected LoadConst, got {:?}", module.inst(iid).expect("inst").op);
    };
    match module.consts.get(*cid).expect("const") {
        Const::Number(bits) => f64::from_bits(*bits),
        other => panic!("expected a numeric const, got {other:?}"),
    }
}

/// `ldai FUNC; sta v0; ldai VALUE; <modern async op> v0; return` —
/// vendor: funcobj = v0 (FUNC), value = acc (VALUE), result → acc.
fn modern_body(mk: impl Fn(Reg) -> Bytecode) -> abcd_ir::Module {
    const FUNC: i64 = 7;
    const VALUE: i64 = 9;
    let file = build_file(
        &[
            Bytecode::Ldai(Imm(FUNC)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(VALUE)),
            Bytecode::Sta(Reg(1)), // keep FUNC and VALUE in distinct regs
            Bytecode::Lda(Reg(1)), // acc = VALUE (the real pre-op shape)
            mk(Reg(0)),
            Bytecode::Return,
        ],
        4,
    );
    lift_file(&file).expect("lift")
}

/// `ldai FUNC; sta v0; ldai MID; sta v1; ldai VALUE; sta v2;
/// <deprecated 3-reg op> v0, v1, v2; return` — vendor: funcobj = FIRST
/// reg, value = LAST reg, middle reg read only for the log line.
fn deprecated3_body(mk: impl Fn(Reg, Reg, Reg) -> Bytecode) -> abcd_ir::Module {
    const FUNC: i64 = 7;
    const MID: i64 = 8;
    const VALUE: i64 = 9;
    let file = build_file(
        &[
            Bytecode::Ldai(Imm(FUNC)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(MID)),
            Bytecode::Sta(Reg(1)),
            Bytecode::Ldai(Imm(VALUE)),
            Bytecode::Sta(Reg(2)),
            mk(Reg(0), Reg(1), Reg(2)),
            Bytecode::Return,
        ],
        4,
    );
    lift_file(&file).expect("lift")
}

const FUNC: f64 = 7.0;
const VALUE: f64 = 9.0;

#[test]
fn awaituncaught_reads_acc_as_value_and_reg_as_funcobj() {
    let module = modern_body(Bytecode::Asyncfunctionawaituncaught);
    let Op::AwaitUncaught { value } = find_op(&module, |op| matches!(op, Op::AwaitUncaught { .. }))
    else {
        panic!("expected Op::AwaitUncaught");
    };
    assert_eq!(
        const_of(&module, value),
        VALUE,
        "the value operand is the ACCUMULATOR (isa.yaml:1311-1314 acc: inout:top)"
    );
}

#[test]
fn asyncfunctionresolve_reads_acc_as_value_and_reg_as_funcobj() {
    let module = modern_body(Bytecode::Asyncfunctionresolve);
    let Op::AsyncResolve { value } = find_op(&module, |op| matches!(op, Op::AsyncResolve { .. }))
    else {
        panic!("expected Op::AsyncResolve");
    };
    assert_eq!(const_of(&module, value), VALUE, "value = acc (interpreter-inl.cpp:6583)");
}

#[test]
fn asyncfunctionreject_reads_acc_as_value_and_reg_as_funcobj() {
    let module = modern_body(Bytecode::Asyncfunctionreject);
    let Op::AsyncReject { value } = find_op(&module, |op| matches!(op, Op::AsyncReject { .. }))
    else {
        panic!("expected Op::AsyncReject");
    };
    assert_eq!(const_of(&module, value), VALUE, "value = acc (interpreter-inl.cpp:6611)");
}

#[test]
fn deprecated_awaituncaught_explicit_regs() {
    // v1 = funcobj, v2 = value (interpreter-inl.cpp:5369-5381).
    let file = build_file(
        &[
            Bytecode::Ldai(Imm(7)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(9)),
            Bytecode::Sta(Reg(1)),
            Bytecode::DeprecatedAsyncfunctionawaituncaught(Reg(0), Reg(1)),
            Bytecode::Return,
        ],
        4,
    );
    let module = lift_file(&file).expect("lift");
    let Op::AwaitUncaught { value } = find_op(&module, |op| matches!(op, Op::AwaitUncaught { .. }))
    else {
        panic!("expected Op::AwaitUncaught");
    };
    assert_eq!(const_of(&module, value), VALUE, "value = v2 (interpreter-inl.cpp:5375)");
}

#[test]
fn deprecated_resolve_value_is_the_LAST_register() {
    // Vendor reads funcobj = FIRST reg, value = THIRD reg; the middle
    // register is read only for the log line
    // (interpreter-inl.cpp:6590-6603).
    let module = deprecated3_body(Bytecode::DeprecatedAsyncfunctionresolve);
    let Op::AsyncResolve { value } = find_op(&module, |op| matches!(op, Op::AsyncResolve { .. }))
    else {
        panic!("expected Op::AsyncResolve");
    };
    assert_eq!(const_of(&module, value), VALUE, "value = v3, NOT the middle register");
}

#[test]
fn deprecated_reject_value_is_the_LAST_register() {
    // interpreter-inl.cpp:6618-6631.
    let module = deprecated3_body(Bytecode::DeprecatedAsyncfunctionreject);
    let Op::AsyncReject { value } = find_op(&module, |op| matches!(op, Op::AsyncReject { .. }))
    else {
        panic!("expected Op::AsyncReject");
    };
    assert_eq!(const_of(&module, value), VALUE, "value = v3, NOT the middle register");
}
