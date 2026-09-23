//! N67 regression (v0.2 lifter): `Bytecode::Ldthis` must bind the
//! THIS-role frame slot of the vendored frame-slot model (design
//! ir-v0.2.md T4/§5.3 — canonical; abcd_ir::frame), NOT `params[0]`.
//!
//! Vendor grounding (arkcompiler_ets_runtime-master): `ldthis` reads the
//! frame's `thisObj` (`EcmaInterpreter::GetThis`,
//! ecmascript/interpreter/interpreter-inl.cpp:7907-7912;
//! `HANDLE_OPCODE(LDTHIS)`, interpreter-inl.cpp:6970-6973), which the
//! caller bound from the this-role argument slot. The leading slots are
//! `[func][new.target][this]` per the callee's `L_ESCallTypeAnnotation;`
//! callType bits (`method_literal.h:59-62`: bit0=this, bit1=new.target,
//! bit3=func); annotation absent → the vendored `0xF` default (all
//! three). Under `0xF`, `params[0]` is the FUNC slot — the pre-N67 lift
//! bound `ldthis` to it (latent: `ldthis` is absent from the entire
//! corpus — es2abc reads the this slot directly — so every gate was
//! blind).

use abcd_file::{AccessFlags, AnnotationElemDef, Builder, Type, decode};
use abcd_ir::{Op, ValueDef};
use abcd_isa::{Bytecode, encode as encode_bytecodes};
use abcd_lift::lift_file;

/// Build a 12.x file whose global class carries one static method `f`
/// with the given bytecodes and code-header argument count.
fn build_file(bytecodes: &[Bytecode], num_args: u32) -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _offsets) = encode_bytecodes(bytecodes).unwrap();
    b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 0, num_args);
    decode(&b.finalize().unwrap()).unwrap()
}

/// Build the same file with an `L_ESCallTypeAnnotation;` `callType`
/// (U32 scalar) on the method.
fn build_annotated(bytecodes: &[Bytecode], num_args: u32, call_type: u32) -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _offsets) = encode_bytecodes(bytecodes).unwrap();
    let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 0, num_args);
    let ann_cls = b.add_class("L_ESCallTypeAnnotation;");
    let elem = b.add_string("callType");
    let ann = b.create_annotation(
        ann_cls,
        &[AnnotationElemDef {
            name: elem,
            tag: b'7', // U32 scalar element
            value: call_type,
        }],
    );
    b.method_add_annotation(m, ann);
    decode(&b.finalize().unwrap()).unwrap()
}

/// The `Op::Return` operand's value definition in `f` (the single
/// method of the built file).
fn return_value_def(module: &abcd_ir::Module) -> ValueDef {
    assert_eq!(module.functions.len(), 1, "one method in the built file");
    let f = &module.functions[0];
    let mut found = None;
    for &b in &f.blocks {
        for &iid in &module.blocks[b.index()].insts {
            if let Op::Return { value: Some(v) } = &module.insts[iid.index()].op {
                assert!(found.is_none(), "single Return in the body");
                found = Some(module.values[v.index()].def.clone());
            }
        }
    }
    found.expect("a Return returning the ldthis value")
}

#[test]
fn ldthis_binds_this_role_slot_under_0xf_default() {
    // 0xF default (annotation absent): [func][new.target][this] → this
    // is params[2], NOT params[0] (the FUNC slot).
    let file = build_file(&[Bytecode::Ldthis, Bytecode::Return], 3);
    let module = lift_file(&file).expect("lift");
    assert_eq!(
        module.functions[0].params.len(),
        3,
        "three code-header arg slots"
    );
    let this = module.functions[0].params[2];
    match return_value_def(&module) {
        ValueDef::Param(2) => {}
        other => panic!("ldthis must bind params[2] (the this-role slot), got {other:?}"),
    }
    // And it is literally the this-role param value.
    let ValueDef::Param(i) = module.values[this.index()].def else {
        panic!("params[2] is a Param value")
    };
    assert_eq!(i, 2);
}

#[test]
fn ldthis_binds_this_role_slot_with_calltype_annotation() {
    // callType 0b1001 = func + this (no new.target): [func][this] →
    // this is params[1].
    let file = build_annotated(&[Bytecode::Ldthis, Bytecode::Return], 2, 0b1001);
    let module = lift_file(&file).expect("lift");
    match return_value_def(&module) {
        ValueDef::Param(1) => {}
        other => panic!("annotated 0b1001: ldthis must bind params[1], got {other:?}"),
    }
}

#[test]
fn ldthis_without_this_bit_yields_undefined() {
    // callType 0b1000 = func only: no this slot — the documented
    // conservative fallback is a materialized `undefined`.
    let file = build_annotated(&[Bytecode::Ldthis, Bytecode::Return], 1, 0b1000);
    let module = lift_file(&file).expect("lift");
    let def = return_value_def(&module);
    let ValueDef::Inst(iid) = def else {
        panic!("no-this-bit: ldthis must yield a materialized value, got {def:?}")
    };
    let Op::LoadConst(cid) = &module.insts[iid.index()].op else {
        panic!(
            "no-this-bit: expected LoadConst, got {:?}",
            module.insts[iid.index()].op
        )
    };
    assert!(
        matches!(module.consts.get(*cid), Some(abcd_ir::Const::Undefined)),
        "no-this-bit: ldthis must yield undefined"
    );
}

#[test]
fn ldthis_with_params_shorter_than_implicit_slots_yields_undefined() {
    // Malformed under 0xF (params < the 3 implicit slots — the vendor
    // ASSERT's shape): conservative undefined, never params[0].
    let file = build_file(&[Bytecode::Ldthis, Bytecode::Return], 2);
    let module = lift_file(&file).expect("lift");
    let def = return_value_def(&module);
    let ValueDef::Inst(iid) = def else {
        panic!("short-params: ldthis must yield a materialized value, got {def:?}")
    };
    assert!(
        matches!(
            &module.insts[iid.index()].op,
            Op::LoadConst(cid) if matches!(module.consts.get(*cid), Some(abcd_ir::Const::Undefined))
        ),
        "short-params: ldthis must yield undefined"
    );
}
