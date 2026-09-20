//! N59 regression (v0.2 lifter): `createobjectwithbuffer` and
//! `createarraywithbuffer` must NOT both fold to
//! `AllocObject { shape }` — the object/array tag is opcode-carried
//! and never recoverable from the flat literal-buffer content. v0.1
//! keeps them distinct (`InstData::CreateObjectWithBuffer` /
//! `CreateArrayWithBuffer`, abcd-ir/src/lift/translate.rs:172-190) and
//! isel emits the matching opcode family. v0.2:
//! `createobjectwithbuffer` → `AllocObject { shape }`,
//! `createarraywithbuffer` → `AllocArray { shape: Some(shape) }`,
//! `createemptyarray` → `AllocArray { shape: None }`. The deprecated
//! pair folds to `AllocArray` (v0.1 lifts BOTH deprecated forms to
//! `CreateArrayWithBuffer` — abcd-ir/src/lift/translate.rs:1822).

use abcd_file::{AccessFlags, Builder, CodeEntity, Type, decode};
use abcd_ir2::{Const, Op};
use abcd_isa::{Bytecode, EntityId, Imm, encode as encode_bytecodes};
use abcd_lift::lift_file;

/// Placeholder entity id wired later via `relocate_code_id`.
const PLACEHOLDER: EntityId = EntityId(u16::MAX as u32);

fn verify_clean(m: &abcd_ir2::Module) {
    let report = abcd_ir2::verify_module(m);
    assert!(
        report.errors.is_empty(),
        "verifier errors: {:?}",
        report.errors
    );
}

/// Build a 12.x file whose global class carries one static method `f`
/// with a single `create{object,array}withbuffer` over a one-string
/// literal array.
fn build_withbuffer(make: impl FnOnce(EntityId) -> Bytecode) -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, offsets) =
        encode_bytecodes(&[make(PLACEHOLDER), Bytecode::Returnundefined]).unwrap();
    let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 0, 0);
    let la = b.add_literal_array("lit");
    let s = b.add_string("x");
    b.literal_array_add_string(la, s);
    b.relocate_code_id(m, offsets[0], 0, CodeEntity::LiteralArray(la))
        .unwrap();
    decode(&b.finalize().unwrap()).unwrap()
}

#[test]
fn createemptyarray_lifts_to_alloc_array_without_shape() {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(&[
        Bytecode::Createemptyarray(Imm(0)),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 0, 0);
    let file = decode(&b.finalize().unwrap()).unwrap();

    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    assert!(
        m.insts
            .iter()
            .any(|i| matches!(i.op, Op::AllocArray { shape: None })),
        "createemptyarray → AllocArray{{shape: None}}"
    );
}

#[test]
fn createarraywithbuffer_lifts_to_alloc_array_with_shape() {
    let file = build_withbuffer(|id| Bytecode::Createarraywithbuffer(Imm(0), id));
    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let alloc = m
        .insts
        .iter()
        .find(|i| matches!(i.op, Op::AllocArray { shape: Some(_) }))
        .expect("N59: createarraywithbuffer must not fold to AllocObject");
    let Op::AllocArray { shape: Some(shape) } = alloc.op else {
        unreachable!()
    };
    let x = m.sym.intern("x");
    assert_eq!(
        m.consts.get(shape),
        Some(&Const::ArrayLiteral(vec![Const::String(x)])),
        "the literal buffer content rides the shape"
    );
    // And no AllocObject was invented for the same instruction.
    assert!(
        !m.insts
            .iter()
            .any(|i| matches!(i.op, Op::AllocObject { .. })),
        "no AllocObject for an array literal"
    );
}

#[test]
fn createobjectwithbuffer_stays_alloc_object() {
    let file = build_withbuffer(|id| Bytecode::Createobjectwithbuffer(Imm(0), id));
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    assert!(
        m.insts
            .iter()
            .any(|i| matches!(i.op, Op::AllocObject { .. })),
        "createobjectwithbuffer keeps AllocObject"
    );
    assert!(
        !m.insts
            .iter()
            .any(|i| matches!(i.op, Op::AllocArray { shape: Some(_) })),
        "no AllocArray for an object literal"
    );
}

#[test]
fn deprecated_buffer_forms_fold_to_alloc_array() {
    // v0.1 lifts BOTH deprecated forms to CreateArrayWithBuffer (the
    // raw table index, no entity indirection) — v0.2 folds both to
    // AllocArray{Some} for parity.
    for make in [
        (|idx| Bytecode::DeprecatedCreatearraywithbuffer(idx)) as fn(Imm) -> Bytecode,
        (|idx| Bytecode::DeprecatedCreateobjectwithbuffer(idx)) as fn(Imm) -> Bytecode,
    ] {
        let mut b = Builder::new();
        b.set_api(9, "");
        let cls = b.add_global_class();
        let proto = b.create_proto(Type::Void, &[]);
        let (code, _) = encode_bytecodes(&[make(Imm(0)), Bytecode::Returnundefined]).unwrap();
        b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 0, 0);
        let la = b.add_literal_array("lit");
        let s = b.add_string("x");
        b.literal_array_add_string(la, s);
        let file = decode(&b.finalize().unwrap()).unwrap();

        let m = lift_file(&file).expect("lift");
        verify_clean(&m);
        assert!(
            m.insts
                .iter()
                .any(|i| matches!(i.op, Op::AllocArray { shape: Some(_) })),
            "deprecated buffer form → AllocArray{{Some}} (v0.1 parity)"
        );
    }
}
