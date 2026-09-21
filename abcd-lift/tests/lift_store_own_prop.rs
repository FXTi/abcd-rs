//! N60 regression (v0.2 lifter): the OWN-STORE family must NOT fold
//! into the plain `StoreProp*` ops — own-stores are define-own-property
//! semantics (CreateDataProperty/DefineField: no setters, no
//! prototype-chain walk), while `stobjby*` is ordinary assignment.
//! v0.1 keeps the distinction (`InstData::StoreOwnProperty` with
//! `PropKind::{ByName,ByValue,ByIndex}` — abcd-ir/src/lift/
//! translate.rs:322-367, :506-521, :1582-1616; isel emits `stownby*`).
//! Covered bytecodes: stownbyname(+withnameset), stownbyvalue
//! (+withnameset), stownbyindex(+wide), definefieldbyname,
//! definepropertybyname, callruntime.definefieldbyvalue,
//! callruntime.definefieldbyindex.

use abcd_file::{AccessFlags, Builder, CodeEntity, Type, decode};
use abcd_ir::{Const, Op, ValueDef};
use abcd_isa::{Bytecode, EntityId, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;

/// Placeholder entity id wired later via `relocate_code_id`.
const PLACEHOLDER: EntityId = EntityId(u16::MAX as u32);

fn verify_clean(m: &abcd_ir::Module) {
    let report = abcd_ir::verify_module(m);
    assert!(
        report.errors.is_empty(),
        "verifier errors: {:?}",
        report.errors
    );
}

/// Build a 12.x file whose global class carries one static method `f`
/// with the given bytecodes; `wire` relocates entity operands.
fn build(
    bytecodes: &[Bytecode],
    num_vregs: u32,
    wire: impl FnOnce(&mut Builder, abcd_file::MethodHandle, &[u32]),
) -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, offsets) = encode_bytecodes(bytecodes).unwrap();
    let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, num_vregs, 0);
    wire(&mut b, m, &offsets);
    decode(&b.finalize().unwrap()).unwrap()
}

/// A by-name own-store body: acc = value (v0), object in v1; the name
/// operand wired to a real string.
fn build_byname(make: impl FnOnce(EntityId) -> Bytecode) -> abcd_file::File {
    build(
        &[
            Bytecode::Lda(Reg(0)),
            make(PLACEHOLDER),
            Bytecode::Returnundefined,
        ],
        2,
        |b, m, offsets| {
            let name = b.add_string("key");
            b.relocate_code_id(m, offsets[1], 0, CodeEntity::String(name))
                .unwrap();
        },
    )
}

/// All ops of the lifted module's single function body.
fn ops(m: &abcd_ir::Module) -> Vec<&Op> {
    m.insts.iter().map(|i| &i.op).collect()
}

fn assert_no_plain_store(m: &abcd_ir::Module) {
    assert!(
        !m.insts.iter().any(|i| matches!(
            i.op,
            Op::StoreProp { .. } | Op::StorePropDyn { .. } | Op::StorePropIdx { .. }
        )),
        "N60: own-store must not fold to a plain StoreProp* op"
    );
}

#[test]
fn stownbyname_lifts_to_store_own_prop_name() {
    for make in [
        (|id| Bytecode::Stownbyname(Imm(0), id, Reg(1))) as fn(EntityId) -> Bytecode,
        (|id| Bytecode::Stownbynamewithnameset(Imm(0), id, Reg(1))) as fn(EntityId) -> Bytecode,
        (|id| Bytecode::Definefieldbyname(Imm(0), id, Reg(1))) as fn(EntityId) -> Bytecode,
        (|id| Bytecode::Definepropertybyname(Imm(0), id, Reg(1))) as fn(EntityId) -> Bytecode,
    ] {
        let file = build_byname(make);
        let m = lift_file(&file).expect("lift");
        verify_clean(&m);
        let all = ops(&m);
        let own: Vec<&&Op> = all
            .iter()
            .filter(|op| matches!(op, Op::StoreOwnPropName { .. }))
            .collect();
        assert_eq!(own.len(), 1, "exactly one StoreOwnPropName: {all:?}");
        let Op::StoreOwnPropName { name, .. } = **own[0] else {
            unreachable!()
        };
        assert_eq!(m.sym.resolve(name), Some("key"));
        assert_no_plain_store(&m);
    }
}

#[test]
fn stownbyvalue_lifts_to_store_own_prop_dyn() {
    // acc = value, v1 = receiver, v2 = key.
    for make in [
        (|| Bytecode::Stownbyvalue(Imm(0), Reg(1), Reg(2))) as fn() -> Bytecode,
        (|| Bytecode::Stownbyvaluewithnameset(Imm(0), Reg(1), Reg(2))) as fn() -> Bytecode,
    ] {
        let file = build(
            &[Bytecode::Lda(Reg(0)), make(), Bytecode::Returnundefined],
            3,
            |_, _, _| {},
        );
        let m = lift_file(&file).expect("lift");
        verify_clean(&m);
        assert!(
            ops(&m)
                .iter()
                .any(|op| matches!(op, Op::StoreOwnPropDyn { .. })),
            "expected StoreOwnPropDyn: {:?}",
            ops(&m)
        );
        assert_no_plain_store(&m);
    }
}

#[test]
fn callruntime_definefieldbyvalue_lifts_to_store_own_prop_dyn() {
    // Vendor: FIRST register = propKey, SECOND = obj, acc = value.
    let file = build(
        &[
            Bytecode::Lda(Reg(0)),
            Bytecode::CallruntimeDefinefieldbyvalue(Imm(0), Reg(2), Reg(1)),
            Bytecode::Returnundefined,
        ],
        3,
        |_, _, _| {},
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    assert!(
        ops(&m)
            .iter()
            .any(|op| matches!(op, Op::StoreOwnPropDyn { .. })),
        "expected StoreOwnPropDyn: {:?}",
        ops(&m)
    );
    assert_no_plain_store(&m);
}

#[test]
fn stownbyindex_lifts_to_store_own_prop_idx() {
    // acc = value, v1 = receiver, index immediate 7 (materialized as a
    // LoadConst — §9 resolution 3).
    for make in [
        (|| Bytecode::Stownbyindex(Imm(0), Reg(1), Imm(7))) as fn() -> Bytecode,
        (|| Bytecode::WideStownbyindex(Reg(1), Imm(7))) as fn() -> Bytecode,
        (|| Bytecode::CallruntimeDefinefieldbyindex(Imm(0), Imm(7), Reg(1))) as fn() -> Bytecode,
    ] {
        let file = build(
            &[Bytecode::Lda(Reg(0)), make(), Bytecode::Returnundefined],
            2,
            |_, _, _| {},
        );
        let m = lift_file(&file).expect("lift");
        verify_clean(&m);
        let all = ops(&m);
        let own: Vec<&&Op> = all
            .iter()
            .filter(|op| matches!(op, Op::StoreOwnPropIdx { .. }))
            .collect();
        assert_eq!(own.len(), 1, "exactly one StoreOwnPropIdx: {all:?}");
        let Op::StoreOwnPropIdx { index, .. } = **own[0] else {
            unreachable!()
        };
        let ValueDef::Inst(iid) = m.values[index.index()].def else {
            panic!("the index must be a materialized LoadConst inst");
        };
        let Op::LoadConst(c) = m.insts[iid.index()].op else {
            panic!("the index must be a materialized LoadConst inst");
        };
        assert_eq!(m.consts.get(c), Some(&Const::number(7.0)));
        assert_no_plain_store(&m);
    }
}

#[test]
fn stobjbyname_stays_plain_store_prop() {
    // Regression: ordinary assignment keeps the plain StoreProp op.
    let file = build(
        &[
            Bytecode::Lda(Reg(0)),
            Bytecode::Stobjbyname(Imm(0), PLACEHOLDER, Reg(1)),
            Bytecode::Returnundefined,
        ],
        2,
        |b, m, offsets| {
            let name = b.add_string("key");
            b.relocate_code_id(m, offsets[1], 0, CodeEntity::String(name))
                .unwrap();
        },
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    assert!(
        ops(&m).iter().any(|op| matches!(op, Op::StoreProp { .. })),
        "stobjbyname keeps StoreProp: {:?}",
        ops(&m)
    );
    assert!(
        !ops(&m)
            .iter()
            .any(|op| matches!(op, Op::StoreOwnPropName { .. })),
        "ordinary assignment is not an own-store"
    );
}
