//! N61 regression (v0.2 lifter): `trystglobalbyname` must NOT fold to
//! `Op::StoreGlobal` — it is the TOLERANT store (no ReferenceError
//! when the global is absent), while `stglobalvar` is the throwing
//! global-OBJECT store. v0.1 keeps the
//! distinction (`InstData::TryStoreGlobalByName`,
//! abcd-ir/src/lift/translate.rs:539; isel emits
//! `trystglobalbyname`).
//!
//! N72-C4 (l-P2): `sttoglobalrecord`/`stconsttoglobalrecord` are NOT
//! `StoreGlobal` either — they are the global LEXICAL record
//! declaration (`Op::StoreGlobalRecord { is_const }`, vendor
//! `RuntimeStGlobalRecord`); the record/object split is what the
//! decl-lex-configurable-global test262 row needed.

use abcd_file::{AccessFlags, Builder, CodeEntity, Type, decode};
use abcd_ir::Op;
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

/// Build a 12.x file: acc = value (v0), then a global-store opcode
/// whose name operand is wired to the string "g".
fn build(make: impl FnOnce(EntityId) -> Bytecode) -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, offsets) = encode_bytecodes(&[
        Bytecode::Lda(Reg(0)),
        make(PLACEHOLDER),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 1, 0);
    let name = b.add_string("g");
    b.relocate_code_id(m, offsets[1], 0, CodeEntity::String(name))
        .unwrap();
    decode(&b.finalize().unwrap()).unwrap()
}

fn ops(m: &abcd_ir::Module) -> Vec<&Op> {
    m.insts.iter().map(|i| &i.op).collect()
}

#[test]
fn trystglobalbyname_lifts_to_try_store_global() {
    let file = build(|id| Bytecode::Trystglobalbyname(Imm(0), id));
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let tolerant: Vec<&Op> = ops(&m)
        .into_iter()
        .filter(|op| matches!(op, Op::TryStoreGlobal { .. }))
        .collect();
    assert_eq!(
        tolerant.len(),
        1,
        "N61: trystglobalbyname must not fold to StoreGlobal"
    );
    let Op::TryStoreGlobal { name, .. } = tolerant[0] else {
        unreachable!()
    };
    assert_eq!(m.sym.resolve(*name), Some("g"));
    assert!(
        !ops(&m)
            .iter()
            .any(|op| matches!(op, Op::StoreGlobal { .. })),
        "the tolerant store is not the throwing StoreGlobal"
    );
}

#[test]
fn throwing_global_stores_stay_store_global() {
    // N61 regression: stglobalvar keeps the throwing StoreGlobal op.
    let file = build(|id| Bytecode::Stglobalvar(Imm(0), id));
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    assert!(
        ops(&m)
            .iter()
            .any(|op| matches!(op, Op::StoreGlobal { .. })),
        "throwing store keeps StoreGlobal: {:?}",
        ops(&m)
    );
    assert!(
        !ops(&m)
            .iter()
            .any(|op| matches!(op, Op::TryStoreGlobal { .. })),
        "the throwing store is not the tolerant TryStoreGlobal"
    );
}

/// N72-C4: the record stores lift to `StoreGlobalRecord` with the
/// constness flag — never folded to the global-OBJECT `StoreGlobal`
/// (the fold rewrote a global `let Array` into `globalThis.Array =
/// undefined`, clobbering the builtin).
#[test]
fn global_record_stores_lift_to_store_global_record() {
    for (make, expect_const) in [
        (
            (|id| Bytecode::Sttoglobalrecord(Imm(0), id)) as fn(EntityId) -> Bytecode,
            false,
        ),
        (
            (|id| Bytecode::Stconsttoglobalrecord(Imm(0), id)) as fn(EntityId) -> Bytecode,
            true,
        ),
    ] {
        let file = build(make);
        let m = lift_file(&file).expect("lift");
        verify_clean(&m);
        let records: Vec<&Op> = ops(&m)
            .into_iter()
            .filter(|op| matches!(op, Op::StoreGlobalRecord { .. }))
            .collect();
        assert_eq!(
            records.len(),
            1,
            "the record store must keep its own op: {:?}",
            ops(&m)
        );
        let Op::StoreGlobalRecord { name, is_const, .. } = records[0] else {
            unreachable!()
        };
        assert_eq!(m.sym.resolve(*name), Some("g"));
        assert_eq!(*is_const, expect_const, "constness must survive the lift");
        assert!(
            !ops(&m)
                .iter()
                .any(|op| matches!(op, Op::StoreGlobal { .. } | Op::TryStoreGlobal { .. })),
            "the record store never folds to the object/tolerant stores: {:?}",
            ops(&m)
        );
    }
}
