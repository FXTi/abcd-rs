//! N57 regression (v0.2 lifter): `apply imm, v_this, v_args` (and its
//! deprecated.callspread twin) must lift to
//! `Call { kind: Apply, this: Some(this), args: [array] }` — the
//! receiver + spread-array roles are known at lift time and must
//! survive into the IR (v0.1 `CallKind::Apply`,
//! abcd-ir/src/lift/translate.rs:1035, :1978; isel emits the `apply`
//! opcode, abcd-ir/src/lower/isel.rs:1632). Pre-N57 the arm folded to
//! `Call{kind: Dynamic}` — byte-identical to `callthis1`, erasing the
//! distinction the v0.2 lower needs.

use abcd_file::{AccessFlags, Builder, Type, decode};
use abcd_ir::{CallKind, Op};
use abcd_isa::{Bytecode, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;

/// Build a file whose global class carries one static method `f` with
/// the given bytecodes.
fn build(api: u8, bytecodes: &[Bytecode], num_vregs: u32) -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(api, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(bytecodes).unwrap();
    b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, num_vregs, 0);
    decode(&b.finalize().unwrap()).unwrap()
}

/// The single Call in the lifted module.
fn the_call(m: &abcd_ir::Module) -> &Op {
    let calls: Vec<&Op> = m
        .insts
        .iter()
        .map(|i| &i.op)
        .filter(|op| matches!(op, Op::Call { .. }))
        .collect();
    assert_eq!(calls.len(), 1, "exactly one Call expected: {calls:?}");
    calls[0]
}

fn verify_clean(m: &abcd_ir::Module) {
    let report = abcd_ir::verify_module(m);
    assert!(
        report.errors.is_empty(),
        "verifier errors: {:?}",
        report.errors
    );
}

#[test]
fn apply_lifts_to_call_kind_apply() {
    // acc = v0 (the func); apply v1 (this), v2 (the args array).
    let file = build(
        12,
        &[
            Bytecode::Lda(Reg(0)),
            Bytecode::Apply(Imm(0), Reg(1), Reg(2)),
            Bytecode::Returnundefined,
        ],
        3,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::Call {
        this, args, kind, ..
    } = the_call(&m)
    else {
        unreachable!()
    };
    assert_eq!(
        *kind,
        CallKind::Apply,
        "N57: apply must not fold to Dynamic"
    );
    assert!(this.is_some(), "apply carries an explicit receiver");
    assert_eq!(args.len(), 1, "apply's single argument is the args ARRAY");
}

#[test]
fn deprecated_callspread_lifts_to_call_kind_apply() {
    // deprecated.callspread v0 (func), v1 (this), v2 (array) — the
    // modern apply with the func in a register instead of the acc
    // (v0.1 parity: lifts to the 2-role Apply form).
    let file = build(
        9,
        &[
            Bytecode::DeprecatedCallspread(Reg(0), Reg(1), Reg(2)),
            Bytecode::Returnundefined,
        ],
        3,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::Call {
        this, args, kind, ..
    } = the_call(&m)
    else {
        unreachable!()
    };
    assert_eq!(
        *kind,
        CallKind::Apply,
        "N57: deprecated.callspread is the modern apply"
    );
    assert!(this.is_some());
    assert_eq!(args.len(), 1);
}
