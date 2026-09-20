//! N58 regression (v0.2 lifter): the two single-argument super-call
//! opcodes must NOT collide on `Call{kind: Super, args: [x]}`:
//!
//! - `supercallspread imm, v_args` spreads an argument ARRAY into the
//!   super constructor → `CallKind::SuperSpread` (v0.1
//!   `CallKind::SuperCallSpread`, abcd-ir/src/lift/translate.rs:1020;
//!   isel emits `supercallspread`, abcd-ir/src/lower/isel.rs:1617);
//! - `callruntime.supercallforwardallargs v_this` forwards ALL of the
//!   enclosing constructor's own arguments →
//!   `CallKind::SuperForwardAllArgs` (v0.1's SuperCall approximation —
//!   args [this], lowering to supercallthisrange argc=1 — kept
//!   verbatim, abcd-ir/src/lift/translate.rs:1764).
//!
//! `supercallthisrange` keeps `CallKind::Super` (explicit arguments).

use abcd_file::{AccessFlags, Builder, Type, decode};
use abcd_ir2::{CallKind, Op};
use abcd_isa::{Bytecode, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;

/// Build a file whose global class carries one static method `f` with
/// the given bytecodes.
fn build(bytecodes: &[Bytecode], num_vregs: u32) -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(bytecodes).unwrap();
    b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, num_vregs, 0);
    decode(&b.finalize().unwrap()).unwrap()
}

/// The single Call in the lifted module.
fn the_call(m: &abcd_ir2::Module) -> &Op {
    let calls: Vec<&Op> = m
        .insts
        .iter()
        .map(|i| &i.op)
        .filter(|op| matches!(op, Op::Call { .. }))
        .collect();
    assert_eq!(calls.len(), 1, "exactly one Call expected: {calls:?}");
    calls[0]
}

fn verify_clean(m: &abcd_ir2::Module) {
    let report = abcd_ir2::verify_module(m);
    assert!(
        report.errors.is_empty(),
        "verifier errors: {:?}",
        report.errors
    );
}

#[test]
fn supercallspread_lifts_to_super_spread() {
    // acc = the super ctor; v0 = the args ARRAY.
    let file = build(
        &[
            Bytecode::Lda(Reg(1)),
            Bytecode::Supercallspread(Imm(0), Reg(0)),
            Bytecode::Returnundefined,
        ],
        2,
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
        CallKind::SuperSpread,
        "N58: supercallspread must not fold to Super"
    );
    assert!(this.is_none(), "super calls inherit this");
    assert_eq!(args.len(), 1, "the single argument is the args ARRAY");
}

#[test]
fn supercallforwardallargs_lifts_to_super_forward_all_args() {
    // acc = the super ctor; v1 = the enclosing this (v0.1's
    // approximation: the single forwarded argument).
    let file = build(
        &[
            Bytecode::Lda(Reg(0)),
            Bytecode::CallruntimeSupercallforwardallargs(Reg(1)),
            Bytecode::Returnundefined,
        ],
        2,
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
        CallKind::SuperForwardAllArgs,
        "N58: the forward-all form keeps its own kind"
    );
    assert!(this.is_none());
    assert_eq!(args.len(), 1, "v0.1's approximation: args = [this]");
}

#[test]
fn supercallthisrange_stays_super() {
    // Explicit-arguments super call: acc = ctor, window [v0, v1].
    let file = build(
        &[
            Bytecode::Lda(Reg(2)),
            Bytecode::Supercallthisrange(Imm(0), Imm(2), Reg(0)),
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
    assert_eq!(*kind, CallKind::Super, "explicit-arguments super call");
    assert!(this.is_none());
    assert_eq!(args.len(), 2);
}
