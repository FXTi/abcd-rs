mod common;

use abcd_isa::*;
use common::assert_roundtrip;

#[test]
fn roundtrip_single_no_operand() {
    assert_roundtrip(&[insn::Ldundefined::new()]);
}

#[test]
fn roundtrip_simple_literals() {
    assert_roundtrip(&[
        insn::Ldundefined::new(),
        insn::Ldnull::new(),
        insn::Ldtrue::new(),
        insn::Ldfalse::new(),
        insn::Ldnan::new(),
        insn::Ldinfinity::new(),
        insn::Ldhole::new(),
        insn::Createemptyobject::new(),
    ]);
}

#[test]
fn roundtrip_register_ops() {
    assert_roundtrip(&[
        insn::Mov::new(Reg(0), Reg(1)),
        insn::Lda::new(Reg(2)),
        insn::Sta::new(Reg(3)),
    ]);
}

#[test]
fn roundtrip_immediate_ops() {
    assert_roundtrip(&[
        insn::Ldai::new(Imm(42)),
        insn::Fldai::new(Imm(0)),
        insn::Inc::new(Imm(0)),
        insn::Dec::new(Imm(0)),
        insn::Neg::new(Imm(0)),
        insn::Not::new(Imm(0)),
    ]);
}

#[test]
fn roundtrip_binary_ops() {
    assert_roundtrip(&[
        insn::Add2::new(Imm(0), Reg(1)),
        insn::Sub2::new(Imm(0), Reg(2)),
        insn::Mul2::new(Imm(0), Reg(3)),
        insn::Div2::new(Imm(0), Reg(4)),
    ]);
}

#[test]
fn roundtrip_call_instructions() {
    assert_roundtrip(&[
        insn::Callarg0::new(Imm(0)),
        insn::Callarg1::new(Imm(0), Reg(1)),
        insn::Callargs2::new(Imm(0), Reg(1), Reg(2)),
        insn::Callargs3::new(Imm(0), Reg(1), Reg(2), Reg(3)),
    ]);
}

#[test]
fn roundtrip_entity_id_ops() {
    assert_roundtrip(&[
        insn::Createarraywithbuffer::new(Imm(0), EntityId(0)),
        insn::Createobjectwithbuffer::new(Imm(0), EntityId(0)),
    ]);
}

#[test]
fn roundtrip_forward_jump() {
    assert_roundtrip(&[insn::Jmp::new(Label(1)), insn::Ldundefined::new()]);
}

#[test]
fn roundtrip_backward_jump() {
    assert_roundtrip(&[insn::Ldundefined::new(), insn::Jmp::new(Label(0))]);
}

#[test]
fn roundtrip_self_jump() {
    assert_roundtrip(&[insn::Jmp::new(Label(0))]);
}

#[test]
fn roundtrip_conditional_jump() {
    assert_roundtrip(&[
        insn::Ldtrue::new(),
        insn::Jeqz::new(Label(3)),
        insn::Ldfalse::new(),
        insn::Returnundefined::new(),
    ]);
}

#[test]
fn roundtrip_reg_label_jump() {
    assert_roundtrip(&[
        insn::Lda::new(Reg(0)),
        insn::Jeq::new(Reg(1), Label(2)),
        insn::Ldundefined::new(),
    ]);
}

#[test]
fn roundtrip_multiple_jumps_same_target() {
    assert_roundtrip(&[
        insn::Jmp::new(Label(2)),
        insn::Jeqz::new(Label(2)),
        insn::Ldundefined::new(),
    ]);
}

#[test]
fn roundtrip_mixed_program() {
    assert_roundtrip(&[
        insn::Ldai::new(Imm(10)),
        insn::Sta::new(Reg(0)),
        insn::Lda::new(Reg(0)),
        insn::Jeqz::new(Label(6)),
        insn::Dec::new(Imm(0)),
        insn::Jmp::new(Label(2)),
        insn::Returnundefined::new(),
    ]);
}

#[test]
fn roundtrip_prefixed_throw() {
    assert_roundtrip(&[insn::Throw::new()]);
}

#[test]
fn roundtrip_prefixed_wide() {
    assert_roundtrip(&[insn::WideNewlexenv::new(Imm(1000))]);
}

#[test]
fn roundtrip_prefixed_callruntime() {
    assert_roundtrip(&[insn::CallruntimeNotifyconcurrentresult::new()]);
}

#[test]
fn roundtrip_idempotent() {
    let program = [
        insn::Ldai::new(Imm(10)),
        insn::Sta::new(Reg(0)),
        insn::Jmp::new(Label(0)),
    ];
    let (bytes1, _) = encode(&program).unwrap();
    let decoded = decode(&bytes1).unwrap();
    let bcs: Vec<Bytecode> = decoded.into_iter().map(|(bc, _)| bc).collect();
    let (bytes2, _) = encode(&bcs).unwrap();
    assert_eq!(bytes1, bytes2, "re-encoded bytes differ");
}

// --- Supplementary instruction categories ---

#[test]
fn roundtrip_generator_ops() {
    assert_roundtrip(&[
        insn::Creategeneratorobj::new(Reg(0)),
        insn::Suspendgenerator::new(Reg(0)),
        insn::Resumegenerator::new(),
        insn::Getresumemode::new(),
        insn::Asyncfunctionenter::new(),
    ]);
}

#[test]
fn roundtrip_object_ops() {
    assert_roundtrip(&[
        insn::Ldobjbyvalue::new(Imm(0), Reg(0)),
        insn::Stobjbyvalue::new(Imm(0), Reg(0), Reg(1)),
        insn::Ldobjbyindex::new(Imm(0), Imm(0)),
        insn::Stobjbyindex::new(Imm(0), Reg(0), Imm(0)),
    ]);
}

#[test]
fn roundtrip_lexenv_ops() {
    assert_roundtrip(&[
        insn::Newlexenv::new(Imm(5)),
        insn::Poplexenv::new(),
        insn::Ldlexvar::new(Imm(0), Imm(1)),
        insn::Stlexvar::new(Imm(2), Imm(3)),
    ]);
}

#[test]
fn roundtrip_global_ops() {
    assert_roundtrip(&[
        insn::Tryldglobalbyname::new(Imm(0), EntityId(1)),
        insn::Trystglobalbyname::new(Imm(0), EntityId(2)),
        insn::Ldglobalvar::new(Imm(0), EntityId(3)),
        insn::Stglobalvar::new(Imm(0), EntityId(4)),
    ]);
}

#[test]
fn roundtrip_more_jumps() {
    // Jnez: forward conditional
    assert_roundtrip(&[insn::Jnez::new(Label(1)), insn::Ldundefined::new()]);
    // Jne: reg + label
    assert_roundtrip(&[insn::Jne::new(Reg(0), Label(1)), insn::Ldundefined::new()]);
    // Jstricteq / Jnstricteq: reg + label
    assert_roundtrip(&[
        insn::Jstricteq::new(Reg(0), Label(1)),
        insn::Ldundefined::new(),
    ]);
    assert_roundtrip(&[
        insn::Jnstricteq::new(Reg(0), Label(1)),
        insn::Ldundefined::new(),
    ]);
}
