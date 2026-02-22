mod common;

use abcd_isa::*;
use common::assert_roundtrip;

#[test]
fn imm_4bit_signed() {
    assert_roundtrip(&[
        insn::Ldai::new(Imm(-8)),
        insn::Ldai::new(Imm(7)),
        insn::Ldai::new(Imm(0)),
    ]);
}

#[test]
fn imm_8bit_signed() {
    assert_roundtrip(&[
        insn::Ldai::new(Imm(-9)),
        insn::Ldai::new(Imm(8)),
        insn::Ldai::new(Imm(-128)),
        insn::Ldai::new(Imm(127)),
    ]);
}

#[test]
fn imm_16bit_signed() {
    assert_roundtrip(&[
        insn::Ldai::new(Imm(-129)),
        insn::Ldai::new(Imm(128)),
        insn::Ldai::new(Imm(-32768)),
        insn::Ldai::new(Imm(32767)),
    ]);
}

#[test]
fn imm_32bit_signed() {
    assert_roundtrip(&[
        insn::Ldai::new(Imm(-32769)),
        insn::Ldai::new(Imm(32768)),
        insn::Ldai::new(Imm(i32::MIN as i64)),
        insn::Ldai::new(Imm(i32::MAX as i64)),
    ]);
}

#[test]
fn imm_unsigned_boundaries() {
    assert_roundtrip(&[
        insn::Ldobjbyindex::new(Imm(0), Imm(15)),
        insn::Ldobjbyindex::new(Imm(0), Imm(16)),
        insn::Ldobjbyindex::new(Imm(0), Imm(255)),
        insn::Ldobjbyindex::new(Imm(0), Imm(256)),
    ]);
}
