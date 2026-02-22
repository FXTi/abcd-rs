mod common;

use abcd_isa::*;
use common::assert_roundtrip;

#[test]
fn format_op_none_extra() {
    assert_roundtrip(&[
        insn::Istrue::new(),
        insn::Isfalse::new(),
        insn::Poplexenv::new(),
        insn::Nop::new(),
        insn::Getpropiterator::new(),
        insn::Asyncfunctionenter::new(),
        insn::Resumegenerator::new(),
        insn::Getresumemode::new(),
    ]);
}

#[test]
fn format_v4_v4_boundary() {
    assert_roundtrip(&[
        insn::Mov::new(Reg(0), Reg(15)),
        insn::Mov::new(Reg(15), Reg(0)),
    ]);
}

#[test]
fn format_v8_v8() {
    assert_roundtrip(&[
        insn::Createiterresultobj::new(Reg(200), Reg(100)),
        insn::Starrayspread::new(Reg(50), Reg(60)),
    ]);
}

#[test]
fn format_v4_v4_v4_v4() {
    assert_roundtrip(&[insn::Definegettersetterbyvalue::new(
        Reg(1),
        Reg(2),
        Reg(3),
        Reg(4),
    )]);
}

#[test]
fn format_v8_v8_v8() {
    assert_roundtrip(&[insn::Asyncgeneratorresolve::new(Reg(10), Reg(20), Reg(30))]);
}

#[test]
fn format_callthis3() {
    assert_roundtrip(&[insn::Callthis3::new(Imm(0), Reg(1), Reg(2), Reg(3), Reg(4))]);
}

#[test]
fn format_imm4_imm4() {
    assert_roundtrip(&[
        insn::Ldlexvar::new(Imm(0), Imm(7)),
        insn::Stlexvar::new(Imm(3), Imm(5)),
    ]);
}

#[test]
fn format_imm8_imm8() {
    assert_roundtrip(&[
        insn::Ldlexvar::new(Imm(100), Imm(50)),
        insn::Stlexvar::new(Imm(200), Imm(100)),
    ]);
}

#[test]
fn format_imm16_imm16() {
    assert_roundtrip(&[
        insn::WideLdlexvar::new(Imm(1000), Imm(2000)),
        insn::WideStlexvar::new(Imm(3000), Imm(4000)),
    ]);
}

#[test]
fn format_imm_id16() {
    assert_roundtrip(&[
        insn::Tryldglobalbyname::new(Imm(0), EntityId(42)),
        insn::Ldglobalvar::new(Imm(0), EntityId(7)),
        insn::Stglobalvar::new(Imm(0), EntityId(13)),
    ]);
}

#[test]
fn format_imm16_id16() {
    assert_roundtrip(&[
        insn::Ldobjbyname::new(Imm(0), EntityId(100)),
        insn::Stobjbyname::new(Imm(0), EntityId(200), Reg(5)),
    ]);
}

#[test]
fn format_range() {
    assert_roundtrip(&[
        insn::Callthisrange::new(Imm(0), Imm(3), Reg(5)),
        insn::Callrange::new(Imm(0), Imm(4), Reg(1)),
        insn::Newobjrange::new(Imm(0), Imm(2), Reg(3)),
        insn::Supercallarrowrange::new(Imm(0), Imm(1), Reg(0)),
    ]);
}

#[test]
fn format_wide_range() {
    assert_roundtrip(&[
        insn::WideNewobjrange::new(Imm(5), Reg(1)),
        insn::WideCallrange::new(Imm(3), Reg(2)),
        insn::WideCallthisrange::new(Imm(4), Reg(3)),
    ]);
}

#[test]
fn format_imm8_imm16_imm16() {
    assert_roundtrip(&[
        insn::Ldprivateproperty::new(Imm(0), Imm(1), Imm(2)),
        insn::Testin::new(Imm(0), Imm(1), Imm(2)),
    ]);
}

#[test]
fn format_imm8_imm16_imm16_v8() {
    assert_roundtrip(&[insn::Stprivateproperty::new(Imm(0), Imm(1), Imm(2), Reg(3))]);
}

#[test]
fn format_id16_only() {
    assert_roundtrip(&[
        insn::LdaStr::new(EntityId(42)),
        insn::Ldbigint::new(EntityId(99)),
    ]);
}

#[test]
fn format_imm32() {
    assert_roundtrip(&[insn::Ldai::new(Imm(100_000))]);
}

#[test]
fn format_imm64() {
    assert_roundtrip(&[insn::Fldai::new(Imm(0x4000000000000000))]);
}

#[test]
fn format_prefixed_no_op() {
    assert_roundtrip(&[
        insn::ThrowNotexists::new(),
        insn::ThrowPatternnoncoercible::new(),
        insn::ThrowDeletesuperproperty::new(),
        insn::CallruntimeTopropertykey::new(),
        insn::DeprecatedLdlexenv::new(),
        insn::DeprecatedPoplexenv::new(),
    ]);
}

#[test]
fn format_five_operands() {
    assert_roundtrip(&[
        insn::Defineclasswithbuffer::new(Imm(0), EntityId(1), EntityId(2), Imm(3), Reg(4)),
        insn::CallruntimeDefinesendableclass::new(Imm(0), EntityId(1), EntityId(2), Imm(3), Reg(4)),
    ]);
}

#[test]
fn format_comparison_ops() {
    assert_roundtrip(&[
        insn::Eq::new(Imm(0), Reg(1)),
        insn::Noteq::new(Imm(0), Reg(2)),
        insn::Less::new(Imm(0), Reg(3)),
        insn::Lesseq::new(Imm(0), Reg(4)),
        insn::Greater::new(Imm(0), Reg(5)),
        insn::Greatereq::new(Imm(0), Reg(6)),
        insn::Stricteq::new(Imm(0), Reg(7)),
        insn::Strictnoteq::new(Imm(0), Reg(8)),
    ]);
}

#[test]
fn format_bitwise_ops() {
    assert_roundtrip(&[
        insn::Shl2::new(Imm(0), Reg(1)),
        insn::Shr2::new(Imm(0), Reg(2)),
        insn::Ashr2::new(Imm(0), Reg(3)),
        insn::And2::new(Imm(0), Reg(4)),
        insn::Or2::new(Imm(0), Reg(5)),
        insn::Xor2::new(Imm(0), Reg(6)),
        insn::Exp::new(Imm(0), Reg(7)),
        insn::Mod2::new(Imm(0), Reg(8)),
    ]);
}

#[test]
fn format_type_ops() {
    assert_roundtrip(&[
        insn::Typeof::new(Imm(0)),
        insn::Tonumber::new(Imm(0)),
        insn::Tonumeric::new(Imm(0)),
        insn::Isin::new(Imm(0), Reg(0)),
        insn::Instanceof::new(Imm(0), Reg(0)),
    ]);
}
