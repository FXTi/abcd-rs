//! Full-coverage exercise of the legacy (file format 0.0.0.2) translation
//! table (`abcd-isa/src/legacy_table.rs`, generated).
//!
//! The wild-corpus sweep in `legacy.rs` covers only the mappings real
//! 0.0.0.2 files happen to use (103 of 152). This file synthesizes a minimal
//! hand-laid legacy stream for every mapping the wild corpus never
//! exercises (the 49 ranges listed as dark in the merged coverage report)
//! and pins the exact decoded instruction: variant, operand order, and
//! operand values are all asserted, so a wrong table row (swapped registers,
//! wrong endianness, wrong synthesized IC slot) fails the test.
//!
//! Legacy operand encodings (see `abcd-isa/src/legacy.rs`):
//! - ecma-prefixed opcodes are `[0xff, opcode, operands...]`
//! - `id32` string operands are direct 32-bit file offsets (LE)
//! - `imm16`/`id16` operands are 16-bit LE
//! - instructions whose modern encoding gained an IC-slot immediate decode
//!   with `Imm(0)` synthesized in the first position

use abcd_isa::{Bytecode, EntityId, Imm, Reg, decode_legacy};

/// Decode a stream that must contain exactly one instruction and return it.
fn decode_one(bytes: &[u8]) -> Bytecode {
    let v = decode_legacy(bytes).unwrap();
    assert_eq!(v.len(), 1, "expected exactly one instruction");
    assert_eq!(v[0].1, 0, "single instruction must start at offset 0");
    v[0].0
}

/// legacy pref_none mappings: `[0xff, opcode]`, no operands.
#[test]
fn pref_none_mappings() {
    // ecma.ldnan (table lines 125-128)
    assert!(matches!(decode_one(&[0xff, 0x00]), Bytecode::Ldnan));
    // ecma.ldinfinity (130-133)
    assert!(matches!(decode_one(&[0xff, 0x01]), Bytecode::Ldinfinity));
    // ecma.ldsymbol (145-148)
    assert!(matches!(decode_one(&[0xff, 0x05]), Bytecode::Ldsymbol));
    // ecma.throwthrownotexists (225-228)
    assert!(matches!(
        decode_one(&[0xff, 0x15]),
        Bytecode::ThrowNotexists
    ));
    // ecma.throwpatternnoncoercible (230-233)
    assert!(matches!(
        decode_one(&[0xff, 0x16]),
        Bytecode::ThrowPatternnoncoercible
    ));
    // ecma.throwdeletesuperproperty (240-243)
    assert!(matches!(
        decode_one(&[0xff, 0x18]),
        Bytecode::ThrowDeletesuperproperty
    ));
    // ecma.notifyconcurrentresult (1166-1169)
    assert!(matches!(
        decode_one(&[0xff, 0x90]),
        Bytecode::CallruntimeNotifyconcurrentresult
    ));
}

/// legacy pref_v8 mappings whose modern encoding gained an IC slot:
/// `[0xff, opcode, v]` -> `Variant(Imm(0), Reg(v))`.
#[test]
fn pref_v8_ic_slot_mappings() {
    // ecma.shl2dyn (300-303)
    assert!(matches!(
        decode_one(&[0xff, 0x25, 0x11]),
        Bytecode::Shl2(Imm(0), Reg(0x11))
    ));
    // ecma.shr2dyn (305-308)
    assert!(matches!(
        decode_one(&[0xff, 0x26, 0x12]),
        Bytecode::Shr2(Imm(0), Reg(0x12))
    ));
    // ecma.ashr2dyn (310-313)
    assert!(matches!(
        decode_one(&[0xff, 0x27, 0x13]),
        Bytecode::Ashr2(Imm(0), Reg(0x13))
    ));
    // ecma.or2dyn (320-323)
    assert!(matches!(
        decode_one(&[0xff, 0x29, 0x15]),
        Bytecode::Or2(Imm(0), Reg(0x15))
    ));
    // ecma.xor2dyn (325-328)
    assert!(matches!(
        decode_one(&[0xff, 0x2a, 0x16]),
        Bytecode::Xor2(Imm(0), Reg(0x16))
    ));
    // ecma.instanceofdyn (360-363)
    assert!(matches!(
        decode_one(&[0xff, 0x32, 0x1e]),
        Bytecode::Instanceof(Imm(0), Reg(0x1e))
    ));
}

/// legacy pref_v8 mappings that keep a bare register (deprecated layouts
/// and throw/create helpers): `[0xff, opcode, v]` -> `Variant(Reg(v))`.
#[test]
fn pref_v8_single_reg_mappings() {
    // ecma.notdyn -> DeprecatedNot (340-343)
    assert!(matches!(
        decode_one(&[0xff, 0x2d, 0x21]),
        Bytecode::DeprecatedNot(Reg(0x21))
    ));
    // ecma.throwconstassignment (390-393)
    assert!(matches!(
        decode_one(&[0xff, 0x38, 0x26]),
        Bytecode::ThrowConstassignment(Reg(0x26))
    ));
    // ecma.gettemplateobject -> DeprecatedGettemplateobject (395-401)
    assert!(matches!(
        decode_one(&[0xff, 0x39, 0x27]),
        Bytecode::DeprecatedGettemplateobject(Reg(0x27))
    ));
    // ecma.createasyncgeneratorobj (1112-1115)
    assert!(matches!(
        decode_one(&[0xff, 0x89, 0x42]),
        Bytecode::Createasyncgeneratorobj(Reg(0x42))
    ));
    // ecma.dynamicimport -> DeprecatedDynamicimport (1137-1140)
    assert!(matches!(
        decode_one(&[0xff, 0x8c, 0x45]),
        Bytecode::DeprecatedDynamicimport(Reg(0x45))
    ));
}

/// legacy pref_v8_v8 mappings: `[0xff, opcode, v1, v2]`. Distinct register
/// values pin the operand order (a swapped row fails).
#[test]
fn pref_v8_v8_mappings() {
    // ecma.delobjprop -> DeprecatedDelobjprop (428-434)
    assert!(matches!(
        decode_one(&[0xff, 0x41, 0x21, 0x37]),
        Bytecode::DeprecatedDelobjprop(Reg(0x21), Reg(0x37))
    ));
    // ecma.createiterresultobj (436-442)
    assert!(matches!(
        decode_one(&[0xff, 0x43, 0x22, 0x38]),
        Bytecode::Createiterresultobj(Reg(0x22), Reg(0x38))
    ));
    // ecma.copydataproperties -> DeprecatedCopydataproperties (476-482)
    assert!(matches!(
        decode_one(&[0xff, 0x48, 0x23, 0x39]),
        Bytecode::DeprecatedCopydataproperties(Reg(0x23), Reg(0x39))
    ));
    // ecma.setobjectwithproto -> DeprecatedSetobjectwithproto (500-506)
    assert!(matches!(
        decode_one(&[0xff, 0x4b, 0x24, 0x3a]),
        Bytecode::DeprecatedSetobjectwithproto(Reg(0x24), Reg(0x3a))
    ));
    // ecma.stownbyvalue: gained an IC slot (524-530)
    assert!(matches!(
        decode_one(&[0xff, 0x4e, 0x25, 0x3b]),
        Bytecode::Stownbyvalue(Imm(0), Reg(0x25), Reg(0x3b))
    ));
    // ecma.ldsuperbyvalue -> DeprecatedLdsuperbyvalue (532-538)
    assert!(matches!(
        decode_one(&[0xff, 0x4f, 0x26, 0x3c]),
        Bytecode::DeprecatedLdsuperbyvalue(Reg(0x26), Reg(0x3c))
    ));
    // ecma.stsuperbyvalue: gained an IC slot (540-546)
    assert!(matches!(
        decode_one(&[0xff, 0x50, 0x27, 0x3d]),
        Bytecode::Stsuperbyvalue(Imm(0), Reg(0x27), Reg(0x3d))
    ));
    // ecma.stownbyvaluewithnameset: gained an IC slot (1077-1083)
    assert!(matches!(
        decode_one(&[0xff, 0x83, 0x28, 0x3e]),
        Bytecode::Stownbyvaluewithnameset(Imm(0), Reg(0x28), Reg(0x3e))
    ));
    // ecma.asyncgeneratorreject -> DeprecatedAsyncgeneratorreject (1158-1164)
    assert!(matches!(
        decode_one(&[0xff, 0x8f, 0x29, 0x3f]),
        Bytecode::DeprecatedAsyncgeneratorreject(Reg(0x29), Reg(0x3f))
    ));
}

/// legacy pref_v8_v8_v8 mappings: `[0xff, opcode, v1, v2, v3]`.
#[test]
fn pref_v8_v8_v8_mappings() {
    // ecma.callspreaddyn -> DeprecatedCallspread (583-589)
    assert!(matches!(
        decode_one(&[0xff, 0x54, 0x21, 0x37, 0x49]),
        Bytecode::DeprecatedCallspread(Reg(0x21), Reg(0x37), Reg(0x49))
    ));
    // ecma.asyncgeneratorresolve (1117-1123)
    assert!(matches!(
        decode_one(&[0xff, 0x8a, 0x22, 0x38, 0x4a]),
        Bytecode::Asyncgeneratorresolve(Reg(0x22), Reg(0x38), Reg(0x4a))
    ));
}

/// legacy pref_imm16 mappings: `[0xff, opcode, imm_lo, imm_hi]`.
/// The wide patchvar opcodes take a 16-bit immediate directly.
#[test]
fn pref_imm16_mappings() {
    // ecma.ldpatchvar -> WideLdpatchvar; multi-byte value pins endianness
    // (1142-1148)
    assert!(matches!(
        decode_one(&[0xff, 0x8d, 0x34, 0x12]),
        Bytecode::WideLdpatchvar(Imm(0x1234))
    ));
    // ecma.stpatchvar -> WideStpatchvar (1150-1156)
    assert!(matches!(
        decode_one(&[0xff, 0x8e, 0x78, 0x56]),
        Bytecode::WideStpatchvar(Imm(0x5678))
    ));
}

/// legacy pref_imm16_v8 mapping: `[0xff, opcode, imm_lo, imm_hi, v]`.
#[test]
fn pref_imm16_v8_mapping() {
    // ecma.callirangedyn -> Callrange(ic=0, argc, v0); multi-byte argc pins
    // endianness (661-671)
    assert!(matches!(
        decode_one(&[0xff, 0x5b, 0x05, 0x01, 0x21]),
        Bytecode::Callrange(Imm(0), Imm(0x0105), Reg(0x21))
    ));
}

/// legacy pref_imm16_v8_v8 mapping: `[0xff, opcode, imm_lo, imm_hi, v1, v2]`.
#[test]
fn pref_imm16_v8_v8_mapping() {
    // ecma.createobjectwithexcludedkeys: imm16 key count, then the object
    // and first-key registers (697-707)
    assert!(matches!(
        decode_one(&[0xff, 0x5e, 0x07, 0x01, 0x21, 0x37]),
        Bytecode::Createobjectwithexcludedkeys(Imm(0x0107), Reg(0x21), Reg(0x37))
    ));
}

/// legacy pref_id16_imm16_v8 definefunc forms: all map to modern
/// `Definefunc(Imm(0), EntityId(method), Imm(kind))`; the trailing lexenv
/// register is dropped (see `legacy.rs` module docs).
#[test]
fn pref_id16_imm16_v8_definefunc_forms() {
    // ecma.definegeneratorfunc (733-743)
    assert!(matches!(
        decode_one(&[0xff, 0x61, 0x34, 0x12, 0x05, 0x00, 0x09]),
        Bytecode::Definefunc(Imm(0), EntityId(0x1234), Imm(5))
    ));
    // ecma.defineasyncgeneratorfunc (1125-1135)
    assert!(matches!(
        decode_one(&[0xff, 0x8b, 0x78, 0x56, 0x03, 0x00, 0x07]),
        Bytecode::Definefunc(Imm(0), EntityId(0x5678), Imm(3))
    ));
}

/// legacy wide lexvar forms: 16-bit level/slot immediates.
#[test]
fn pref_imm16_imm16_mappings() {
    // ecma.ldlexvardyn wide -> WideLdlexvar; asymmetric values pin operand
    // order and endianness (835-844)
    assert!(matches!(
        decode_one(&[0xff, 0x6c, 0x01, 0x02, 0x03, 0x04]),
        Bytecode::WideLdlexvar(Imm(0x0201), Imm(0x0403))
    ));
    // ecma.stlexvardyn wide -> DeprecatedStlexvar (pref_imm16_imm16_v8)
    // (866-876)
    assert!(matches!(
        decode_one(&[0xff, 0x6f, 0x01, 0x02, 0x03, 0x04, 0x09]),
        Bytecode::DeprecatedStlexvar(Imm(0x0201), Imm(0x0403), Reg(0x09))
    ));
}

/// legacy pref_id32 mappings: `[0xff, opcode, id0, id1, id2, id3]` where
/// the id is a direct 32-bit string file offset (LE). Multi-byte values pin
/// endianness.
#[test]
fn pref_id32_mappings() {
    // ecma.getmodulenamespace -> DeprecatedGetmodulenamespace (892-900)
    assert!(matches!(
        decode_one(&[0xff, 0x71, 0xef, 0xbe, 0xad, 0xde]),
        Bytecode::DeprecatedGetmodulenamespace(EntityId(0xdeadbeef))
    ));
    // ecma.stmodulevar -> DeprecatedStmodulevar (902-910)
    assert!(matches!(
        decode_one(&[0xff, 0x72, 0x78, 0x56, 0x34, 0x12]),
        Bytecode::DeprecatedStmodulevar(EntityId(0x12345678))
    ));
    // ecma.trystglobalbyname: gained an IC slot (923-932)
    assert!(matches!(
        decode_one(&[0xff, 0x74, 0x21, 0x43, 0x65, 0x07]),
        Bytecode::Trystglobalbyname(Imm(0), EntityId(0x07654321))
    ));
    // ecma.ldglobalvar: gained an IC slot (934-943)
    assert!(matches!(
        decode_one(&[0xff, 0x75, 0x22, 0x44, 0x66, 0x08]),
        Bytecode::Ldglobalvar(Imm(0), EntityId(0x08664422))
    ));
    // ecma.stconsttoglobalrecord -> DeprecatedStconsttoglobalrecord
    // (1047-1055)
    assert!(matches!(
        decode_one(&[0xff, 0x80, 0x11, 0x22, 0x33, 0x44]),
        Bytecode::DeprecatedStconsttoglobalrecord(EntityId(0x44332211))
    ));
    // ecma.stlettoglobalrecord -> DeprecatedStlettoglobalrecord (1057-1065)
    assert!(matches!(
        decode_one(&[0xff, 0x81, 0x55, 0x66, 0x77, 0x09]),
        Bytecode::DeprecatedStlettoglobalrecord(EntityId(0x09776655))
    ));
    // ecma.stclasstoglobalrecord -> DeprecatedStclasstoglobalrecord
    // (1067-1075)
    assert!(matches!(
        decode_one(&[0xff, 0x82, 0x88, 0x99, 0xaa, 0x0b]),
        Bytecode::DeprecatedStclasstoglobalrecord(EntityId(0x0baa9988))
    ));
    // ecma.ldbigint (1097-1105)
    assert!(matches!(
        decode_one(&[0xff, 0x87, 0xcc, 0xdd, 0xee, 0x0c]),
        Bytecode::Ldbigint(EntityId(0x0ceeddcc))
    ));
}

/// legacy pref_id32_v8 mappings: `[0xff, opcode, id0..id3, v]`.
#[test]
fn pref_id32_v8_mappings() {
    // ecma.ldsuperbyname -> DeprecatedLdsuperbyname (991-1000)
    assert!(matches!(
        decode_one(&[0xff, 0x7a, 0xef, 0xbe, 0x00, 0x00, 0x21]),
        Bytecode::DeprecatedLdsuperbyname(EntityId(0xbeef), Reg(0x21))
    ));
    // ecma.stsuperbyname: gained an IC slot (1002-1012)
    assert!(matches!(
        decode_one(&[0xff, 0x7b, 0xef, 0xbe, 0x00, 0x00, 0x37]),
        Bytecode::Stsuperbyname(Imm(0), EntityId(0xbeef), Reg(0x37))
    ));
    // ecma.stownbynamewithnameset: gained an IC slot (1085-1095)
    assert!(matches!(
        decode_one(&[0xff, 0x84, 0x34, 0x12, 0x00, 0x00, 0x49]),
        Bytecode::Stownbynamewithnameset(Imm(0), EntityId(0x1234), Reg(0x49))
    ));
}

/// legacy pref_id32_imm8 mapping: `[0xff, opcode, id0..id3, imm8]`.
#[test]
fn pref_id32_imm8_mapping() {
    // ecma.ldmodulevar -> DeprecatedLdmodulevar (1014-1023)
    assert!(matches!(
        decode_one(&[0xff, 0x7c, 0x78, 0x56, 0x34, 0x12, 0x07]),
        Bytecode::DeprecatedLdmodulevar(EntityId(0x12345678), Imm(7))
    ));
}

/// All 49 synthesized streams concatenated: the decoder must walk every
/// instruction at its exact table size, so per-instruction byte offsets and
/// the total instruction count pin the size column of every exercised row.
#[test]
fn concatenated_stream_offsets() {
    let streams: [&[u8]; 49] = [
        &[0xff, 0x00],
        &[0xff, 0x01],
        &[0xff, 0x05],
        &[0xff, 0x15],
        &[0xff, 0x16],
        &[0xff, 0x18],
        &[0xff, 0x90],
        &[0xff, 0x25, 0x11],
        &[0xff, 0x26, 0x12],
        &[0xff, 0x27, 0x13],
        &[0xff, 0x29, 0x15],
        &[0xff, 0x2a, 0x16],
        &[0xff, 0x32, 0x1e],
        &[0xff, 0x2d, 0x21],
        &[0xff, 0x38, 0x26],
        &[0xff, 0x39, 0x27],
        &[0xff, 0x89, 0x42],
        &[0xff, 0x8c, 0x45],
        &[0xff, 0x41, 0x21, 0x37],
        &[0xff, 0x43, 0x22, 0x38],
        &[0xff, 0x48, 0x23, 0x39],
        &[0xff, 0x4b, 0x24, 0x3a],
        &[0xff, 0x4e, 0x25, 0x3b],
        &[0xff, 0x4f, 0x26, 0x3c],
        &[0xff, 0x50, 0x27, 0x3d],
        &[0xff, 0x83, 0x28, 0x3e],
        &[0xff, 0x8f, 0x29, 0x3f],
        &[0xff, 0x54, 0x21, 0x37, 0x49],
        &[0xff, 0x8a, 0x22, 0x38, 0x4a],
        &[0xff, 0x8d, 0x34, 0x12],
        &[0xff, 0x8e, 0x78, 0x56],
        &[0xff, 0x5b, 0x05, 0x01, 0x21],
        &[0xff, 0x5e, 0x07, 0x01, 0x21, 0x37],
        &[0xff, 0x61, 0x34, 0x12, 0x05, 0x00, 0x09],
        &[0xff, 0x8b, 0x78, 0x56, 0x03, 0x00, 0x07],
        &[0xff, 0x6c, 0x01, 0x02, 0x03, 0x04],
        &[0xff, 0x6f, 0x01, 0x02, 0x03, 0x04, 0x09],
        &[0xff, 0x71, 0xef, 0xbe, 0xad, 0xde],
        &[0xff, 0x72, 0x78, 0x56, 0x34, 0x12],
        &[0xff, 0x74, 0x21, 0x43, 0x65, 0x07],
        &[0xff, 0x75, 0x22, 0x44, 0x66, 0x08],
        &[0xff, 0x80, 0x11, 0x22, 0x33, 0x44],
        &[0xff, 0x81, 0x55, 0x66, 0x77, 0x09],
        &[0xff, 0x82, 0x88, 0x99, 0xaa, 0x0b],
        &[0xff, 0x87, 0xcc, 0xdd, 0xee, 0x0c],
        &[0xff, 0x7a, 0xef, 0xbe, 0x00, 0x00, 0x21],
        &[0xff, 0x7b, 0xef, 0xbe, 0x00, 0x00, 0x37],
        &[0xff, 0x84, 0x34, 0x12, 0x00, 0x00, 0x49],
        &[0xff, 0x7c, 0x78, 0x56, 0x34, 0x12, 0x07],
    ];
    let mut code = Vec::new();
    let mut expected_offsets = Vec::new();
    for s in streams {
        expected_offsets.push(code.len() as u32);
        code.extend_from_slice(s);
    }
    let v = decode_legacy(&code).unwrap();
    assert_eq!(v.len(), 49, "every mapping must decode one instruction");
    let offsets: Vec<u32> = v.iter().map(|(_, o)| *o).collect();
    assert_eq!(
        offsets, expected_offsets,
        "a wrong legacy size in the table desyncs the stream walk"
    );
}
