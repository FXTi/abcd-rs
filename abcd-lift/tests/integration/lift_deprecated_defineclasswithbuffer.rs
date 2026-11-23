//! N54 regression (v0.2 lifter): `deprecated.defineclasswithbuffer
//! method_id, imm1:u16, imm2:u16, v1:in:top, v2:in:top`
//! (abcd-isa-sys/arkcompiler_runtime_core/isa/isa.yaml:1239-1244) — the vendor runtime
//! reads v1 as the LEXENV and v2 as the PROTO
//! (arkcompiler_ets_runtime-master/ecmascript/interpreter/
//! interpreter_assembly.cpp:4622-4648,
//! `HandleDeprecatedDefineclasswithbufferPrefId16Imm16Imm16V8V8` —
//! `lexenv = GET_VREG_VALUE(v0)`, `proto = GET_VREG_VALUE(v1)`), but
//! this lifter historically took v1 as the base (proto) and DROPPED
//! v2 — double role corruption. Corpus coverage is zero (reference.pa
//! grep: none), so there is no evidence path for a corrected lift —
//! a hard error (maintainer ruling N8/N51: hard error, never a
//! warning, never silent pass-through), mirroring v0.1.
//!
//! Red-first: pre-fix this synthetic body lifted SILENTLY (the arm
//! resolved the ctor + literal array and succeeded with the corrupted
//! roles); post-fix it errs.

use abcd_file::{AccessFlags, Builder, CodeEntity, File, Type, decode};
use abcd_isa::{Bytecode, EntityId, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;

/// Placeholder entity id wired later via `relocate_code_id`.
const PLACEHOLDER: EntityId = EntityId(u16::MAX as u32);

/// Build a 12.x file whose global class carries one static method `f`
/// whose body is `[deprecated.defineclasswithbuffer ..., returnundefined]`
/// with the method_id operand wired to `f` itself and one literal array
/// at table index 0 (pre-fix the arm resolved both and succeeded
/// silently).
fn build_file() -> File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    // The pre-fix arm resolved imm1 as a raw literal-array TABLE index
    // (v0.1 parity); one array keeps index 0 in range.
    let la = b.add_literal_array("litarr");
    b.literal_array_add_u32(la, 1);
    let bytecodes = [
        Bytecode::DeprecatedDefineclasswithbuffer(PLACEHOLDER, Imm(0), Imm(1), Reg(0), Reg(1)),
        Bytecode::Returnundefined,
    ];
    let (code, offsets) = encode_bytecodes(&bytecodes).unwrap();
    let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 2, 0);
    b.relocate_code_id(m, offsets[0], 0, CodeEntity::Method(m))
        .unwrap();
    decode(&b.finalize().unwrap()).unwrap()
}

#[test]
fn deprecated_defineclasswithbuffer_is_hard_error() {
    let file = build_file();
    let err = lift_file(&file).expect_err("deprecated.defineclasswithbuffer must fail lift (N54)");
    assert!(
        matches!(
            err,
            abcd_lift::LiftError::UnsupportedDeprecatedDefineClassWithBuffer
        ),
        "dedicated N54 variant, got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("deprecated.defineclasswithbuffer"),
        "error names the opcode: {msg}"
    );
    assert!(msg.contains("N54"), "error cites the ruling: {msg}");
    assert!(
        msg.contains("v1=lexenv") && msg.contains("v2=proto"),
        "error cites the vendor roles: {msg}"
    );
}
