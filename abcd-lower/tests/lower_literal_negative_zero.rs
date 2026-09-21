//! N37 regression (v0.2 port of
//! `abcd-ir/tests/lower_literal_negative_zero.rs`): lowering a `-0.0`
//! number constant must NOT take the integer `ldai` path.
//!
//! `-0.0 == (-0.0 as i32) as f64` is TRUE (`-0.0 == 0.0` in IEEE), so the
//! plain integer check would emit `ldai 0` for `-0.0` — losing the sign
//! bit. `1 / -0` is `-Infinity`, `Object.is(-0, 0)` is false: the VM can
//! observe the difference (corpus: literals opt variant).

mod common;

use abcd_ir::{Const, FunctionKind, Module, Op};
use abcd_isa::Bytecode;
use abcd_lower::lower_function;

use common::V2Builder;

fn lower_single_literal(n: f64) -> Vec<Bytecode> {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let cid = builder.konst(Const::Number(n.to_bits()));
        let v = builder.emit_val(Op::LoadConst(cid));
        builder.emit_void(Op::Return { value: Some(v) });
    }
    lower_function(&module, func)
        .expect("single-literal function must lower")
        .bytecodes
}

/// Red pin (dispatch): -0.0 → Fldai with bits 0x8000000000000000, never
/// Ldai(0).
#[test]
fn negative_zero_lowers_to_fldai() {
    let codes = lower_single_literal(-0.0);
    assert!(
        !codes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldai(imm) if imm.0 == 0)),
        "-0.0 must not lower to ldai 0 (loses the sign bit): {codes:?}"
    );
    assert!(
        codes.iter().any(|bc| matches!(
            bc,
            Bytecode::Fldai(bits) if *bits == abcd_isa::Imm(0x8000000000000000u64 as i64)
        )),
        "-0.0 must lower to fldai 0x8000000000000000: {codes:?}"
    );
}

/// Positive zero keeps the cheap integer path (guard must not
/// over-fire).
#[test]
fn positive_zero_still_lowers_to_ldai() {
    let codes = lower_single_literal(0.0);
    assert!(
        codes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldai(imm) if imm.0 == 0)),
        "+0.0 must keep the ldai path: {codes:?}"
    );
}

/// Ordinary integers and non-integers are unaffected.
#[test]
fn integer_and_fraction_paths_unchanged() {
    let codes = lower_single_literal(42.0);
    assert!(
        codes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldai(imm) if imm.0 == 42)),
        "42.0 must keep the ldai path: {codes:?}"
    );
    let codes = lower_single_literal(1.5);
    assert!(
        codes.iter().any(|bc| matches!(
            bc,
            Bytecode::Fldai(bits) if *bits == abcd_isa::Imm(1.5f64.to_bits() as i64)
        )),
        "1.5 must keep the fldai path: {codes:?}"
    );
}
