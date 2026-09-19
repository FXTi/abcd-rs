//! N36 regression (P3-T22): constant folding in BOTH engines (peephole
//! and SCCP) computed `left OP right`, but the vendored `*2` semantics
//! compute `vreg OP acc` — and the IR convention (lift `binary_op`,
//! translate.rs) is `left` = acc operand, `right` = register operand —
//! so the true semantics is `right OP left` in IR field terms.
//!
//! Vendor facts (arkcompiler_ets_runtime-master/ecmascript/interpreter/
//! interpreter_assembly.cpp):
//! - `div2` (:1095-1096): `left = GET_VREG_VALUE(v0); right = acc;`
//!   `FastDiv(left, right)` — i.e. `vreg / acc`.
//! - `less` (:1188-1189): `left = GET_VREG_VALUE(v0); right = GET_ACC();`
//!   — i.e. `vreg < acc`.
//! - `shl2` (:1319-1320), `shr2`/`ashr2` (:1394+), `eq` (:1139-1140):
//!   same `left = vreg, right = acc` pattern.
//! - `shr2` is the LOGICAL (unsigned) shift (JS `>>>`): the fast path
//!   computes `uint32(vreg) >> (acc & 0x1f)`; `ashr2` is the ARITHMETIC
//!   (signed) shift (JS `>>`): `int32(vreg) >> (acc & 0x1f)`. Both fold
//!   engines additionally had these two arms' signedness inverted.
//!
//! Every non-commutative op (Sub/Div/Mod/Exp/Shl/Shr/Ashr + Less/LessEq/
//! Greater/GreaterEq) therefore folded to the wrong value whenever both
//! operands were constants (corpus: numeric-operators, bitwise,
//! test-branch-elimination opt variants).

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::inst::{BinOp, InstData};
use abcd_ir::module::Module;
use abcd_ir::opt::FuncPass;
use abcd_ir::opt::peephole::Peephole;
use abcd_ir::opt::sccp::Sccp;
use abcd_ir::types::IrType;

/// Build `f() { return <acc_lit> OP <reg_lit> }` — left = the acc-slot
/// literal, right = the register-slot literal, exactly the field order
/// lift's `binary_op` emits — and return (module, func, binop inst).
fn build_binop_module(
    op: BinOp,
    acc_lit: f64,
    reg_lit: f64,
) -> (Module, abcd_ir::entity::FuncId, abcd_ir::entity::Inst) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let inst;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let left = builder.emit_val(InstData::LiteralNumber(acc_lit), IrType::default());
        let right = builder.emit_val(InstData::LiteralNumber(reg_lit), IrType::default());
        let (binop_inst, result) =
            builder.emit(InstData::BinaryOp { op, left, right }, IrType::default());
        inst = binop_inst;
        builder.emit_void(InstData::Return { value: result });
    }
    (module, func, inst)
}

/// Fold one binop through the given pass and return the resulting data.
fn fold<P: FuncPass>(pass: P, op: BinOp, acc_lit: f64, reg_lit: f64) -> InstData {
    let (mut module, func, inst) = build_binop_module(op, acc_lit, reg_lit);
    pass.run(&mut module, func);
    module.inst(inst).data.clone()
}

/// Extract a folded number, panicking with context otherwise.
fn folded_number(data: &InstData, ctx: &str) -> f64 {
    match data {
        InstData::LiteralNumber(n) => *n,
        other => panic!("{ctx}: expected LiteralNumber fold, got {other:?}"),
    }
}

/// Extract a folded bool, panicking with context otherwise.
fn folded_bool(data: &InstData, ctx: &str) -> bool {
    match data {
        InstData::LiteralBool(b) => *b,
        other => panic!("{ctx}: expected LiteralBool fold, got {other:?}"),
    }
}

/// The vendored semantics for the arithmetic/shift ops: `vreg OP acc`
/// (reg_lit OP acc_lit), including the JS `>>>` (logical) vs `>>`
/// (arithmetic) distinction for Shr/Ashr.
fn expected_arith(op: BinOp, acc_lit: f64, reg_lit: f64) -> f64 {
    let a = reg_lit; // vendored `left` = vreg
    let b = acc_lit; // vendored `right` = acc
    match op {
        BinOp::Add => a + b,
        BinOp::Sub => a - b,
        BinOp::Mul => a * b,
        BinOp::Div => a / b,
        BinOp::Mod => a % b,
        BinOp::Exp => a.powf(b),
        BinOp::Shl => ((a as i32) << (b as u32 & 0x1f)) as f64,
        // JS `>>>` — logical (unsigned) shift through the i32 reinterpret.
        BinOp::Shr => (((a as i32) as u32) >> (b as u32 & 0x1f)) as f64,
        // JS `>>` — arithmetic (signed) shift.
        BinOp::Ashr => ((a as i32) >> (b as u32 & 0x1f)) as f64,
        BinOp::BitAnd => ((a as i32) & (b as i32)) as f64,
        BinOp::BitOr => ((a as i32) | (b as i32)) as f64,
        BinOp::BitXor => ((a as i32) ^ (b as i32)) as f64,
        other => panic!("not an arithmetic op: {other:?}"),
    }
}

/// The vendored semantics for the comparisons: `vreg CMP acc`.
fn expected_cmp(op: BinOp, acc_lit: f64, reg_lit: f64) -> bool {
    let a = reg_lit;
    let b = acc_lit;
    match op {
        BinOp::Eq => a == b,
        BinOp::NotEq => a != b,
        BinOp::Less => a < b,
        BinOp::LessEq => a <= b,
        BinOp::Greater => a > b,
        BinOp::GreaterEq => a >= b,
        other => panic!("not a comparison op: {other:?}"),
    }
}

const ARITH_OPS: [BinOp; 11] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::Div,
    BinOp::Mod,
    BinOp::Exp,
    BinOp::Shl,
    BinOp::Shr,
    BinOp::Ashr,
    BinOp::BitOr,
    BinOp::BitXor,
];

const CMP_OPS: [BinOp; 6] = [
    BinOp::Eq,
    BinOp::NotEq,
    BinOp::Less,
    BinOp::LessEq,
    BinOp::Greater,
    BinOp::GreaterEq,
];

/// Peephole: every op folds `reg OP acc` (vendored), not `acc OP reg`.
#[test]
fn peephole_folds_vendored_operand_order() {
    // Operand pairs chosen so the swapped (buggy) order gives a
    // DIFFERENT answer for every non-commutative op.
    for op in ARITH_OPS {
        for (acc_lit, reg_lit) in [(2.0, 8.0), (1.0, 3.0), (0.5, 4.0)] {
            let data = fold(Peephole, op, acc_lit, reg_lit);
            let got = folded_number(&data, &format!("peephole {op:?}"));
            let want = expected_arith(op, acc_lit, reg_lit);
            assert_eq!(
                got.to_bits(),
                want.to_bits(),
                "peephole {op:?} must fold vreg({reg_lit}) OP acc({acc_lit}) = {want}, got {got}"
            );
        }
    }
    for op in CMP_OPS {
        for (acc_lit, reg_lit) in [(0.0, 1.0), (2.0, 1.0)] {
            let data = fold(Peephole, op, acc_lit, reg_lit);
            let got = folded_bool(&data, &format!("peephole {op:?}"));
            let want = expected_cmp(op, acc_lit, reg_lit);
            assert_eq!(
                got, want,
                "peephole {op:?} must fold vreg({reg_lit}) CMP acc({acc_lit}) = {want}, got {got}"
            );
        }
    }
}

/// SCCP: same operand order, independently (the two engines share no
/// fold code — fixing only one leaves the other misfiring).
#[test]
fn sccp_folds_vendored_operand_order() {
    for op in ARITH_OPS {
        for (acc_lit, reg_lit) in [(2.0, 8.0), (1.0, 3.0), (0.5, 4.0)] {
            let data = fold(Sccp, op, acc_lit, reg_lit);
            let got = folded_number(&data, &format!("sccp {op:?}"));
            let want = expected_arith(op, acc_lit, reg_lit);
            assert_eq!(
                got.to_bits(),
                want.to_bits(),
                "sccp {op:?} must fold vreg({reg_lit}) OP acc({acc_lit}) = {want}, got {got}"
            );
        }
    }
    for op in CMP_OPS {
        for (acc_lit, reg_lit) in [(0.0, 1.0), (2.0, 1.0)] {
            let data = fold(Sccp, op, acc_lit, reg_lit);
            let got = folded_bool(&data, &format!("sccp {op:?}"));
            let want = expected_cmp(op, acc_lit, reg_lit);
            assert_eq!(
                got, want,
                "sccp {op:?} must fold vreg({reg_lit}) CMP acc({acc_lit}) = {want}, got {got}"
            );
        }
    }
}

/// The dispatch's canonical red pins, verbatim:
/// - `BinaryOp{Div, left: Lit(2), right: Lit(8)}` folds to 4.0 (vreg 8 /
///   acc 2) — the swapped engines produced 0.25.
/// - `BinaryOp{Less, left: Lit(0), right: Lit(1)}` folds to false
///   (vreg 1 < acc 0) — the swapped engines produced true.
#[test]
fn dispatch_red_pins() {
    let data = fold(Peephole, BinOp::Div, 2.0, 8.0);
    assert_eq!(folded_number(&data, "peephole div pin"), 4.0);
    let data = fold(Sccp, BinOp::Div, 2.0, 8.0);
    assert_eq!(folded_number(&data, "sccp div pin"), 4.0);

    let data = fold(Peephole, BinOp::Less, 0.0, 1.0);
    assert!(!folded_bool(&data, "peephole less pin"));
    let data = fold(Sccp, BinOp::Less, 0.0, 1.0);
    assert!(!folded_bool(&data, "sccp less pin"));
}

/// Shr (`>>>`, logical) vs Ashr (`>>`, arithmetic) signedness, per the
/// vendored fast paths: `-8 >>> 1 = 2147483644` but `-8 >> 1 = -4`.
/// Both engines had the two arms inverted (a separate latent wrong-fold
/// in the same eval arms, fixed with the operand swap).
#[test]
fn shift_signedness_matches_vendored() {
    for (op, want) in [
        (BinOp::Shr, 2147483644.0), // (-8 as u32) >> 1
        (BinOp::Ashr, -4.0),        // (-8 as i32) >> 1
    ] {
        // acc (shift amount) = 1, vreg (value) = -8.
        let data = fold(Peephole, op, 1.0, -8.0);
        assert_eq!(
            folded_number(&data, "peephole shift"),
            want,
            "peephole {op:?} signedness"
        );
        let data = fold(Sccp, op, 1.0, -8.0);
        assert_eq!(
            folded_number(&data, "sccp shift"),
            want,
            "sccp {op:?} signedness"
        );
    }
}
