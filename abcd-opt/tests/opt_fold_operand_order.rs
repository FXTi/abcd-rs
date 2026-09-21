//! N36 regression (v0.2 port of v0.1 `opt_fold_operand_order.rs`):
//! constant folding in BOTH engines (peephole and SCCP) computes
//! `right OP left` in IR field terms — the IR convention (lift
//! `binary_op`/`compare`, translate.rs) is `left` = acc operand,
//! `right` = register operand, and the vendored `*2` semantics compute
//! `vreg OP acc`.
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
//!   (signed) shift (JS `>>`): `int32(vreg) >> (acc & 0x1f)`.
//!
//! v0.2 taxonomy note: arithmetic lives in [`BinOp`] (`Op::BinaryOp`),
//! comparisons in [`CmpOp`] (`Op::Compare`) — the operand roles are
//! identical (lift emits `left = acc, right = vreg` for both).

mod common;

use abcd_ir::{BinOp, CmpOp, Const, FuncId, FunctionKind, InstId, Module, Op};
use abcd_ir::{VerifyReport, verify_func};
use abcd_opt::FuncPass;
use abcd_opt::peephole::Peephole;
use abcd_opt::sccp::Sccp;

use common::V2Builder;

/// Build `f() { return <acc_lit> OP <reg_lit> }` — left = the acc-slot
/// literal, right = the register-slot literal, exactly the field order
/// lift's `binary_op` emits — and return (module, func, binop inst).
fn build_binop_module(op: BinOp, acc_lit: f64, reg_lit: f64) -> (Module, FuncId, InstId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let inst;
    {
        let mut b = V2Builder::new(&mut module, func);
        let left = b.emit_number(acc_lit);
        let right = b.emit_number(reg_lit);
        let (binop_inst, _result) = b.emit(Op::BinaryOp { op, left, right });
        inst = binop_inst;
        b.emit_void(Op::Return {
            value: Some(_result.unwrap()),
        });
    }
    (module, func, inst)
}

/// Build `f() { return <acc_lit> CMP <reg_lit> }`.
fn build_compare_module(op: CmpOp, acc_lit: f64, reg_lit: f64) -> (Module, FuncId, InstId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let inst;
    {
        let mut b = V2Builder::new(&mut module, func);
        let left = b.emit_number(acc_lit);
        let right = b.emit_number(reg_lit);
        let (cmp_inst, result) = b.emit(Op::Compare { op, left, right });
        inst = cmp_inst;
        b.emit_void(Op::Return { value: result });
    }
    (module, func, inst)
}

/// Extract the pooled constant an instruction loads, post-fold.
fn folded_const(module: &Module, inst: InstId, ctx: &str) -> Const {
    match &module.insts[inst.index()].op {
        Op::LoadConst(cid) => module
            .consts
            .get(*cid)
            .unwrap_or_else(|| panic!("{ctx}: folded const id must resolve"))
            .clone(),
        other => panic!("{ctx}: expected LoadConst fold, got {other:?}"),
    }
}

/// Extract a folded number, panicking with context otherwise.
fn folded_number(module: &Module, inst: InstId, ctx: &str) -> f64 {
    match folded_const(module, inst, ctx) {
        Const::Number(bits) => f64::from_bits(bits),
        other => panic!("{ctx}: expected Number fold, got {other:?}"),
    }
}

/// Extract a folded bool, panicking with context otherwise.
fn folded_bool(module: &Module, inst: InstId, ctx: &str) -> bool {
    match folded_const(module, inst, ctx) {
        Const::Bool(b) => b,
        other => panic!("{ctx}: expected Bool fold, got {other:?}"),
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
    }
}

/// The vendored semantics for the comparisons: `vreg CMP acc`.
fn expected_cmp(op: CmpOp, acc_lit: f64, reg_lit: f64) -> bool {
    let a = reg_lit;
    let b = acc_lit;
    match op {
        CmpOp::Eq => a == b,
        CmpOp::NotEq => a != b,
        CmpOp::Less => a < b,
        CmpOp::LessEq => a <= b,
        CmpOp::Greater => a > b,
        CmpOp::GreaterEq => a >= b,
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

const CMP_OPS: [CmpOp; 6] = [
    CmpOp::Eq,
    CmpOp::NotEq,
    CmpOp::Less,
    CmpOp::LessEq,
    CmpOp::Greater,
    CmpOp::GreaterEq,
];

/// Fold one binop through the given pass and return the pooled constant.
fn fold<P: FuncPass>(pass: P, op: BinOp, acc_lit: f64, reg_lit: f64) -> (Module, FuncId, InstId) {
    let (mut module, func, inst) = build_binop_module(op, acc_lit, reg_lit);
    pass.run(&mut module, func);
    (module, func, inst)
}

/// Fold one comparison through the given pass.
fn fold_cmp<P: FuncPass>(
    pass: P,
    op: CmpOp,
    acc_lit: f64,
    reg_lit: f64,
) -> (Module, FuncId, InstId) {
    let (mut module, func, inst) = build_compare_module(op, acc_lit, reg_lit);
    pass.run(&mut module, func);
    (module, func, inst)
}

/// Peephole: every op folds `reg OP acc` (vendored), not `acc OP reg`.
#[test]
fn peephole_folds_vendored_operand_order() {
    // Operand pairs chosen so the swapped (buggy) order gives a
    // DIFFERENT answer for every non-commutative op.
    for op in ARITH_OPS {
        for (acc_lit, reg_lit) in [(2.0, 8.0), (1.0, 3.0), (0.5, 4.0)] {
            let (module, _func, inst) = fold(Peephole, op, acc_lit, reg_lit);
            let got = folded_number(&module, inst, "peephole");
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
            let (module, _func, inst) = fold_cmp(Peephole, op, acc_lit, reg_lit);
            let got = folded_bool(&module, inst, "peephole");
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
            let (module, _func, inst) = fold(Sccp, op, acc_lit, reg_lit);
            let got = folded_number(&module, inst, "sccp");
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
            let (module, _func, inst) = fold_cmp(Sccp, op, acc_lit, reg_lit);
            let got = folded_bool(&module, inst, "sccp");
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
/// - `Compare{Less, left: Lit(0), right: Lit(1)}` folds to false
///   (vreg 1 < acc 0) — the swapped engines produced true.
#[test]
fn dispatch_red_pins() {
    let (module, _f, inst) = fold(Peephole, BinOp::Div, 2.0, 8.0);
    assert_eq!(folded_number(&module, inst, "peephole div pin"), 4.0);
    let (module, _f, inst) = fold(Sccp, BinOp::Div, 2.0, 8.0);
    assert_eq!(folded_number(&module, inst, "sccp div pin"), 4.0);

    let (module, _f, inst) = fold_cmp(Peephole, CmpOp::Less, 0.0, 1.0);
    assert!(!folded_bool(&module, inst, "peephole less pin"));
    let (module, _f, inst) = fold_cmp(Sccp, CmpOp::Less, 0.0, 1.0);
    assert!(!folded_bool(&module, inst, "sccp less pin"));
}

/// Shr (`>>>`, logical) vs Ashr (`>>`, arithmetic) signedness, per the
/// vendored fast paths: `-8 >>> 1 = 2147483644` but `-8 >> 1 = -4`.
#[test]
fn shift_signedness_matches_vendored() {
    for (op, want) in [
        (BinOp::Shr, 2147483644.0), // (-8 as u32) >> 1
        (BinOp::Ashr, -4.0),        // (-8 as i32) >> 1
    ] {
        // acc (shift amount) = 1, vreg (value) = -8.
        let (module, _f, inst) = fold(Peephole, op, 1.0, -8.0);
        assert_eq!(
            folded_number(&module, inst, "peephole shift"),
            want,
            "peephole {op:?} signedness"
        );
        let (module, _f, inst) = fold(Sccp, op, 1.0, -8.0);
        assert_eq!(
            folded_number(&module, inst, "sccp shift"),
            want,
            "sccp {op:?} signedness"
        );
    }
}

/// Folded modules stay verifier-clean (the N27/N28 hygiene rule applies
/// to every pass, peephole included).
#[test]
fn folds_keep_module_verifier_clean() {
    let (module, func, _inst) = fold(Peephole, BinOp::Div, 2.0, 8.0);
    let report: VerifyReport = verify_func(&module, func);
    assert!(report.is_ok(), "post-peephole verify: {:?}", report.errors);
    let (module, func, _inst) = fold(Sccp, BinOp::Div, 2.0, 8.0);
    let report = verify_func(&module, func);
    assert!(report.is_ok(), "post-sccp verify: {:?}", report.errors);
}
