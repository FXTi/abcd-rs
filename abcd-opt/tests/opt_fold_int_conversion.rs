//! N42 regression (v0.2 port of v0.1 `opt_fold_int_conversion.rs`): both
//! fold engines (peephole and SCCP) must convert f64 constants to
//! integers with ECMA-262 ToInt32/ToUint32 — WRAP mod 2^32, with
//! NaN/±Infinity → +0 — not Rust's saturating `as` casts.
//!
//! Vendor facts (arkcompiler_ets_runtime-master):
//! - Every `*2` bitwise/shift fast path (shl2/ashr2/and2/or2/xor2
//!   interpreter_assembly.cpp:1313+, shr2 :1357+) converts double operands
//!   with `base::NumberHelper::DoubleToInt(v, base::INT32_BITS)`.
//! - `NumberHelper::DoubleToInt` (ecmascript/base/number_helper.cpp:1137-
//!   1158) is truncate-then-wrap mod 2^32: values whose exponent leaves no
//!   significand bits after mod 2^32 — including NaN and ±Infinity — map
//!   to 0. It is NOT saturating (`SaturateTruncDoubleToInt32` is a
//!   separate, explicitly-named function that these handlers do NOT use).
//! - The shift count is masked `& 0x1f` AFTER the ToInt32/ToUint32
//!   conversion (e.g. HandleShl2Imm8V8: `static_cast<uint32_t>(opNumber1)
//!   & 0x1f`), so a negative count like -1 wraps to 0xFFFFFFFF and then
//!   masks to 31 — the old code saturated -1 to 0 first and masked to 0.

mod common;

use abcd_ir::{BinOp, Const, FuncId, FunctionKind, InstId, Module, Op, UnOp};
use abcd_opt::FuncPass;
use abcd_opt::peephole::Peephole;
use abcd_opt::sccp::Sccp;

use common::V2Builder;

/// Build `f() { return <acc_lit> OP <reg_lit> }` — left = acc operand,
/// right = register operand, the field order lift's `binary_op` emits —
/// so the vendored semantics is `reg_lit OP acc_lit` (N36).
fn build_binop_module(op: BinOp, acc_lit: f64, reg_lit: f64) -> (Module, FuncId, InstId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let inst;
    {
        let mut b = V2Builder::new(&mut module, func);
        let left = b.emit_number(acc_lit);
        let right = b.emit_number(reg_lit);
        let (binop_inst, result) = b.emit(Op::BinaryOp { op, left, right });
        inst = binop_inst;
        b.emit_void(Op::Return { value: result });
    }
    (module, func, inst)
}

/// Build `f() { return ~<lit> }` (vendor `not` is bitwise, N39).
fn build_bitnot_module(lit: f64) -> (Module, FuncId, InstId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let inst;
    {
        let mut b = V2Builder::new(&mut module, func);
        let operand = b.emit_number(lit);
        let (unop_inst, result) = b.emit(Op::UnaryOp {
            op: UnOp::BitNot,
            operand,
        });
        inst = unop_inst;
        b.emit_void(Op::Return { value: result });
    }
    (module, func, inst)
}

fn fold_binop<P: FuncPass>(pass: P, op: BinOp, acc_lit: f64, reg_lit: f64) -> f64 {
    let (mut module, func, inst) = build_binop_module(op, acc_lit, reg_lit);
    pass.run(&mut module, func);
    match &module.insts[inst.index()].op {
        Op::LoadConst(cid) => match module.consts.get(*cid) {
            Some(Const::Number(bits)) => f64::from_bits(*bits),
            other => panic!("expected Number fold, got {other:?}"),
        },
        other => panic!("expected LoadConst fold, got {other:?}"),
    }
}

fn fold_bitnot<P: FuncPass>(pass: P, lit: f64) -> f64 {
    let (mut module, func, inst) = build_bitnot_module(lit);
    pass.run(&mut module, func);
    match &module.insts[inst.index()].op {
        Op::LoadConst(cid) => match module.consts.get(*cid) {
            Some(Const::Number(bits)) => f64::from_bits(*bits),
            other => panic!("expected Number fold, got {other:?}"),
        },
        other => panic!("expected LoadConst fold, got {other:?}"),
    }
}

/// ECMA-262 ToInt32 reference for the expected values (truncate, wrap mod
/// 2^32, NaN/±Inf → +0). Deliberately independent of the implementation
/// under test: computed with i128 intermediates.
fn ref_to_int32(n: f64) -> i32 {
    if !n.is_finite() || n == 0.0 {
        return 0;
    }
    let t = n.trunc() as i128; // exact: these probes are all < 2^63
    (t.rem_euclid(1 << 32)) as u32 as i32
}

/// ECMA-262 ToUint32 reference.
fn ref_to_uint32(n: f64) -> u32 {
    ref_to_int32(n) as u32
}

/// The dispatch's canonical red probes, through BOTH engines.
#[test]
fn js_int_conversion_probes_peephole() {
    // 2147483648 | 0 → -2147483648 (wrap), NOT 2147483647 (saturate).
    // vreg = 2147483648, acc = 0 (order immaterial for |, kept uniform).
    assert_eq!(
        fold_binop(Peephole, BinOp::BitOr, 0.0, 2147483648.0),
        -2147483648.0
    );
    // 1 << -1 → 1 << (0xFFFFFFFF & 31) = 1 << 31 = -2147483648.
    // vreg = 1 (value), acc = -1 (shift count).
    assert_eq!(fold_binop(Peephole, BinOp::Shl, -1.0, 1.0), -2147483648.0);
    // Infinity | 0 → ToInt32(Inf) = 0.
    assert_eq!(fold_binop(Peephole, BinOp::BitOr, 0.0, f64::INFINITY), 0.0);
    // ~4294967296 → ~ToInt32(2^32) = ~0 = -1.
    assert_eq!(fold_bitnot(Peephole, 4294967296.0), -1.0);
}

#[test]
fn js_int_conversion_probes_sccp() {
    assert_eq!(
        fold_binop(Sccp, BinOp::BitOr, 0.0, 2147483648.0),
        -2147483648.0
    );
    assert_eq!(fold_binop(Sccp, BinOp::Shl, -1.0, 1.0), -2147483648.0);
    assert_eq!(fold_binop(Sccp, BinOp::BitOr, 0.0, f64::INFINITY), 0.0);
    assert_eq!(fold_bitnot(Sccp, 4294967296.0), -1.0);
}

/// Broader conversion table: NaN/±Inf → 0, wrap for out-of-range values,
/// negative shift counts masked AFTER wrapping — both engines, every
/// bitwise/shift arm.
#[test]
fn js_int_conversion_table() {
    // (op, acc_lit, reg_lit): vendored semantics is reg_lit OP acc_lit.
    let binop_cases: &[(BinOp, f64, f64)] = &[
        (BinOp::BitOr, 0.0, f64::NAN),          // NaN|0 → 0
        (BinOp::BitOr, 0.0, f64::NEG_INFINITY), // -Inf|0 → 0
        (BinOp::BitAnd, -1.0, 4294967296.0),    // ToInt32(2^32)=0 → 0 & -1 = 0
        (BinOp::BitXor, 0.0, -2147483649.0),    // wraps to 2147483647
        (BinOp::BitOr, 0.0, 4294967297.0),      // wraps to 1 (saturate: 2147483647)
        (BinOp::Shl, 32.0, 1.0),                // 1 << (32&31)=1<<0 → 1
        (BinOp::Shl, 33.0, 1.0),                // 1 << 1 → 2
        (BinOp::Shl, -2.0, 1.0),                // 1 << 30 → 1073741824
        (BinOp::Ashr, -1.0, -8.0),              // -8 >> 31 → -1
        (BinOp::Shr, -1.0, -8.0),               // (-8 as u32) >>> 31 → 1
        (BinOp::Shr, 0.0, 4294967297.0),        // ToInt32 → 1 >>> 0 → 1
    ];
    for &(op, acc_lit, reg_lit) in binop_cases {
        let a = ref_to_int32(reg_lit); // vendored left = vreg
        let b = ref_to_uint32(acc_lit); // vendored right = acc, masked below
        let want = match op {
            BinOp::BitAnd => (a & ref_to_int32(acc_lit)) as f64,
            BinOp::BitOr => (a | ref_to_int32(acc_lit)) as f64,
            BinOp::BitXor => (a ^ ref_to_int32(acc_lit)) as f64,
            BinOp::Shl => (a << (b & 0x1f)) as f64,
            BinOp::Shr => ((a as u32) >> (b & 0x1f)) as f64,
            BinOp::Ashr => (a >> (b & 0x1f)) as f64,
            other => panic!("not a bitwise/shift op: {other:?}"),
        };
        let got = fold_binop(Peephole, op, acc_lit, reg_lit);
        assert_eq!(
            got.to_bits(),
            want.to_bits(),
            "peephole {op:?} vreg({reg_lit}) OP acc({acc_lit}): want {want}, got {got}"
        );
        let got = fold_binop(Sccp, op, acc_lit, reg_lit);
        assert_eq!(
            got.to_bits(),
            want.to_bits(),
            "sccp {op:?} vreg({reg_lit}) OP acc({acc_lit}): want {want}, got {got}"
        );
    }

    // BitNot through ToInt32.
    for lit in [4294967296.0, f64::NAN, f64::INFINITY, -4294967297.0, 0.5] {
        let want = !ref_to_int32(lit) as f64;
        assert_eq!(
            fold_bitnot(Peephole, lit),
            want,
            "peephole ~({lit}): want {want}"
        );
        assert_eq!(fold_bitnot(Sccp, lit), want, "sccp ~({lit}): want {want}");
    }
}
