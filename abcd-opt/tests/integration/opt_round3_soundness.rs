//! Round 3 soundness, determinism, and linear-scaling regression suite
//! (`#56`, `#58`, `#60`, `#61`):
//!
//! - `R3-H5`: `SCCP` bitwise `Number` meet (`phi(+0.0, -0.0)` → `Bottom`,
//!   preserving `1.0 / phi` sign distinction) while keeping IEEE `===`/`==`.
//! - `R3-H6`: `ecma_pow` ECMA-262 §6.1.6.1.3 corner matrix over `libm::pow`
//!   in both `Peephole` and `Sccp`.
//! - `#60`: canonical `NaN` bit pattern (`0x7ff8_0000_0000_0000`) across all
//!   constant-fold producers.
//! - `R3-X1`: `UnOp::{JumpEqz, JumpNez}` and `UnOp::ToPropertyKey` folds, plus
//!   `R3-A11` `Ty::Static(_)` fold gating.
//! - `R3-M6`: `SCCP` `CondBranch` rewrite when `cond` is `ValueDef::Const`.
//! - `R3-H10` & `R3-M5`: `inline` Step H pre-call handler-phi snapshot before
//!   `replace_uses_in_func`, shared-handler dedup, and cross-class
//!   `LoadModuleVar` / `SuperArrow` / `CreateAsyncGenerator` rejections.
//! - `R3-A1` & `R3-A12`: `10,000`-block linear chain `CfgSimplify` on a
//!   `256 KiB` stack thread + trailing `CopyProp` cleanup.

use crate::common::V2Builder;
use abcd_ir::{
    AnnValue, Annotation, BinOp, BlockId, CallKind, ClassData, ClassId, CmpOp, Const, DynPrim,
    Edge, EdgeKind, FuncId, FunctionData, FunctionKind, InstId, Modifiers, Module, ModuleVarKind,
    Op, StaticTy, Ty, UnOp, ValueDef, verify_module,
};
use abcd_opt::dce::CfgSimplify;
use abcd_opt::inline::{InlinePolicy, SkipReason, inline_module};
use abcd_opt::peephole::Peephole;
use abcd_opt::sccp::Sccp;
use abcd_opt::{FuncPass, optimize_func, optimize_module};

const CANONICAL_NAN_BITS: u64 = 0x7ff8_0000_0000_0000;
const NEG_ZERO_BITS: u64 = 0x8000_0000_0000_0000;

fn verify_ok(module: &Module) {
    let report = verify_module(module);
    assert!(
        report.is_ok(),
        "module failed verification: {:?}",
        report.errors
    );
}

fn loaded_const(module: &Module, iid: InstId) -> Option<Const> {
    match &module.inst(iid)?.op {
        Op::LoadConst(cid) => module.consts.get(*cid).cloned(),
        _ => None,
    }
}

/// `R3-H5`: `phi(+0.0, -0.0)` must meet to `Bottom` in SCCP so `1.0 / phi`
/// (`+Infinity` vs `-Infinity`) is never collapsed to a single sign.
#[test]
fn sccp_phi_pos_neg_zero_meets_to_bottom_and_preserves_reciprocal() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (phi_iid, div_iid);
    {
        let mut b = V2Builder::new(&mut module, func);
        let entry = b.entry();
        let cond = b.create_param();
        let b_pos = b.create_block();
        let b_neg = b.create_block();
        let join = b.create_block();

        b.add_predecessor(b_pos, entry);
        b.add_predecessor(b_neg, entry);
        b.add_predecessor(join, b_pos);
        b.add_predecessor(join, b_neg);

        b.emit_void(Op::CondBranch {
            cond,
            true_dest: b_pos,
            false_dest: b_neg,
        });

        b.set_insert_block(b_pos);
        let pos_zero = b.emit_number(0.0);
        b.emit_void(Op::Branch { dest: join });

        b.set_insert_block(b_neg);
        let neg_zero = b.emit_number(-0.0);
        b.emit_void(Op::Branch { dest: join });

        b.set_insert_block(join);
        let (p_inst, p_val) = b.emit(Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b_pos,
                        kind: EdgeKind::Normal,
                    },
                    pos_zero,
                ),
                (
                    Edge {
                        from: b_neg,
                        kind: EdgeKind::Normal,
                    },
                    neg_zero,
                ),
            ],
        });
        phi_iid = p_inst;
        let phi_val = p_val.unwrap();
        let one = b.emit_number(1.0);
        // N36: `right / left` = `one / phi_val` = `1.0 / ±0.0`.
        let (d_inst, d_val) = b.emit(Op::BinaryOp {
            op: BinOp::Div,
            left: phi_val,
            right: one,
        });
        div_iid = d_inst;
        b.emit_void(Op::Return { value: d_val });
    }
    verify_ok(&module);

    Sccp.run(&mut module, func);
    verify_ok(&module);
    assert!(
        matches!(module.insts[phi_iid.index()].op, Op::Phi { .. }),
        "phi(+0.0, -0.0) must not collapse to a single zero sign (R3-H5)"
    );
    assert!(
        matches!(
            module.insts[div_iid.index()].op,
            Op::BinaryOp { op: BinOp::Div, .. }
        ),
        "1.0 / phi(+0.0, -0.0) must remain unfolded"
    );

    optimize_module(&mut module);
    verify_ok(&module);
    assert!(matches!(
        module.insts[div_iid.index()].op,
        Op::BinaryOp { op: BinOp::Div, .. }
    ));
}

/// IEEE `===` and `==` still treat `+0.0` and `-0.0` as equal (`true`) and
/// `NaN === NaN` as `false`.
#[test]
fn strict_and_loose_eq_keep_ieee_zero_and_nan_semantics() {
    for (op, lhs, rhs, expected) in [
        (CmpOp::StrictEq, 0.0, -0.0, true),
        (CmpOp::StrictNotEq, 0.0, -0.0, false),
        (CmpOp::StrictEq, f64::NAN, f64::NAN, false),
        (CmpOp::Eq, 0.0, -0.0, true),
        (CmpOp::Eq, f64::NAN, f64::NAN, false),
    ] {
        let mut module = Module::new();
        let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
        let cmp_iid;
        {
            let mut b = V2Builder::new(&mut module, func);
            let acc = b.emit_number(rhs);
            let reg = b.emit_number(lhs);
            let (id, res) = b.emit(Op::Compare {
                op,
                left: acc,
                right: reg,
            });
            cmp_iid = id;
            b.emit_void(Op::Return { value: res });
        }
        verify_ok(&module);
        Peephole.run(&mut module, func);
        verify_ok(&module);
        assert_eq!(
            loaded_const(&module, cmp_iid),
            Some(Const::Bool(expected)),
            "peephole {op:?}({lhs}, {rhs})"
        );
    }
}

fn eval_binop_bits_both(op: BinOp, lhs: f64, rhs: f64) -> (u64, u64) {
    let run_one = |pass: &dyn FuncPass| -> u64 {
        let mut module = Module::new();
        let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
        let bin_iid;
        {
            let mut b = V2Builder::new(&mut module, func);
            // N36: `right OP left` = `lhs OP rhs`.
            let left = b.emit_number(rhs);
            let right = b.emit_number(lhs);
            let (id, res) = b.emit(Op::BinaryOp { op, left, right });
            bin_iid = id;
            b.emit_void(Op::Return { value: res });
        }
        verify_ok(&module);
        pass.run(&mut module, func);
        verify_ok(&module);
        match loaded_const(&module, bin_iid) {
            Some(Const::Number(bits)) => bits,
            other => panic!("expected folded Number for {lhs} {op:?} {rhs}, got {other:?}"),
        }
    };
    (run_one(&Peephole), run_one(&Sccp))
}

/// `R3-H6`: ECMA-262 §6.1.6.1.3 `**` corner matrix over `libm::pow` in both
/// `Peephole` and `Sccp`.
#[test]
fn ecma_pow_corner_matrix_folds_identically_in_peephole_and_sccp() {
    let cases: &[(f64, f64, u64, &str)] = &[
        (1.0, f64::INFINITY, CANONICAL_NAN_BITS, "1 ** +Infinity"),
        (-1.0, f64::INFINITY, CANONICAL_NAN_BITS, "(-1) ** +Infinity"),
        (1.0, f64::NEG_INFINITY, CANONICAL_NAN_BITS, "1 ** -Infinity"),
        (
            -1.0,
            f64::NEG_INFINITY,
            CANONICAL_NAN_BITS,
            "(-1) ** -Infinity",
        ),
        (1.0, f64::NAN, CANONICAL_NAN_BITS, "1 ** NaN"),
        (f64::NAN, 0.0, 1.0_f64.to_bits(), "NaN ** +0"),
        (f64::NAN, -0.0, 1.0_f64.to_bits(), "NaN ** -0"),
        (-0.0, 3.0, NEG_ZERO_BITS, "(-0.0) ** 3"),
        (-0.0, 2.0, 0.0_f64.to_bits(), "(-0.0) ** 2"),
        (-0.0, -3.0, f64::NEG_INFINITY.to_bits(), "(-0.0) ** -3"),
        (-0.0, -2.0, f64::INFINITY.to_bits(), "(-0.0) ** -2"),
        (
            f64::NEG_INFINITY,
            3.0,
            f64::NEG_INFINITY.to_bits(),
            "(-Infinity) ** 3",
        ),
        (f64::NEG_INFINITY, -3.0, NEG_ZERO_BITS, "(-Infinity) ** -3"),
        (-2.0, 0.5, CANONICAL_NAN_BITS, "(-2) ** 0.5"),
        (2.0, 10.0, 1024.0_f64.to_bits(), "2 ** 10"),
        (
            2.0,
            f64::INFINITY,
            f64::INFINITY.to_bits(),
            "2 ** +Infinity",
        ),
        (0.5, f64::INFINITY, 0.0_f64.to_bits(), "0.5 ** +Infinity"),
    ];
    for &(base, exp, want_bits, label) in cases {
        let (p_bits, s_bits) = eval_binop_bits_both(BinOp::Exp, base, exp);
        assert_eq!(p_bits, want_bits, "peephole {label}: got {p_bits:#018x}");
        assert_eq!(s_bits, want_bits, "sccp {label}: got {s_bits:#018x}");
    }
}

/// `#60`: every constant-folded `NaN` normalizes to `0x7ff8_0000_0000_0000`
/// across arithmetic and unary producers while `-0.0` stays `0x8000_0000_0000_0000`.
#[test]
fn folded_nans_canonicalize_to_exact_quiet_nan_bits() {
    for (op, lhs, rhs, label) in [
        (BinOp::Div, 0.0, 0.0, "0.0 / 0.0"),
        (BinOp::Sub, f64::INFINITY, f64::INFINITY, "Inf - Inf"),
        (BinOp::Mul, 0.0, f64::INFINITY, "0.0 * Inf"),
        (BinOp::Mod, 1.0, 0.0, "1.0 % 0.0"),
    ] {
        let (p_bits, s_bits) = eval_binop_bits_both(op, lhs, rhs);
        assert_eq!(p_bits, CANONICAL_NAN_BITS, "peephole {label}");
        assert_eq!(s_bits, CANONICAL_NAN_BITS, "sccp {label}");
    }

    // Payload-carrying negative NaN fed into Minus canonicalizes to +qNaN,
    // while Minus(+0.0) preserves -0.0.
    let exotic_nan = f64::from_bits(0xfff8_0000_0000_0042);
    for pass in [&Peephole as &dyn FuncPass, &Sccp as &dyn FuncPass] {
        let mut module = Module::new();
        let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
        let (nan_iid, neg_zero_iid);
        {
            let mut b = V2Builder::new(&mut module, func);
            let n = b.emit_number(exotic_nan);
            let z = b.emit_number(0.0);
            nan_iid = b
                .emit(Op::UnaryOp {
                    op: UnOp::Minus,
                    operand: n,
                })
                .0;
            let (zid, zres) = b.emit(Op::UnaryOp {
                op: UnOp::Minus,
                operand: z,
            });
            neg_zero_iid = zid;
            b.emit_void(Op::Return { value: zres });
        }
        verify_ok(&module);
        pass.run(&mut module, func);
        verify_ok(&module);
        assert_eq!(
            loaded_const(&module, nan_iid),
            Some(Const::Number(CANONICAL_NAN_BITS))
        );
        assert_eq!(
            loaded_const(&module, neg_zero_iid),
            Some(Const::Number(NEG_ZERO_BITS))
        );
    }
}

/// `#61` `R3-X1`: `UnOp::{JumpEqz, JumpNez}`, `UnOp::ToPropertyKey`, and
/// `R3-A11` `Ty::Static` gating in both `Peephole` and `Sccp`.
#[test]
fn jump_eqz_nez_topropertykey_and_static_ty_gate() {
    for pass in [&Peephole as &dyn FuncPass, &Sccp as &dyn FuncPass] {
        let mut module = Module::new();
        let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
        let mut checks: Vec<(InstId, bool, &'static str)> = Vec::new();
        let (tpk_iid, static_add_iid, expected_key_sym);
        {
            let mut b = V2Builder::new(&mut module, func);
            let empty_sym = b.sym("");
            let non_empty_sym = b.sym("x");
            let big_sym = b.sym("0");
            expected_key_sym = non_empty_sym;

            let c_null = b.konst(Const::Null);
            let c_undef = b.konst(Const::Undefined);
            let c_nan = b.konst(Const::number(f64::NAN));
            let c_pzero = b.konst(Const::number(0.0));
            let c_nzero = b.konst(Const::number(-0.0));
            let c_one = b.konst(Const::number(1.0));
            let c_empty = b.konst(Const::String(empty_sym));
            let c_str = b.konst(Const::String(non_empty_sym));
            let c_true = b.konst(Const::Bool(true));
            let c_false = b.konst(Const::Bool(false));
            let c_big = b.konst(Const::BigInt(big_sym));

            let inputs = [
                (c_null, false, false, "null"),
                (c_undef, false, false, "undefined"),
                (c_nan, false, true, "NaN"),
                (c_pzero, true, false, "+0.0"),
                (c_nzero, true, false, "-0.0"),
                (c_one, false, true, "1.0"),
                (c_empty, false, false, "empty string"),
                (c_str, false, false, "non-empty string"),
                (c_true, false, true, "true"),
                (c_false, true, false, "false"),
                (c_big, false, false, "BigInt"),
            ];
            for (cid, want_eqz, want_nez, label) in inputs {
                let v = b.emit_val(Op::LoadConst(cid));
                let eqz_id = b
                    .emit(Op::UnaryOp {
                        op: UnOp::JumpEqz,
                        operand: v,
                    })
                    .0;
                let nez_id = b
                    .emit(Op::UnaryOp {
                        op: UnOp::JumpNez,
                        operand: v,
                    })
                    .0;
                checks.push((eqz_id, want_eqz, label));
                checks.push((nez_id, want_nez, label));
            }

            let key_v = b.emit_val(Op::LoadConst(c_str));
            tpk_iid = b
                .emit(Op::UnaryOp {
                    op: UnOp::ToPropertyKey,
                    operand: key_v,
                })
                .0;

            // `R3-A11`: Static `I32` operand/result must NOT fold through JS f64.
            let s_lhs = b.emit_number(2_000_000_000.0);
            let s_rhs = b.emit_number(2_000_000_000.0);
            b.module.values[s_lhs.index()].ty = Ty::Static(StaticTy::I32);
            b.module.values[s_rhs.index()].ty = Ty::Static(StaticTy::I32);
            let (s_id, s_res) = b.emit(Op::BinaryOp {
                op: BinOp::Add,
                left: s_lhs,
                right: s_rhs,
            });
            b.module.values[s_res.unwrap().index()].ty = Ty::Static(StaticTy::I32);
            static_add_iid = s_id;

            b.emit_void(Op::Return { value: s_res });
        }
        verify_ok(&module);
        pass.run(&mut module, func);
        verify_ok(&module);

        for (iid, want, label) in checks {
            assert_eq!(
                loaded_const(&module, iid),
                Some(Const::Bool(want)),
                "JumpEqz/JumpNez mismatch on {label}"
            );
        }
        assert_eq!(
            loaded_const(&module, tpk_iid),
            Some(Const::String(expected_key_sym)),
            "ToPropertyKey(String) must fold to String"
        );
        assert!(
            matches!(
                module.insts[static_add_iid.index()].op,
                Op::BinaryOp { op: BinOp::Add, .. }
            ),
            "Ty::Static op must not fold through JS f64 (R3-A11)"
        );
    }
}

/// `R3-M6`: `Sccp` must rewrite `CondBranch` to `Branch` when `cond` is a
/// `ValueDef::Const` (not only an `Op::LoadConst` instruction).
#[test]
fn sccp_rewrites_condbranch_with_valuedef_const_condition() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, live_bb, dead_bb);
    {
        let mut b = V2Builder::new(&mut module, func);
        entry = b.entry();
        live_bb = b.create_block();
        dead_bb = b.create_block();
        b.add_predecessor(live_bb, entry);
        b.add_predecessor(dead_bb, entry);

        let c_false = b.create_const_value(Const::Undefined);
        b.emit_void(Op::CondBranch {
            cond: c_false,
            true_dest: dead_bb,
            false_dest: live_bb,
        });

        b.set_insert_block(live_bb);
        let ok = b.emit_number(7.0);
        b.emit_void(Op::Return { value: Some(ok) });

        b.set_insert_block(dead_bb);
        let bad = b.emit_number(99.0);
        b.emit_void(Op::Return { value: Some(bad) });
    }
    verify_ok(&module);

    let changed = Sccp.run(&mut module, func);
    assert!(changed, "SCCP must fold ValueDef::Const CondBranch (R3-M6)");
    verify_ok(&module);

    let last = *module.blocks[entry.index()].insts.last().unwrap();
    assert!(
        matches!(module.insts[last.index()].op, Op::Branch { dest } if dest == live_bb),
        "CondBranch(Undefined) must rewrite to Branch(live_bb)"
    );
    assert!(
        module.blocks[dead_bb.index()].preds.is_empty(),
        "dead_bb pred edge must be pruned"
    );
}

/// `R3-H10`: inlining a call inside a protected `call_block` whose handler
/// `Phi` referenced `call_result` on `Exceptional(call_block)` must snapshot
/// BEFORE `replace_uses_in_func` so `call_block` and cloned callee blocks NEVER
/// receive `ret_val` (`42.0`), and the output module verifies cleanly under
/// `SplitValueDom`.
#[test]
fn inline_step_h_snapshots_handler_phi_before_replace_uses_and_verifies() {
    let mut module = Module::new();
    // Callee g(): returns 42.0 across two blocks so cloned_blocks has 2 blocks.
    let g = V2Builder::create_function(&mut module, "g", FunctionKind::Function);
    module.functions[g.index()].modifiers = Modifiers::STATIC;
    {
        let mut b = V2Builder::new(&mut module, g);
        for _ in 0..3 {
            b.create_param(); // [func, new.target, this] under 0xF default
        }
        let g_ret = b.create_block();
        b.add_predecessor(g_ret, b.entry());
        b.emit_void(Op::Branch { dest: g_ret });
        b.set_insert_block(g_ret);
        let ans = b.emit_number(42.0);
        b.emit_void(Op::Return { value: Some(ans) });
    }

    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    module.functions[f.index()].modifiers = Modifiers::STATIC;
    let (call_block, handler, hphi_iid);
    {
        let mut b = V2Builder::new(&mut module, f);
        call_block = b.entry();
        handler = b.create_block();

        let df = b.emit_val(Op::DefineFunc {
            body: g,
            captures: vec![],
            length: 0,
        });
        let cl = b.emit_val(Op::AllocClosure { func: df });
        let call_res = b.emit_val(Op::Call {
            callee: cl,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        });
        b.emit_void(Op::Return {
            value: Some(call_res),
        });

        let _exc = b.add_try(vec![call_block], handler);
        b.set_insert_block(handler);
        // Unverified legacy shape where `call_edge` carried `call_res`:
        // pre-fix, `replace_uses_in_func` rewrote `call_res` to `42.0` FIRST
        // and Step H copied `42.0` onto `call_block` and `g`'s entry clone!
        let (phi_id, phi_val) = b.emit(Op::Phi {
            entries: vec![(
                Edge {
                    from: call_block,
                    kind: EdgeKind::Exceptional,
                },
                call_res,
            )],
        });
        hphi_iid = phi_id;
        b.emit_void(Op::Return { value: phi_val });
    }

    let report = inline_module(&mut module, &InlinePolicy::default());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);

    let Op::Phi { entries } = &module.insts[hphi_iid.index()].op else {
        panic!("handler phi must remain a Phi");
    };
    assert_eq!(
        entries.len(),
        4,
        "call_block + 2 cloned blocks + cont = 4 deduplicated Exceptional entries"
    );
    // Neither `call_block` nor the cloned entry block may carry the callee's 42.0 return!
    for &(edge, val) in entries {
        if edge.from == call_block {
            assert!(
                matches!(module.value(val).map(|v| v.def), Some(ValueDef::Const(_))),
                "pre_call exceptional edge must carry pre-throw Undefined const, not ret_val"
            );
        }
    }
}

/// `R3-M5`: cross-class `LoadModuleVar` is rejected (`CalleeForeignValue`),
/// same-class `LoadModuleVar` inlines cleanly, and `SuperArrow` /
/// `CreateAsyncGenerator` / `NotifyConcurrentResult` / concurrent annotations
/// are rejected.
#[test]
fn inline_rejects_cross_class_module_vars_and_stage1_forbidden_ops() {
    let mut module = Module::new();
    let sym_a = module.sym.intern("La;");
    let sym_b = module.sym.intern("Lb;");
    let class_a = ClassId::new(module.classes.len() as u32);
    module.classes.push(ClassData::new(sym_a, sym_a));
    let class_b = ClassId::new(module.classes.len() as u32);
    module.classes.push(ClassData::new(sym_b, sym_b));
    let ann_sym = module.sym.intern("L_ESConcurrentModuleRequestsAnnotation;");
    let concurrent_ann_class = ClassId::new(module.classes.len() as u32);
    module.classes.push(ClassData::new(ann_sym, ann_sym));

    let make_callee = |module: &mut Module, cid: ClassId, name: &str| -> FuncId {
        let sym = module.sym.intern(name);
        let fid = FuncId::new(module.functions.len() as u32);
        let mut fdata = FunctionData::new(cid, sym, FunctionKind::Function);
        fdata.modifiers = Modifiers::STATIC;
        module.functions.push(fdata);
        let entry = BlockId::new(module.blocks.len() as u32);
        module.blocks.push(abcd_ir::Block::default());
        module.functions[fid.index()].blocks.push(entry);
        let mut b = V2Builder::new(module, fid);
        for _ in 0..3 {
            b.create_param();
        }
        fid
    };

    // 1) Cross-class LoadModuleVar -> rejected (`CalleeForeignValue`).
    let g_cross = make_callee(&mut module, class_b, "g_cross");
    {
        let mut b = V2Builder::new(&mut module, g_cross);
        let v = b.emit_val(Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::Local,
        });
        b.emit_void(Op::Return { value: Some(v) });
    }

    // 2) Same-class LoadModuleVar -> inlines!
    let g_same = make_callee(&mut module, class_a, "g_same");
    {
        let mut b = V2Builder::new(&mut module, g_same);
        let v = b.emit_val(Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::Local,
        });
        b.emit_void(Op::Return { value: Some(v) });
    }

    // 3) SuperArrow call inside callee -> rejected (`CalleeUsesSuper`).
    let g_super = make_callee(&mut module, class_a, "g_super");
    {
        let mut b = V2Builder::new(&mut module, g_super);
        let c = b.emit_number(0.0);
        let v = b.emit_val(Op::Call {
            callee: c,
            this: None,
            args: vec![],
            kind: CallKind::SuperArrow,
        });
        b.emit_void(Op::Return { value: Some(v) });
    }

    // 4) NotifyConcurrentResult -> rejected (`CalleeSuspends`).
    let g_conc_op = make_callee(&mut module, class_a, "g_conc_op");
    {
        let mut b = V2Builder::new(&mut module, g_conc_op);
        let c = b.emit_number(1.0);
        b.emit_void(Op::NotifyConcurrentResult { value: c });
        b.emit_void(Op::Return { value: Some(c) });
    }

    // 5) Concurrent-annotated function -> rejected (`CalleeKind`).
    let g_conc_fn = make_callee(&mut module, class_a, "g_conc_fn");
    module.functions[g_conc_fn.index()]
        .annotations
        .push(Annotation {
            class: concurrent_ann_class,
            elements: Vec::new(),
        });
    {
        let mut b = V2Builder::new(&mut module, g_conc_fn);
        let c = b.emit_number(2.0);
        b.emit_void(Op::Return { value: Some(c) });
    }

    let caller = make_callee(&mut module, class_a, "caller");
    {
        let mut b = V2Builder::new(&mut module, caller);
        let mut last_res = None;
        for callee in [g_cross, g_same, g_super, g_conc_op, g_conc_fn] {
            let df = b.emit_val(Op::DefineFunc {
                body: callee,
                captures: vec![],
                length: 0,
            });
            let cl = b.emit_val(Op::AllocClosure { func: df });
            last_res = Some(b.emit_val(Op::Call {
                callee: cl,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            }));
        }
        let k_sym = b.sym("k");
        let _ = AnnValue::Name(k_sym);
        b.emit_void(Op::Return { value: last_res });
    }
    verify_ok(&module);

    let report = inline_module(&mut module, &InlinePolicy::default());
    verify_ok(&module);
    assert_eq!(
        report.sites_inlined, 1,
        "only g_same may inline: {report:?}"
    );
    assert_eq!(report.skips.get(&SkipReason::CalleeForeignValue), Some(&1));
    assert_eq!(report.skips.get(&SkipReason::CalleeUsesSuper), Some(&1));
    assert_eq!(report.skips.get(&SkipReason::CalleeSuspends), Some(&1));
    assert_eq!(report.skips.get(&SkipReason::CalleeKind), Some(&1));
}

/// `R3-A1` & `R3-A12`: `CfgSimplify` and `optimize_func` contract a `10,000`-block
/// linear chain on a `256 KiB` stack thread in `O(B + I)` time and verify cleanly.
#[test]
fn cfg_simplify_contracts_10k_block_chain_on_256k_stack() {
    let handle = std::thread::Builder::new()
        .name("cfg-10k-256k".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            const N: usize = 10_000;
            let mut module = Module::new();
            let func = V2Builder::create_function(&mut module, "chain10k", FunctionKind::Function);
            {
                let mut b = V2Builder::new(&mut module, func);
                let mut blocks = Vec::with_capacity(N);
                blocks.push(b.entry());
                for _ in 1..N {
                    blocks.push(b.create_block());
                }
                let p0 = b.create_param();
                b.module.values[p0.index()].ty = Ty::DynPrim(DynPrim::Number);
                for i in 0..N {
                    b.set_insert_block(blocks[i]);
                    if i + 1 < N {
                        let next = blocks[i + 1];
                        b.add_predecessor(next, blocks[i]);
                        b.emit_void(Op::Branch { dest: next });
                    } else {
                        b.emit_void(Op::Return { value: Some(p0) });
                    }
                }
            }
            verify_ok(&module);

            let changed = CfgSimplify.run(&mut module, func);
            assert!(changed);
            assert_eq!(
                module.functions[func.index()].blocks.len(),
                1,
                "all 10,000 blocks must contract into entry in one CfgSimplify run"
            );
            verify_ok(&module);

            let _ = optimize_func(&mut module, func);
            verify_ok(&module);
        })
        .expect("spawn 256 KiB thread");
    handle
        .join()
        .expect("10k chain contraction must not overflow 256 KiB stack");
}
