//! Round 5 Wave 1 regression tests covering:
//! - Issue #86 (`D1`–`D4`, `D6`, `D11`): control-flow structuring & Stage-A soundness
//! - Issue #87: folds (`Try.finally`, `literals`, `count_temp_uses`), `FrameSlots` ABI,
//!   bare-name reservation, single-file ESM & `--split-modules`, `DefineFunc` cycles,
//!   precedence/escaping/`BigInt`/`RegExp`/sentinel `Loc`, and `--arkui` AST safety
//! - Issue #88 (Part 1): `MAX_LIT_NODES` (`S2`), `Legalizer` amortized `O(1)` (`S3`),
//!   `flush_phi_tail` (`S4`), `Arc<EnvFrame>` (`S5`), and portable `split.rs` paths

use crate::common::*;
use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_decompile::legalize::Legalizer;
use abcd_decompile::split::{decompile_module_split, normalize_record_path};
use abcd_ir::consts::Const;
use abcd_ir::function::{Block, DebugData, FunctionData, Loc};
use abcd_ir::module::{
    AnnValue, Annotation, ClassData, EsModule, ExportDecl, FunctionKind, ImportDecl, ModuleRequest,
    SourceLang,
};
use abcd_ir::op::{BinOp, CallKind, CmpOp, LexEnvKind, ModuleVarKind, Op, OwnStoreKind, UnOp};
use abcd_ir::ty::{DynPrim, Ty};
use abcd_ir::{BlockId, ClassId, Edge, EdgeKind, FuncId, Modifiers, Module, ValueId};

fn body_only(m: &Module) -> String {
    let d = decompile_module(m, &EmitOptions::default());
    let mut lines: Vec<&str> = d.text.lines().collect();
    assert!(lines.len() >= 2, "header missing:\n{}", d.text);
    let mut out = lines.split_off(2).join("\n");
    if !out.is_empty() {
        out.push('\n');
    }
    out
}

fn wire_phi(m: &mut Module, phi_val: ValueId, entries: Vec<(Edge, ValueId)>) {
    let abcd_ir::ValueDef::Inst(iid) = m.value(phi_val).unwrap().def else {
        panic!("expected instruction-defined phi value");
    };
    m.inst_mut(iid).unwrap().op = Op::Phi { entries };
}

// ── Issue #86: D1, D2, D3, D4, D6, D11 ─────────────────────────────────────

#[test]
fn d1_exceptional_phi_hoisted_after_feeding_decl_and_before_first_throw() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let h0 = add_block(&mut m, f);

    // Pure `StrictEq` (two uses: exceptional phi + normal return -> materialized `const`!)
    let zero = load_number(&mut m, b0, 0.0);
    let flag = emit(
        &mut m,
        b0,
        Op::Compare {
            op: CmpOp::StrictEq,
            left: zero,
            right: p1,
        },
    );
    // Throwing call (`p2()`) followed by non-throw return (`return flag`).
    let _call = emit(
        &mut m,
        b0,
        Op::Call {
            callee: p2,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b0, Op::Return { value: Some(flag) });

    let exc = add_exception_param(&mut m, h0);
    let xphi = emit(
        &mut m,
        h0,
        Op::Phi {
            entries: vec![(
                Edge {
                    from: b0,
                    kind: EdgeKind::Exceptional,
                },
                flag,
            )],
        },
    );
    emit_void(&mut m, h0, Op::Return { value: Some(xphi) });
    add_try(&mut m, f, vec![b0], h0, exc);

    let text = body_only(&m);
    let decl_pos = text
        .find("const v4 = p1 === 0.0;")
        .expect("feeding pure Declare present");
    let xphi_pos = text.find("= v4;").expect("exceptional PhiAssign present");
    let call_pos = text.find("p2();").expect("throwing call present");
    let ret_pos = text.find("return v4;").expect("normal return present");
    assert!(
        decl_pos < xphi_pos && xphi_pos < call_pos && call_pos < ret_pos,
        "xphi must sit AFTER feeding pure Declare and BEFORE first throwing stmt:\n{text}"
    );
}

#[test]
fn d2_clean_while_rejects_impure_or_escaped_header_decl() {
    // Case A: header has effectful `Declare` (`const t = p1();` used twice in body).
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "impureHdr");
        let b_entry = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p1 = add_param(&mut m, f);
        let p2 = add_param(&mut m, f);
        let b_hdr = add_block(&mut m, f);
        let b_body = add_block(&mut m, f);
        let b_exit = add_block(&mut m, f);

        emit_void(&mut m, b_entry, Op::Branch { dest: b_hdr });
        let t = emit(
            &mut m,
            b_hdr,
            Op::Call {
                callee: p1,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let cond = emit(
            &mut m,
            b_hdr,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p2,
            },
        );
        emit_void(
            &mut m,
            b_hdr,
            Op::CondBranch {
                cond,
                true_dest: b_body,
                false_dest: b_exit,
            },
        );
        let _ = emit(
            &mut m,
            b_body,
            Op::Call {
                callee: p1,
                this: None,
                args: vec![t, t],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_body, Op::Branch { dest: b_hdr });
        emit_void(&mut m, b_exit, Op::Return { value: None });

        link(&mut m, b_entry, b_hdr);
        link(&mut m, b_hdr, b_body);
        link(&mut m, b_hdr, b_exit);
        link(&mut m, b_body, b_hdr);

        let text = body_only(&m);
        assert!(
            text.contains("while (true)"),
            "impure header Declare must NOT move into clean-while body:\n{text}"
        );
        let call_pos = text.find("= p1();").expect("header call");
        let break_pos = text.find("break;").expect("header break");
        assert!(
            call_pos < break_pos,
            "header call must run before exit check:\n{text}"
        );
    }

    // Case B: header has pure `Declare` that escapes to `b_exit`.
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "escapedHdr");
        let b_entry = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p1 = add_param(&mut m, f);
        let p2 = add_param(&mut m, f);
        let b_hdr = add_block(&mut m, f);
        let b_body = add_block(&mut m, f);
        let b_exit = add_block(&mut m, f);

        emit_void(&mut m, b_entry, Op::Branch { dest: b_hdr });
        let zero = load_number(&mut m, b_hdr, 0.0);
        let pure_val = emit(
            &mut m,
            b_hdr,
            Op::Compare {
                op: CmpOp::StrictEq,
                left: zero,
                right: p1,
            },
        );
        let cond = emit(
            &mut m,
            b_hdr,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p2,
            },
        );
        emit_void(
            &mut m,
            b_hdr,
            Op::CondBranch {
                cond,
                true_dest: b_body,
                false_dest: b_exit,
            },
        );
        let _ = emit(
            &mut m,
            b_body,
            Op::Call {
                callee: p1,
                this: None,
                args: vec![pure_val],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_body, Op::Branch { dest: b_hdr });
        emit_void(
            &mut m,
            b_exit,
            Op::Return {
                value: Some(pure_val),
            },
        );

        link(&mut m, b_entry, b_hdr);
        link(&mut m, b_hdr, b_body);
        link(&mut m, b_hdr, b_exit);
        link(&mut m, b_body, b_hdr);

        let text = body_only(&m);
        assert!(
            text.contains("while (true)"),
            "escaped header Declare must NOT move into clean-while body:\n{text}"
        );
    }
}

#[test]
fn d3_do_while_escapes_body_temp_and_bails_when_phi_clobbers_cond_var() {
    // Case A: 2-block `do { p1(); const v = p1(); p2(v); } while (v)` -> `v`
    // declared in latch (`DoWhile.body`) and read in `DoWhile.cond` must hoist to `var`!
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "doEscape");
        let b_entry = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p1 = add_param(&mut m, f);
        let p2 = add_param(&mut m, f);
        let b_hdr = add_block(&mut m, f);
        let b_latch = add_block(&mut m, f);
        let b_exit = add_block(&mut m, f);

        emit_void(&mut m, b_entry, Op::Branch { dest: b_hdr });
        let _ = emit(
            &mut m,
            b_hdr,
            Op::Call {
                callee: p1,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_hdr, Op::Branch { dest: b_latch });

        let v = emit(
            &mut m,
            b_latch,
            Op::Call {
                callee: p1,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let _ = emit(
            &mut m,
            b_latch,
            Op::Call {
                callee: p2,
                this: None,
                args: vec![v],
                kind: CallKind::Dynamic,
            },
        );
        let cond = emit(
            &mut m,
            b_latch,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: v,
            },
        );
        emit_void(
            &mut m,
            b_latch,
            Op::CondBranch {
                cond,
                true_dest: b_hdr,
                false_dest: b_exit,
            },
        );
        emit_void(&mut m, b_exit, Op::Return { value: None });

        link(&mut m, b_entry, b_hdr);
        link(&mut m, b_hdr, b_latch);
        link(&mut m, b_latch, b_hdr);
        link(&mut m, b_latch, b_exit);

        let text = body_only(&m);
        assert!(
            text.contains("do {") && text.contains("var v4;"),
            "temp declared in do-body and read in while(cond) must hoist to var:\n{text}"
        );
    }

    // Case B: 2-block `do { p2(x); } while (x++ < 3)` shape where `while_cond` reads OLD `x`
    // while `phi_cont` updates `x = x + 1.0`. Moving `x = x + 1.0` into the end of
    // `do { ... }` before `while (x < 3.0)` would test the NEW `x`!
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "postIncDoWhile");
        let b_entry = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p_x = add_param(&mut m, f);
        let p_fn = add_param(&mut m, f);
        let b_hdr = add_block(&mut m, f);
        let b_latch = add_block(&mut m, f);
        let b_exit = add_block(&mut m, f);

        emit_void(&mut m, b_entry, Op::Branch { dest: b_hdr });
        let phi_x = emit(
            &mut m,
            b_hdr,
            Op::Phi {
                entries: Vec::new(),
            },
        );
        let _ = emit(
            &mut m,
            b_hdr,
            Op::Call {
                callee: p_fn,
                this: None,
                args: vec![phi_x],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_hdr, Op::Branch { dest: b_latch });

        let one = load_number(&mut m, b_latch, 1.0);
        let next_x = add(&mut m, b_latch, phi_x, one);
        let three = load_number(&mut m, b_latch, 3.0);
        let lt = emit(
            &mut m,
            b_latch,
            Op::Compare {
                op: CmpOp::Less,
                left: three,
                right: phi_x,
            },
        );
        let cond = emit(
            &mut m,
            b_latch,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: lt,
            },
        );
        emit_void(
            &mut m,
            b_latch,
            Op::CondBranch {
                cond,
                true_dest: b_hdr,
                false_dest: b_exit,
            },
        );
        emit_void(
            &mut m,
            b_exit,
            Op::Return {
                value: Some(next_x),
            },
        );

        wire_phi(
            &mut m,
            phi_x,
            vec![
                (
                    Edge {
                        from: b_entry,
                        kind: EdgeKind::Normal,
                    },
                    p_x,
                ),
                (
                    Edge {
                        from: b_latch,
                        kind: EdgeKind::Normal,
                    },
                    next_x,
                ),
            ],
        );
        link(&mut m, b_entry, b_hdr);
        link(&mut m, b_hdr, b_latch);
        link(&mut m, b_latch, b_hdr);
        link(&mut m, b_latch, b_exit);

        let text = body_only(&m);
        assert!(
            !text.contains("} while ("),
            "do-while must bail when phi_cont clobbers variable read in while_cond:\n{text}"
        );
    }
}

#[test]
fn d4_negate_preserves_nan_ordered_comparisons() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "nanSafe");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let b_else = add_block(&mut m, f);
    let b_join = add_block(&mut m, f);

    let lt = emit(
        &mut m,
        b0,
        Op::Compare {
            op: CmpOp::Less,
            left: p2,
            right: p1,
        },
    );
    let cond = emit(
        &mut m,
        b0,
        Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: lt,
        },
    );
    // Empty `true_dest` (`b_join`) with `b_else` rejoining `b_join`
    // forces `structure` to negate `p1 < p2`.
    emit_void(
        &mut m,
        b0,
        Op::CondBranch {
            cond,
            true_dest: b_join,
            false_dest: b_else,
        },
    );
    let _ = emit(
        &mut m,
        b_else,
        Op::Call {
            callee: p1,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_else, Op::Branch { dest: b_join });
    let zero = load_number(&mut m, b_join, 0.0);
    emit_void(&mut m, b_join, Op::Return { value: Some(zero) });

    link(&mut m, b0, b_join);
    link(&mut m, b0, b_else);
    link(&mut m, b_else, b_join);

    let text = body_only(&m);
    assert!(
        text.contains("if (!(p1 < p2))") && !text.contains(">="),
        "negating `<` must emit `!(p1 < p2)`, never `>=` (NaN unsound):\n{text}"
    );
}

#[test]
fn d6_throw_not_exists_and_pattern_non_coercible_materialized() {
    let mut m = mk_module();
    let f1 = add_func_named(&mut m, "tne");
    {
        let b = entry_of(&m, f1);
        let _this = add_param(&mut m, f1);
        emit_void(&mut m, b, Op::ThrowNotExists);
    }
    let f2 = add_func_named(&mut m, "tpnc");
    {
        let b = entry_of(&m, f2);
        let _this = add_param(&mut m, f2);
        emit_void(&mut m, b, Op::ThrowPatternNonCoercible);
    }

    let d = decompile_module(&m, &EmitOptions::default());
    assert!(
        d.text
            .contains(r#"throw new ReferenceError("Variable does not exist");"#),
        "ThrowNotExists must materialize ReferenceError:\n{}",
        d.text
    );
    assert!(
        d.text
            .contains(r#"throw new TypeError("Cannot destructure undefined or null");"#),
        "ThrowPatternNonCoercible must materialize TypeError:\n{}",
        d.text
    );
    assert!(
        !d.text.contains("elided ThrowNotExists")
            && !d.text.contains("elided ThrowPatternNonCoercible"),
        "neither throw op may be elided:\n{}",
        d.text
    );
}

#[test]
fn d11_stage_a_inlining_respects_coercion_and_eval_order() {
    // Case A: `GetLexVar` across un-absorbed `ToNumber(p1)` (`+p1;` may run
    // `p1.valueOf()` which mutates lexical slot `(0, 0)`!).
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "coercionBarrier");
        let b = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p1 = add_param(&mut m, f);

        let saved = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: LexEnvKind::Plain,
            },
        );
        let _coerced = emit(
            &mut m,
            b,
            Op::UnaryOp {
                op: UnOp::ToNumber,
                operand: p1,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(saved) });

        let text = body_only(&m);
        let decl_pos = text
            .find("const ")
            .expect("GetLexVar must materialize before +p1");
        let coerce_pos = text.find("+p1;").expect("un-absorbed +p1 statement");
        let ret_pos = text.find("return ").expect("return materialized temp");
        assert!(
            decl_pos < coerce_pos && coerce_pos < ret_pos,
            "GetLexVar must not inline across +p1:\n{text}"
        );
    }

    // Case B: Out-of-order `ToNumeric` binary ops (`t1 = p1 + p2; t2 = p3 + p4; p5(t2, t1)`).
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "outOfOrder");
        let b = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p1 = add_param(&mut m, f);
        let p2 = add_param(&mut m, f);
        let p3 = add_param(&mut m, f);
        let p4 = add_param(&mut m, f);
        let p5 = add_param(&mut m, f);

        let t1 = add(&mut m, b, p1, p2);
        let t2 = add(&mut m, b, p3, p4);
        let res = emit(
            &mut m,
            b,
            Op::Call {
                callee: p5,
                this: None,
                args: vec![t2, t1],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(res) });

        let text = body_only(&m);
        assert!(
            text.contains("const v6 = p1 + p2;") && text.contains("p5(p3 + p4, v6);"),
            "t1 must materialize before t2 so p1+p2 evaluates before p3+p4:\n{text}"
        );
    }

    // Case C: In-order binary ops (`p5(t1, t2)`) still inline cleanly!
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "inOrder");
        let b = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p1 = add_param(&mut m, f);
        let p2 = add_param(&mut m, f);
        let p3 = add_param(&mut m, f);
        let p4 = add_param(&mut m, f);
        let p5 = add_param(&mut m, f);

        let t1 = add(&mut m, b, p1, p2);
        let t2 = add(&mut m, b, p3, p4);
        let res = emit(
            &mut m,
            b,
            Op::Call {
                callee: p5,
                this: None,
                args: vec![t1, t2],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(res) });

        let text = body_only(&m);
        assert!(
            text.contains("p5(p1 + p2, p3 + p4);"),
            "in-order binary ops must remain inlined:\n{text}"
        );
    }
}

// ── Issue #87: Literals, ABI, ESM/Split, Precedence, Escaping & ArkUI ──────

#[test]
fn issue87_literal_builder_eval_order_and_own_proto_computed_key() {
    // Case A: Out-of-order effectful `o = {}; t1 = p1(); t2 = p2(); o.a = t2; o.b = t1;`
    // must NOT fold into `{a: p2(), b: p1()}`!
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "litEvalOrder");
        let b = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p1 = add_param(&mut m, f);
        let p2 = add_param(&mut m, f);

        let empty_shape = const_object(&mut m, vec![], vec![]);
        let obj = emit(&mut m, b, Op::AllocObject { shape: empty_shape });
        let t1 = emit(
            &mut m,
            b,
            Op::Call {
                callee: p1,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let t2 = emit(
            &mut m,
            b,
            Op::Call {
                callee: p2,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let sa = intern(&mut m, "a");
        let sb = intern(&mut m, "b");
        emit_void(
            &mut m,
            b,
            Op::StoreOwnPropName {
                object: obj,
                name: sa,
                value: t2,
                kind: OwnStoreKind::OwnProp,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StoreOwnPropName {
                object: obj,
                name: sb,
                value: t1,
                kind: OwnStoreKind::OwnProp,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(obj) });

        let text = body_only(&m);
        let p1_pos = text.find("p1()").expect("p1 call");
        let p2_pos = text.find("p2()").expect("p2 call");
        assert!(
            p1_pos < p2_pos,
            "literal fold must preserve p1() before p2():\n{text}"
        );
    }

    // Case B: `StoreOwnPropName("__proto__")` and `Const::ObjectLiteral("__proto__")`
    // must render computed `["__proto__"]` (own property), never `{__proto__: ...}`!
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "ownProto");
        let b = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p1 = add_param(&mut m, f);

        let empty_shape = const_object(&mut m, vec![], vec![]);
        let obj = emit(&mut m, b, Op::AllocObject { shape: empty_shape });
        let s_proto = intern(&mut m, "__proto__");
        emit_void(
            &mut m,
            b,
            Op::StoreOwnPropName {
                object: obj,
                name: s_proto,
                value: p1,
                kind: OwnStoreKind::OwnProp,
            },
        );
        let lit_cid = const_object(&mut m, vec![Const::String(s_proto)], vec![Const::Int32(42)]);
        let lit_obj = emit(&mut m, b, Op::AllocObject { shape: lit_cid });
        let arr = emit(&mut m, b, Op::AllocArray { shape: None });
        let zero = load_number(&mut m, b, 0.0);
        let one = load_number(&mut m, b, 1.0);
        emit_void(
            &mut m,
            b,
            Op::StoreOwnPropIdx {
                object: arr,
                index: zero,
                value: obj,
                kind: OwnStoreKind::OwnProp,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StoreOwnPropIdx {
                object: arr,
                index: one,
                value: lit_obj,
                kind: OwnStoreKind::OwnProp,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(arr) });

        let text = body_only(&m);
        assert!(
            text.contains(r#"["__proto__"]: p1"#) && text.contains(r#"["__proto__"]: 42"#),
            "own __proto__ property must use computed [\"__proto__\"] syntax:\n{text}"
        );
    }
}

#[test]
fn issue87_frame_slots_abi_and_bare_name_reservation() {
    // 1. StaticArkTS: static method has H=0 (`params[0]` is `p0`, NOT `this`);
    //    instance method has H=1 (`params[0]` is `this`, `params[1]` is `p0`).
    {
        let mut m = Module::with_dialect(abcd_ir::Dialect::StaticArkTS);
        let c_sym = m.sym.intern("LAoo;");
        let mut cls = ClassData::new(c_sym, c_sym);
        cls.source_lang = SourceLang::ArkTS;
        m.classes.push(cls);

        let f_static = FuncId::new(0);
        let s_name = m.sym.intern("staticFn");
        let mut fd_s = FunctionData::new(ClassId::new(0), s_name, FunctionKind::Function);
        fd_s.modifiers |= Modifiers::STATIC;
        m.functions.push(fd_s);
        m.classes[0].methods.push(f_static);
        let bs = add_block(&mut m, f_static);
        let ps0 = add_param(&mut m, f_static);
        emit_void(&mut m, bs, Op::Return { value: Some(ps0) });

        let f_inst = FuncId::new(1);
        let i_name = m.sym.intern("instFn");
        let fd_i = FunctionData::new(ClassId::new(0), i_name, FunctionKind::Function);
        m.functions.push(fd_i);
        m.classes[0].methods.push(f_inst);
        let bi = add_block(&mut m, f_inst);
        let pi_this = add_param(&mut m, f_inst);
        let pi_arg0 = add_param(&mut m, f_inst);
        let sum = add(&mut m, bi, pi_this, pi_arg0);
        emit_void(&mut m, bi, Op::Return { value: Some(sum) });

        let text = body_only(&m);
        assert!(
            text.contains("function staticFn(p0) {\n  return p0;\n}"),
            "StaticArkTS static method must have H=0:\n{text}"
        );
        assert!(
            text.contains("function instFn(p1) {\n  return this + p1;\n}"),
            "StaticArkTS instance method must have H=1 (this + p1):\n{text}"
        );
    }

    // 2. DynamicEcma with `L_ESCallTypeAnnotation;` (`callType = 0b0011` -> new.target, this; H=2)
    //    AND bare-name reservation so synthetic `p2` / `e` never shadow global `p2` / `e`!
    {
        let mut m = mk_module();
        let ann_cls = add_catch_class(&mut m, "L_ESCallTypeAnnotation;");
        let f = add_func_named(&mut m, "dynAbi");
        let ct_sym = m.sym.intern("callType");
        let ct_cid = m.consts.push(Const::Int32(0b0011));
        m.func_mut(f).unwrap().annotations.push(Annotation {
            class: ann_cls,
            elements: vec![(ct_sym, AnnValue::Const(ct_cid))],
        });

        let b0 = entry_of(&m, f);
        let h0 = add_block(&mut m, f);
        let nt = add_param(&mut m, f); // idx 0 -> new.target (func=false, new_target=true)
        let this_v = add_param(&mut m, f); // idx 1 -> this
        let p_formal = add_param(&mut m, f); // idx 2 -> default synthetic base "p2"

        // Reference global `p2` and global `e` so synthetic parameter/catch names
        // must avoid shadowing them!
        let sym_p2 = m.sym.intern("p2");
        let g_p2 = emit(
            &mut m,
            b0,
            Op::TryGetGlobal {
                name: sym_p2,
                default: None,
            },
        );
        let t1 = add(&mut m, b0, nt, this_v);
        let t2 = add(&mut m, b0, t1, p_formal);
        let t3 = add(&mut m, b0, t2, g_p2);
        emit_void(&mut m, b0, Op::Return { value: Some(t3) });

        let exc = add_exception_param(&mut m, h0);
        let sym_e = m.sym.intern("e");
        let g_e = emit(
            &mut m,
            h0,
            Op::TryGetGlobal {
                name: sym_e,
                default: None,
            },
        );
        let hsum = add(&mut m, h0, exc, g_e);
        emit_void(&mut m, h0, Op::Return { value: Some(hsum) });
        add_try(&mut m, f, vec![b0], h0, exc);

        let text = body_only(&m);
        assert!(
            text.contains("function dynAbi(p2$1)")
                && text.contains("const p2$2 = p2;")
                && text.contains("return new.target + this + p2$1 + p2$2;"),
            "callType 0b0011 must decode new.target/this and synthetic p2$1 must not shadow global p2:\n{text}"
        );
        assert!(
            text.contains("catch (e$1)")
                && text.contains("const e$2 = e;")
                && text.contains("return e$1 + e$2;"),
            "synthetic catch binding e$1 must not shadow global e:\n{text}"
        );
    }

    // 3. Explicit debug `param_names` keep their natural name (`x`), even when
    //    body also references `x`.
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "explicitParam");
        let b = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let px = add_param(&mut m, f);
        let sym_this = m.sym.intern("this");
        let sym_x = m.sym.intern("x");
        m.func_mut(f).unwrap().debug = Some(DebugData {
            param_names: vec![sym_this, sym_x],
            ..DebugData::default()
        });
        emit_void(&mut m, b, Op::Return { value: Some(px) });

        let text = body_only(&m);
        assert!(
            text.contains("function explicitParam(x) {\n  return x;\n}"),
            "explicit debug param_names must keep natural name x:\n{text}"
        );
    }
}

#[test]
fn issue87_single_file_esm_side_effect_import_default_export_and_define_func_cycle() {
    // 1. Single-file ESM: External import, Namespace import, side-effect-only request,
    //    and local module slot (`let localVar;` only — NO `let m0;` or `let extFoo;`).
    {
        let mut m = mk_module();
        let s_dep = m.sym.intern("./dep");
        let s_ns_mod = m.sym.intern("./ns");
        let s_side = m.sym.intern("./polyfill");
        let s_foo = m.sym.intern("extFoo");
        let s_ns = m.sym.intern("nsObj");
        let s_local = m.sym.intern("localVar");

        m.module_requests = vec![
            ModuleRequest {
                specifier: s_dep,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_ns_mod,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_side,
                lazy: false,
            },
        ];
        m.imports = vec![
            ImportDecl::Regular {
                local_name: s_foo,
                import_name: s_foo,
                module_request: s_dep,
            },
            ImportDecl::Namespace {
                local_name: s_ns,
                module_request: s_ns_mod,
            },
        ];
        m.exports = vec![ExportDecl::Local {
            local_name: s_local,
            export_name: s_local,
        }];

        let main = add_func_named(&mut m, "func_main_0");
        let b = entry_of(&m, main);
        let _this = add_param(&mut m, main);
        let imp_v = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let ns_v = emit(&mut m, b, Op::GetModuleNamespace { index: 1 });
        let sum = add(&mut m, b, imp_v, ns_v);
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: sum,
            },
        );
        let loc_v = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::Local,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::ThrowUndefinedIfHoleWithName {
                name: s_local,
                value: loc_v,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });

        let text = body_only(&m);
        assert!(
            text.contains(r#"import { extFoo } from "./dep";"#)
                && text.contains(r#"import * as nsObj from "./ns";"#)
                && text.contains(r#"import "./polyfill";"#),
            "single-file ESM must emit regular, namespace, and side-effect imports:\n{text}"
        );
        assert!(
            text.contains("let localVar;")
                && !text.contains("let m0;")
                && !text.contains("let extFoo;")
                && !text.contains("let nsObj;")
                && text.contains("localVar = extFoo + nsObj;"),
            "single-file ESM must resolve imported bindings without let predeclarations:\n{text}"
        );
    }

    // 2. `--split-modules` anonymous `export default <expr>` (`local_name = "*default*"`)
    //    stored at slot 0: must bind slot 0 without duplicate `let _default_;`!
    {
        let mut m = Module::new();
        let desc = m.sym.intern("L@bundle:app/entry/ets/mod;");
        let mut cls = ClassData::new(desc, desc);
        let s_star_def = m.sym.intern("*default*");
        let s_def = m.sym.intern("default");
        cls.es_module = Some(EsModule {
            imports: vec![],
            exports: vec![ExportDecl::Local {
                local_name: s_star_def,
                export_name: s_def,
            }],
            module_requests: vec![],
        });
        m.classes.push(cls);

        let fid = FuncId::new(0);
        let fname = m.sym.intern("func_main_0");
        let mut fd = FunctionData::new(ClassId::new(0), fname, FunctionKind::Function);
        fd.modifiers |= Modifiers::STATIC;
        m.functions.push(fd);
        m.classes[0].methods.push(fid);
        let b = add_block(&mut m, fid);
        for _ in 0..3 {
            add_param(&mut m, fid);
        }
        let val = load_number(&mut m, b, 42.0);
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: val,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });

        let split = decompile_module_split(&m, &EmitOptions::default());
        assert_eq!(split.files.len(), 1);
        let content = &split.files[0].text;
        let let_count = content.matches("let ").count();
        assert_eq!(
            let_count, 1,
            "default export slot must be declared once without duplicate synthetic let:\n{content}"
        );
        assert!(
            content.contains("= 42.0;") && content.contains("as default };"),
            "default export slot must bind 42.0 and export as default:\n{content}"
        );
    }

    // 3. Mutual `DefineFunc` cycle (`fa` <-> `fb` with no external parent):
    //    neither dropped nor infinite-recursing!
    {
        let mut m = mk_module();
        let fa = add_func_named(&mut m, "fa");
        let fb = add_func_named(&mut m, "fb");
        {
            let ba = entry_of(&m, fa);
            let _this = add_param(&mut m, fa);
            let d = emit(
                &mut m,
                ba,
                Op::DefineFunc {
                    body: fb,
                    captures: vec![],
                    length: 0,
                },
            );
            emit_void(&mut m, ba, Op::Return { value: Some(d) });
        }
        {
            let bb = entry_of(&m, fb);
            let _this = add_param(&mut m, fb);
            let d = emit(
                &mut m,
                bb,
                Op::DefineFunc {
                    body: fa,
                    captures: vec![],
                    length: 0,
                },
            );
            emit_void(&mut m, bb, Op::Return { value: Some(d) });
        }

        let text = body_only(&m);
        assert!(
            text.contains("function fa()") && text.contains("fb"),
            "mutual DefineFunc cycle must emit without dropping the component or overflowing:\n{text}"
        );
    }
}

#[test]
fn issue87_precedence_escaping_bigint_regexp_loc_and_arkui() {
    // 1. String `\0` + digit, BigInt > 2^53-1, negative literal precedence,
    //    RegExp escaping, R5-D1 Option B BigInt unary ops, and sentinel
    //    `Loc { line: u32::MAX }` suppression.
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "lexAndPrec");
        let b = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p1 = add_param(&mut m, f);
        let p2 = add_param(&mut m, f);

        // NUL byte followed by `'1'` vs NUL byte followed by `'b'`
        let s_octal_hazard = load_string(&mut m, b, "a\x001b");
        let s_plain_nul = load_string(&mut m, b, "a\x00b");

        // `Const::Int64` and `Const::UInt64` > 2^53 - 1
        let big_i64 = load_const(&mut m, b, Const::Int64(9_007_199_254_740_993));
        let big_u64 = load_const(&mut m, b, Const::UInt64(9_007_199_254_740_995));

        // Negative numeric literal precedence: `(-1.0).x`, `(-2.0) ** p1`, `-(-3.0)`
        let neg1 = load_number(&mut m, b, -1.0);
        let sx = intern(&mut m, "x");
        let neg_prop = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: neg1,
                name: sx,
            },
        );
        let neg2 = load_number(&mut m, b, -2.0);
        let neg_exp = emit(
            &mut m,
            b,
            Op::BinaryOp {
                op: BinOp::Exp,
                left: p1,
                right: neg2,
            },
        );
        let neg3 = load_number(&mut m, b, -3.0);
        let double_neg = emit(
            &mut m,
            b,
            Op::UnaryOp {
                op: UnOp::Minus,
                operand: neg3,
            },
        );

        // RegExp: empty `""`, unescaped `"a/b"`, already-escaped `"a\/b"`
        let s_empty = intern(&mut m, "");
        let re_empty = emit(
            &mut m,
            b,
            Op::AllocRegExp {
                pattern: s_empty,
                flags: 0,
            },
        );
        let s_slash = intern(&mut m, "a/b");
        let re_slash = emit(
            &mut m,
            b,
            Op::AllocRegExp {
                pattern: s_slash,
                flags: 0,
            },
        );
        let s_esc_slash = intern(&mut m, r"a\/b");
        let re_esc_slash = emit(
            &mut m,
            b,
            Op::AllocRegExp {
                pattern: s_esc_slash,
                flags: 0,
            },
        );

        // R5-D1 Option B: BigInt `ToNumeric`, `Inc`, `Dec`
        let sym_5 = intern(&mut m, "5");
        let bi_cid = m.consts.push(Const::BigInt(sym_5));
        let bi5_a = emit(&mut m, b, Op::LoadConst(bi_cid));
        m.values[bi5_a.index()].ty = Ty::DynPrim(DynPrim::BigInt);
        let bi_tonum = emit(
            &mut m,
            b,
            Op::UnaryOp {
                op: UnOp::ToNumeric,
                operand: bi5_a,
            },
        );
        let bi5_b = emit(&mut m, b, Op::LoadConst(bi_cid));
        m.values[bi5_b.index()].ty = Ty::DynPrim(DynPrim::BigInt);
        let bi_inc = emit(
            &mut m,
            b,
            Op::UnaryOp {
                op: UnOp::Inc,
                operand: bi5_b,
            },
        );
        let bi5_c = emit(&mut m, b, Op::LoadConst(bi_cid));
        m.values[bi5_c.index()].ty = Ty::DynPrim(DynPrim::BigInt);
        let bi_dec = emit(
            &mut m,
            b,
            Op::UnaryOp {
                op: UnOp::Dec,
                operand: bi5_c,
            },
        );

        // Sentinel `Loc { line: u32::MAX, column: 0 }` must be suppressed under `line_anchors: true`.
        let call_val = emit(
            &mut m,
            b,
            Op::Call {
                callee: p2,
                this: None,
                args: vec![
                    s_octal_hazard,
                    s_plain_nul,
                    big_i64,
                    big_u64,
                    neg_prop,
                    neg_exp,
                    double_neg,
                    re_empty,
                    re_slash,
                    re_esc_slash,
                    bi_tonum,
                    bi_inc,
                    bi_dec,
                ],
                kind: CallKind::Dynamic,
            },
        );
        let abcd_ir::ValueDef::Inst(call_iid) = m.value(call_val).unwrap().def else {
            unreachable!()
        };
        m.inst_mut(call_iid).unwrap().loc = Some(Loc {
            line: u32::MAX,
            column: Some(0),
        });
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(call_val),
            },
        );

        let out = decompile_module(
            &m,
            &EmitOptions {
                line_anchors: true,
                ..EmitOptions::default()
            },
        )
        .text;

        assert!(out.contains(r#""a\x001b""#), "digit after NUL:\n{out}");
        assert!(out.contains(r#""a\0b""#), "non-digit after NUL:\n{out}");
        assert!(
            out.contains("9007199254740993n") && out.contains("9007199254740995n"),
            "unsafe 64-bit ints must render as BigInt:\n{out}"
        );
        assert!(out.contains("(-1.0).x"), "negative member base:\n{out}");
        assert!(out.contains("(-2.0) ** p1"), "negative ** LHS:\n{out}");
        assert!(out.contains("-(-3.0)"), "double unary minus:\n{out}");
        assert!(
            out.contains("/(?:)/") && out.contains(r"/a\/b/") && !out.contains(r"/a\\/b/"),
            "RegExp empty and slash escaping:\n{out}"
        );
        assert!(
            !out.contains("+5n") && out.contains("5n + 1n") && out.contains("5n - 1n"),
            "BigInt ToNumeric/Inc/Dec (R5-D1 Option B):\n{out}"
        );
        assert!(
            !out.contains("4294967295"),
            "sentinel u32::MAX line anchor must be suppressed:\n{out}"
        );
    }

    // 2. `--arkui`: string literals containing `this.__foo` / `v1_1.bar` must stay
    //    untouched, and user `if ("finalizeConstruction" in p1)` must NOT be elided!
    {
        let mut m = Module::new();
        let desc = m.sym.intern("L@bundle:app/entry/ets/pages/Safe;");
        m.classes.push(ClassData::new(desc, desc));
        let cid = ClassId::new(0);

        let add_fn3 = |m: &mut Module, name: &str, kind: FunctionKind| -> FuncId {
            let sym = m.sym.intern(name);
            let fid = FuncId::new(m.functions.len() as u32);
            let mut fd = FunctionData::new(cid, sym, kind);
            fd.modifiers |= Modifiers::STATIC;
            m.functions.push(fd);
            m.classes[0].methods.push(fid);
            let bid = BlockId::new(m.blocks.len() as u32);
            m.blocks.push(Block::default());
            m.func_mut(fid).unwrap().blocks.push(bid);
            for _ in 0..3 {
                add_param(m, fid);
            }
            fid
        };

        let f_ctor = add_fn3(&mut m, "SafeView", FunctionKind::Constructor);
        {
            let b = entry_of(&m, f_ctor);
            let this = m.func(f_ctor).unwrap().params[2];
            let s_msg = m.sym.intern("__msg");
            let g_obs = m.sym.intern("ObservedPropertySimplePU");
            let u_cid = m.consts.push(Const::Undefined);
            let u = emit(&mut m, b, Op::LoadConst(u_cid));
            let obs_cls = emit(
                &mut m,
                b,
                Op::TryGetGlobal {
                    name: g_obs,
                    default: Some(u),
                },
            );
            let init_s = load_string(&mut m, b, "this.__msg and v1_1.raw stay literal");
            let prop = emit(
                &mut m,
                b,
                Op::Call {
                    callee: obs_cls,
                    this: None,
                    args: vec![init_s, this],
                    kind: CallKind::New,
                },
            );
            emit_void(
                &mut m,
                b,
                Op::StoreProp {
                    object: this,
                    name: s_msg,
                    value: prop,
                },
            );
            emit_void(&mut m, b, Op::Return { value: Some(this) });
        }

        let f_render = add_fn3(&mut m, "initialRender", FunctionKind::Function);
        {
            let b = entry_of(&m, f_render);
            emit_void(&mut m, b, Op::Return { value: None });
        }

        let f_helper = add_fn3(&mut m, "helper", FunctionKind::Function);
        {
            let p1 = add_param(&mut m, f_helper);
            let b0 = entry_of(&m, f_helper);
            let b_then = add_block(&mut m, f_helper);
            let b_join = add_block(&mut m, f_helper);

            let fc = load_string(&mut m, b0, "finalizeConstruction");
            let has_fc = emit(
                &mut m,
                b0,
                Op::Compare {
                    op: CmpOp::In,
                    left: p1,
                    right: fc,
                },
            );
            let cond = emit(
                &mut m,
                b0,
                Op::UnaryOp {
                    op: UnOp::IsTrue,
                    operand: has_fc,
                },
            );
            emit_void(
                &mut m,
                b0,
                Op::CondBranch {
                    cond,
                    true_dest: b_then,
                    false_dest: b_join,
                },
            );
            let lit = load_string(&mut m, b_then, "keep this.__msg and v1_1.foo");
            emit_void(&mut m, b_then, Op::Return { value: Some(lit) });
            emit_void(&mut m, b_join, Op::Return { value: None });
            link(&mut m, b0, b_then);
            link(&mut m, b0, b_join);
        }

        let f_main = add_fn3(&mut m, "func_main_0", FunctionKind::Function);
        {
            let b = entry_of(&m, f_main);
            let g_vpu = m.sym.intern("ViewPU");
            let u_cid = m.consts.push(Const::Undefined);
            let u = emit(&mut m, b, Op::LoadConst(u_cid));
            let vpu = emit(
                &mut m,
                b,
                Op::TryGetGlobal {
                    name: g_vpu,
                    default: Some(u),
                },
            );
            let s_render = m.sym.intern("initialRender");
            let s_helper = m.sym.intern("helper");
            let items = [
                Const::String(s_render),
                Const::method_ref(f_render),
                Const::String(s_helper),
                Const::method_ref(f_helper),
            ]
            .map(|c| m.consts.intern(c));
            let members = m.consts.push_array(items.to_vec());
            let _cls_val = emit(
                &mut m,
                b,
                Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                    ctor: f_ctor,
                    heritage: Some(vpu),
                    members,
                    member_attrs: vec![],
                    count: 2,
                })),
            );
            // Non-polyfill user `if` mentioning `"finalizeConstruction"` in `func_main_0`:
            let b_then = add_block(&mut m, f_main);
            let b_end = add_block(&mut m, f_main);
            let fc = load_string(&mut m, b, "finalizeConstruction");
            let cond = emit(
                &mut m,
                b,
                Op::UnaryOp {
                    op: UnOp::IsTrue,
                    operand: fc,
                },
            );
            emit_void(
                &mut m,
                b,
                Op::CondBranch {
                    cond,
                    true_dest: b_then,
                    false_dest: b_end,
                },
            );
            let _ = emit(
                &mut m,
                b_then,
                Op::Call {
                    callee: vpu,
                    this: None,
                    args: vec![],
                    kind: CallKind::Dynamic,
                },
            );
            emit_void(&mut m, b_then, Op::Branch { dest: b_end });
            emit_void(&mut m, b_end, Op::Return { value: None });
            link(&mut m, b, b_then);
            link(&mut m, b, b_end);
            link(&mut m, b_then, b_end);
        }

        let out = decompile_module(
            &m,
            &EmitOptions {
                arkui: true,
                ..EmitOptions::default()
            },
        )
        .text;
        assert!(
            out.contains(r#""this.__msg and v1_1.raw stay literal""#)
                && out.contains(r#""keep this.__msg and v1_1.foo""#),
            "ArkUI AST rewrite must never corrupt string literals:\n{out}"
        );
        assert!(
            out.contains(r#"if ("finalizeConstruction")"#),
            "non-polyfill user if mentioning finalizeConstruction must NOT be elided:\n{out}"
        );
    }
}

// ── Issue #88 Part 1: S2, S3, S4 & Portable Split Paths ─────────────────────

#[test]
fn issue88_s2_exponential_const_dag_capped_cleanly() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "dagBomb");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);

    // 30-level shared diamond DAG -> 2^30 (> 1 billion) virtual leaf nodes!
    let mut cur = m.consts.intern(Const::Int32(1));
    for _ in 0..30 {
        cur = m.consts.push_array(vec![cur, cur]);
    }
    let arr = emit(&mut m, b, Op::AllocArray { shape: Some(cur) });
    emit_void(&mut m, b, Op::Return { value: Some(arr) });

    let start = std::time::Instant::now();
    let text = body_only(&m);
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_secs_f64() < 1.0,
        "MAX_LIT_NODES cap must bound exponential literal DAG in O(MAX_LIT_NODES): took {elapsed:?}"
    );
    assert!(
        text.contains("AllocArray"),
        "capped literal DAG must emit loud fallback:\n{text}"
    );
}

#[test]
fn issue88_s3_legalizer_amortized_o1_on_duplicate_mints() {
    let mut leg = Legalizer::new();
    let start = std::time::Instant::now();
    let mut last = String::new();
    for _ in 0..10_000 {
        last = leg.mint("dup");
    }
    let elapsed = start.elapsed();
    assert_eq!(last, "dup$9999");
    assert!(
        elapsed.as_secs_f64() < 1.0,
        "10k duplicate mints must run in amortized O(1): took {elapsed:?}"
    );
}

#[test]
fn issue88_portable_split_paths_windows_devices_and_case_insensitive_dedup() {
    assert_eq!(
        normalize_record_path("Laux.config.js;", false, "js"),
        Some("aux_.config.js".to_string())
    );
    assert_eq!(
        normalize_record_path("Ldir/CONIN$/COM0/LPT0.ts;", false, "js"),
        Some("dir/CONIN$_/COM0_/LPT0_.js".to_string())
    );
    assert_eq!(
        normalize_record_path("Ldir/trailing. /file. ..js;", false, "js"),
        Some("dir/trailing/file.js".to_string())
    );
    assert_eq!(
        normalize_record_path("L@package:pkg_modules/.ohpm/pkg@1.0.0/index;", false, "js"),
        Some("pkg_modules/.ohpm/pkg@1.0.0/index.js".to_string())
    );

    // Case-insensitive collision (`LFoo;` + `Lfoo;`) must disambiguate to `Foo.js` + `foo$1.js`.
    let mut m = Module::new();
    for (idx, desc) in ["LFoo;", "Lfoo;"].into_iter().enumerate() {
        let cid = ClassId::new(idx as u32);
        let sym = m.sym.intern(desc);
        let mut cls = ClassData::new(sym, sym);
        cls.es_module = Some(EsModule::default());
        m.classes.push(cls);

        let fid = FuncId::new(idx as u32);
        let fname = m.sym.intern("func_main_0");
        let mut fd = FunctionData::new(cid, fname, FunctionKind::Function);
        fd.modifiers |= Modifiers::STATIC;
        m.functions.push(fd);
        m.classes[cid.index()].methods.push(fid);
        let b = add_block(&mut m, fid);
        for _ in 0..3 {
            add_param(&mut m, fid);
        }
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let split = decompile_module_split(&m, &EmitOptions::default());
    let paths: Vec<&str> = split.files.iter().map(|f| f.rel_path.as_str()).collect();
    assert_eq!(paths, vec!["Foo.js", "foo$1.js"]);
}
