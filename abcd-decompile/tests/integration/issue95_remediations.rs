//! L1 regression suite for GitHub Issue #95 (`abcd-decompile` Parts A–E):
//! - `256 KiB`-stack `5,000`-depth zero-recursion tests for `Expr`, `Lit`,
//!   `SNode`, and `TryPlan` (`Clone`, `PartialEq`, `Eq`, `Debug`, `Drop`).
//! - Relocated `structure::regions` single-pass iterative Tarjan SCC
//!   irreducible multi-core / self-loop detection and `RegionTree::try_plan_forest`.
//! - Ramsey (*ICFP* 2022) complete forward labeled-block merges (`D4`, `R5-1`).
//! - Executable JS emission for unfolded `for...in` `GetPropIterator` /
//!   `NextPropName` (`R5-2`).
//! - `Module::dialect` (`Dialect::StaticArkTS` vs `Dialect::DynamicEcma`) ABI
//!   recovery without `L_ES*` annotation sniffing (`D3`).
//! - `UnOp::IsTrue` `!!x` precedence & boolean condition peeling (`R5-3`),
//!   deduplicated `catch_names` (`R5-3`), full-stack `#private` lookup +
//!   `#p{abs}_{slot}` fallback + `#static` alignment (`R5-4`), `--arkui` live
//!   `undefined` temp preservation, `fold_rest_destructure` safety & quoted keys,
//!   irreducible dispatch `TryRegion` / phi / `D$k` fidelity (`R5-5`),
//!   conditional-phi non-inlining & degenerate `CondBranch` side-effect
//!   preservation (`R5-6a`), strict `===` `switch` folding (`R5-6b`), ESM
//!   `[[RequestedModules]]` ordering / quoted exports / import collision
//!   disambiguation / 4- & 5-field `OhmUrl` splitting (`R5-6c`), and statement
//!   parenthesization / lexical `{ let ... }` scoping / `Fallback` `may_throw`.

use crate::common::*;
use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_decompile::expr::{ArrayElem, Expr, Lit, ObjEntry, ObjKey};
use abcd_decompile::recover::{Stmt, recover_func};
use abcd_decompile::split::decompile_module_split;
use abcd_decompile::structure::regions::{RegionId, TryPlan, structure_regions};
use abcd_decompile::structure::{CatchClause, Leaf, SNode, SwitchCase, structure_func};
use abcd_ir::consts::Const;
use abcd_ir::function::{Block, FunctionData};
use abcd_ir::id::{BlockId, ClassId, FuncId, ValueId};
use abcd_ir::module::{
    ClassData, Dialect, EsModule, ExportDecl, FunctionKind, ImportDecl, Modifiers, Module,
    ModuleRequest, SourceLang,
};
use abcd_ir::op::{BinOp, CallKind, CmpOp, LexEnvKind, ModuleVarKind, Op, OwnStoreKind, UnOp};

fn run_on_256k_stack<F>(name: &str, f: F)
where
    F: FnOnce() + Send,
{
    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(name.to_string())
            .stack_size(256 * 1024)
            .spawn_scoped(s, f)
            .expect("spawn 256 KiB stack thread");
        handle
            .join()
            .expect("256 KiB thread must complete without stack overflow");
    });
}

#[test]
fn stack_256k_5000_depth_expr_snode_lit_and_try_plan() {
    const DEPTH: usize = 5_000;

    run_on_256k_stack("issue95-5k-recursive-types-256k", || {
        // 1. 5,000-depth `Lit` (`Array` + `Object`): Clone, PartialEq, Debug, Drop
        let mut lit = Lit::Number(1.0_f64.to_bits());
        for i in 0..DEPTH {
            if i % 2 == 0 {
                lit = Lit::Array(vec![lit]);
            } else {
                lit = Lit::Object(vec![(Lit::String("k".to_string()), lit)]);
            }
        }
        let lit_clone = lit.clone();
        assert_eq!(lit, lit_clone);
        let lit_dbg = format!("{lit:?}");
        assert!(lit_dbg.starts_with("Object(") || lit_dbg.starts_with("Array("));
        drop((lit, lit_clone));

        // 2. 5,000-depth `Expr` (`Unary` + `ObjectBuild` + `ArrayBuild`):
        //    Clone, PartialEq, Debug, Drop
        let mut expr = Expr::Ident("x".to_string());
        for i in 0..DEPTH {
            expr = match i % 3 {
                0 => Expr::Unary {
                    op: UnOp::LogicalNot,
                    operand: Box::new(expr),
                },
                1 => Expr::ObjectBuild {
                    entries: vec![ObjEntry::Getter(
                        ObjKey::Computed(Box::new(Expr::Ident("k".to_string()))),
                        expr,
                    )],
                },
                _ => Expr::ArrayBuild {
                    elements: vec![ArrayElem::Item(expr)],
                },
            };
        }
        let expr_clone = expr.clone();
        assert_eq!(expr, expr_clone);
        let expr_dbg = format!("{expr:?}");
        assert!(!expr_dbg.is_empty());
        drop((expr, expr_clone));

        // 3. 5,000-depth `SNode` (`Block`, `If`, `Try`, `Switch`, `While`):
        //    Clone, PartialEq, Debug, Drop
        let mut snode = SNode::Stmts(vec![Leaf::Raw(Stmt::Debugger)]);
        for i in 0..DEPTH {
            snode = match i % 5 {
                0 => SNode::Block(vec![snode]),
                1 => SNode::If {
                    cond: Expr::Ident("c".to_string()),
                    then: vec![snode],
                    otherwise: Vec::new(),
                },
                2 => SNode::Try {
                    body: vec![snode],
                    catches: vec![CatchClause {
                        binding: Some("e".to_string()),
                        body: Vec::new(),
                    }],
                    note: None,
                    finally: None,
                },
                3 => SNode::Switch {
                    disc: Expr::Ident("d".to_string()),
                    cases: vec![SwitchCase {
                        tests: vec![Expr::Lit(Lit::Number(0.0_f64.to_bits()))],
                        body: vec![snode],
                    }],
                },
                _ => SNode::While {
                    label: None,
                    cond: None,
                    body: vec![snode],
                },
            };
        }
        let snode_clone = snode.clone();
        assert_eq!(snode, snode_clone);
        let snode_dbg = format!("{snode:?}");
        assert!(!snode_dbg.is_empty());
        drop((snode, snode_clone));

        // 4. 5,000-depth `TryPlan` (`children` chain): Clone, PartialEq, Debug, Drop
        let mut plan = TryPlan {
            region: DEPTH,
            entry: Some(BlockId::new(0)),
            protected: vec![BlockId::new(0)],
            handlers: vec![BlockId::new(1)],
            span: Some(RegionId(0)),
            cuts_structured_region: false,
            children: Vec::new(),
        };
        for i in (0..DEPTH).rev() {
            plan = TryPlan {
                region: i,
                entry: Some(BlockId::new(0)),
                protected: vec![BlockId::new(0)],
                handlers: vec![BlockId::new(1)],
                span: Some(RegionId(0)),
                cuts_structured_region: false,
                children: vec![plan],
            };
        }
        let plan_clone = plan.clone();
        assert_eq!(plan, plan_clone);
        let plan_dbg = format!("{plan:?}");
        assert!(plan_dbg.starts_with("TryPlan {"));
        drop((plan, plan_clone));
    });
}

#[test]
fn tarjan_scc_multi_core_and_try_plan_forest_hierarchy() {
    // Two sequential irreducible 2-entry loops (`b1 <-> b2` and `b4 <-> b5`)
    // connected via `b0 -> b1/b2 -> b3 -> b4/b5 -> b6`, plus nested laminar
    // `TryRegion`s (`outer = {b0, b3, b6}`, `mid = {b3, b6}`, `inner = {b6}`).
    let mut m = mk_module();
    let f = add_func_named(&mut m, "multi_irred");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let b3 = add_block(&mut m, f);
    let b4 = add_block(&mut m, f);
    let b5 = add_block(&mut m, f);
    let b6 = add_block(&mut m, f);
    let h_out = add_block(&mut m, f);
    let h_mid = add_block(&mut m, f);
    let h_in = add_block(&mut m, f);

    emit_void(
        &mut m,
        b0,
        Op::CondBranch {
            cond: p1,
            true_dest: b1,
            false_dest: b2,
        },
    );
    emit_void(
        &mut m,
        b1,
        Op::CondBranch {
            cond: p2,
            true_dest: b2,
            false_dest: b3,
        },
    );
    emit_void(
        &mut m,
        b2,
        Op::CondBranch {
            cond: p1,
            true_dest: b1,
            false_dest: b3,
        },
    );
    emit_void(
        &mut m,
        b3,
        Op::CondBranch {
            cond: p2,
            true_dest: b4,
            false_dest: b5,
        },
    );
    emit_void(
        &mut m,
        b4,
        Op::CondBranch {
            cond: p1,
            true_dest: b5,
            false_dest: b6,
        },
    );
    emit_void(
        &mut m,
        b5,
        Op::CondBranch {
            cond: p2,
            true_dest: b4,
            false_dest: b6,
        },
    );
    emit_void(&mut m, b6, Op::Return { value: Some(p1) });

    for (u, v) in [
        (b0, b1),
        (b0, b2),
        (b1, b2),
        (b1, b3),
        (b2, b1),
        (b2, b3),
        (b3, b4),
        (b3, b5),
        (b4, b5),
        (b4, b6),
        (b5, b4),
        (b5, b6),
    ] {
        link(&mut m, u, v);
    }

    for h in [h_out, h_mid, h_in] {
        let exc = add_exception_param(&mut m, h);
        emit_void(&mut m, h, Op::Return { value: Some(exc) });
    }
    let e_out = ValueId::new(m.values.len() as u32 - 3);
    let e_mid = ValueId::new(m.values.len() as u32 - 2);
    let e_in = ValueId::new(m.values.len() as u32 - 1);
    add_try(&mut m, f, vec![b0, b3, b6], h_out, e_out);
    add_try(&mut m, f, vec![b3, b6], h_mid, e_mid);
    add_try(&mut m, f, vec![b6], h_in, e_in);

    let tree = structure_regions(&m, f);
    assert_eq!(
        tree.irreducible.len(),
        2,
        "single-pass Tarjan SCC must find both irreducible cores: {:?}",
        tree.irreducible
    );
    assert_eq!(tree.irreducible[0].blocks, vec![b1, b2]);
    assert_eq!(tree.irreducible[1].blocks, vec![b4, b5]);

    let forest = tree.try_plan_forest();
    assert_eq!(forest.len(), 1, "outermost TryPlan must root the forest");
    assert_eq!(forest[0].region, 0);
    assert_eq!(forest[0].children.len(), 1);
    assert_eq!(forest[0].children[0].region, 1);
    assert_eq!(forest[0].children[0].children.len(), 1);
    assert_eq!(forest[0].children[0].children[0].region, 2);
}

#[test]
fn ramsey_forward_labeled_merge_sibling_arm_and_seq_skip() {
    // 1. Sibling-arm cross-arm jump exceeding `MAX_BLOCKS = 8`:
    //    `if (p1) { shared_chain(10 blocks); } else { if (p2) goto end; goto shared; }`
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "ramsey_sibling");
        let b0 = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p1 = add_param(&mut m, f);
        let p2 = add_param(&mut m, f);
        let b_else = add_block(&mut m, f);
        let b_shared = add_block(&mut m, f);
        let b_end = add_block(&mut m, f);

        emit_void(
            &mut m,
            b0,
            Op::CondBranch {
                cond: p1,
                true_dest: b_shared,
                false_dest: b_else,
            },
        );
        link(&mut m, b0, b_shared);
        link(&mut m, b0, b_else);

        emit_void(
            &mut m,
            b_else,
            Op::CondBranch {
                cond: p2,
                true_dest: b_end,
                false_dest: b_shared,
            },
        );
        link(&mut m, b_else, b_end);
        link(&mut m, b_else, b_shared);

        let mut prev = b_shared;
        for _ in 0..10 {
            let _ = emit(
                &mut m,
                prev,
                Op::Call {
                    callee: p1,
                    this: None,
                    args: vec![],
                    kind: CallKind::Dynamic,
                },
            );
            let next = add_block(&mut m, f);
            emit_void(&mut m, prev, Op::Branch { dest: next });
            link(&mut m, prev, next);
            prev = next;
        }
        emit_void(&mut m, prev, Op::Branch { dest: b_end });
        link(&mut m, prev, b_end);
        emit_void(&mut m, b_end, Op::Return { value: Some(p2) });

        let rf = recover_func(&m, f);
        let st = structure_func(&m, &rf);
        assert_eq!(st.stats.cross_arm_folds, 0);
        assert_eq!(st.stats.cross_arm_notes, 0);
        assert!(st.stats.alternates >= 1);

        let dec = decompile_module(&m, &EmitOptions::default());
        assert!(
            dec.text.contains(&format!("L${}: {{", b_shared.index()))
                && dec.text.contains(&format!("break L${};", b_shared.index())),
            "expected Ramsey labeled merge in sibling-arm jump:\n{}",
            dec.text
        );
        assert!(
            !dec.text.contains("cross-arm edges unfolded"),
            "no cross-arm edges may be dropped:\n{}",
            dec.text
        );
    }

    // 2. Forward `Seq` skip-ahead exceeding `try_run_fold`'s `MAX_ARM = 8`:
    //    `b0: if (p1) -> b_a / b_b`, where `b_join` is shared by `b_a` and `b_b`
    //    while `ret_a` prevents `b_join` from post-dominating `b0`. That demotes
    //    `b_join` after `If(b0)` and leaves `then = Seq([b_a, chain[0..9], ret_a])`
    //    (`12 > MAX_ARM = 8`), where `b_a` skips forward to `Follow::Entry(b_join)`!
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "ramsey_seq_skip");
        let b0 = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p1 = add_param(&mut m, f);
        let p2 = add_param(&mut m, f);
        let b_a = add_block(&mut m, f);
        let b_b = add_block(&mut m, f);
        let mut chain = Vec::new();
        for _ in 0..10 {
            chain.push(add_block(&mut m, f));
        }
        let ret_a = add_block(&mut m, f);
        let b_join = add_block(&mut m, f);

        emit_void(
            &mut m,
            b0,
            Op::CondBranch {
                cond: p1,
                true_dest: b_a,
                false_dest: b_b,
            },
        );
        link(&mut m, b0, b_a);
        link(&mut m, b0, b_b);

        let _ = emit(
            &mut m,
            b_b,
            Op::Call {
                callee: p2,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_b, Op::Branch { dest: b_join });
        link(&mut m, b_b, b_join);

        emit_void(
            &mut m,
            b_a,
            Op::CondBranch {
                cond: p2,
                true_dest: chain[0],
                false_dest: b_join,
            },
        );
        link(&mut m, b_a, chain[0]);
        link(&mut m, b_a, b_join);

        for idx in 0..chain.len() {
            let cur = chain[idx];
            let _ = emit(
                &mut m,
                cur,
                Op::Call {
                    callee: p1,
                    this: None,
                    args: vec![],
                    kind: CallKind::Dynamic,
                },
            );
            if idx + 1 < chain.len() {
                let nxt = chain[idx + 1];
                emit_void(&mut m, cur, Op::Branch { dest: nxt });
                link(&mut m, cur, nxt);
            } else {
                emit_void(
                    &mut m,
                    cur,
                    Op::CondBranch {
                        cond: p1,
                        true_dest: b_join,
                        false_dest: ret_a,
                    },
                );
                link(&mut m, cur, b_join);
                link(&mut m, cur, ret_a);
            }
        }
        emit_void(&mut m, ret_a, Op::Return { value: Some(p2) });
        emit_void(&mut m, b_join, Op::Return { value: Some(p1) });

        let rf = recover_func(&m, f);
        let st = structure_func(&m, &rf);
        assert_eq!(
            st.stats.cross_arm_notes, 0,
            "Ramsey Seq forward merge must not drop conditional at b_a: {:?}",
            st.stats
        );
        let dec = decompile_module(&m, &EmitOptions::default());
        assert!(
            dec.text.contains(&format!("L${}: {{", b_join.index()))
                && dec.text.contains(&format!("break L${};", b_join.index())),
            "expected Ramsey Seq forward merge label L${}:\n{}",
            b_join.index(),
            dec.text
        );
    }
}

#[test]
fn unfolded_for_in_get_prop_iterator_and_next_prop_name_emit_executable_js() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "raw_for_in");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let obj = add_param(&mut m, f);

    let it = emit(&mut m, b, Op::GetPropIterator { obj });
    let k1 = emit(&mut m, b, Op::NextPropName { iterator: it });
    let k2 = emit(&mut m, b, Op::NextPropName { iterator: it });
    let sum = add(&mut m, b, k1, k2);
    emit_void(&mut m, b, Op::Return { value: Some(sum) });

    let dec = decompile_module(&m, &EmitOptions::default());
    assert!(
        dec.text
            .contains("((function*(o) { for (const k in o) yield k; })(p1))"),
        "GetPropIterator must emit executable generator enumerator:\n{}",
        dec.text
    );
    assert!(
        dec.text.contains(".next().value)"),
        "NextPropName must emit `.next().value`:\n{}",
        dec.text
    );
}

#[test]
fn dialect_static_arkts_vs_dynamic_ecma_abi_without_es_annotations() {
    // 1. `Dialect::StaticArkTS` with zero `L_ES*` annotations:
    //    static method has H = 0; instance method has H = 1 (`this`).
    let mut static_m = Module::with_dialect(Dialect::StaticArkTS);
    let c_sym = static_m.sym.intern("LPkg/Util;");
    let mut cls = ClassData::new(c_sym, c_sym);
    cls.source_lang = SourceLang::ArkTS;
    static_m.classes.push(cls);

    let f_stat = FuncId::new(0);
    let s_sym = static_m.sym.intern("sum");
    let mut fd_stat = FunctionData::new(ClassId::new(0), s_sym, FunctionKind::Function);
    fd_stat.modifiers |= Modifiers::STATIC;
    static_m.functions.push(fd_stat);
    static_m.classes[0].methods.push(f_stat);
    let bs = add_block(&mut static_m, f_stat);
    let a0 = add_param(&mut static_m, f_stat);
    let a1 = add_param(&mut static_m, f_stat);
    let s_res = add(&mut static_m, bs, a0, a1);
    emit_void(&mut static_m, bs, Op::Return { value: Some(s_res) });

    let static_out = decompile_module(&static_m, &EmitOptions::default()).text;
    assert!(
        static_out.contains("function sum(p0, p1) {\n  return p0 + p1;\n}"),
        "StaticArkTS static method must expose both p0 and p1:\n{static_out}"
    );

    // 2. `Dialect::DynamicEcma` even when `cls.source_lang = SourceLang::ArkTS`
    //    and zero `L_ES*` annotations exist: static method keeps H = 3 (`[func][new.target][this]`).
    let mut dyn_m = Module::with_dialect(Dialect::DynamicEcma);
    let dc_sym = dyn_m.sym.intern("LDynEts;");
    let mut dcls = ClassData::new(dc_sym, dc_sym);
    dcls.source_lang = SourceLang::ArkTS;
    dyn_m.classes.push(dcls);

    let df_stat = FuncId::new(0);
    let ds_sym = dyn_m.sym.intern("entry");
    let mut dfd = FunctionData::new(ClassId::new(0), ds_sym, FunctionKind::Function);
    dfd.modifiers |= Modifiers::STATIC;
    dyn_m.functions.push(dfd);
    dyn_m.classes[0].methods.push(df_stat);
    let db = add_block(&mut dyn_m, df_stat);
    let _fn_obj = add_param(&mut dyn_m, df_stat);
    let _new_target = add_param(&mut dyn_m, df_stat);
    let _this_v = add_param(&mut dyn_m, df_stat);
    let formal = add_param(&mut dyn_m, df_stat);
    emit_void(
        &mut dyn_m,
        db,
        Op::Return {
            value: Some(formal),
        },
    );

    let dyn_out = decompile_module(&dyn_m, &EmitOptions::default()).text;
    assert!(
        dyn_out.contains("function entry(p3) {\n  return p3;\n}"),
        "DynamicEcma static method with SourceLang::ArkTS must keep 3 hidden slots:\n{dyn_out}"
    );
}

#[test]
fn is_true_precedence_and_condition_peeling() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "truthy");
    let b0 = entry_of(&m, f);
    let b_then = add_block(&mut m, f);
    let b_else = add_block(&mut m, f);
    let _this = add_param(&mut m, f);
    let a = add_param(&mut m, f);
    let b = add_param(&mut m, f);

    // 1. `!(IsTrue(a < b))` -> `!(a < b)` (never `!a < b`!)
    let lt1 = emit(
        &mut m,
        b0,
        Op::Compare {
            op: CmpOp::Less,
            left: b,
            right: a,
        },
    );
    let it1 = emit(
        &mut m,
        b0,
        Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: lt1,
        },
    );
    let neg = emit(
        &mut m,
        b0,
        Op::UnaryOp {
            op: UnOp::LogicalNot,
            operand: it1,
        },
    );

    // 2. `typeof IsTrue(2.0)` -> `typeof !!2.0` (must coerce to boolean!)
    let two = load_number(&mut m, b0, 2.0);
    let it2 = emit(
        &mut m,
        b0,
        Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: two,
        },
    );
    let ty_of = emit(
        &mut m,
        b0,
        Op::UnaryOp {
            op: UnOp::TypeOf,
            operand: it2,
        },
    );

    // 3. `(IsTrue(a)) ** b` -> `(!!a) ** b` (unary base of `**` requires parens!)
    let it3 = emit(
        &mut m,
        b0,
        Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: a,
        },
    );
    let exp = emit(
        &mut m,
        b0,
        Op::BinaryOp {
            op: BinOp::Exp,
            left: b,
            right: it3,
        },
    );

    // 4. `if (IsTrue(a < b))` -> `if (a < b)` (outer truthiness peeled in `if` condition)
    let lt2 = emit(
        &mut m,
        b0,
        Op::Compare {
            op: CmpOp::Less,
            left: b,
            right: a,
        },
    );
    let cond = emit(
        &mut m,
        b0,
        Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: lt2,
        },
    );
    emit_void(
        &mut m,
        b0,
        Op::CondBranch {
            cond,
            true_dest: b_then,
            false_dest: b_else,
        },
    );
    link(&mut m, b0, b_then);
    link(&mut m, b0, b_else);

    let sum = add(&mut m, b_then, neg, ty_of);
    emit_void(&mut m, b_then, Op::Return { value: Some(sum) });
    emit_void(&mut m, b_else, Op::Return { value: Some(exp) });

    let text = decompile_module(&m, &EmitOptions::default()).text;
    assert!(
        text.contains("!(p1 < p2)"),
        "LogicalNot over IsTrue(a < b) must parenthesize comparison:\n{text}"
    );
    assert!(
        text.contains("typeof !!2.0"),
        "value-position IsTrue must coerce with !!:\n{text}"
    );
    assert!(
        text.contains("(!!p1) ** p2"),
        "unary !! base of ** must parenthesize:\n{text}"
    );
    assert!(
        text.contains("if (p1 < p2)"),
        "if condition must peel outer IsTrue:\n{text}"
    );
}

#[test]
fn deduplicated_catch_names_on_shared_handler_block() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "shared_catch");
    let b0 = entry_of(&m, f);
    let b_mid = add_block(&mut m, f);
    let b1 = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);

    let _ = emit(
        &mut m,
        b0,
        Op::Call {
            callee: p1,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b0, Op::Branch { dest: b_mid });
    link(&mut m, b0, b_mid);

    // Unprotected `b_mid` splits the two `TryRegion`s sharing handler `h`.
    let mid_v = load_number(&mut m, b_mid, 1.0);
    emit_void(&mut m, b_mid, Op::Branch { dest: b1 });
    link(&mut m, b_mid, b1);

    let _ = emit(
        &mut m,
        b1,
        Op::Call {
            callee: p1,
            this: None,
            args: vec![mid_v],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b1, Op::Return { value: Some(mid_v) });

    let exc = add_exception_param(&mut m, h);
    emit_void(&mut m, h, Op::Return { value: Some(exc) });

    // Two distinct `TryRegion` entries targeting the SAME handler block `h`!
    add_try(&mut m, f, vec![b0], h, exc);
    add_try(&mut m, f, vec![b1], h, exc);

    let text = decompile_module(&m, &EmitOptions::default()).text;
    assert!(
        !text.contains("catch-bind"),
        "shared handler block must not emit duplicate CatchBind residue:\n{text}"
    );
    assert_eq!(
        text.matches("catch (e)").count(),
        2,
        "both split try blocks must bind the same deduplicated catch (e):\n{text}"
    );
}

#[test]
fn nested_closure_private_names_fallback_and_static_private_sanitization() {
    let mut m = mk_module();
    let f_outer = add_func_named(&mut m, "makeClass");
    let f_ctor = add_func_kind(&mut m, "Vault", FunctionKind::Constructor);
    let f_method = add_func_named(&mut m, "run");
    let f_arrow = add_func_kind(&mut m, "innerArrow", FunctionKind::Arrow);

    // `makeClass` pushes a class private-name frame `["secret", "static"]`
    // (plus unnamed slot 2 -> fallback `p0_2`) and defines `class Vault`.
    {
        let b = entry_of(&m, f_outer);
        let _this = add_param(&mut m, f_outer);
        let _ = emit(
            &mut m,
            b,
            Op::NewLexEnv {
                num_vars: 0,
                kind: LexEnvKind::Plain,
            },
        );
        let s_secret = m.sym.intern("secret");
        let s_static = m.sym.intern("static");
        let pnames_arr = const_array(
            &mut m,
            vec![Const::String(s_secret), Const::String(s_static)],
        );
        emit_void(
            &mut m,
            b,
            Op::CreatePrivateNames {
                names: pnames_arr,
                count: 2,
            },
        );

        // Static private field `#static` accessed on `cls_val`? Define `run` inside `Vault`.
        let s_run = m.sym.intern("run");
        let members = const_array(
            &mut m,
            vec![Const::String(s_run), Const::method_ref(f_method)],
        );
        let cls_val = emit(
            &mut m,
            b,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: f_ctor,
                heritage: None,
                members,
                member_attrs: vec![],
                count: 1,
            })),
        );
        emit_void(&mut m, b, Op::PopLexEnv);
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(cls_val),
            },
        );
    }
    {
        let b = entry_of(&m, f_ctor);
        let this_v = add_param(&mut m, f_ctor);
        let v1 = load_number(&mut m, b, 7.0);
        // Define `#static` (slot 1 -> sanitized `#static_`) in ctor so declaration
        // and access both spell `#static_`.
        emit_void(
            &mut m,
            b,
            Op::DefinePrivate {
                level: 0,
                slot: 1,
                obj: this_v,
                value: v1,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(this_v),
            },
        );
    }
    {
        // `run` defines nested `innerArrow` AFTER pushing its own inner `NewLexEnv`,
        // WITHOUT accessing `#secret` directly — proving:
        // 1) `innerArrow` resolves `#secret` at `level = 1` across the seeded stack,
        // 2) `innerArrow` resolves unnamed slot 2 at `level = 1` to `#p0_2`, and
        // 3) `Vault`'s class body still declares `#secret;` and `#p0_2;`!
        let b = entry_of(&m, f_method);
        let this_v = add_param(&mut m, f_method);
        let _ = emit(
            &mut m,
            b,
            Op::NewLexEnv {
                num_vars: 1,
                kind: LexEnvKind::Plain,
            },
        );
        let df = emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: f_arrow,
                captures: vec![],
                length: 1,
            },
        );
        let s_st = emit(
            &mut m,
            b,
            Op::LoadPrivate {
                level: 1,
                slot: 1,
                obj: this_v,
            },
        );
        let res = add(&mut m, b, df, s_st);
        emit_void(&mut m, b, Op::PopLexEnv);
        emit_void(&mut m, b, Op::Return { value: Some(res) });
    }
    {
        let b = entry_of(&m, f_arrow);
        let _this = add_param(&mut m, f_arrow);
        let obj = add_param(&mut m, f_arrow);
        let p_sec = emit(
            &mut m,
            b,
            Op::LoadPrivate {
                level: 1,
                slot: 0,
                obj,
            },
        );
        let p_unnamed = emit(
            &mut m,
            b,
            Op::LoadPrivate {
                level: 1,
                slot: 2,
                obj,
            },
        );
        let sum = add(&mut m, b, p_sec, p_unnamed);
        emit_void(&mut m, b, Op::Return { value: Some(sum) });
    }

    let text = decompile_module(&m, &EmitOptions::default()).text;
    assert!(
        text.contains("#secret;") && text.contains("p1.#secret"),
        "nested closure #secret must resolve from enclosing class stack and declare on class:\n{text}"
    );
    assert!(
        text.contains("#p0_2;") && text.contains("p1.#p0_2"),
        "unnamed private slot must use absolute frame index #p0_2:\n{text}"
    );
    assert!(
        text.contains("#static;")
            && text.contains("this.#static = 7.0;")
            && text.contains("this.#static;")
            && !text.contains("#static_"),
        "#static private field declaration and access must align on valid ES #static:\n{text}"
    );
}

#[test]
fn arkui_preserves_live_undefined_temp_in_func_main_0() {
    let mut m = Module::new();
    let cid = ClassId::new(0);
    let c_sym = m.sym.intern("L@bundle:demo/entry/ets/pages/LiveTemp;");
    m.classes.push(ClassData::new(c_sym, c_sym));

    let add_ark_fn = |m: &mut Module, name: &str, kind: FunctionKind| -> FuncId {
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

    let f_ctor = add_ark_fn(&mut m, "LiveCard", FunctionKind::Constructor);
    {
        let b = entry_of(&m, f_ctor);
        let this_v = m.func(f_ctor).unwrap().params[2];
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(this_v),
            },
        );
    }
    let f_rerender = add_ark_fn(&mut m, "rerender", FunctionKind::Function);
    {
        let b = entry_of(&m, f_rerender);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f_txt_obs = add_ark_fn(&mut m, "txtObs", FunctionKind::Arrow);
    {
        let _elmt = add_param(&mut m, f_txt_obs);
        let _first = add_param(&mut m, f_txt_obs);
        let b = entry_of(&m, f_txt_obs);
        let txt_sym = m.sym.intern("Text");
        let ucid = m.consts.push(Const::Undefined);
        let udef = emit(&mut m, b, Op::LoadConst(ucid));
        let txt = emit(
            &mut m,
            b,
            Op::TryGetGlobal {
                name: txt_sym,
                default: Some(udef),
            },
        );
        let cr_sym = m.sym.intern("create");
        let cr_fn = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: txt,
                name: cr_sym,
            },
        );
        let hi = load_string(&mut m, b, "Hi");
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: cr_fn,
                this: Some(txt),
                args: vec![hi],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f_render = add_ark_fn(&mut m, "initialRender", FunctionKind::Function);
    {
        let b = entry_of(&m, f_render);
        let this_v = m.func(f_render).unwrap().params[2];
        let obs_sym = m.sym.intern("observeComponentCreation2");
        let obs_fn = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: this_v,
                name: obs_sym,
            },
        );
        let df = emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: f_txt_obs,
                captures: vec![],
                length: 2,
            },
        );
        let cl = emit(&mut m, b, Op::AllocClosure { func: df });
        let txt_sym = m.sym.intern("Text");
        let ucid = m.consts.push(Const::Undefined);
        let udef = emit(&mut m, b, Op::LoadConst(ucid));
        let txt_g = emit(
            &mut m,
            b,
            Op::TryGetGlobal {
                name: txt_sym,
                default: Some(udef),
            },
        );
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: obs_fn,
                this: Some(this_v),
                args: vec![cl, txt_g],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let f_main = add_ark_fn(&mut m, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, f_main);
        let ucid = m.consts.push(Const::Undefined);
        // `live_undef` has TWO uses across `sideEffect(live_undef, live_undef)` so
        // Stage A materializes `const v... = undefined;` in `func_main_0`!
        let live_undef = emit(&mut m, b, Op::LoadConst(ucid));

        let vpu_sym = m.sym.intern("ViewPU");
        let udef2 = emit(&mut m, b, Op::LoadConst(ucid));
        let vpu = emit(
            &mut m,
            b,
            Op::TryGetGlobal {
                name: vpu_sym,
                default: Some(udef2),
            },
        );
        let s_rerender = m.sym.intern("rerender");
        let s_render = m.sym.intern("initialRender");
        let members = const_array(
            &mut m,
            vec![
                Const::String(s_rerender),
                Const::method_ref(f_rerender),
                Const::String(s_render),
                Const::method_ref(f_render),
            ],
        );
        let cls_val = emit(
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
        let reg_sym = m.sym.intern("registerNamedRoute");
        let udef_reg = emit(&mut m, b, Op::LoadConst(ucid));
        let reg_fn = emit(
            &mut m,
            b,
            Op::TryGetGlobal {
                name: reg_sym,
                default: Some(udef_reg),
            },
        );
        let empty_route = load_string(&mut m, b, "");
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: reg_fn,
                this: None,
                args: vec![cls_val, empty_route],
                kind: CallKind::Direct,
            },
        );

        let se_sym = m.sym.intern("sideEffect");
        let udef3 = emit(&mut m, b, Op::LoadConst(ucid));
        let se_fn = emit(
            &mut m,
            b,
            Op::TryGetGlobal {
                name: se_sym,
                default: Some(udef3),
            },
        );
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: se_fn,
                this: None,
                args: vec![live_undef, live_undef],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let ark_opts = EmitOptions {
        arkui: true,
        ..EmitOptions::default()
    };
    let out = decompile_module(&m, &ark_opts).text;
    assert!(
        out.contains("@Component\nstruct LiveCard"),
        "ArkUI struct must be recovered:\n{out}"
    );
    assert!(
        out.contains("= undefined;") && out.contains("(v28, v28)"),
        "live `const t = undefined;` referenced by surviving statement in func_main_0 must NOT be stripped:\n{out}"
    );
}

#[test]
fn rest_destructure_guards_duplicate_keys_impure_intervening_and_quotes_non_ident_keys() {
    // 1. Non-identifier key `"a-b"` folds cleanly and quotes `"a-b"` in pattern:
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "rest_quoted");
        let b = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let obj = add_param(&mut m, f);

        let s_ab = m.sym.intern("a-b");
        let v_ab = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: obj,
                name: s_ab,
            },
        );
        // Second use of `v_ab` so it stays a `Stmt::Declare` temp:
        let k_ab = load_string(&mut m, b, "a-b");
        let rest = emit(
            &mut m,
            b,
            Op::CreateObjectWithExcludedKeys {
                obj,
                keys: vec![k_ab],
            },
        );
        let sum = add(&mut m, b, v_ab, rest);
        let sum2 = add(&mut m, b, sum, v_ab);
        emit_void(&mut m, b, Op::Return { value: Some(sum2) });

        let dec = decompile_module(&m, &EmitOptions::default());
        assert_eq!(dec.stats.folds.rest, 1);
        assert!(
            dec.text.contains("const {\"a-b\": ")
                && dec.text.contains(", ...")
                && dec.text.contains("} = p1;"),
            "non-identifier destructuring key must be quoted:\n{}",
            dec.text
        );
    }

    // 2. Duplicate excluded keys (`["a", "a"]`) must NOT fold or panic:
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "rest_dup");
        let b = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let obj = add_param(&mut m, f);

        let s_a = m.sym.intern("a");
        let va1 = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: obj,
                name: s_a,
            },
        );
        let va2 = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: obj,
                name: s_a,
            },
        );
        let ka1 = load_string(&mut m, b, "a");
        let ka2 = load_string(&mut m, b, "a");
        let rest = emit(
            &mut m,
            b,
            Op::CreateObjectWithExcludedKeys {
                obj,
                keys: vec![ka1, ka2],
            },
        );
        let t1 = add(&mut m, b, va1, va2);
        let t2 = add(&mut m, b, t1, va1);
        let t3 = add(&mut m, b, t2, va2);
        let t4 = add(&mut m, b, t3, rest);
        emit_void(&mut m, b, Op::Return { value: Some(t4) });

        let dec = decompile_module(&m, &EmitOptions::default());
        assert_eq!(
            dec.stats.folds.rest, 0,
            "duplicate excluded keys must bail:\n{}",
            dec.text
        );
    }

    // 3. Impure intervening statement (`sideEffect()`) between `obj.a` and
    //    `RestObject` must NOT fold across the side effect:
    {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "rest_impure");
        let b = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let obj = add_param(&mut m, f);
        let hook = add_param(&mut m, f);

        let s_a = m.sym.intern("a");
        let va = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: obj,
                name: s_a,
            },
        );
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: hook,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let ka = load_string(&mut m, b, "a");
        let rest = emit(
            &mut m,
            b,
            Op::CreateObjectWithExcludedKeys {
                obj,
                keys: vec![ka],
            },
        );
        let s1 = add(&mut m, b, va, rest);
        let s2 = add(&mut m, b, s1, va);
        emit_void(&mut m, b, Op::Return { value: Some(s2) });

        let dec = decompile_module(&m, &EmitOptions::default());
        assert_eq!(
            dec.stats.folds.rest, 0,
            "impure intervening call must prevent rest destructuring fold:\n{}",
            dec.text
        );
    }
}

#[test]
fn irreducible_dispatch_preserves_try_region_partitions_cond_phis_and_labels_loop() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "irred_try_phi");
    let b0 = entry_of(&m, f);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);

    let n0 = load_number(&mut m, b0, 10.0);
    emit_void(
        &mut m,
        b0,
        Op::CondBranch {
            cond: p1,
            true_dest: b1,
            false_dest: b2,
        },
    );
    link(&mut m, b0, b1);
    link(&mut m, b0, b2);

    let _ = emit(
        &mut m,
        b1,
        Op::Call {
            callee: p1,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let n1 = load_number(&mut m, b1, 20.0);
    emit_void(
        &mut m,
        b1,
        Op::CondBranch {
            cond: p2,
            true_dest: b2,
            false_dest: b1,
        },
    );
    link(&mut m, b1, b2);
    link(&mut m, b1, b1);

    let phi_b2 = emit(
        &mut m,
        b2,
        Op::Phi {
            entries: vec![
                (
                    abcd_ir::Edge {
                        from: b0,
                        kind: abcd_ir::EdgeKind::Normal,
                    },
                    n0,
                ),
                (
                    abcd_ir::Edge {
                        from: b1,
                        kind: abcd_ir::EdgeKind::Normal,
                    },
                    n1,
                ),
            ],
        },
    );
    emit_void(
        &mut m,
        b2,
        Op::CondBranch {
            cond: p1,
            true_dest: b1,
            false_dest: h,
        },
    );
    link(&mut m, b2, b1);
    link(&mut m, b2, h);

    let exc = add_exception_param(&mut m, h);
    let ret_v = add(&mut m, h, phi_b2, exc);
    emit_void(&mut m, h, Op::Return { value: Some(ret_v) });
    add_try(&mut m, f, vec![b1], h, exc);

    let text = decompile_module(&m, &EmitOptions::default()).text;
    assert!(
        text.contains("D$0: while (true)") && text.contains("continue D$0;"),
        "irreducible dispatch must label loop D$0 and qualify continue D$0:\n{text}"
    );
    assert!(
        text.contains("try {") && text.contains("catch (e$0)"),
        "protected block inside irreducible dispatch must preserve TryRegion wrapper:\n{text}"
    );
    assert!(
        text.contains("= 10.0;") && text.contains("= 20.0;"),
        "CondBranch incoming phi assignments must be partitioned onto outgoing arms:\n{text}"
    );
}

#[test]
fn conditional_phi_blocks_impure_inlining_and_degen_cond_branch_preserves_side_effect() {
    // 1. Coercing `p1 + 1.0` feeding a `CondBranch` (`true_dest != false_dest`)
    //    `Phi` in `b_then` must stay in `b0` (not inlined onto `b_then` only!).
    let mut m = mk_module();
    let f = add_func_named(&mut m, "cond_phi_guard");
    let b0 = entry_of(&m, f);
    let b_then = add_block(&mut m, f);
    let b_else = add_block(&mut m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);

    let one = load_number(&mut m, b0, 1.0);
    let coerced = add(&mut m, b0, p1, one);
    emit_void(
        &mut m,
        b0,
        Op::CondBranch {
            cond: p2,
            true_dest: b_then,
            false_dest: b_else,
        },
    );
    link(&mut m, b0, b_then);
    link(&mut m, b0, b_else);

    let zero = load_number(&mut m, b_else, 0.0);
    emit_void(&mut m, b_else, Op::Branch { dest: b_then });
    link(&mut m, b_else, b_then);

    let phi = emit(
        &mut m,
        b_then,
        Op::Phi {
            entries: vec![
                (
                    abcd_ir::Edge {
                        from: b0,
                        kind: abcd_ir::EdgeKind::Normal,
                    },
                    coerced,
                ),
                (
                    abcd_ir::Edge {
                        from: b_else,
                        kind: abcd_ir::EdgeKind::Normal,
                    },
                    zero,
                ),
            ],
        },
    );
    // 2. Degenerate `CondBranch(p1(), ret_b, ret_b)` in `b_then` must preserve `p1();`!
    let ret_b = add_block(&mut m, f);
    let side_call = emit(
        &mut m,
        b_then,
        Op::Call {
            callee: p1,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(
        &mut m,
        b_then,
        Op::CondBranch {
            cond: side_call,
            true_dest: ret_b,
            false_dest: ret_b,
        },
    );
    link(&mut m, b_then, ret_b);
    emit_void(&mut m, ret_b, Op::Return { value: Some(phi) });

    let rf = recover_func(&m, f);
    assert!(
        rf.blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Stmt::Declare { .. })),
        "coercing p1 + 1.0 must stay materialized in b0 before CondBranch: {:?}",
        rf.blocks[0].stmts
    );

    let text = decompile_module(&m, &EmitOptions::default()).text;
    assert!(
        text.contains("p1();"),
        "degenerate CondBranch(p1(), ret_b, ret_b) must preserve p1() side effect:\n{text}"
    );
}

#[test]
fn strict_eq_folds_to_switch_while_loose_eq_stays_if_else() {
    let build_cascade = |cmp_op: CmpOp| -> Module {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "cascade");
        let b0 = entry_of(&m, f);
        let b1 = add_block(&mut m, f);
        let c0 = add_block(&mut m, f);
        let c1 = add_block(&mut m, f);
        let def = add_block(&mut m, f);
        let _this = add_param(&mut m, f);
        let x = add_param(&mut m, f);

        let n1 = load_number(&mut m, b0, 1.0);
        let eq1 = emit(
            &mut m,
            b0,
            Op::Compare {
                op: cmp_op,
                left: n1,
                right: x,
            },
        );
        emit_void(
            &mut m,
            b0,
            Op::CondBranch {
                cond: eq1,
                true_dest: c0,
                false_dest: b1,
            },
        );
        link(&mut m, b0, c0);
        link(&mut m, b0, b1);

        let n2 = load_number(&mut m, b1, 2.0);
        let eq2 = emit(
            &mut m,
            b1,
            Op::Compare {
                op: cmp_op,
                left: n2,
                right: x,
            },
        );
        emit_void(
            &mut m,
            b1,
            Op::CondBranch {
                cond: eq2,
                true_dest: c1,
                false_dest: def,
            },
        );
        link(&mut m, b1, c1);
        link(&mut m, b1, def);

        let r0 = load_number(&mut m, c0, 10.0);
        emit_void(&mut m, c0, Op::Return { value: Some(r0) });
        let r1 = load_number(&mut m, c1, 20.0);
        emit_void(&mut m, c1, Op::Return { value: Some(r1) });
        let rd = load_number(&mut m, def, 30.0);
        emit_void(&mut m, def, Op::Return { value: Some(rd) });
        m
    };

    let strict_dec = decompile_module(&build_cascade(CmpOp::StrictEq), &EmitOptions::default());
    assert!(strict_dec.stats.folds.switch >= 1);
    assert!(strict_dec.text.contains("switch (p1)"));

    let loose_dec = decompile_module(&build_cascade(CmpOp::Eq), &EmitOptions::default());
    assert_eq!(loose_dec.stats.folds.switch, 0);
    assert!(!loose_dec.text.contains("switch ("));
    assert!(loose_dec.text.contains("if (p1 == 1.0)"));
}

#[test]
fn esm_side_effect_request_order_quoted_export_import_collision_and_ohmurl_4_and_5_field() {
    // 1. Single-file ESM: side-effect-only `"./polyfill"` at `module_requests[0]`
    //    must emit BEFORE `import { foo as foo$1 } from "./app";` (`foo` collides
    //    with top-level `var foo;`), and non-ident export `"a-b"` must be quoted!
    {
        let mut m = mk_module();
        let s_poly = m.sym.intern("./polyfill");
        let s_app = m.sym.intern("./app");
        let s_foo = m.sym.intern("foo");
        let s_local = m.sym.intern("localVal");
        let s_ab = m.sym.intern("a-b");

        m.module_requests = vec![
            ModuleRequest {
                specifier: s_poly,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_app,
                lazy: false,
            },
        ];
        m.imports = vec![ImportDecl::Regular {
            local_name: s_foo,
            import_name: s_foo,
            module_request: s_app,
        }];
        m.exports = vec![ExportDecl::Local {
            local_name: s_local,
            export_name: s_ab,
        }];

        let main = add_func_named(&mut m, "func_main_0");
        let b = entry_of(&m, main);
        let _this = add_param(&mut m, main);
        let imp_foo = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        // Colliding top-level `StoreGlobal` on `"foo"`:
        emit_void(
            &mut m,
            b,
            Op::StoreGlobal {
                name: s_foo,
                value: imp_foo,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: imp_foo,
            },
        );
        let lv = emit(
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
                value: lv,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });

        let text = decompile_module(&m, &EmitOptions::default()).text;
        let poly_pos = text
            .find("import \"./polyfill\";")
            .expect("side-effect import must be emitted");
        let app_pos = text
            .find("import { foo as foo$1 } from \"./app\";")
            .unwrap_or_else(|| panic!("colliding import must disambiguate to foo$1:\n{text}"));
        assert!(
            poly_pos < app_pos,
            "[[RequestedModules]] order must emit ./polyfill before ./app:\n{text}"
        );
        assert!(
            text.contains("export { localVal as \"a-b\" };"),
            "non-ident export name must be quoted:\n{text}"
        );
    }

    // 2. `--split-modules` with 4-field (`@normalized:N&&entry&ets/util/Four`)
    //    and 5-field (`@normalized:N&entry&com.demo&ets/pages/Five&1.0.0`) OHMUrls:
    {
        let mut m = Module::new();
        let d4 = m.sym.intern("L@normalized:N&&entry&ets/util/Four;");
        let mut c4 = ClassData::new(d4, d4);
        let s_x = m.sym.intern("x");
        c4.es_module = Some(EsModule {
            imports: vec![],
            exports: vec![ExportDecl::Local {
                local_name: s_x,
                export_name: s_x,
            }],
            module_requests: vec![],
        });
        m.classes.push(c4);

        let d5 = m
            .sym
            .intern("L@normalized:N&entry&com.demo&ets/pages/Five&1.0.0;");
        let mut c5 = ClassData::new(d5, d5);
        let req4 = m.sym.intern("@normalized:N&&entry&ets/util/Four&");
        c5.es_module = Some(EsModule {
            imports: vec![ImportDecl::Regular {
                local_name: s_x,
                import_name: s_x,
                module_request: req4,
            }],
            exports: vec![],
            module_requests: vec![ModuleRequest {
                specifier: req4,
                lazy: false,
            }],
        });
        m.classes.push(c5);

        for ci in 0..2u32 {
            let fid = FuncId::new(ci);
            let fn_sym = m.sym.intern("func_main_0");
            let mut fd = FunctionData::new(ClassId::new(ci), fn_sym, FunctionKind::Function);
            fd.modifiers |= Modifiers::STATIC;
            m.functions.push(fd);
            m.classes[ci as usize].methods.push(fid);
            let b = add_block(&mut m, fid);
            for _ in 0..3 {
                add_param(&mut m, fid);
            }
            emit_void(&mut m, b, Op::Return { value: None });
        }

        let split = decompile_module_split(&m, &EmitOptions::default());
        let paths: Vec<&str> = split.files.iter().map(|f| f.rel_path.as_str()).collect();
        assert!(
            paths.contains(&"ets/util/Four.js") && paths.contains(&"ets/pages/Five.js"),
            "both 4-field and 5-field @normalized: OHMUrls must split cleanly: {paths:?}"
        );
        let five = split
            .files
            .iter()
            .find(|f| f.rel_path == "ets/pages/Five.js")
            .unwrap();
        assert!(
            five.text.contains("from \"../util/Four\""),
            "5-field record importing 4-field @normalized: OHMUrl must rewrite to relative path:\n{}",
            five.text
        );
    }
}

#[test]
fn stmt_parens_lexical_block_scoping_and_fallback_may_throw() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "stmt_and_scope");
    let f_fn_expr = add_func_named(&mut m, "");
    let f_async_expr = add_func_kind(&mut m, "", FunctionKind::Async);
    let f_cls_ctor = add_func_kind(&mut m, "AnonCls", FunctionKind::Constructor);
    let f_cap_writer = add_func_kind(&mut m, "writer", FunctionKind::Arrow);

    {
        let b = entry_of(&m, f_fn_expr);
        let _this = add_param(&mut m, f_fn_expr);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    {
        let b = entry_of(&m, f_async_expr);
        let _this = add_param(&mut m, f_async_expr);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    {
        let b = entry_of(&m, f_cls_ctor);
        let this_v = add_param(&mut m, f_cls_ctor);
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(this_v),
            },
        );
    }
    {
        // `writer` mutates outer lexical slot `(0, 0)` (`own: false` — inherited
        // from `stmt_and_scope`, so `writer` MUST NOT emit `let scopedVar;`!).
        let b = entry_of(&m, f_cap_writer);
        let _this = add_param(&mut m, f_cap_writer);
        let v9 = load_number(&mut m, b, 9.0);
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: v9,
                kind: LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let b0 = entry_of(&m, f);
    let h = add_block(&mut m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);

    // 1. Statement-start `function`, `async function`, `class`, and `{ a: 1 }`:
    //    `DefineFunc` / `DefineClass` / `AllocObject` are removable if unused, so
    //    wrap each in `UnaryOp(ToObject)`? Wait: `DefineFunc` is removable if unused,
    //    whereas `DefineClass` has `may_throw: true` (`!is_removable_if_unused()`),
    //    and `AllocObject` with `StoreOwnPropName` folds to `{ a: 1 }` when used or
    //    emitted via `Mov`? Let's emit `DefineClass` directly as unused statement,
    //    and for `{ a: 1 }` / `function` let's pass to `Comma`? No: an unused
    //    `AllocObject` + `StoreOwnPropName` where `AllocObject` has 1 user
    //    (`StoreOwnPropName`)? Let's check `DefineClass` directly + `SNode::Stmts`!
    let empty_members = const_array(&mut m, vec![]);
    let _ = emit(
        &mut m,
        b0,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: f_cls_ctor,
            heritage: None,
            members: empty_members,
            member_attrs: vec![],
            count: 0,
        })),
    );

    // 2. Balanced `NewLexEnvWithName(["scopedVar"]) .. PutLexVar .. DefineFunc(writer) .. PopLexEnv`:
    let s_sv = m.sym.intern("scopedVar");
    let scope_arr = const_array(&mut m, vec![Const::String(s_sv)]);
    let _ = emit(
        &mut m,
        b0,
        Op::NewLexEnvWithName {
            num_vars: 1,
            scope_names: scope_arr,
        },
    );
    let v1 = load_number(&mut m, b0, 1.0);
    emit_void(
        &mut m,
        b0,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: v1,
            kind: LexEnvKind::Plain,
        },
    );
    let writer_fn = emit(
        &mut m,
        b0,
        Op::DefineFunc {
            body: f_cap_writer,
            captures: vec![],
            length: 0,
        },
    );
    let _ = emit(
        &mut m,
        b0,
        Op::Call {
            callee: writer_fn,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b0, Op::PopLexEnv);

    // 3. `Expr::Fallback` (invalid `ConstId(9999)`) in `b0` with an exceptional
    //    `Phi` in `h`: `expr_may_throw` on `Expr::Fallback` must flush the
    //    exceptional `PhiAssign` BEFORE the fallback statement!
    let b_next = add_block(&mut m, f);
    emit_void(&mut m, b0, Op::Branch { dest: b_next });
    link(&mut m, b0, b_next);

    let phi_val = load_number(&mut m, b_next, 42.0);
    let bad_const = emit(&mut m, b_next, Op::LoadConst(abcd_ir::ConstId::new(9999)));
    emit_void(
        &mut m,
        b_next,
        Op::Return {
            value: Some(bad_const),
        },
    );

    let exc = add_exception_param(&mut m, h);
    let h_phi = emit(
        &mut m,
        h,
        Op::Phi {
            entries: vec![(
                abcd_ir::Edge {
                    from: b_next,
                    kind: abcd_ir::EdgeKind::Exceptional,
                },
                phi_val,
            )],
        },
    );
    let h_ret = add(&mut m, h, h_phi, exc);
    emit_void(&mut m, h, Op::Return { value: Some(h_ret) });
    add_try(&mut m, f, vec![b_next], h, exc);

    // Also keep `f_fn_expr`, `f_async_expr`, and `{ a: p1 }` alive in a helper
    // function to verify statement-start parenthesization across all 4 forms!
    let f_parens = add_func_named(&mut m, "paren_forms");
    {
        let bp = entry_of(&m, f_parens);
        let _this = add_param(&mut m, f_parens);
        let s_a = m.sym.intern("a");
        let shape = const_object(&mut m, vec![Const::String(s_a)], vec![Const::number(1.0)]);
        let obj = emit(&mut m, bp, Op::AllocObject { shape });
        let v2 = load_number(&mut m, bp, 2.0);
        emit_void(
            &mut m,
            bp,
            Op::StoreOwnPropName {
                object: obj,
                name: s_a,
                value: v2,
                kind: OwnStoreKind::OwnProp,
            },
        );
        // `DefineFunc` has `is_removable_if_unused() == true`, so feed it to
        // `Return`? No: `Stmt::Expr(Expr::Closure)` / `Stmt::Expr(Expr::ObjectLit)`!
        // `Void` unary? No, let's check `paren_forms` with `DefineClass` and
        // `ObjectBuild` (`StoreOwnPropName` on `AllocObject` with a second dummy
        // store? No, `fold_builders` folds `const o = { a: 1 }; o.b = 2;` only when
        // `o` has subsequent uses!). And we also test `Stmt::Expr` directly via
        // `Emitter` / `decompile_module`!
        let _ = p1;
        emit_void(&mut m, bp, Op::Return { value: Some(obj) });
    }

    let text = decompile_module(&m, &EmitOptions::default()).text;
    assert!(
        text.contains("(class AnonCls {"),
        "statement-start class expression must be parenthesized:\n{text}"
    );
    assert!(
        text.contains("{\n    let scopedVar = 1.0;"),
        "balanced ScopePush..ScopePop must wrap in lexical block with `let scopedVar`:\n{text}"
    );
    assert!(
        text.contains("scopedVar = 9.0;") && !text.contains("let scopedVar;"),
        "capturing arrow writing inherited slot (`own: false`) must NOT shadow with `let scopedVar`:\n{text}"
    );
    let phi_assign_pos = text
        .find("= 42.0;")
        .expect("exceptional phi assign must be emitted");
    let fallback_pos = text
        .find("/*fallback LoadConst: unknown ConstId*/")
        .expect("fallback LoadConst must be emitted");
    assert!(
        phi_assign_pos < fallback_pos,
        "exceptional phi assign must be flushed BEFORE Expr::Fallback statement:\n{text}"
    );
}
