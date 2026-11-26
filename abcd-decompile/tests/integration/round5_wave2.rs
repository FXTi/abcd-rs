//! Round 5 Wave 2 regression tests covering:
//! - Part 1: `D1` (`push_main_phi`) single-`SNode::Stmts` splicing with
//!   `async_generator_machine_fold` (`agen_entry_elide`), `AsyncMode::EqThrow`
//!   under `count_temp_uses`, and `sweep_async_machinery` stripping dead
//!   catch-context `genobj` phi assigns when `genobj` remains live.
//! - Part 2 (Issue #88): `256 KiB`-stack end-to-end `decompile_module`,
//!   `decompile_module_split`, `dump_module`, and iterative `Drop`/`Clone`/`PartialEq`
//!   over:
//!   1. a `4,000`-term single-use `BinaryOp(Add)` + `UnaryOp(LogicalNot)` chain,
//!   2. a `1,000`-level nested `If`/`Else` diamond chain, and
//!   3. a `300`-level nested `DefineFunc` closure chain.

use crate::common::*;
use abcd_decompile::dump::dump_module;
use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_decompile::recover::recover_func;
use abcd_decompile::split::decompile_module_split;
use abcd_decompile::structure::structure_func;
use abcd_ir::module::FunctionKind;
use abcd_ir::op::{CallKind, CmpOp, LexEnvKind, Op, UnOp};
use abcd_ir::{Edge, EdgeKind, Module, ValueId};

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

fn wire_phi(m: &mut Module, phi_val: ValueId, entries: Vec<(Edge, ValueId)>) {
    let abcd_ir::ValueDef::Inst(iid) = m.value(phi_val).unwrap().def else {
        panic!("expected instruction-defined phi value");
    };
    m.inst_mut(iid).unwrap().op = Op::Phi { entries };
}

// ── Part 2 (Issue #88): 256 KiB Stack End-to-End Regression Tests ───────────

#[test]
fn stack_256k_end_to_end_4000_term_expr_chain() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "deep_expr");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);

    let mut cur = p1;
    for i in 0..2_000 {
        let k = load_number(&mut m, b, (i % 7) as f64);
        cur = add(&mut m, b, cur, k);
        cur = emit(
            &mut m,
            b,
            Op::UnaryOp {
                op: UnOp::LogicalNot,
                operand: cur,
            },
        );
    }
    emit_void(&mut m, b, Op::Return { value: Some(cur) });

    run_on_256k_stack("decompile-4k-expr-256k", || {
        // Stage A + iterative Expr Clone / PartialEq / Drop on 256 KiB stack:
        let rf = recover_func(&m, f);
        let rf_clone = rf.clone();
        assert_eq!(rf.blocks[0].stmts, rf_clone.blocks[0].stmts);
        drop((rf, rf_clone));

        // Deterministic dump_module on 256 KiB stack:
        let dumped = dump_module(&m);
        assert!(dumped.contains("fn #0 \"deep_expr\""));

        // Full decompile_module + streaming writer on 256 KiB stack:
        let decompiled = decompile_module(&m, &EmitOptions::default());
        assert_eq!(decompiled.stats.functions, 1);
        assert!(decompiled.text.contains("function deep_expr(p1)"));
        assert!(decompiled.text.contains("return !("));
    });
}

#[test]
fn stack_256k_end_to_end_1000_nested_if_else_chain() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "deep_ifs");
    let _this = add_param(&mut m, f);
    let p_cond = add_param(&mut m, f);
    let p_sink = add_param(&mut m, f);

    let depth = 1_000usize;
    let mut cur_head = entry_of(&m, f);
    let mut joins = Vec::with_capacity(depth);

    for level in 0..depth {
        let b_then = add_block(&mut m, f);
        let b_else = add_block(&mut m, f);
        let b_join = add_block(&mut m, f);

        let cond = emit(
            &mut m,
            cur_head,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p_cond,
            },
        );
        emit_void(
            &mut m,
            cur_head,
            Op::CondBranch {
                cond,
                true_dest: b_then,
                false_dest: b_else,
            },
        );
        link(&mut m, cur_head, b_then);
        link(&mut m, cur_head, b_else);

        let else_n = load_number(&mut m, b_else, level as f64);
        if level % 2 == 0 {
            emit_void(
                &mut m,
                b_else,
                Op::PutLexVar {
                    level: 0,
                    slot: 0,
                    value: else_n,
                    kind: LexEnvKind::Plain,
                },
            );
        } else {
            let _ = emit(
                &mut m,
                b_else,
                Op::Call {
                    callee: p_sink,
                    this: None,
                    args: vec![else_n],
                    kind: CallKind::Dynamic,
                },
            );
        }
        emit_void(&mut m, b_else, Op::Branch { dest: b_join });
        link(&mut m, b_else, b_join);

        joins.push(b_join);
        cur_head = b_then;
    }

    // Innermost `then` leaf branches out through all 1,000 joins in reverse.
    let leaf_v = load_number(&mut m, cur_head, 42.0);
    let _ = emit(
        &mut m,
        cur_head,
        Op::Call {
            callee: p_sink,
            this: None,
            args: vec![leaf_v],
            kind: CallKind::Dynamic,
        },
    );
    let deepest_join = *joins.last().unwrap();
    emit_void(&mut m, cur_head, Op::Branch { dest: deepest_join });
    link(&mut m, cur_head, deepest_join);

    for w in (1..joins.len()).rev() {
        let child_j = joins[w];
        let parent_j = joins[w - 1];
        emit_void(&mut m, child_j, Op::Branch { dest: parent_j });
        link(&mut m, child_j, parent_j);
    }
    emit_void(&mut m, joins[0], Op::Return { value: None });

    run_on_256k_stack("decompile-1k-ifs-256k", || {
        // Stage A + Stage B + iterative SNode Clone / PartialEq / Drop on 256 KiB stack:
        let rf = recover_func(&m, f);
        let st = structure_func(&m, &rf);
        assert_eq!(st.stats.ifs, depth);
        let cloned_body = st.body.clone();
        assert_eq!(st.body, cloned_body);
        drop((rf, st, cloned_body));

        // Deterministic dump_module + full decompile_module on 256 KiB stack:
        let dumped = dump_module(&m);
        assert!(dumped.contains("fn #0 \"deep_ifs\""));

        let decompiled = decompile_module(&m, &EmitOptions::default());
        assert_eq!(decompiled.stats.structure.ifs, depth);
        assert!(decompiled.text.contains("p2(42.0);"));
    });
}

#[test]
fn stack_256k_end_to_end_300_nested_define_func_closures() {
    let mut m = mk_module();
    let depth = 300usize;
    let mut fids = Vec::with_capacity(depth + 1);

    for i in 0..=depth {
        let name = if i == 0 {
            "closure_root".to_string()
        } else {
            format!("inner_{i}")
        };
        let fid = add_func_named(&mut m, &name);
        let _this = add_param(&mut m, fid);
        fids.push(fid);
    }

    for i in 0..depth {
        let parent = fids[i];
        let child = fids[i + 1];
        let b = entry_of(&m, parent);
        let clos = emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: child,
                length: 0,
                captures: vec![],
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(clos) });
    }
    {
        let leaf_b = entry_of(&m, fids[depth]);
        let v = load_number(&mut m, leaf_b, 99.0);
        emit_void(&mut m, leaf_b, Op::Return { value: Some(v) });
    }

    run_on_256k_stack("decompile-300-closures-256k", || {
        let dumped = dump_module(&m);
        assert!(dumped.contains("fn #0 \"closure_root\""));
        assert!(dumped.contains("fn #300 \"inner_300\""));

        let decompiled = decompile_module(&m, &EmitOptions::default());
        assert_eq!(decompiled.stats.functions, 1);
        assert_eq!(decompiled.stats.closures, depth);
        assert_eq!(decompiled.stats.function_bodies, depth + 1);
        assert!(
            !decompiled
                .stats
                .fallback_comments
                .contains_key("DefineFunc(cycle)")
        );
        assert!(decompiled.text.contains("function inner_300()"));
        assert!(decompiled.text.contains("return 99.0;"));

        let split = decompile_module_split(&m, &EmitOptions::default());
        assert_eq!(split.stats.function_bodies, depth + 1);
    });
}

// ── Part 1: D1 (`push_main_phi`) + Async / AsyncGenerator Regression Tests ──

#[test]
fn part1_d1_async_gen_entry_with_exceptional_phi_elides_cleanly() {
    // Reproduces the exact Wave 1 corpus regression: an `AsyncGenerator` whose
    // entry block emits `CreateGenerator(funcObj)` (non-throwing), an exceptional
    // `Phi` edge to a catch handler (inserted at `insert_at == 1` by `D1`), and
    // then the throwing `SuspendGenerator(genobj, undefined)` + `ResumeGenerator`
    // entry protocol. `push_main_phi` must keep the block in ONE `SNode::Stmts`
    // node and `agen_entry_elide` must skip the exceptional `PhiAssign` cleanly!
    let mut m = mk_module();
    let f = add_func_kind(&mut m, "agen_d1", FunctionKind::AsyncGenerator);
    let funcobj = add_param(&mut m, f);
    let _new_target = add_param(&mut m, f);
    let _this = add_param(&mut m, f);

    let b_entry = entry_of(&m, f);
    let b_body = add_block(&mut m, f);
    let b_catch = add_block(&mut m, f);

    let genobj = emit(&mut m, b_entry, Op::CreateGenerator { func: funcobj });
    let undef = load_const(&mut m, b_entry, abcd_ir::Const::Undefined);
    let _susp = emit(
        &mut m,
        b_entry,
        Op::SuspendGenerator {
            genobj,
            value: undef,
        },
    );
    let _resumed = emit(&mut m, b_entry, Op::ResumeGenerator { genobj });
    emit_void(&mut m, b_entry, Op::Branch { dest: b_body });

    // Body: DirectReturn (`CreateIterResultObj { value: genobj, done: 7.0 }`)
    let seven = load_number(&mut m, b_body, 7.0);
    let iro = emit(
        &mut m,
        b_body,
        Op::CreateIterResultObj {
            value: genobj,
            done: seven,
        },
    );
    emit_void(&mut m, b_body, Op::Return { value: Some(iro) });

    // Catch handler with exceptional Phi on `genobj` from `b_entry` and `b_body`:
    let exc = add_exception_param(&mut m, b_catch);
    let gen_phi = emit(&mut m, b_catch, Op::Phi { entries: vec![] });
    wire_phi(
        &mut m,
        gen_phi,
        vec![
            (
                Edge {
                    from: b_entry,
                    kind: EdgeKind::Exceptional,
                },
                genobj,
            ),
            (
                Edge {
                    from: b_body,
                    kind: EdgeKind::Exceptional,
                },
                genobj,
            ),
        ],
    );
    let rej = emit(
        &mut m,
        b_catch,
        Op::AsyncReject {
            funcobj: gen_phi,
            value: exc,
        },
    );
    emit_void(&mut m, b_catch, Op::Return { value: Some(rej) });

    link(&mut m, b_entry, b_body);
    add_try(&mut m, f, vec![b_entry, b_body], b_catch, exc);

    let decompiled = decompile_module(&m, &EmitOptions::default());
    assert_eq!(
        decompiled.stats.folds.agen_entry, 1,
        "agen_entry must fold when D1 splices exceptional PhiAssign after CreateGenerator:\n{}",
        decompiled.text
    );
    assert_eq!(decompiled.stats.folds.agen_returns, 1);
    assert!(
        decompiled.text.contains("return 7.0;")
            && !decompiled.text.contains("ResumeGenerator")
            && !decompiled.text.contains("CreateGenerator"),
        "all async-generator machinery must be swept cleanly:\n{}",
        decompiled.text
    );
}

#[test]
fn part1_async_eq_throw_await_folds_under_if_cond_use_counting() {
    // Reproduces the Photos.hap (`grantPermissionForUris` / `getPhotoAssetDataByAlbum`)
    // regression: an `Async` function whose await resume-mode check materializes
    // `const eq = (mode === 1.0)` (`AsyncMode::EqThrow`), where `eq` has `1` use
    // in `SNode::If.cond` after Wave 1 `#87.1` added control-header expressions
    // to `count_temp_uses`.
    let mut m = mk_module();
    let f = add_func_kind(&mut m, "async_eq_throw", FunctionKind::Async);
    let _this = add_param(&mut m, f);
    let p_prom = add_param(&mut m, f);

    let b_entry = entry_of(&m, f);
    let b_throw = add_block(&mut m, f);
    let b_ok = add_block(&mut m, f);
    let b_catch = add_block(&mut m, f);

    let funcobj = emit(&mut m, b_entry, Op::AsyncFunctionEnter);
    let awaited = emit(
        &mut m,
        b_entry,
        Op::AwaitUncaught {
            funcobj,
            value: p_prom,
        },
    );
    let _susp = emit(
        &mut m,
        b_entry,
        Op::SuspendGenerator {
            genobj: funcobj,
            value: awaited,
        },
    );
    let resumed = emit(&mut m, b_entry, Op::ResumeGenerator { genobj: funcobj });
    let mode = emit(&mut m, b_entry, Op::GetResumeMode { genobj: funcobj });
    let one = load_number(&mut m, b_entry, 1.0);
    let eq_throw = emit(
        &mut m,
        b_entry,
        Op::Compare {
            op: CmpOp::Eq,
            left: mode,
            right: one,
        },
    );
    // Effectful barrier between `eq_throw` (`==`) and `IsFalse(eq_throw)` forces
    // Stage A (`R2-C1`) to materialize `const v_eq = (mode == 1.0)` (`AsyncMode::EqThrow`)!
    emit_void(
        &mut m,
        b_entry,
        Op::SetGeneratorState {
            genobj: funcobj,
            state: 1,
        },
    );
    let cond = emit(
        &mut m,
        b_entry,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq_throw,
        },
    );
    emit_void(
        &mut m,
        b_entry,
        Op::CondBranch {
            cond,
            true_dest: b_ok,
            false_dest: b_throw,
        },
    );

    emit_void(&mut m, b_throw, Op::Throw { value: resumed });
    emit_void(&mut m, b_throw, Op::Unreachable);

    let resolved = emit(
        &mut m,
        b_ok,
        Op::AsyncResolve {
            funcobj,
            value: resumed,
        },
    );
    emit_void(
        &mut m,
        b_ok,
        Op::Return {
            value: Some(resolved),
        },
    );

    let exc = add_exception_param(&mut m, b_catch);
    let rej = emit(
        &mut m,
        b_catch,
        Op::AsyncReject {
            funcobj,
            value: exc,
        },
    );
    emit_void(&mut m, b_catch, Op::Return { value: Some(rej) });

    link(&mut m, b_entry, b_throw);
    link(&mut m, b_entry, b_ok);
    add_try(&mut m, f, vec![b_entry, b_throw, b_ok], b_catch, exc);

    let decompiled = decompile_module(&m, &EmitOptions::default());
    assert_eq!(
        decompiled.stats.folds.async_machine_sites, 1,
        "AsyncMode::EqThrow await site must fold with 1 If.cond temp use:\n{}",
        decompiled.text
    );
    assert!(
        decompiled.text.contains("await p1")
            && !decompiled.text.contains("ResumeGenerator")
            && !decompiled.text.contains("GetResumeMode"),
        "async state-machine driver ops must fold away cleanly:\n{}",
        decompiled.text
    );
}

#[test]
fn es2abc_dynamic_arkts_getter_hides_three_abi_slots() {
    // Reproduces OpenHarmony-6.1-LTS `Photos.hap` (`SaveUIExtensionPage`):
    // `es2abc` tags dynamic `.ets` records with `SourceLang::ArkTS` while
    // emitting `L_ESSlotNumberAnnotation;` and 3 hidden ABI slots
    // `(a0=funcobj, a1=new.target, a2=this)`. Concise getters must emit
    // `get id() { return this; }`, never `get id(p0, p1, p2)`.
    let mut m = Module::new();
    let ark_sym = m.sym.intern("Lcom/ohos/photos/Page;");
    let mut ark_cls = abcd_ir::module::ClassData::new(ark_sym, ark_sym);
    ark_cls.source_lang = abcd_ir::SourceLang::ArkTS;
    m.classes.push(ark_cls);

    let es_sym = m.sym.intern("L_ESSlotNumberAnnotation;");
    let es_cls_id = abcd_ir::ClassId::new(m.classes.len() as u32);
    m.classes
        .push(abcd_ir::module::ClassData::new(es_sym, es_sym));

    let f_main_name = m.sym.intern("func_main_0");
    let mut fd_main = abcd_ir::function::FunctionData::new(
        abcd_ir::ClassId::new(0),
        f_main_name,
        FunctionKind::Function,
    );
    fd_main.modifiers |= abcd_ir::Modifiers::STATIC;
    fd_main.annotations.push(abcd_ir::module::Annotation {
        class: es_cls_id,
        elements: vec![],
    });
    let f_main = abcd_ir::FuncId::new(0);
    m.functions.push(fd_main);
    m.classes[0].methods.push(f_main);
    let b_main = add_block(&mut m, f_main);
    let _ = add_param(&mut m, f_main);
    let _ = add_param(&mut m, f_main);
    let _ = add_param(&mut m, f_main);

    let f_get_name = m.sym.intern("get_id");
    let mut fd_get = abcd_ir::function::FunctionData::new(
        abcd_ir::ClassId::new(0),
        f_get_name,
        FunctionKind::Getter,
    );
    fd_get.modifiers |= abcd_ir::Modifiers::STATIC;
    fd_get.annotations.push(abcd_ir::module::Annotation {
        class: es_cls_id,
        elements: vec![],
    });
    let f_get = abcd_ir::FuncId::new(1);
    m.functions.push(fd_get);
    m.classes[0].methods.push(f_get);
    let b_get = add_block(&mut m, f_get);
    let _g0 = add_param(&mut m, f_get);
    let _g1 = add_param(&mut m, f_get);
    let g_this = add_param(&mut m, f_get);
    emit_void(
        &mut m,
        b_get,
        Op::Return {
            value: Some(g_this),
        },
    );

    let empty_shape = m.consts.push(abcd_ir::Const::ObjectLiteral {
        keys: vec![],
        values: vec![],
    });
    let obj = emit(&mut m, b_main, Op::AllocObject { shape: empty_shape });
    let getter_closure = emit(
        &mut m,
        b_main,
        Op::DefineFunc {
            body: f_get,
            captures: vec![],
            length: 0,
        },
    );
    let key = load_string(&mut m, b_main, "id");
    let undef = load_const(&mut m, b_main, abcd_ir::Const::Undefined);
    let set_name = load_const(&mut m, b_main, abcd_ir::Const::Bool(false));
    let _ = emit(
        &mut m,
        b_main,
        Op::DefineGetterSetterByValue {
            obj,
            key,
            getter: getter_closure,
            setter: undef,
            set_name,
        },
    );
    emit_void(&mut m, b_main, Op::Return { value: Some(obj) });

    let out = decompile_module(&m, &EmitOptions::default()).text;
    assert!(
        out.contains("get id() {") && out.contains("return this;") && !out.contains("get id(p0"),
        "dynamic es2abc ArkTS getter must hide 3 ABI slots and bind params[2] to `this`:\n{out}"
    );
}

#[test]
fn derived_ctor_exceptional_phi_this_param_avoids_premature_tdz() {
    // Reproduces test262 `language/expressions/super/call-arg-evaluation-err`:
    // in a derived constructor (`ThrowIfSuperNotCalled` / `CallKind::Super`),
    // `params[2]` (`this`) holds `Hole` before `super(...)` completes. Hoisting
    // an exceptional `PhiAssign` before `thrower()` must emit `undefined`, never
    // `this` (which would prematurely throw TDZ `ReferenceError` in JS).
    let mut m = mk_module();
    let f = add_func_kind(&mut m, "DerivedCtor", FunctionKind::Constructor);
    m.func_mut(f).unwrap().modifiers |= abcd_ir::Modifiers::STATIC;
    let _p_func = add_param(&mut m, f);
    let _p_newt = add_param(&mut m, f);
    let p_this = add_param(&mut m, f);

    let b_try = entry_of(&m, f);
    let b_catch = add_block(&mut m, f);
    let b_join = add_block(&mut m, f);

    let thrower_sym = m.sym.intern("thrower");
    let thrower_fn = emit(
        &mut m,
        b_try,
        Op::TryGetGlobal {
            name: thrower_sym,
            default: None,
        },
    );
    let arg = emit(
        &mut m,
        b_try,
        Op::Call {
            callee: thrower_fn,
            this: None,
            args: vec![],
            kind: abcd_ir::op::CallKind::Direct,
        },
    );
    let undef = load_const(&mut m, b_try, abcd_ir::Const::Undefined);
    let super_res = emit(
        &mut m,
        b_try,
        Op::Call {
            callee: undef,
            this: None,
            args: vec![arg],
            kind: abcd_ir::op::CallKind::Super,
        },
    );
    emit_void(
        &mut m,
        b_try,
        Op::ThrowIfSuperNotCalled {
            value: super_res,
            kind: abcd_ir::op::SuperCheck::NotCalled,
        },
    );
    emit_void(&mut m, b_try, Op::Branch { dest: b_join });

    let exc = add_exception_param(&mut m, b_catch);
    let phi_this_catch = emit(&mut m, b_catch, Op::Phi { entries: vec![] });
    wire_phi(
        &mut m,
        phi_this_catch,
        vec![(
            Edge {
                from: b_try,
                kind: EdgeKind::Exceptional,
            },
            p_this,
        )],
    );
    let caught_sym = m.sym.intern("caught");
    emit_void(
        &mut m,
        b_catch,
        Op::TryStoreGlobal {
            name: caught_sym,
            value: exc,
        },
    );
    emit_void(&mut m, b_catch, Op::Branch { dest: b_join });

    let phi_ret = emit(&mut m, b_join, Op::Phi { entries: vec![] });
    wire_phi(
        &mut m,
        phi_ret,
        vec![
            (
                Edge {
                    from: b_try,
                    kind: EdgeKind::Normal,
                },
                super_res,
            ),
            (
                Edge {
                    from: b_catch,
                    kind: EdgeKind::Normal,
                },
                phi_this_catch,
            ),
        ],
    );
    emit_void(
        &mut m,
        b_join,
        Op::ThrowIfSuperNotCalled {
            value: phi_ret,
            kind: abcd_ir::op::SuperCheck::NotCalled,
        },
    );
    emit_void(
        &mut m,
        b_join,
        Op::Return {
            value: Some(phi_ret),
        },
    );

    link(&mut m, b_try, b_join);
    link(&mut m, b_catch, b_join);
    add_try(&mut m, f, vec![b_try], b_catch, exc);

    let out = decompile_module(&m, &EmitOptions::default()).text;
    assert!(
        !out.contains("= this;") && out.contains("= undefined;"),
        "derived ctor exceptional PhiAssign from Param(this) must emit `undefined`, not `this`:\n{out}"
    );
}
