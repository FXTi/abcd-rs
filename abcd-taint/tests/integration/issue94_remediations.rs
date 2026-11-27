//! Regression tests for GitHub Issue #94 (Parts 1–3: `abcd-taint`):
//! - `D6`: Zero-copy `FlowSink::pass_through()` parity with `*_flow` wrappers
//! - `D5`, `R1`, `R2`, `T1`, `R3`: Concrete-singleton strong-update discipline,
//!   `EdgeKind::Exceptional` strong-kill ban, and partly-unknown store receivers
//! - `R4`: Separated `uncaught_edge_set` + multi-frame uncaught-exit witness paths
//! - `R5`: Dynamic ECMAScript `class Sub extends Base` virtual `this.method()` override
//! - `cut_first`: 2-step property reads (`source().a.b` and `x.a.b = source()`)
//! - `BodyStep` excess actuals (`arguments` / `...rest`) & `exclusive` summary bypass
//! - `R7`: `globalThis` (`LoadGlobalObject`) `Mov`-peeled transfer & reader cone
//! - `#private` fields (`LoadPrivate`, `StorePrivate`, `DefinePrivate`)
//! - `R8`: `export * as ns` namespace re-exports & `GetModuleNamespace`
//! - `R10`: Rung 0/1 captured `LexVar` `level` shift
//! - `D3`: Steady-state `EntryModel` OHOS lifecycle & `OhmUrl` specifier normalization
//! - `names.rs` / `prototype.rs` diamond DAG memoization, `call_base_value` `Mov` peeling,
//!   `gap.rs` `DefineMethod` callback resolution, and `L6` `Endpoint::parse`.

use std::cell::RefCell;
use std::collections::HashMap;

use crate::common::*;
use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::dataflow::Rung0AliasOracle;
use abcd_ir::consts::Const;
use abcd_ir::function::FunctionData;
use abcd_ir::module::{ClassData, EsModule, ExportDecl, FunctionKind, ImportDecl, ModuleRequest};
use abcd_ir::op::{DefineClassData, MemberAttrs, ModuleVarKind, SuperKey};
use abcd_ir::{
    CallKind, ClassId, Edge, EdgeKind, FuncId, LexEnvKind, LitMethodKind, Modifiers, Module, Op,
    ValueId,
};
use abcd_taint::driver::{run_taint, run_taint_full};
use abcd_taint::fact::{Fact, TaintBase};
use abcd_taint::names::{call_base_value, callee_name_candidates, normalize_sdk_specifier};
use abcd_taint::summary::{Endpoint, Summary};
use abcd_taint::{
    Oracle, ProtoFamily, PrototypeResolver, SinkSpec, SourceSpec, SummaryRegistry, TaintConfig,
    ohos_preset,
};

fn std_config_at(rung: u8) -> TaintConfig {
    TaintConfig {
        sources: vec![SourceSpec::FunctionParams {
            name: "func_main_0".to_owned(),
            params: None,
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        builtin_summaries: false,
        alias_rung: rung,
        ..TaintConfig::default()
    }
}

fn emit_print(m: &mut Module, b: abcd_ir::BlockId, arg: ValueId) -> abcd_ir::InstId {
    let p = try_get_global(m, b, "print");
    push_inst(
        m,
        b,
        Op::Call {
            callee: p,
            this: None,
            args: vec![arg],
            kind: CallKind::Dynamic,
        },
    )
}

/// `R1`: Allocation inside a `while` loop is NOT a concrete runtime singleton;
/// overwriting `o.f = clean` on a subsequent iteration must perform a WEAK update
/// and preserve iteration 1's taint across Rungs 0, 1, and 2.
#[test]
fn r1_loop_allocation_weak_update_preserves_taint_across_rungs() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let loop_hdr = add_block(&mut m, f);
    let loop_body = add_block(&mut m, f);
    let set_taint = add_block(&mut m, f);
    let set_clean = add_block(&mut m, f);
    let loop_latch = add_block(&mut m, f);
    let exit = add_block(&mut m, f);

    add_param(&mut m, f, 0);
    let secret = add_param(&mut m, f, 1);
    let field_f = intern(&mut m, "f");

    let init_prev = alloc_object(&mut m, entry);
    emit_void(&mut m, entry, Op::Branch { dest: loop_hdr });
    link(&mut m, entry, loop_hdr);

    // Loop header: `prev = Phi(entry: init_prev, latch: next_prev)`
    let prev_phi = emit(
        &mut m,
        loop_hdr,
        Op::Phi {
            entries: Vec::new(),
        },
    );
    let cond = try_get_global(&mut m, loop_hdr, "LOOP_COND");
    emit_void(
        &mut m,
        loop_hdr,
        Op::CondBranch {
            cond,
            true_dest: loop_body,
            false_dest: exit,
        },
    );
    link(&mut m, loop_hdr, loop_body);
    link(&mut m, loop_hdr, exit);

    // Loop body allocates `o = {}` on EVERY iteration.
    let o = alloc_object(&mut m, loop_body);
    let iter_cond = try_get_global(&mut m, loop_body, "FIRST_ITER");
    emit_void(
        &mut m,
        loop_body,
        Op::CondBranch {
            cond: iter_cond,
            true_dest: set_taint,
            false_dest: set_clean,
        },
    );
    link(&mut m, loop_body, set_taint);
    link(&mut m, loop_body, set_clean);

    // Iteration 1: `o.f = secret; next_prev = o;`
    emit_void(
        &mut m,
        set_taint,
        Op::StoreProp {
            object: o,
            name: field_f,
            value: secret,
        },
    );
    emit_void(&mut m, set_taint, Op::Branch { dest: loop_latch });
    link(&mut m, set_taint, loop_latch);

    // Iteration 2: `o.f = "clean"; next_prev = prev_phi;`
    let clean = load_string(&mut m, set_clean, "clean");
    emit_void(
        &mut m,
        set_clean,
        Op::StoreProp {
            object: o,
            name: field_f,
            value: clean,
        },
    );
    emit_void(&mut m, set_clean, Op::Branch { dest: loop_latch });
    link(&mut m, set_clean, loop_latch);

    let next_prev = emit(
        &mut m,
        loop_latch,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: set_taint,
                        kind: EdgeKind::Normal,
                    },
                    o,
                ),
                (
                    Edge {
                        from: set_clean,
                        kind: EdgeKind::Normal,
                    },
                    prev_phi,
                ),
            ],
        },
    );
    emit_void(&mut m, loop_latch, Op::Branch { dest: loop_hdr });
    link(&mut m, loop_latch, loop_hdr);

    // Patch `prev_phi` entries now that `next_prev` exists.
    let abcd_ir::ValueDef::Inst(phi_iid) = m.value(prev_phi).unwrap().def else {
        panic!("phi inst");
    };
    m.inst_mut(phi_iid).unwrap().op = Op::Phi {
        entries: vec![
            (
                Edge {
                    from: entry,
                    kind: EdgeKind::Normal,
                },
                init_prev,
            ),
            (
                Edge {
                    from: loop_latch,
                    kind: EdgeKind::Normal,
                },
                next_prev,
            ),
        ],
    };

    let leaked = emit(
        &mut m,
        exit,
        Op::LoadProp {
            object: prev_phi,
            name: field_f,
        },
    );
    emit_print(&mut m, exit, leaked);
    emit_void(&mut m, exit, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let report = run_taint(&m, &std_config_at(rung));
        assert!(
            report
                .hits
                .iter()
                .any(|h| h.fact.local_base() == Some(leaked)),
            "rung {rung}: loop-allocated object must NOT be strong-killed: {:?}",
            report.hits
        );
    }
}

/// `R2`: Multi-call factory `make()` called twice (`let a = make(); a.f = secret;
/// let b = make(); b.f = clean; print(a.f)`) must perform a WEAK update on `b.f`
/// and preserve `a.f`'s taint across Rungs 0, 1, and 2.
#[test]
fn r2_multi_call_factory_weak_update_preserves_taint_across_rungs() {
    let mut m = mk_module();
    let make_fn = add_func_named(&mut m, "make");
    m.func_mut(make_fn).unwrap().modifiers = Modifiers::STATIC;
    {
        let mb = entry_of(&m, make_fn);
        add_param(&mut m, make_fn, 0);
        add_param(&mut m, make_fn, 1);
        add_param(&mut m, make_fn, 2);
        let fresh = alloc_object(&mut m, mb);
        emit_void(&mut m, mb, Op::Return { value: Some(fresh) });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    add_param(&mut m, main_fn, 0);
    let secret = add_param(&mut m, main_fn, 1);
    let field_f = intern(&mut m, "f");

    let make_ref1 = load_method_ref(&mut m, entry, make_fn);
    let a = emit(
        &mut m,
        entry,
        Op::Call {
            callee: make_ref1,
            this: None,
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: a,
            name: field_f,
            value: secret,
        },
    );

    let make_ref2 = load_method_ref(&mut m, entry, make_fn);
    let b = emit(
        &mut m,
        entry,
        Op::Call {
            callee: make_ref2,
            this: None,
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    let clean = load_string(&mut m, entry, "clean");
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: b,
            name: field_f,
            value: clean,
        },
    );

    let read_a = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: a,
            name: field_f,
        },
    );
    emit_print(&mut m, entry, read_a);
    emit_void(&mut m, entry, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let report = run_taint(&m, &std_config_at(rung));
        assert!(
            report
                .hits
                .iter()
                .any(|h| h.fact.local_base() == Some(read_a)),
            "rung {rung}: multi-call factory site must NOT strong-kill sibling instance `a.f`: {:?}",
            report.hits
        );
    }
}

/// `T1` & `D5`: A throwing store (`StoreProp` / `StorePrivate`) inside a `try`
/// block NEVER strong-kills existing taint along `EdgeKind::Exceptional` into
/// `catch`, whereas along the `Normal` continuation it DOES strong-kill both
/// concrete-singleton `Heap(site)` and same-`ValueId` `Local(v)`!
#[test]
fn t1_exceptional_edge_never_strong_kills_while_normal_edge_does() {
    let mut m = mk_module();
    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    let try_blk = add_block(&mut m, main_fn);
    let normal_after = add_block(&mut m, main_fn);
    let catch_blk = add_block(&mut m, main_fn);
    let done = add_block(&mut m, main_fn);

    add_param(&mut m, main_fn, 0);
    let secret = add_param(&mut m, main_fn, 1);
    let obj_param = add_param(&mut m, main_fn, 2);
    let k = intern(&mut m, "k");

    // 1. Concrete singleton heap object `o` + `Local(obj_param)` seeded BEFORE `try`.
    let o = alloc_object(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: o,
            name: k,
            value: secret,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::StorePrivate {
            level: 0,
            slot: 0,
            obj: o,
            value: secret,
        },
    );
    // Give `obj_param` field-precise `Local(obj_param, [k])` taint via a summary.
    let set_k = try_get_global(&mut m, entry, "seedFieldK");
    let _ = emit(
        &mut m,
        entry,
        Op::Call {
            callee: set_k,
            this: Some(obj_param),
            args: vec![secret],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Branch { dest: try_blk });
    link(&mut m, entry, try_blk);

    let exc = add_exception_param(&mut m, catch_blk);
    add_try(&mut m, main_fn, vec![try_blk], catch_blk, exc);

    // Inside `try`: overwrite `o.k = clean`, `o.#0 = clean`, `obj_param.k = clean`.
    // If any of these throws (e.g. setter / frozen object / proxy trap), the write
    // did NOT complete when entering `catch_blk`!
    let clean = load_string(&mut m, try_blk, "clean");
    emit_void(
        &mut m,
        try_blk,
        Op::StoreProp {
            object: o,
            name: k,
            value: clean,
        },
    );
    emit_void(
        &mut m,
        try_blk,
        Op::StorePrivate {
            level: 0,
            slot: 0,
            obj: o,
            value: clean,
        },
    );
    emit_void(
        &mut m,
        try_blk,
        Op::StoreProp {
            object: obj_param,
            name: k,
            value: clean,
        },
    );
    emit_void(&mut m, try_blk, Op::Branch { dest: normal_after });
    link(&mut m, try_blk, normal_after);

    // Normal continuation: all three overwrote cleanly -> MUST be sanitized (0 hits).
    let norm_heap = emit(&mut m, normal_after, Op::LoadProp { object: o, name: k });
    let norm_priv = emit(
        &mut m,
        normal_after,
        Op::LoadPrivate {
            level: 0,
            slot: 0,
            obj: o,
        },
    );
    let norm_local = emit(
        &mut m,
        normal_after,
        Op::LoadProp {
            object: obj_param,
            name: k,
        },
    );
    let sink_norm_heap = emit_print(&mut m, normal_after, norm_heap);
    let sink_norm_priv = emit_print(&mut m, normal_after, norm_priv);
    let sink_norm_local = emit_print(&mut m, normal_after, norm_local);
    emit_void(&mut m, normal_after, Op::Branch { dest: done });
    link(&mut m, normal_after, done);

    // Catch handler: store threw BEFORE completing -> all three MUST remain tainted!
    let catch_heap = emit(&mut m, catch_blk, Op::LoadProp { object: o, name: k });
    let catch_priv = emit(
        &mut m,
        catch_blk,
        Op::LoadPrivate {
            level: 0,
            slot: 0,
            obj: o,
        },
    );
    let catch_local = emit(
        &mut m,
        catch_blk,
        Op::LoadProp {
            object: obj_param,
            name: k,
        },
    );
    let sink_catch_heap = emit_print(&mut m, catch_blk, catch_heap);
    let sink_catch_priv = emit_print(&mut m, catch_blk, catch_priv);
    let sink_catch_local = emit_print(&mut m, catch_blk, catch_local);
    emit_void(&mut m, catch_blk, Op::Branch { dest: done });
    link(&mut m, catch_blk, done);

    emit_void(&mut m, done, Op::Return { value: None });

    let k_chain = abcd_analysis::dataflow::heap::FieldChain::new()
        .pushed(abcd_analysis::dataflow::heap::FieldKey::Named(k), 5);
    for rung in [0u8, 1, 2] {
        let mut cfg = TaintConfig {
            sources: vec![SourceSpec::FunctionParams {
                name: "func_main_0".to_owned(),
                params: Some(vec![1]), // only `secret` is tainted, NOT `obj_param` whole-object!
            }],
            ..std_config_at(rung)
        };
        cfg.extra_summaries.push((
            "seedFieldK".to_owned(),
            Some(1),
            Summary::new("param0 -> this.k")
                .flow(Endpoint::Param(0), Endpoint::Field(k_chain.clone())),
        ));
        let report = run_taint(&m, &cfg);
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();

        assert!(
            hit_calls.contains(&sink_catch_heap),
            "rung {rung}: exceptional edge must NOT kill Heap(o).k: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_catch_priv),
            "rung {rung}: exceptional edge must NOT kill Heap(o).#priv: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_catch_local),
            "rung {rung}: exceptional edge must NOT kill Local(obj_param).k: {hit_calls:?}"
        );

        assert!(
            !hit_calls.contains(&sink_norm_heap),
            "rung {rung}: normal edge MUST strong-kill concrete singleton Heap(o).k: {hit_calls:?}"
        );
        assert!(
            !hit_calls.contains(&sink_norm_priv),
            "rung {rung}: normal edge MUST strong-kill concrete singleton Heap(o).#priv: {hit_calls:?}"
        );
        assert!(
            !hit_calls.contains(&sink_norm_local),
            "rung {rung}: normal edge MUST strong-kill same-ValueId Local(obj_param).k: {hit_calls:?}"
        );
    }
}

/// `R3`: Storing into `object` whose `SiteInfo` has `has_unknown && !sites.is_empty()`
/// (`let m = cond ? {} : ext; m.f = secret;`) emits taint on BOTH
/// `TaintBase::Heap(sites)` AND `TaintBase::Local(m)`.
#[test]
fn r3_partly_unknown_store_receiver_preserves_local_and_heap_facts() {
    let mut m = mk_module();
    let helper = add_func_named(&mut m, "buildMixed");
    m.func_mut(helper).unwrap().modifiers = Modifiers::STATIC;
    let mixed;
    {
        let entry = entry_of(&m, helper);
        let t_blk = add_block(&mut m, helper);
        let f_blk = add_block(&mut m, helper);
        let join = add_block(&mut m, helper);

        add_param(&mut m, helper, 0);
        add_param(&mut m, helper, 1);
        add_param(&mut m, helper, 2);
        let sec = add_param(&mut m, helper, 3);
        let f_sym = intern(&mut m, "f");

        let cond = try_get_global(&mut m, entry, "COND");
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond,
                true_dest: t_blk,
                false_dest: f_blk,
            },
        );
        link(&mut m, entry, t_blk);
        link(&mut m, entry, f_blk);

        let concrete = alloc_object(&mut m, t_blk);
        emit_void(&mut m, t_blk, Op::Branch { dest: join });
        link(&mut m, t_blk, join);

        let ext = try_get_global(&mut m, f_blk, "EXT_OBJ");
        emit_void(&mut m, f_blk, Op::Branch { dest: join });
        link(&mut m, f_blk, join);

        mixed = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: t_blk,
                            kind: EdgeKind::Normal,
                        },
                        concrete,
                    ),
                    (
                        Edge {
                            from: f_blk,
                            kind: EdgeKind::Normal,
                        },
                        ext,
                    ),
                ],
            },
        );
        emit_void(
            &mut m,
            join,
            Op::StoreProp {
                object: mixed,
                name: f_sym,
                value: sec,
            },
        );
        emit_void(&mut m, join, Op::Return { value: Some(mixed) });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    add_param(&mut m, main_fn, 0);
    let secret = add_param(&mut m, main_fn, 1);
    let f_sym = intern(&mut m, "f");

    let href = load_method_ref(&mut m, entry, helper);
    let ret_obj = emit(
        &mut m,
        entry,
        Op::Call {
            callee: href,
            this: None,
            args: vec![secret],
            kind: CallKind::Direct,
        },
    );
    // Passing `ret_obj` directly to `print(ret_obj)` requires `Local(mixed, [f])`
    // at Rung 0 (since `known_sites_at(ret_obj)` is empty at Rung 0!), and reading
    // `ret_obj.f` exercises field projection across all rungs.
    let sink_whole = emit_print(&mut m, entry, ret_obj);
    let val_f = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: ret_obj,
            name: f_sym,
        },
    );
    let sink_field = emit_print(&mut m, entry, val_f);
    emit_void(&mut m, entry, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let (report, result) = run_taint_full(&m, &std_config_at(rung));
        let has_local_mixed = result.path_edges().iter().any(|e| {
            matches!(&e.target_fact, Fact::Taint(tf) if tf.base == TaintBase::Local(mixed) && tf.fields.len() == 1)
        });
        let has_heap_mixed = result.path_edges().iter().any(|e| {
            matches!(&e.target_fact, Fact::Taint(tf) if matches!(&tf.base, TaintBase::Heap(s) if s.len() == 1) && tf.fields.len() == 1)
        });
        assert!(
            has_local_mixed && has_heap_mixed,
            "rung {rung}: partly-unknown receiver must emit BOTH Local(mixed) and Heap(sites)"
        );
        assert!(
            report.hits.iter().any(|h| h.call == sink_whole),
            "rung {rung}: returned Local(ret_obj).[f] must hit print(ret_obj): {:?}",
            report.hits
        );
        assert!(
            report.hits.iter().any(|h| h.call == sink_field),
            "rung {rung}: ret_obj.f must hit print(ret_obj.f): {:?}",
            report.hits
        );
    }
}

/// `R4`: A single call site `mid(secret)` that BOTH throws uncaught (via `leafThrow`)
/// on one branch AND returns tainted `secret` normally on the other branch delivers
/// BOTH flows via separated `uncaught_edge_set`, and `reconstruct_path` includes
/// `leafThrow`'s `Throw` and `mid`'s uncaught `Call` in `hit.path`.
#[test]
fn r4_separated_uncaught_edge_set_and_witness_path_reconstruction() {
    let mut m = mk_module();

    let leaf = add_func_named(&mut m, "leafMayThrow");
    m.func_mut(leaf).unwrap().modifiers = Modifiers::STATIC;
    let leaf_throw_iid;
    {
        let entry = entry_of(&m, leaf);
        let th_blk = add_block(&mut m, leaf);
        let ok_blk = add_block(&mut m, leaf);
        add_param(&mut m, leaf, 0);
        add_param(&mut m, leaf, 1);
        add_param(&mut m, leaf, 2);
        let x = add_param(&mut m, leaf, 3);

        let cond = try_get_global(&mut m, entry, "MAY_THROW");
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond,
                true_dest: th_blk,
                false_dest: ok_blk,
            },
        );
        link(&mut m, entry, th_blk);
        link(&mut m, entry, ok_blk);

        leaf_throw_iid = emit_void(&mut m, th_blk, Op::Throw { value: x });
        emit_void(&mut m, ok_blk, Op::Return { value: Some(x) });
    }

    let mid = add_func_named(&mut m, "midForward");
    m.func_mut(mid).unwrap().modifiers = Modifiers::STATIC;
    let mid_call_iid;
    {
        let b = entry_of(&m, mid);
        add_param(&mut m, mid, 0);
        add_param(&mut m, mid, 1);
        add_param(&mut m, mid, 2);
        let y = add_param(&mut m, mid, 3);
        let lref = load_method_ref(&mut m, b, leaf);
        let r = emit(
            &mut m,
            b,
            Op::Call {
                callee: lref,
                this: None,
                args: vec![y],
                kind: CallKind::Direct,
            },
        );
        let abcd_ir::ValueDef::Inst(ciid) = m.value(r).unwrap().def else {
            panic!("call inst");
        };
        mid_call_iid = ciid;
        emit_void(&mut m, b, Op::Return { value: Some(r) });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    let try_blk = add_block(&mut m, main_fn);
    let norm_blk = add_block(&mut m, main_fn);
    let catch_blk = add_block(&mut m, main_fn);
    let done = add_block(&mut m, main_fn);

    add_param(&mut m, main_fn, 0);
    let secret = add_param(&mut m, main_fn, 1);
    emit_void(&mut m, entry, Op::Branch { dest: try_blk });
    link(&mut m, entry, try_blk);

    let exc = add_exception_param(&mut m, catch_blk);
    add_try(&mut m, main_fn, vec![try_blk], catch_blk, exc);

    let mref = load_method_ref(&mut m, try_blk, mid);
    let ret = emit(
        &mut m,
        try_blk,
        Op::Call {
            callee: mref,
            this: None,
            args: vec![secret],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, try_blk, Op::Branch { dest: norm_blk });
    link(&mut m, try_blk, norm_blk);

    let norm_sink = emit_print(&mut m, norm_blk, ret);
    emit_void(&mut m, norm_blk, Op::Branch { dest: done });
    link(&mut m, norm_blk, done);

    let catch_sink = emit_print(&mut m, catch_blk, exc);
    emit_void(&mut m, catch_blk, Op::Branch { dest: done });
    link(&mut m, catch_blk, done);

    emit_void(&mut m, done, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let report = run_taint(&m, &std_config_at(rung));
        let norm_hit = report.hits.iter().find(|h| h.call == norm_sink);
        let catch_hit = report.hits.iter().find(|h| h.call == catch_sink);
        assert!(
            norm_hit.is_some(),
            "rung {rung}: normal return on same call site must hit: {:?}",
            report.hits
        );
        let catch_hit = catch_hit.unwrap_or_else(|| {
            panic!(
                "rung {rung}: uncaught exception on same call site must hit: {:?}",
                report.hits
            )
        });
        let path_insts: Vec<_> = catch_hit.path.iter().map(|s| s.inst).collect();
        assert!(
            path_insts.contains(&leaf_throw_iid),
            "rung {rung}: witness path must contain leaf `Throw` ({leaf_throw_iid:?}): {:?}",
            catch_hit.path
        );
        assert!(
            path_insts.contains(&mid_call_iid),
            "rung {rung}: witness path must contain intermediate uncaught `Call` ({mid_call_iid:?}): {:?}",
            catch_hit.path
        );
    }
}

/// `R5`: Dynamic ECMAScript `class Sub extends Base` virtual `this.getSecret()`
/// override resolves via prototype inheritance (`DefineClass` `super_class`) and
/// propagates taint to the sink.
#[test]
fn r5_dynamic_ecmascript_subclass_virtual_this_method_override_taint() {
    let mut m = mk_module();
    let run_sym = intern(&mut m, "run");
    let get_sym = intern(&mut m, "getSecret");

    // Base constructor & methods:
    // Base.prototype.getSecret() { return "clean"; }
    // Base.prototype.run() { let v = this.getSecret(); print(v); }
    let base_ctor = add_func_named(&mut m, "Base");
    m.func_mut(base_ctor).unwrap().kind = FunctionKind::Constructor;
    m.func_mut(base_ctor).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, base_ctor);
        add_param(&mut m, base_ctor, 0);
        add_param(&mut m, base_ctor, 1);
        let this_v = add_param(&mut m, base_ctor, 2);
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(this_v),
            },
        );
    }

    let base_get = add_func_named(&mut m, "Base_getSecret");
    m.func_mut(base_get).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, base_get);
        add_param(&mut m, base_get, 0);
        add_param(&mut m, base_get, 1);
        add_param(&mut m, base_get, 2);
        let c = load_string(&mut m, b, "clean");
        emit_void(&mut m, b, Op::Return { value: Some(c) });
    }

    let base_run = add_func_named(&mut m, "Base_run");
    m.func_mut(base_run).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, base_run);
        add_param(&mut m, base_run, 0);
        add_param(&mut m, base_run, 1);
        let this_v = add_param(&mut m, base_run, 2);
        let m_fn = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: this_v,
                name: get_sym,
            },
        );
        let val = emit(
            &mut m,
            b,
            Op::Call {
                callee: m_fn,
                this: Some(this_v),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_print(&mut m, b, val);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Sub constructor & override:
    // Sub.prototype.getSecret() { return TryGetGlobal("TAINT_SRC"); }
    let sub_ctor = add_func_named(&mut m, "Sub");
    m.func_mut(sub_ctor).unwrap().kind = FunctionKind::Constructor;
    m.func_mut(sub_ctor).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, sub_ctor);
        add_param(&mut m, sub_ctor, 0);
        add_param(&mut m, sub_ctor, 1);
        let this_v = add_param(&mut m, sub_ctor, 2);
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(this_v),
            },
        );
    }

    let sub_get = add_func_named(&mut m, "Sub_getSecret");
    m.func_mut(sub_get).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, sub_get);
        add_param(&mut m, sub_get, 0);
        add_param(&mut m, sub_get, 1);
        add_param(&mut m, sub_get, 2);
        let sec = try_get_global(&mut m, b, "TAINT_SRC");
        emit_void(&mut m, b, Op::Return { value: Some(sec) });
    }

    let base_members = {
        let k_get = push_const(&mut m, Const::String(get_sym));
        let v_get = push_const(
            &mut m,
            Const::MethodRef {
                func: base_get,
                kind: LitMethodKind::Method,
            },
        );
        let k_run = push_const(&mut m, Const::String(run_sym));
        let v_run = push_const(
            &mut m,
            Const::MethodRef {
                func: base_run,
                kind: LitMethodKind::Method,
            },
        );
        let n_inst = push_const(&mut m, Const::Int32(2));
        push_const(
            &mut m,
            Const::ArrayLiteral(vec![k_get, v_get, k_run, v_run, n_inst]),
        )
    };
    let sub_members = {
        let k_get = push_const(&mut m, Const::String(get_sym));
        let v_get = push_const(
            &mut m,
            Const::MethodRef {
                func: sub_get,
                kind: LitMethodKind::Method,
            },
        );
        let n_inst = push_const(&mut m, Const::Int32(1));
        push_const(&mut m, Const::ArrayLiteral(vec![k_get, v_get, n_inst]))
    };

    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    let base_cls = emit(
        &mut m,
        entry,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: base_ctor,
            heritage: None,
            members: base_members,
            member_attrs: vec![
                MemberAttrs {
                    is_static: false,
                    kind: FunctionKind::Function,
                },
                MemberAttrs {
                    is_static: false,
                    kind: FunctionKind::Function,
                },
            ],
            count: 0,
        })),
    );
    let sub_cls = emit(
        &mut m,
        entry,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: sub_ctor,
            heritage: Some(base_cls),
            members: sub_members,
            member_attrs: vec![MemberAttrs {
                is_static: false,
                kind: FunctionKind::Function,
            }],
            count: 0,
        })),
    );
    let inst = emit(
        &mut m,
        entry,
        Op::Call {
            callee: sub_cls,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    let run_fn = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: inst,
            name: run_sym,
        },
    );
    let _ = emit(
        &mut m,
        entry,
        Op::Call {
            callee: run_fn,
            this: Some(inst),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let cfg = TaintConfig {
        sources: vec![SourceSpec::GlobalLoad {
            name: "TAINT_SRC".to_owned(),
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        builtin_summaries: false,
        alias_rung: 2,
        ..TaintConfig::default()
    };
    let report = run_taint(&m, &cfg);
    assert_eq!(
        report.hits.len(),
        1,
        "virtual `this.getSecret()` in `Base.run()` must dispatch to `Sub.getSecret()`: {:?}",
        report.hits
    );
}

/// `cut_first` 2-step property reads:
/// 1. `let x = source(); let t = x.a; print(t.b)` (whole-object taint cuts `[] -> []`)
/// 2. `let inner = {}; inner.b = source(); let outer = {}; outer.a = inner; let t = outer.a; print(t.b)`
/// 3. `x.a.b = source(); let t = x.a; print(t.b)` (in-place nested store on opaque `x`)
///
/// Plus clean negative control `print(t.clean)` == 0 FP!
#[test]
fn cut_first_two_step_property_reads_whole_and_nested_chain() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let secret = add_param(&mut m, f, 1);
    let opaque_x = add_param(&mut m, f, 2);

    let sym_a = intern(&mut m, "a");
    let sym_b = intern(&mut m, "b");
    let sym_clean = intern(&mut m, "clean");

    // Shape 1: whole-object taint `secret.a.b`
    let t1 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: secret,
            name: sym_a,
        },
    );
    let v1 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: t1,
            name: sym_b,
        },
    );
    let sink1 = emit_print(&mut m, entry, v1);

    // Shape 2: nested concrete objects `outer.a = inner; inner.b = secret`
    let inner = alloc_object(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: inner,
            name: sym_b,
            value: secret,
        },
    );
    let outer = alloc_object(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: outer,
            name: sym_a,
            value: inner,
        },
    );
    let t2 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: outer,
            name: sym_a,
        },
    );
    let v2 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: t2,
            name: sym_b,
        },
    );
    let v2_clean = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: t2,
            name: sym_clean,
        },
    );
    let sink2 = emit_print(&mut m, entry, v2);
    let sink2_clean = emit_print(&mut m, entry, v2_clean);

    // Shape 3: in-place nested mutation `opaque_x.a.b = secret; let t3 = opaque_x.a; print(t3.b)`
    let xa_write = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: opaque_x,
            name: sym_a,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: xa_write,
            name: sym_b,
            value: secret,
        },
    );
    let t3 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: opaque_x,
            name: sym_a,
        },
    );
    let v3 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: t3,
            name: sym_b,
        },
    );
    let v3_clean = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: t3,
            name: sym_clean,
        },
    );
    let sink3 = emit_print(&mut m, entry, v3);
    let sink3_clean = emit_print(&mut m, entry, v3_clean);

    emit_void(&mut m, entry, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let cfg = TaintConfig {
            sources: vec![SourceSpec::FunctionParams {
                name: "func_main_0".to_owned(),
                params: Some(vec![1]), // only `secret` is tainted!
            }],
            ..std_config_at(rung)
        };
        let report = run_taint(&m, &cfg);
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink1),
            "rung {rung}: `source().a.b` must hit: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink2),
            "rung {rung}: nested `outer.a = inner; inner.b = source(); outer.a.b` must hit: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink3),
            "rung {rung}: in-place `x.a.b = source(); let t = x.a; t.b` must hit: {hit_calls:?}"
        );
        assert!(
            !hit_calls.contains(&sink2_clean) && !hit_calls.contains(&sink3_clean),
            "rung {rung}: sibling `.clean` properties must remain clean: {hit_calls:?}"
        );
    }
}

/// `BodyStep` excess actuals (`GetUnmappedArgs` / `CopyRestArgs`) + preserving
/// caller field-bearing facts across excess-arg `BodyStep`, callable-field calls,
/// caught exceptions, and read-only `exclusive` builtin summaries (`JSON.stringify`).
#[test]
fn bodystep_excess_actuals_variadic_and_readonly_exclusive_summaries() {
    let mut m = mk_module();
    let k_sym = intern(&mut m, "k");

    // 1. `readArguments()` declares 0 formals, reads `arguments[1]` via `GetUnmappedArgs`.
    let fn_args = add_func_named(&mut m, "readArguments");
    m.func_mut(fn_args).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, fn_args);
        add_param(&mut m, fn_args, 0);
        add_param(&mut m, fn_args, 1);
        add_param(&mut m, fn_args, 2);
        let args_arr = emit(&mut m, b, Op::GetUnmappedArgs);
        let idx1 = load_number(&mut m, b, 1.0);
        let elem = emit(
            &mut m,
            b,
            Op::LoadPropIdx {
                object: args_arr,
                index: idx1,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(elem) });
    }

    // 2. `readRest(first, ...rest)` declares 1 formal, reads `rest[0].k` via `CopyRestArgs`.
    let fn_rest = add_func_named(&mut m, "readRest");
    m.func_mut(fn_rest).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, fn_rest);
        add_param(&mut m, fn_rest, 0);
        add_param(&mut m, fn_rest, 1);
        add_param(&mut m, fn_rest, 2);
        add_param(&mut m, fn_rest, 3); // `first`
        let rest_arr = emit(&mut m, b, Op::CopyRestArgs { start_index: 1 });
        let idx0 = load_number(&mut m, b, 0.0);
        let item = emit(
            &mut m,
            b,
            Op::LoadPropIdx {
                object: rest_arr,
                index: idx0,
            },
        );
        let v = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: item,
                name: k_sym,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(v) });
    }

    // 3. `noopZeroFormals()` — 0 formals, returns undefined.
    let fn_noop = add_func_named(&mut m, "noopZeroFormals");
    m.func_mut(fn_noop).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, fn_noop);
        add_param(&mut m, fn_noop, 0);
        add_param(&mut m, fn_noop, 1);
        add_param(&mut m, fn_noop, 2);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    add_param(&mut m, main_fn, 0);
    let secret = add_param(&mut m, main_fn, 1);
    let ext_holder = add_param(&mut m, main_fn, 2);
    let clean = load_string(&mut m, entry, "clean");

    // (a) `let r1 = readArguments(clean, secret); print(r1)`
    let ref_args = load_method_ref(&mut m, entry, fn_args);
    let r1 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: ref_args,
            this: None,
            args: vec![clean, secret],
            kind: CallKind::Direct,
        },
    );
    let sink_args = emit_print(&mut m, entry, r1);

    // (b) `let box_obj = {}; box_obj.k = secret; let r2 = readRest(clean, box_obj); print(r2)`
    let box_obj = alloc_object(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: box_obj,
            name: k_sym,
            value: secret,
        },
    );
    let ref_rest = load_method_ref(&mut m, entry, fn_rest);
    let r2 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: ref_rest,
            this: None,
            args: vec![clean, box_obj],
            kind: CallKind::Direct,
        },
    );
    let sink_rest = emit_print(&mut m, entry, r2);

    // (c) `ext_holder.k = secret; noopZeroFormals(ext_holder); Array.isArray(ext_holder); print(ext_holder.k)`
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: ext_holder,
            name: k_sym,
            value: secret,
        },
    );
    let ref_noop = load_method_ref(&mut m, entry, fn_noop);
    let _ = emit(
        &mut m,
        entry,
        Op::Call {
            callee: ref_noop,
            this: None,
            args: vec![ext_holder],
            kind: CallKind::Direct,
        },
    );
    // Also attach field taint directly onto callable `ref_noop.k = secret` and call `ref_noop()`!
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: ref_noop,
            name: k_sym,
            value: secret,
        },
    );
    let _ = emit(
        &mut m,
        entry,
        Op::Call {
            callee: ref_noop,
            this: None,
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    let fn_meta = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: ref_noop,
            name: k_sym,
        },
    );
    let sink_callable_field = emit_print(&mut m, entry, fn_meta);

    // Call an `exclusive` read-only builtin (`Array.isArray(ext_holder)`) and then read `ext_holder.k`.
    let arr_global = try_get_global(&mut m, entry, "Array");
    let is_arr_sym = intern(&mut m, "isArray");
    let is_arr_fn = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: arr_global,
            name: is_arr_sym,
        },
    );
    let _ = emit(
        &mut m,
        entry,
        Op::Call {
            callee: is_arr_fn,
            this: Some(arr_global),
            args: vec![ext_holder],
            kind: CallKind::Dynamic,
        },
    );
    let ext_k_after = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: ext_holder,
            name: k_sym,
        },
    );
    let sink_after_exclusive = emit_print(&mut m, entry, ext_k_after);
    emit_void(&mut m, entry, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let cfg = TaintConfig {
            sources: vec![SourceSpec::FunctionParams {
                name: "func_main_0".to_owned(),
                params: Some(vec![1]),
            }],
            builtin_summaries: true,
            ..std_config_at(rung)
        };
        let report = run_taint(&m, &cfg);
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_args),
            "rung {rung}: excess arg into `GetUnmappedArgs` must hit: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_rest),
            "rung {rung}: heap-field excess arg into `CopyRestArgs` must hit: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_callable_field),
            "rung {rung}: callable field `fn.k` must survive `fn()` BodyStep: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_after_exclusive),
            "rung {rung}: `Local(ext).k` must survive excess BodyStep + read-only `exclusive` summary: {hit_calls:?}"
        );
    }
}

/// `R7`: `globalThis` (`Op::LoadGlobalObject`) peeled through `Op::Mov` chains
/// writes `TaintBase::Global(name)`, passes the interprocedural global reader
/// cone when read ONLY via `globalThis.tok` (no `TryGetGlobal`), and reads back!
#[test]
fn r7_globalthis_load_store_mov_peel_and_interprocedural_reader_cone() {
    let mut m = mk_module();
    let tok_sym = intern(&mut m, "tok");
    let clean_sym = intern(&mut m, "cleanTok");

    let reader = add_func_named(&mut m, "readGlobalThisOnly");
    m.func_mut(reader).unwrap().modifiers = Modifiers::STATIC;
    let sink_hit_iid;
    let sink_clean_iid;
    {
        let b = entry_of(&m, reader);
        add_param(&mut m, reader, 0);
        add_param(&mut m, reader, 1);
        add_param(&mut m, reader, 2);
        let g0 = emit(&mut m, b, Op::LoadGlobalObject);
        let g1 = emit(&mut m, b, Op::Mov { src: g0 });
        let g2 = emit(&mut m, b, Op::Mov { src: g1 });
        let v = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: g2,
                name: tok_sym,
            },
        );
        let vc = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: g2,
                name: clean_sym,
            },
        );
        sink_hit_iid = emit_print(&mut m, b, v);
        sink_clean_iid = emit_print(&mut m, b, vc);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    add_param(&mut m, main_fn, 0);
    let secret = add_param(&mut m, main_fn, 1);

    let g_raw = emit(&mut m, entry, Op::LoadGlobalObject);
    let g_mov = emit(&mut m, entry, Op::Mov { src: g_raw });
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: g_mov,
            name: tok_sym,
            value: secret,
        },
    );
    let rref = load_method_ref(&mut m, entry, reader);
    let _ = emit(
        &mut m,
        entry,
        Op::Call {
            callee: rref,
            this: None,
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let report = run_taint(&m, &std_config_at(rung));
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_hit_iid),
            "rung {rung}: `globalThis.tok` read across interprocedural call must hit: {hit_calls:?}"
        );
        assert!(
            !hit_calls.contains(&sink_clean_iid),
            "rung {rung}: `globalThis.cleanTok` must remain clean: {hit_calls:?}"
        );
    }
}

/// `#private` fields (`StorePrivate`, `DefinePrivate`, `LoadPrivate`):
/// `this.#secret = source(); sink(this.#secret)` propagates across methods at all
/// rungs without colliding with `#clean` (`slot: 1`) or dynamic `this[dynKey]`.
#[test]
fn private_fields_load_store_define_slot_isolation_and_interprocedural() {
    let mut m = mk_module();

    let getter_fn = add_func_named(&mut m, "readPrivates");
    m.func_mut(getter_fn).unwrap().modifiers = Modifiers::STATIC;
    let sink_secret;
    let sink_clean_slot;
    let sink_dyn;
    {
        let b = entry_of(&m, getter_fn);
        add_param(&mut m, getter_fn, 0);
        add_param(&mut m, getter_fn, 1);
        let this_v = add_param(&mut m, getter_fn, 2);

        let v_sec = emit(
            &mut m,
            b,
            Op::LoadPrivate {
                level: 0,
                slot: 0,
                obj: this_v,
            },
        );
        let v_clean = emit(
            &mut m,
            b,
            Op::LoadPrivate {
                level: 0,
                slot: 1,
                obj: this_v,
            },
        );
        let dyn_k = try_get_global(&mut m, b, "DYN_KEY");
        let v_dyn = emit(
            &mut m,
            b,
            Op::LoadPropDyn {
                object: this_v,
                key: dyn_k,
            },
        );
        sink_secret = emit_print(&mut m, b, v_sec);
        sink_clean_slot = emit_print(&mut m, b, v_clean);
        sink_dyn = emit_print(&mut m, b, v_dyn);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    add_param(&mut m, main_fn, 0);
    let secret = add_param(&mut m, main_fn, 1);
    let clean = load_string(&mut m, entry, "clean");

    let inst = alloc_object(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::DefinePrivate {
            level: 0,
            slot: 0,
            obj: inst,
            value: secret,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::DefinePrivate {
            level: 0,
            slot: 1,
            obj: inst,
            value: clean,
        },
    );
    let gref = load_method_ref(&mut m, entry, getter_fn);
    let _ = emit(
        &mut m,
        entry,
        Op::Call {
            callee: gref,
            this: Some(inst),
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let report = run_taint(&m, &std_config_at(rung));
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_secret),
            "rung {rung}: `this.#secret` (slot 0) must propagate across method call: {hit_calls:?}"
        );
        assert!(
            !hit_calls.contains(&sink_clean_slot),
            "rung {rung}: `this.#clean` (slot 1) must NOT collide with slot 0: {hit_calls:?}"
        );
        assert!(
            !hit_calls.contains(&sink_dyn),
            "rung {rung}: `this[dynKey]` must NOT read `#private` slot 0: {hit_calls:?}"
        );
    }
}

/// `R8`: Cross-module `export * as sub from './sub'` (`import { sub } from './barrel'`)
/// and `GetModuleNamespace` (`import * as ns from './sub'`) propagate `ModuleVar`
/// taint AND resolve sink callee names across module boundaries.
#[test]
fn r8_export_star_as_ns_and_get_module_namespace_taint_and_callee_names() {
    let mut m = Module::new();

    let add_esm_record = |m: &mut Module, desc: &str, esm: EsModule| -> ClassId {
        let cid = ClassId::new(m.classes.len() as u32);
        let dsym = m.sym.intern(desc);
        let mut cls = ClassData::new(dsym, dsym);
        cls.es_module = Some(esm);
        m.classes.push(cls);
        cid
    };
    let add_fn_in = |m: &mut Module, cid: ClassId, name: &str| -> FuncId {
        let nsym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(cid, nsym, FunctionKind::Function);
        fd.modifiers = Modifiers::STATIC;
        m.functions.push(fd);
        m.classes[cid.index()].methods.push(fid);
        add_block(m, fid);
        fid
    };

    let sym_secret = m.sym.intern("secretVal");
    let sym_sink_fn = m.sym.intern("customSink");
    let sym_sub_req = m.sym.intern("./sub");
    let sym_barrel_req = m.sym.intern("./barrel");
    let sym_sub_ns = m.sym.intern("sub");
    let sym_star = m.sym.intern("*");

    // Record 0: `Lsub;` exports `secretVal` (slot 0) and `customSink` (slot 1).
    let sub_cid = add_esm_record(
        &mut m,
        "Lsub;",
        EsModule {
            imports: vec![],
            exports: vec![
                ExportDecl::Local {
                    export_name: sym_secret,
                    local_name: sym_secret,
                },
                ExportDecl::Local {
                    export_name: sym_sink_fn,
                    local_name: sym_sink_fn,
                },
            ],
            module_requests: vec![],
        },
    );
    // Record 1: `Lbarrel;` has `export * as sub from './sub'`.
    let barrel_cid = add_esm_record(
        &mut m,
        "Lbarrel;",
        EsModule {
            imports: vec![],
            exports: vec![ExportDecl::Indirect {
                export_name: sym_sub_ns,
                import_name: sym_star,
                module_request: sym_sub_req,
            }],
            module_requests: vec![ModuleRequest {
                specifier: sym_sub_req,
                lazy: false,
            }],
        },
    );
    // Record 2: `Lentry;` imports `{ sub } from './barrel'` AND `* as directNs from './sub'`.
    let entry_cid = add_esm_record(
        &mut m,
        "Lentry;",
        EsModule {
            imports: vec![ImportDecl::Regular {
                local_name: sym_sub_ns,
                import_name: sym_sub_ns,
                module_request: sym_barrel_req,
            }],
            exports: vec![],
            module_requests: vec![
                ModuleRequest {
                    specifier: sym_barrel_req,
                    lazy: false,
                },
                ModuleRequest {
                    specifier: sym_sub_req,
                    lazy: false,
                },
            ],
        },
    );

    // `Lsub::func_main_0`: stores tainted global into slot 0 and sink ref into slot 1.
    let sub_sink_fn = add_fn_in(&mut m, sub_cid, "realCustomSink");
    {
        let sb = entry_of(&m, sub_sink_fn);
        for i in 0..4 {
            add_param(&mut m, sub_sink_fn, i);
        }
        emit_void(&mut m, sb, Op::Return { value: None });
    }
    let sub_main = add_fn_in(&mut m, sub_cid, "func_main_0");
    {
        let b = entry_of(&m, sub_main);
        let src = try_get_global(&mut m, b, "ENV_SECRET");
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: src,
            },
        );
        let sref = load_method_ref(&mut m, b, sub_sink_fn);
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 1,
                value: sref,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let barrel_main = add_fn_in(&mut m, barrel_cid, "func_main_0");
    {
        let b = entry_of(&m, barrel_main);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let entry_main = add_fn_in(&mut m, entry_cid, "func_main_0");
    let call_via_barrel;
    let call_via_ns;
    {
        let b = entry_of(&m, entry_main);
        // Via `import { sub } from './barrel'`: `sub.customSink(sub.secretVal)`
        let sub_obj = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let val1 = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: sub_obj,
                name: sym_secret,
            },
        );
        let sink_callee1 = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: sub_obj,
                name: sym_sink_fn,
            },
        );
        call_via_barrel = push_inst(
            &mut m,
            b,
            Op::Call {
                callee: sink_callee1,
                this: Some(sub_obj),
                args: vec![val1],
                kind: CallKind::Dynamic,
            },
        );

        // Via `GetModuleNamespace(1)` (`./sub`): `directNs.customSink(directNs.secretVal)`
        let ns_obj = emit(&mut m, b, Op::GetModuleNamespace { index: 1 });
        let val2 = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: ns_obj,
                name: sym_secret,
            },
        );
        let sink_callee2 = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: ns_obj,
                name: sym_sink_fn,
            },
        );
        call_via_ns = push_inst(
            &mut m,
            b,
            Op::Call {
                callee: sink_callee2,
                this: Some(ns_obj),
                args: vec![val2],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    for rung in [0u8, 1, 2] {
        let cfg = TaintConfig {
            sources: vec![SourceSpec::GlobalLoad {
                name: "ENV_SECRET".to_owned(),
            }],
            sinks: vec![SinkSpec::Call {
                name: "realCustomSink".to_owned(),
            }],
            builtin_summaries: false,
            alias_rung: rung,
            ..TaintConfig::default()
        };
        let report = run_taint(&m, &cfg);
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&call_via_barrel),
            "rung {rung}: `export * as sub` namespace re-export must propagate taint & callee name: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&call_via_ns),
            "rung {rung}: `GetModuleNamespace` must propagate taint & callee name: {hit_calls:?}"
        );
    }
}

/// `R10`: At Rung 0 and Rung 1 (as well as Rung 2), `PutLexVar { level: 0, slot }`
/// in an outer function matches `GetLexVar { level: 1, slot }` inside a nested
/// closure that pushed its own `NewLexEnv` (and vice versa), without cross-slot
/// false positives.
#[test]
fn r10_rung0_and_rung1_captured_lexvar_level_shift_and_slot_isolation() {
    let mut m = mk_module();

    // `inner` pushes its own `NewLexEnv`, reads outer slot 2 (`level: 1, slot: 2`),
    // reads clean outer slot 9 (`level: 1, slot: 9`), and writes outer slot 3 (`level: 1, slot: 3`).
    let inner = add_func_named(&mut m, "innerClosure");
    m.func_mut(inner).unwrap().modifiers = Modifiers::STATIC;
    let sink_inner_hit;
    let sink_inner_clean;
    {
        let ib = entry_of(&m, inner);
        add_param(&mut m, inner, 0);
        add_param(&mut m, inner, 1);
        add_param(&mut m, inner, 2);
        let arg_sec = add_param(&mut m, inner, 3);
        let _ = emit(
            &mut m,
            ib,
            Op::NewLexEnv {
                num_vars: 2,
                kind: LexEnvKind::Plain,
            },
        );
        let from_outer = emit(
            &mut m,
            ib,
            Op::GetLexVar {
                level: 1,
                slot: 2,
                kind: LexEnvKind::Plain,
            },
        );
        let clean_outer = emit(
            &mut m,
            ib,
            Op::GetLexVar {
                level: 1,
                slot: 9,
                kind: LexEnvKind::Plain,
            },
        );
        sink_inner_hit = emit_print(&mut m, ib, from_outer);
        sink_inner_clean = emit_print(&mut m, ib, clean_outer);
        emit_void(
            &mut m,
            ib,
            Op::PutLexVar {
                level: 1,
                slot: 3,
                value: arg_sec,
                kind: LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, ib, Op::Return { value: None });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    add_param(&mut m, main_fn, 0);
    let secret = add_param(&mut m, main_fn, 1);
    let clean = load_string(&mut m, entry, "clean");

    let _ = emit(
        &mut m,
        entry,
        Op::NewLexEnv {
            num_vars: 10,
            kind: LexEnvKind::Plain,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::PutLexVar {
            level: 0,
            slot: 2,
            value: secret,
            kind: LexEnvKind::Plain,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::PutLexVar {
            level: 0,
            slot: 9,
            value: clean,
            kind: LexEnvKind::Plain,
        },
    );
    let clo = closure_of(&mut m, entry, inner);
    let _ = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo,
            this: None,
            args: vec![secret],
            kind: CallKind::Dynamic,
        },
    );
    // Outer reads slot 3 (`level: 0, slot: 3`) written by `inner` at `level: 1, slot: 3`!
    let back_in_outer = emit(
        &mut m,
        entry,
        Op::GetLexVar {
            level: 0,
            slot: 3,
            kind: LexEnvKind::Plain,
        },
    );
    let sink_outer_back = emit_print(&mut m, entry, back_in_outer);
    emit_void(&mut m, entry, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let report = run_taint(&m, &std_config_at(rung));
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_inner_hit),
            "rung {rung}: outer PutLexVar(0, 2) -> inner GetLexVar(1, 2) must hit: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_outer_back),
            "rung {rung}: inner PutLexVar(1, 3) -> outer GetLexVar(0, 3) must hit: {hit_calls:?}"
        );
        assert!(
            !hit_calls.contains(&sink_inner_clean),
            "rung {rung}: clean slot 9 must NOT be tainted by slot 2/3: {hit_calls:?}"
        );
    }
}

/// `names.rs` & `prototype.rs` diamond DAG sharing (`Phi(v, v)` and shared `v`
/// across two `LoadProp`s), `call_base_value` `Op::Mov` peeling across all member
/// load ops, `gap::resolve_callback_funcs` with `DefineMethod`, and `OhmUrl`.
#[test]
fn names_and_prototype_diamond_dag_sharing_and_call_base_mov_peeling() {
    let mut m = mk_module();
    let cb_fn = add_func_named(&mut m, "myMethodCb");
    {
        let cb_b = entry_of(&m, cb_fn);
        emit_void(&mut m, cb_b, Op::Return { value: None });
    }

    let f = add_func_named(&mut m, "func_main_0");
    let b0 = entry_of(&m, f);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let b_join = add_block(&mut m, f);

    // Shared root `v_glob = TryGetGlobal("console")` and `v_arr = AllocArray` across a diamond `Phi`.
    let v_glob = try_get_global(&mut m, b0, "console");
    let v_arr = alloc_array(&mut m, b0);
    let cond = load_number(&mut m, b0, 1.0);
    emit_void(
        &mut m,
        b0,
        Op::CondBranch {
            cond,
            true_dest: b1,
            false_dest: b2,
        },
    );
    link(&mut m, b0, b1);
    link(&mut m, b0, b2);

    let log_sym = intern(&mut m, "log");
    let warn_sym = intern(&mut m, "warn");
    let lp1 = emit(
        &mut m,
        b1,
        Op::LoadProp {
            object: v_glob,
            name: log_sym,
        },
    );
    let a1 = emit(&mut m, b1, Op::Mov { src: v_arr });
    emit_void(&mut m, b1, Op::Branch { dest: b_join });
    link(&mut m, b1, b_join);

    let lp2 = emit(
        &mut m,
        b2,
        Op::LoadProp {
            object: v_glob,
            name: warn_sym,
        },
    );
    let a2 = emit(&mut m, b2, Op::Mov { src: v_arr });
    emit_void(&mut m, b2, Op::Branch { dest: b_join });
    link(&mut m, b2, b_join);

    let phi_callee = emit(
        &mut m,
        b_join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b1,
                        kind: EdgeKind::Normal,
                    },
                    lp1,
                ),
                (
                    Edge {
                        from: b2,
                        kind: EdgeKind::Normal,
                    },
                    lp2,
                ),
            ],
        },
    );
    let phi_arr = emit(
        &mut m,
        b_join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b1,
                        kind: EdgeKind::Normal,
                    },
                    a1,
                ),
                (
                    Edge {
                        from: b2,
                        kind: EdgeKind::Normal,
                    },
                    a2,
                ),
            ],
        },
    );
    let iter_val = emit(&mut m, b_join, Op::GetIterator { obj: phi_arr });

    // `call_base_value` Mov peeling across LoadProp, LoadPropDyn, LoadPropIdx, LoadPrivate, LoadSuper, and `this`.
    let recv = alloc_object(&mut m, b_join);
    let recv_mov = emit(&mut m, b_join, Op::Mov { src: recv });
    let idx0 = load_number(&mut m, b_join, 0.0);

    let m_prop = emit(
        &mut m,
        b_join,
        Op::LoadProp {
            object: recv_mov,
            name: log_sym,
        },
    );
    let m_prop_mov = emit(&mut m, b_join, Op::Mov { src: m_prop });
    let c_prop = push_inst(
        &mut m,
        b_join,
        Op::Call {
            callee: m_prop_mov,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    let m_dyn = emit(
        &mut m,
        b_join,
        Op::LoadPropDyn {
            object: recv_mov,
            key: idx0,
        },
    );
    let m_dyn_mov = emit(&mut m, b_join, Op::Mov { src: m_dyn });
    let c_dyn = push_inst(
        &mut m,
        b_join,
        Op::Call {
            callee: m_dyn_mov,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    let m_idx = emit(
        &mut m,
        b_join,
        Op::LoadPropIdx {
            object: recv_mov,
            index: idx0,
        },
    );
    let m_idx_mov = emit(&mut m, b_join, Op::Mov { src: m_idx });
    let c_idx = push_inst(
        &mut m,
        b_join,
        Op::Call {
            callee: m_idx_mov,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    let m_priv = emit(
        &mut m,
        b_join,
        Op::LoadPrivate {
            level: 0,
            slot: 0,
            obj: recv_mov,
        },
    );
    let m_priv_mov = emit(&mut m, b_join, Op::Mov { src: m_priv });
    let c_priv = push_inst(
        &mut m,
        b_join,
        Op::Call {
            callee: m_priv_mov,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    let m_sup = emit(
        &mut m,
        b_join,
        Op::LoadSuper {
            key: SuperKey::Name(log_sym),
            this_value: recv_mov,
        },
    );
    let m_sup_mov = emit(&mut m, b_join, Op::Mov { src: m_sup });
    let c_sup = push_inst(
        &mut m,
        b_join,
        Op::Call {
            callee: m_sup_mov,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    let c_this = push_inst(
        &mut m,
        b_join,
        Op::Call {
            callee: v_glob,
            this: Some(recv_mov),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    // `DefineMethod` callback resolution via `gap::resolve_callback_funcs`.
    let def_cb = emit(
        &mut m,
        b_join,
        Op::DefineFunc {
            body: cb_fn,
            captures: vec![],
            length: 0,
        },
    );
    let dm_val = emit(
        &mut m,
        b_join,
        Op::DefineMethod {
            object: recv,
            name: log_sym,
            func: def_cb,
            length: 0,
        },
    );
    emit_void(&mut m, b_join, Op::Return { value: None });

    // 1. Both branches of the diamond `Phi` sharing `v_glob` resolve!
    let cands = callee_name_candidates(&m, phi_callee);
    assert!(
        cands.contains(&"console.log".to_owned()) && cands.contains(&"console.warn".to_owned()),
        "diamond DAG sharing `v_glob` must keep both candidates: {cands:?}"
    );

    // 2. Diamond `Phi(Mov(v_arr), Mov(v_arr))` -> `GetIterator` stays `Iterator` AND `precise == true`!
    let oracle = Oracle::Rung0(Rung0AliasOracle::new(&m));
    let memo = RefCell::new(HashMap::new());
    let resolver = PrototypeResolver::new(&m, &oracle, &memo);
    let fam_arr = resolver.families_of(phi_arr, c_prop);
    assert!(fam_arr.families.contains(&ProtoFamily::Array));
    assert!(
        fam_arr.precise,
        "acyclic diamond Phi(Mov(arr), Mov(arr)) must stay precise"
    );
    let fam_iter = resolver.families_of(iter_val, c_prop);
    assert!(
        fam_iter.families.contains(&ProtoFamily::Iterator),
        "GetIterator over diamond array must resolve Iterator: {fam_iter:?}"
    );

    // 3. `call_base_value` peels `Mov` on both `callee` and `this` across all 5 member-load ops!
    for cid in [c_prop, c_dyn, c_idx, c_priv, c_sup, c_this] {
        assert_eq!(
            call_base_value(&m, m.inst(cid).unwrap()),
            Some(recv),
            "call {cid:?} must recover peeled receiver `recv`"
        );
    }

    // 4. `gap::resolve_callback_funcs` resolves `DefineMethod`!
    let cbs = abcd_taint::gap::resolve_callback_funcs(&m, &oracle, dm_val, c_prop);
    assert_eq!(cbs, vec![cb_fn]);

    // 5. `OhmUrl`-backed `normalize_sdk_specifier`.
    assert_eq!(normalize_sdk_specifier("@ohos:net.http"), "@ohos.net.http");
    assert_eq!(
        normalize_sdk_specifier("@kit:NetworkKit"),
        "@kit.NetworkKit"
    );
    assert_eq!(normalize_sdk_specifier("@hms:core.push"), "@hms.core.push");
    assert_eq!(
        normalize_sdk_specifier("@normalized:N&entry&com.demo&entry/src/main/ets/Api&1.0.0"),
        "entry/src/main/ets/Api"
    );
}

/// `D3`: `EntryModel` steady-state `while (*)` OHOS lifecycle loop discovers
/// order-independent cross-callback taint flows (`onNewWant` / `onBackground`
/// writing `this.pendingWant = want` and `onForeground` reading `this.pendingWant`
/// into `@ohos.hilog.info`, even though `onForeground` precedes `onBackground`
/// in linear declaration order!).
#[test]
fn ohos_entry_model_steady_state_order_independent_lifecycle_flow() {
    let mut m = Module::new();
    let cid = ClassId::new(0);
    let desc = m.sym.intern("LEntryAbility;");
    let ui_ability_sym = m.sym.intern("UIAbility");
    let ability_spec = m.sym.intern("@ohos:app.ability.UIAbility");
    let hilog_spec = m.sym.intern("@ohos:hilog");
    let hilog_sym = m.sym.intern("hilog");
    let default_sym = m.sym.intern("default");
    let entry_sym = m.sym.intern("EntryAbility");
    let info_sym = m.sym.intern("info");
    let pending_sym = m.sym.intern("pendingWant");
    let on_fg_sym = m.sym.intern("onForeground");
    let on_bg_sym = m.sym.intern("onBackground");
    let on_nw_sym = m.sym.intern("onNewWant");

    let mut cls = ClassData::new(desc, desc);
    cls.es_module = Some(EsModule {
        imports: vec![
            ImportDecl::Regular {
                local_name: ui_ability_sym,
                import_name: default_sym,
                module_request: ability_spec,
            },
            ImportDecl::Regular {
                local_name: hilog_sym,
                import_name: default_sym,
                module_request: hilog_spec,
            },
        ],
        exports: vec![ExportDecl::Local {
            export_name: default_sym,
            local_name: entry_sym,
        }],
        module_requests: vec![
            ModuleRequest {
                specifier: ability_spec,
                lazy: false,
            },
            ModuleRequest {
                specifier: hilog_spec,
                lazy: false,
            },
        ],
    });
    m.classes.push(cls);

    let mk_fn = |m: &mut Module, name: &str, kind: FunctionKind| -> FuncId {
        let nsym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(cid, nsym, kind);
        fd.modifiers = Modifiers::STATIC;
        m.functions.push(fd);
        m.classes[0].methods.push(fid);
        add_block(m, fid);
        fid
    };

    let ctor = mk_fn(&mut m, "EntryAbility", FunctionKind::Constructor);
    {
        let b = entry_of(&m, ctor);
        add_param(&mut m, ctor, 0);
        add_param(&mut m, ctor, 1);
        let this_v = add_param(&mut m, ctor, 2);
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(this_v),
            },
        );
    }

    // `onForeground(this)` reads `this.pendingWant` and logs it via `hilog.info`.
    let on_fg = mk_fn(&mut m, "onForeground", FunctionKind::Function);
    let hilog_call_iid;
    {
        let b = entry_of(&m, on_fg);
        add_param(&mut m, on_fg, 0);
        add_param(&mut m, on_fg, 1);
        let this_v = add_param(&mut m, on_fg, 2);
        let pw = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: this_v,
                name: pending_sym,
            },
        );
        let hilog_mod = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 1,
                kind: ModuleVarKind::External,
            },
        );
        let info_fn = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: hilog_mod,
                name: info_sym,
            },
        );
        let dom = load_number(&mut m, b, 0.0);
        let tag = load_string(&mut m, b, "tag");
        hilog_call_iid = push_inst(
            &mut m,
            b,
            Op::Call {
                callee: info_fn,
                this: Some(hilog_mod),
                args: vec![dom, tag, pw],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // `onNewWant(want, launchParam)` runs LATER in linear order and stores `this.pendingWant = want`!
    let on_nw = mk_fn(&mut m, "onNewWant", FunctionKind::Function);
    {
        let b = entry_of(&m, on_nw);
        add_param(&mut m, on_nw, 0);
        add_param(&mut m, on_nw, 1);
        let this_v = add_param(&mut m, on_nw, 2);
        let want_v = add_param(&mut m, on_nw, 3);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: this_v,
                name: pending_sym,
                value: want_v,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let on_bg = mk_fn(&mut m, "onBackground", FunctionKind::Function);
    {
        let b = entry_of(&m, on_bg);
        add_param(&mut m, on_bg, 0);
        add_param(&mut m, on_bg, 1);
        add_param(&mut m, on_bg, 2);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let members_cid = {
        let k1 = push_const(&mut m, Const::String(on_fg_sym));
        let v1 = push_const(
            &mut m,
            Const::MethodRef {
                func: on_fg,
                kind: LitMethodKind::Method,
            },
        );
        let k2 = push_const(&mut m, Const::String(on_bg_sym));
        let v2 = push_const(
            &mut m,
            Const::MethodRef {
                func: on_bg,
                kind: LitMethodKind::Method,
            },
        );
        let k3 = push_const(&mut m, Const::String(on_nw_sym));
        let v3 = push_const(
            &mut m,
            Const::MethodRef {
                func: on_nw,
                kind: LitMethodKind::Method,
            },
        );
        let cnt = push_const(&mut m, Const::Int32(3));
        push_const(
            &mut m,
            Const::ArrayLiteral(vec![k1, v1, k2, v2, k3, v3, cnt]),
        )
    };

    let main_fn = mk_fn(&mut m, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, main_fn);
        let super_cls = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let cls_val = emit(
            &mut m,
            b,
            Op::DefineClass(Box::new(DefineClassData {
                ctor,
                heritage: Some(super_cls),
                members: members_cid,
                member_attrs: vec![
                    MemberAttrs {
                        is_static: false,
                        kind: FunctionKind::Function,
                    },
                    MemberAttrs {
                        is_static: false,
                        kind: FunctionKind::Function,
                    },
                    MemberAttrs {
                        is_static: false,
                        kind: FunctionKind::Function,
                    },
                ],
                count: 0,
            })),
        );
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: cls_val,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let cfg = ohos_preset();
    let report = run_taint(&m, &cfg);
    assert!(
        report.hits.iter().any(|h| h.call == hilog_call_iid),
        "steady-state EntryModel loop must propagate `onNewWant` -> `this.pendingWant` -> `onForeground` hilog sink: {:?}",
        report.hits
    );
}

/// `L6`: `abcd_taint::Endpoint::parse` & `Endpoint::is_valid_flow_source`
/// public crate-root API contract.
#[test]
fn endpoint_parse_reexported_api_contract() {
    let base = abcd_taint::Endpoint::parse("base").expect("base");
    let ret = abcd_taint::Endpoint::parse("return").expect("return");
    let p2 = abcd_taint::Endpoint::parse("param:2").expect("param:2");
    let var1 = abcd_taint::Endpoint::parse("any_param_from:1").expect("any_param_from:1");

    assert_eq!(base, Endpoint::Base);
    assert_eq!(ret, Endpoint::Return);
    assert_eq!(p2, Endpoint::Param(2));
    assert_eq!(var1, Endpoint::AnyParamFrom(1));

    assert!(base.is_valid_flow_source());
    assert!(p2.is_valid_flow_source());
    assert!(var1.is_valid_flow_source());
    assert!(!ret.is_valid_flow_source());
    assert!(abcd_taint::Endpoint::parse("invalid").is_err());
    assert!(abcd_taint::Endpoint::parse("param:99999").is_err());
}

/// `D6`: Direct unit check that `TaintProblem` `*_flow` wrappers and `*_flow_out`
/// zero-copy `FlowSink` produce 100% identical fact sets across normal, call,
/// return, call-to-return, and uncaught-exit edges.
#[test]
fn d6_flow_sink_zero_copy_matches_vec_flow_wrappers_bit_for_bit() {
    use abcd_analysis::dataflow::ifds::{FactId, FlowSink, IfdsProblem};

    let mut m = mk_module();
    let callee = add_func_named(&mut m, "calleeThrow");
    m.func_mut(callee).unwrap().modifiers = Modifiers::STATIC;
    let throw_iid;
    {
        let b = entry_of(&m, callee);
        add_param(&mut m, callee, 0);
        add_param(&mut m, callee, 1);
        add_param(&mut m, callee, 2);
        let p = add_param(&mut m, callee, 3);
        throw_iid = emit_void(&mut m, b, Op::Throw { value: p });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, main_fn);
    add_param(&mut m, main_fn, 0);
    let s = add_param(&mut m, main_fn, 1);
    let mov_s = emit(&mut m, b, Op::Mov { src: s });
    let cref = load_method_ref(&mut m, b, callee);
    let call_res = emit(
        &mut m,
        b,
        Op::Call {
            callee: cref,
            this: None,
            args: vec![mov_s],
            kind: CallKind::Direct,
        },
    );
    let ret_iid = emit_void(
        &mut m,
        b,
        Op::Return {
            value: Some(call_res),
        },
    );

    let cg = CallGraph::build(&m);
    let oracle = Oracle::Rung0(Rung0AliasOracle::new(&m));
    let reg = SummaryRegistry::with_builtins();
    let cfg = std_config_at(0);
    let problem = abcd_taint::TaintProblem::new(&m, &cg, oracle, &reg, &cfg);

    let abcd_ir::ValueDef::Inst(mov_iid) = m.value(mov_s).unwrap().def else {
        panic!("mov");
    };
    let abcd_ir::ValueDef::Inst(call_iid) = m.value(call_res).unwrap().def else {
        panic!("call");
    };

    let expand_sink = |src: &Fact, sink: &mut FlowSink<Fact>| -> Vec<Fact> {
        let mut v = Vec::new();
        if sink.has_pass_through() && !matches!(src, Fact::Zero) {
            v.push(src.clone());
        }
        v.append(sink.facts_mut());
        v
    };

    let src_fact = Fact::of(abcd_taint::TaintFact::local(s));
    let mut v1 = Vec::new();
    let mut s1 = FlowSink::new();
    problem.normal_flow(&m, mov_iid, call_iid, &src_fact, &mut v1);
    problem.normal_flow_out(&m, mov_iid, call_iid, FactId(1), &src_fact, &mut s1);
    assert!(
        s1.has_pass_through(),
        "live local `s` uses zero-copy pass_through"
    );
    assert_eq!(v1, expand_sink(&src_fact, &mut s1));

    let mov_fact = Fact::of(abcd_taint::TaintFact::local(mov_s));
    let mut vc = Vec::new();
    let mut sc = FlowSink::new();
    problem.call_flow(&m, call_iid, callee, &mov_fact, &mut vc);
    problem.call_flow_out(&m, call_iid, callee, FactId(2), &mov_fact, &mut sc);
    assert_eq!(vc, expand_sink(&mov_fact, &mut sc));

    let mut vctr = Vec::new();
    let mut sctr = FlowSink::new();
    problem.call_to_return_flow(&m, call_iid, ret_iid, &src_fact, &mut vctr);
    problem.call_to_return_flow_out(&m, call_iid, ret_iid, FactId(1), &src_fact, &mut sctr);
    assert_eq!(vctr, expand_sink(&src_fact, &mut sctr));

    let callee_p = m.func(callee).unwrap().params[3];
    let throw_fact = Fact::of(abcd_taint::TaintFact::local(callee_p));
    let mut vu = Vec::new();
    let mut su = FlowSink::new();
    problem.call_uncaught_exit_flow(&m, call_iid, callee, throw_iid, &throw_fact, &mut vu);
    problem.call_uncaught_exit_flow_out(
        &m,
        call_iid,
        callee,
        throw_iid,
        FactId(3),
        &throw_fact,
        &mut su,
    );
    assert_eq!(vu, expand_sink(&throw_fact, &mut su));
}
