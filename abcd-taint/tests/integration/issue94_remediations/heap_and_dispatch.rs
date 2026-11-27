//! Issue #94 regressions: concrete-singleton strong-update discipline (`R1`–`R3`, `T1`),
//! separated uncaught-exit edges (`R4`), virtual subclass dispatch (`R5`), `cut_first`,
//! and `BodyStep` variadic/exclusive call handling.

use crate::common::*;
use abcd_ir::consts::Const;
use abcd_ir::module::FunctionKind;
use abcd_ir::op::{DefineClassData, MemberAttrs};
use abcd_ir::{CallKind, Edge, EdgeKind, LitMethodKind, Modifiers, Op};
use abcd_taint::driver::{run_taint, run_taint_full};
use abcd_taint::fact::{Fact, TaintBase};
use abcd_taint::summary::{Endpoint, Summary};
use abcd_taint::{SinkSpec, SourceSpec, TaintConfig};

use super::{emit_print, std_config_at};

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

/// ArkUI / `es2abc` closed-dispatch patterns:
/// - `class Page extends ViewPU` (`ClosedSuperRef::ExternalBase`) with constructor
///   returning `super(...)`, overflow prototype methods attached via
///   `DefineMethod` + `StoreOwnPropName` and `StoreProp`, `@State` accessor via
///   `DefineGetterSetterByValue` on `Page.prototype`, `new Page()` stored in a
///   local container (`arr[0] = page` / `arr[dynIdx] = page`) and passed to clean
///   external `ViewPU.create(page)`, even when an unrelated reflective mutator
///   exists elsewhere in the module.
/// - Static `Log` class invoking `this.join(...args)` via `CallKind::Apply`.
#[test]
fn arkui_viewpu_overflow_proto_accessor_and_static_apply_closed_dispatch() {
    let mut m = mk_module();
    let proto_sym = intern(&mut m, "prototype");
    let clean_sym = intern(&mut m, "cleanHelper");
    let leak_sym = intern(&mut m, "leakHelper");
    let create_sym = intern(&mut m, "create");
    let join_sym = intern(&mut m, "join");
    let info_sym = intern(&mut m, "info");

    // Unrelated dynamic mutator so `inst_mutator_funcs` is non-empty in the module.
    let fn_unrelated_mut = add_func_named(&mut m, "unrelatedMutator");
    m.func_mut(fn_unrelated_mut).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, fn_unrelated_mut);
        add_param(&mut m, fn_unrelated_mut, 0);
        add_param(&mut m, fn_unrelated_mut, 1);
        add_param(&mut m, fn_unrelated_mut, 2);
        let obj = add_param(&mut m, fn_unrelated_mut, 3);
        let dyn_k = add_param(&mut m, fn_unrelated_mut, 4);
        let dyn_fn = add_param(&mut m, fn_unrelated_mut, 5);
        emit_void(
            &mut m,
            b,
            Op::StorePropDyn {
                object: obj,
                key: dyn_k,
                value: dyn_fn,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // `Page` derived constructor: `return super(...)`.
    let page_ctor = add_func_named(&mut m, "Page");
    m.func_mut(page_ctor).unwrap().kind = FunctionKind::Constructor;
    m.func_mut(page_ctor).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, page_ctor);
        let f_obj = add_param(&mut m, page_ctor, 0);
        add_param(&mut m, page_ctor, 1);
        let this_v = add_param(&mut m, page_ctor, 2);
        let sup_res = emit(
            &mut m,
            b,
            Op::Call {
                callee: f_obj,
                this: Some(this_v),
                args: vec![],
                kind: CallKind::Super,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(sup_res),
            },
        );
    }

    // Overflow prototype method 1 (`cleanHelper(x)` -> returns `"ok"`, ignoring `x`).
    let page_clean = add_func_named(&mut m, "Page_cleanHelper");
    m.func_mut(page_clean).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, page_clean);
        add_param(&mut m, page_clean, 0);
        add_param(&mut m, page_clean, 1);
        add_param(&mut m, page_clean, 2);
        add_param(&mut m, page_clean, 3);
        let ok = load_string(&mut m, b, "ok");
        emit_void(&mut m, b, Op::Return { value: Some(ok) });
    }

    // Overflow prototype method 2 (`leakHelper(x)` -> returns `x`).
    let page_leak = add_func_named(&mut m, "Page_leakHelper");
    m.func_mut(page_leak).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, page_leak);
        add_param(&mut m, page_leak, 0);
        add_param(&mut m, page_leak, 1);
        add_param(&mut m, page_leak, 2);
        let arg = add_param(&mut m, page_leak, 3);
        emit_void(&mut m, b, Op::Return { value: Some(arg) });
    }

    // `@State` getter/setter attached via `DefineGetterSetterByValue`.
    let page_get_state = add_func_named(&mut m, "Page_getState");
    m.func_mut(page_get_state).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, page_get_state);
        add_param(&mut m, page_get_state, 0);
        add_param(&mut m, page_get_state, 1);
        add_param(&mut m, page_get_state, 2);
        let z = load_number(&mut m, b, 0.0);
        emit_void(&mut m, b, Op::Return { value: Some(z) });
    }
    let page_set_state = add_func_named(&mut m, "Page_setState");
    m.func_mut(page_set_state).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, page_set_state);
        add_param(&mut m, page_set_state, 0);
        add_param(&mut m, page_set_state, 1);
        add_param(&mut m, page_set_state, 2);
        add_param(&mut m, page_set_state, 3);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Static `Log` class: `static join() { return "tag"; }` and
    // `static info(x) { return this.join(...[x]); }` (`CallKind::Apply`).
    let log_ctor = add_func_named(&mut m, "Log");
    m.func_mut(log_ctor).unwrap().kind = FunctionKind::Constructor;
    m.func_mut(log_ctor).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, log_ctor);
        add_param(&mut m, log_ctor, 0);
        add_param(&mut m, log_ctor, 1);
        let tv = add_param(&mut m, log_ctor, 2);
        emit_void(&mut m, b, Op::Return { value: Some(tv) });
    }
    let log_join = add_func_named(&mut m, "Log_join");
    m.func_mut(log_join).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, log_join);
        add_param(&mut m, log_join, 0);
        add_param(&mut m, log_join, 1);
        add_param(&mut m, log_join, 2);
        add_param(&mut m, log_join, 3);
        let tag = load_string(&mut m, b, "tag");
        emit_void(&mut m, b, Op::Return { value: Some(tag) });
    }
    let log_info = add_func_named(&mut m, "Log_info");
    m.func_mut(log_info).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, log_info);
        add_param(&mut m, log_info, 0);
        add_param(&mut m, log_info, 1);
        let cls_this = add_param(&mut m, log_info, 2);
        let msg = add_param(&mut m, log_info, 3);
        let jf = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: cls_this,
                name: join_sym,
            },
        );
        let spread_buf = emit(&mut m, b, Op::AllocArray { shape: None });
        let idx0 = load_number(&mut m, b, 0.0);
        emit_void(
            &mut m,
            b,
            Op::StoreOwnPropIdx {
                object: spread_buf,
                index: idx0,
                value: msg,
                kind: abcd_ir::OwnStoreKind::OwnProp,
            },
        );
        let joined = emit(
            &mut m,
            b,
            Op::Call {
                callee: jf,
                this: Some(cls_this),
                args: vec![spread_buf],
                kind: CallKind::Apply,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(joined),
            },
        );
    }

    let empty_members = {
        let n_inst = push_const(&mut m, Const::Int32(0));
        push_const(&mut m, Const::ArrayLiteral(vec![n_inst]))
    };
    let log_members = {
        let n_inst = push_const(&mut m, Const::Int32(0));
        let k_join = push_const(&mut m, Const::String(join_sym));
        let v_join = push_const(
            &mut m,
            Const::MethodRef {
                func: log_join,
                kind: LitMethodKind::Method,
            },
        );
        let k_info = push_const(&mut m, Const::String(info_sym));
        let v_info = push_const(
            &mut m,
            Const::MethodRef {
                func: log_info,
                kind: LitMethodKind::Method,
            },
        );
        let n_stat = push_const(&mut m, Const::Int32(2));
        push_const(
            &mut m,
            Const::ArrayLiteral(vec![n_inst, k_join, v_join, k_info, v_info, n_stat]),
        )
    };

    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    add_param(&mut m, main_fn, 0);
    let secret = add_param(&mut m, main_fn, 1);
    let dyn_idx = add_param(&mut m, main_fn, 2);

    let viewpu_base = try_get_global(&mut m, entry, "ViewPU");
    let page_cls = emit(
        &mut m,
        entry,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: page_ctor,
            heritage: Some(viewpu_base),
            members: empty_members,
            member_attrs: vec![],
            count: 0,
        })),
    );
    let proto = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: page_cls,
            name: proto_sym,
        },
    );
    let ref_clean = load_method_ref(&mut m, entry, page_clean);
    let def_clean = emit(
        &mut m,
        entry,
        Op::DefineMethod {
            object: proto,
            name: clean_sym,
            func: ref_clean,
            length: 1,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::StoreOwnPropName {
            object: proto,
            name: clean_sym,
            value: def_clean,
            kind: abcd_ir::OwnStoreKind::DefineProperty,
        },
    );
    let ref_leak = load_method_ref(&mut m, entry, page_leak);
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: proto,
            name: leak_sym,
            value: ref_leak,
        },
    );
    let state_key = load_string(&mut m, entry, "stateVal");
    let ref_get = load_method_ref(&mut m, entry, page_get_state);
    let ref_set = load_method_ref(&mut m, entry, page_set_state);
    let false_cid = push_const(&mut m, Const::Bool(false));
    let false_v = emit(&mut m, entry, Op::LoadConst(false_cid));
    let _ = emit(
        &mut m,
        entry,
        Op::DefineGetterSetterByValue {
            obj: proto,
            key: state_key,
            getter: ref_get,
            setter: ref_set,
            set_name: false_v,
        },
    );

    let log_cls = emit(
        &mut m,
        entry,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: log_ctor,
            heritage: None,
            members: log_members,
            member_attrs: vec![
                MemberAttrs {
                    is_static: true,
                    kind: FunctionKind::Function,
                },
                MemberAttrs {
                    is_static: true,
                    kind: FunctionKind::Function,
                },
            ],
            count: 0,
        })),
    );

    let page = emit(
        &mut m,
        entry,
        Op::Call {
            callee: page_cls,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    // Store `page` into a fresh local array via `StorePropDyn` (`arr[dyn_idx] = page`)
    // and pass `page` to clean external `ViewPU.create(page)`.
    let local_arr = emit(&mut m, entry, Op::AllocArray { shape: None });
    emit_void(
        &mut m,
        entry,
        Op::StorePropDyn {
            object: local_arr,
            key: dyn_idx,
            value: page,
        },
    );
    let create_fn = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: viewpu_base,
            name: create_sym,
        },
    );
    let _ = emit(
        &mut m,
        entry,
        Op::Call {
            callee: create_fn,
            this: Some(viewpu_base),
            args: vec![page],
            kind: CallKind::Dynamic,
        },
    );

    let clean_fn = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: page,
            name: clean_sym,
        },
    );
    let clean_res = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clean_fn,
            this: Some(page),
            args: vec![secret],
            kind: CallKind::Dynamic,
        },
    );
    let sink_page_clean = emit_print(&mut m, entry, clean_res);

    let leak_fn = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: page,
            name: leak_sym,
        },
    );
    let leak_res = emit(
        &mut m,
        entry,
        Op::Call {
            callee: leak_fn,
            this: Some(page),
            args: vec![secret],
            kind: CallKind::Dynamic,
        },
    );
    let sink_page_leak = emit_print(&mut m, entry, leak_res);

    let log_info_fn = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: log_cls,
            name: info_sym,
        },
    );
    let log_res = emit(
        &mut m,
        entry,
        Op::Call {
            callee: log_info_fn,
            this: Some(log_cls),
            args: vec![secret],
            kind: CallKind::Dynamic,
        },
    );
    let sink_log_clean = emit_print(&mut m, entry, log_res);
    emit_void(&mut m, entry, Op::Return { value: None });

    let cfg = TaintConfig {
        sources: vec![SourceSpec::FunctionParams {
            name: "func_main_0".to_owned(),
            params: Some(vec![1]),
        }],
        native_identity: true,
        ..std_config_at(2)
    };
    let report = run_taint(&m, &cfg);
    let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
    assert!(
        hit_calls.contains(&sink_page_leak),
        "closed overflow prototype method `page.leakHelper(secret)` must propagate taint: {hit_calls:?}"
    );
    assert!(
        !hit_calls.contains(&sink_page_clean),
        "closed `ViewPU` subclass overflow prototype method `page.cleanHelper(secret)` must not trigger `native_identity`: {hit_calls:?}"
    );
    assert!(
        !hit_calls.contains(&sink_log_clean),
        "closed static `Log.info(secret)` using `CallKind::Apply` must not trigger `native_identity`: {hit_calls:?}"
    );
}
