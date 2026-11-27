//! Prototype/static class inheritance, `super`, `Array.prototype` mutators & shadows,
//! spread/rest/object-copy ops, private fields, callback escapes, and singleton gating.

use super::*;

#[test]
fn r4_d4_incomplete_ops_arr_push_and_dual_external_internal_callback() {
    let mut m = mk_module();
    let ext_fn = add_func_named(&mut m, "extRegister");
    m.func_mut(ext_fn).unwrap().is_external = true;
    m.func_mut(ext_fn).unwrap().blocks.clear();

    let f_sym = intern(&mut m, "f");
    let push_sym = intern(&mut m, "push");

    // Purely-internal helper: called ONLY from an internal resolved call site.
    let (internal_only, internal_params) = add_static_func(&mut m, "internal_only", 1);
    let internal_read = {
        let b = entry_of(&m, internal_only);
        let r = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: internal_params[3],
                name: f_sym,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(r) });
        r
    };

    // Dual callback: called internally AND passed to `extRegister(dual_cb)`.
    // Also writes a `ctx == None` property + lexical slot read by `inner_reader`
    // and reads `param.f` (which is unknown when invoked externally in `ctx == None`).
    let (inner_reader, _) = add_static_func(&mut m, "inner_reader", 0);
    let inner_loaded_f = {
        let b = entry_of(&m, inner_reader);
        let box_v = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let lf = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: box_v,
                name: f_sym,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(lf) });
        lf
    };

    let (dual_cb, dual_params) = add_static_func(&mut m, "dual_cb", 1);
    let (dual_param_read, dual_default_obj) = {
        let b = entry_of(&m, dual_cb);
        let _env = new_lex_env(&mut m, b);
        let cb_box = alloc_object(&mut m, b);
        let def_obj = alloc_object(&mut m, b);
        // Stored unconditionally (including in `ctx == None` base activation).
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: cb_box,
                name: f_sym,
                value: def_obj,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: cb_box,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let pr = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: dual_params[3],
                name: f_sym,
            },
        );
        let inner_clo = closure_of(&mut m, b, inner_reader);
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(inner_clo),
            },
        );
        (pr, def_obj)
    };

    // Separate module-init store in `ctx == None` read inside an escaped+internal reader.
    let (shared_reader, _) = add_static_func(&mut m, "shared_reader", 0);
    let shared_reader_val = {
        let b = entry_of(&m, shared_reader);
        let holder = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let v = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: holder,
                name: f_sym,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(v) });
        v
    };

    let main = add_func_named(&mut m, "func_main_0");
    let (
        unmodeled_val,
        ext_ret,
        arr_elem_after_push,
        known_elem,
        internal_payload,
        ctx_none_payload,
    ) = {
        let b = entry_of(&m, main);

        // 1) Unmodeled non-primitive op (`GetIterator`) -> `has_unknown == true`.
        let iter_src = alloc_array(&mut m, b);
        let unmodeled = emit(&mut m, b, Op::GetIterator { obj: iter_src });

        // 2) External call return + callback registration -> `has_unknown == true`.
        let ext_callee = load_method_ref(&mut m, b, ext_fn);
        let dual_clo = closure_of(&mut m, b, dual_cb);
        let ext_r = emit(
            &mut m,
            b,
            Op::Call {
                callee: ext_callee,
                this: None,
                args: vec![dual_clo],
                kind: CallKind::Dynamic,
            },
        );

        // 3) `arr.push(x)` (`LoadProp(arr, "push")` + `CallKind::Dynamic` with `this: Some(arr)`) taints `arr` elements.
        let arr = alloc_array(&mut m, b);
        let k_elem = alloc_object(&mut m, b);
        let idx0 = load_number(&mut m, b, 0.0);
        emit_void(
            &mut m,
            b,
            Op::StorePropIdx {
                object: arr,
                index: idx0,
                value: k_elem,
            },
        );
        let pushed_elem = alloc_object(&mut m, b);
        let push_fn = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: arr,
                name: push_sym,
            },
        );
        let _push_ret = emit(
            &mut m,
            b,
            Op::Call {
                callee: push_fn,
                this: Some(arr),
                args: vec![pushed_elem],
                kind: CallKind::Dynamic,
            },
        );
        let elem_after = emit(
            &mut m,
            b,
            Op::LoadPropIdx {
                object: arr,
                index: idx0,
            },
        );

        // 4) Internal call to both `internal_only` and `dual_cb`, plus `ctx == None` lexical holder store.
        let caller_box = alloc_object(&mut m, b);
        let i_payload = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: caller_box,
                name: f_sym,
                value: i_payload,
            },
        );
        let int_clo = closure_of(&mut m, b, internal_only);
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: int_clo,
                this: None,
                args: vec![caller_box],
                kind: CallKind::Dynamic,
            },
        );
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: dual_clo,
                this: None,
                args: vec![caller_box],
                kind: CallKind::Dynamic,
            },
        );

        let _main_env = new_lex_env(&mut m, b);
        let none_holder = alloc_object(&mut m, b);
        let none_payload = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: none_holder,
                name: f_sym,
                value: none_payload,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: none_holder,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let sr_clo = closure_of(&mut m, b, shared_reader);
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: ext_callee,
                this: None,
                args: vec![sr_clo],
                kind: CallKind::Dynamic,
            },
        );
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: sr_clo,
                this: None,
                args: Vec::new(),
                kind: CallKind::Dynamic,
            },
        );

        emit_void(&mut m, b, Op::Return { value: None });
        (
            unmodeled,
            ext_r,
            elem_after,
            k_elem,
            i_payload,
            none_payload,
        )
    };

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let at = InstId::new(0);

    // Unmodeled op & external call return `has_unknown == true`.
    assert!(oracle.query(unmodeled_val, at).has_unknown);
    assert!(oracle.query(ext_ret, at).has_unknown);

    // `arr.push(x)` marks `arr`'s element reads incomplete (`has_unknown == true`) while keeping `known_elem`.
    let arr_ans = oracle.query(arr_elem_after_push, at);
    assert!(
        arr_ans.has_unknown,
        "arr.push(x) must taint receiver elements: {arr_ans:?}"
    );
    assert!(
        arr_ans
            .sites
            .intersects(&oracle.query(known_elem, at).sites)
    );

    // Purely-internal `internal_only` drops `ctx == None` and resolves `param.f` precisely.
    let int_ans = oracle.query(internal_read, at);
    assert!(!int_ans.has_unknown, "{int_ans:?}");
    assert_eq!(int_ans.sites, oracle.query(internal_payload, at).sites);

    // Escaped+internal `dual_cb` retains `ctx == None` (`has_unknown == true` on `param.f`,
    // plus `ctx == None` property/lexical stores remain visible to `inner_reader` & `shared_reader`).
    let dual_ans = oracle.query(dual_param_read, at);
    assert!(
        dual_ans.has_unknown,
        "externally-invocable callback must retain ctx == None unknown param flow: {dual_ans:?}"
    );
    assert!(
        dual_ans
            .sites
            .intersects(&oracle.query(internal_payload, at).sites)
    );

    let inner_ans = oracle.query(inner_loaded_f, at);
    assert!(!inner_ans.has_unknown);
    assert_eq!(inner_ans.sites, oracle.query(dual_default_obj, at).sites);

    let sr_ans = oracle.query(shared_reader_val, at);
    assert!(!sr_ans.has_unknown);
    assert_eq!(sr_ans.sites, oracle.query(ctx_none_payload, at).sites);
}

#[test]
fn r4_h5_spread_copy_props_excluded_keys_apply_super_forward_rest_global_and_split_resume() {
    let mut m = mk_module();
    let a_sym = intern(&mut m, "a");
    let keep_sym = intern(&mut m, "keep");
    let drop_sym = intern(&mut m, "drop");
    let f_sym = intern(&mut m, "f");
    let g_sym = intern(&mut m, "globalProp");

    // 1) `Apply` spread callee: returns formal 0 (`params[3]`).
    let (apply_fn, apply_params) = add_static_func(&mut m, "apply_fn", 1);
    {
        let b = entry_of(&m, apply_fn);
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(apply_params[3]),
            },
        );
    }

    // 2) `SuperForwardAllArgs` derived constructor -> base constructor.
    let (base_ctor, base_params) = add_static_func(&mut m, "BaseCtor", 1);
    {
        let b = entry_of(&m, base_ctor);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: base_params[2],
                name: f_sym,
                value: base_params[3],
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let (sub_ctor, sub_params) = add_static_func(&mut m, "SubCtor", 1);
    {
        let b = entry_of(&m, sub_ctor);
        let super_ret = emit(
            &mut m,
            b,
            Op::Call {
                callee: sub_params[0],
                this: None,
                args: vec![sub_params[2]],
                kind: CallKind::SuperForwardAllArgs,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(super_ret),
            },
        );
    }

    // 3) `CopyRestArgs { start_index: 1 }` skipping formal 0 and capturing formal 1.
    let (rest_fn, _rest_params) = add_static_func(&mut m, "rest_fn", 2);
    let rest_arr_val = {
        let b = entry_of(&m, rest_fn);
        let rest_arr = emit(&mut m, b, Op::CopyRestArgs { start_index: 1 });
        let r_idx0 = load_number(&mut m, b, 0.0);
        let elem0 = emit(
            &mut m,
            b,
            Op::LoadPropIdx {
                object: rest_arr,
                index: r_idx0,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(elem0) });
        rest_arr
    };

    // 4) Split-block `ResumeGenerator` across protected `b0 -> b1 -> b2` try blocks.
    let (async_fn, _) = add_static_func(&mut m, "split_async", 0);
    let (awaited_obj, resumed_val) = {
        let b0 = entry_of(&m, async_fn);
        let b1 = add_block(&mut m, async_fn);
        let b2 = add_block(&mut m, async_fn);
        let bcatch = add_block(&mut m, async_fn);

        let genobj = emit(&mut m, b0, Op::AsyncFunctionEnter);
        let aw_obj = alloc_object(&mut m, b0);
        let aw = emit(
            &mut m,
            b0,
            Op::AwaitUncaught {
                funcobj: genobj,
                value: aw_obj,
            },
        );
        emit_void(&mut m, b0, Op::Branch { dest: b1 });

        let _ = emit(&mut m, b1, Op::SuspendGenerator { genobj, value: aw });
        emit_void(&mut m, b1, Op::Branch { dest: b2 });

        let resumed = emit(&mut m, b2, Op::ResumeGenerator { genobj });
        emit_void(
            &mut m,
            b2,
            Op::Return {
                value: Some(resumed),
            },
        );

        let exc = add_exception_param(&mut m, bcatch);
        emit_void(&mut m, bcatch, Op::Return { value: Some(exc) });

        link(&mut m, b0, b1);
        link(&mut m, b1, b2);
        add_try(&mut m, async_fn, vec![b0, b1, b2], bcatch, exc);
        (aw_obj, resumed)
    };

    let main = add_func_named(&mut m, "func_main_0");
    let (
        spread_elem,
        spread_loaded,
        copied_val,
        copied_loaded,
        kept_val,
        excl_val,
        rest_obj,
        rest_keep_loaded,
        rest_drop_loaded,
        apply_arg,
        apply_res,
        super_arg,
        super_loaded_f,
        skipped_arg,
        kept_rest_arg,
        rest_call_res,
        global_obj,
        global_val,
        global_prop_loaded,
        try_get_global_loaded,
    ) = {
        let b = entry_of(&m, main);

        // `ArraySpread`: `src_arr[0] -> dst_arr[..]`.
        let src_arr = alloc_array(&mut m, b);
        let s_elem = alloc_object(&mut m, b);
        let zero = load_number(&mut m, b, 0.0);
        emit_void(
            &mut m,
            b,
            Op::StorePropIdx {
                object: src_arr,
                index: zero,
                value: s_elem,
            },
        );
        let dst_arr = alloc_array(&mut m, b);
        let _ = emit(
            &mut m,
            b,
            Op::ArraySpread {
                dst: dst_arr,
                index: zero,
                src: src_arr,
            },
        );
        let s_loaded = emit(
            &mut m,
            b,
            Op::LoadPropIdx {
                object: dst_arr,
                index: zero,
            },
        );

        // `CopyDataProps`: `src_obj.a -> dst_obj.a`.
        let src_obj = alloc_object(&mut m, b);
        let c_val = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: src_obj,
                name: a_sym,
                value: c_val,
            },
        );
        let dst_obj = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::CopyDataProps {
                dst: dst_obj,
                src: src_obj,
            },
        );
        let c_loaded = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: dst_obj,
                name: a_sym,
            },
        );

        // `CreateObjectWithExcludedKeys`: copies `keep`, excludes `drop`.
        let full_obj = alloc_object(&mut m, b);
        let k_val = alloc_object(&mut m, b);
        let x_val = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: full_obj,
                name: keep_sym,
                value: k_val,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: full_obj,
                name: drop_sym,
                value: x_val,
            },
        );
        let drop_key = load_string(&mut m, b, "drop");
        let r_obj = emit(
            &mut m,
            b,
            Op::CreateObjectWithExcludedKeys {
                obj: full_obj,
                keys: vec![drop_key],
            },
        );
        let rk_loaded = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: r_obj,
                name: keep_sym,
            },
        );
        let rd_loaded = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: r_obj,
                name: drop_sym,
            },
        );

        // `CallKind::Apply` spread args.
        let apply_arr = alloc_array(&mut m, b);
        let a_arg = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::StorePropIdx {
                object: apply_arr,
                index: zero,
                value: a_arg,
            },
        );
        let apply_clo = closure_of(&mut m, b, apply_fn);
        let a_res = emit(
            &mut m,
            b,
            Op::Call {
                callee: apply_clo,
                this: None,
                args: vec![apply_arr],
                kind: CallKind::Apply,
            },
        );

        // `SuperForwardAllArgs` class construction.
        let empty_mem = m.consts.push_array(Vec::new());
        let base_cls = emit(
            &mut m,
            b,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: base_ctor,
                heritage: None,
                members: empty_mem,
                member_attrs: Vec::new(),
                count: 0,
            })),
        );
        let sub_cls = emit(
            &mut m,
            b,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: sub_ctor,
                heritage: Some(base_cls),
                members: empty_mem,
                member_attrs: Vec::new(),
                count: 0,
            })),
        );
        let sup_arg = alloc_object(&mut m, b);
        let sub_inst = emit(
            &mut m,
            b,
            Op::Call {
                callee: sub_cls,
                this: None,
                args: vec![sup_arg],
                kind: CallKind::New,
            },
        );
        let sup_loaded = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: sub_inst,
                name: f_sym,
            },
        );

        // `CopyRestArgs`.
        let sk_arg = alloc_object(&mut m, b);
        let kr_arg = alloc_object(&mut m, b);
        let rest_clo = closure_of(&mut m, b, rest_fn);
        let r_call_res = emit(
            &mut m,
            b,
            Op::Call {
                callee: rest_clo,
                this: None,
                args: vec![sk_arg, kr_arg],
                kind: CallKind::Dynamic,
            },
        );

        // `LoadGlobalObject` <-> `Ptr::Global` bridge.
        let g_obj = emit(&mut m, b, Op::LoadGlobalObject);
        let g_val = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: g_obj,
                name: g_sym,
                value: g_val,
            },
        );
        let gp_loaded = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: g_obj,
                name: g_sym,
            },
        );
        let tgg_loaded = emit(
            &mut m,
            b,
            Op::TryGetGlobal {
                name: g_sym,
                default: None,
            },
        );

        // Trigger `async_fn` too.
        let async_clo = closure_of(&mut m, b, async_fn);
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: async_clo,
                this: None,
                args: Vec::new(),
                kind: CallKind::Dynamic,
            },
        );

        emit_void(&mut m, b, Op::Return { value: None });
        (
            s_elem, s_loaded, c_val, c_loaded, k_val, x_val, r_obj, rk_loaded, rd_loaded, a_arg,
            a_res, sup_arg, sup_loaded, sk_arg, kr_arg, r_call_res, g_obj, g_val, gp_loaded,
            tgg_loaded,
        )
    };

    let out = run(&m);
    assert!(!out.stats().capped);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let at = InstId::new(0);

    // ArraySpread
    let spread_ans = oracle.query(spread_loaded, at);
    assert!(!spread_ans.has_unknown);
    assert_eq!(spread_ans.sites, oracle.query(spread_elem, at).sites);

    // CopyDataProps
    let copy_ans = oracle.query(copied_loaded, at);
    assert!(!copy_ans.has_unknown);
    assert_eq!(copy_ans.sites, oracle.query(copied_val, at).sites);

    // CreateObjectWithExcludedKeys
    let rest_obj_ans = oracle.query(rest_obj, at);
    assert!(rest_obj_ans.is_single_precise());
    let keep_ans = oracle.query(rest_keep_loaded, at);
    assert!(!keep_ans.has_unknown);
    assert_eq!(keep_ans.sites, oracle.query(kept_val, at).sites);
    let drop_ans = oracle.query(rest_drop_loaded, at);
    assert!(
        !drop_ans.sites.intersects(&oracle.query(excl_val, at).sites),
        "excluded key must not propagate: {drop_ans:?}"
    );
    assert!(drop_ans.has_unknown && drop_ans.sites.is_empty());

    // CallKind::Apply spread args
    let apply_ans = oracle.query(apply_res, at);
    assert!(!apply_ans.has_unknown);
    assert_eq!(apply_ans.sites, oracle.query(apply_arg, at).sites);

    // CallKind::SuperForwardAllArgs:
    // - Whole-module (`roots = None`): 2-hop `main -> SubCtor -> BaseCtor` forwards `super_arg`
    //   into `BaseCtor`'s formal alongside `(SubCtor, None)`'s unrecorded base formal.
    // - Rooted at `main` (`Some(&[main])`): `(SubCtor, None)` is not seeded, so `sub_inst.f`
    //   resolves single-precisely (`!has_unknown`) to `super_arg`.
    let super_ans = oracle.query(super_loaded_f, at);
    assert_eq!(super_ans.sites, oracle.query(super_arg, at).sites);
    let links = ModuleLinkTable::build(&m);
    let base_cg = CallGraph::build_with_links(&m, &links);
    let (_, rooted_tables, rooted_stats) =
        analyze_with_links_and_roots(&m, &links, &base_cg, &PtaConfig::default(), Some(&[main]))
            .into_parts();
    let rooted_oracle = Rung2AliasOracle::new(&m, rooted_tables, rooted_stats);
    let rooted_super = rooted_oracle.query(super_loaded_f, at);
    assert!(!rooted_super.has_unknown, "{rooted_super:?}");
    assert_eq!(rooted_super.sites, rooted_oracle.query(super_arg, at).sites);

    // CopyRestArgs
    let rest_arr_ans = oracle.query(rest_arr_val, at);
    assert!(!rest_arr_ans.has_unknown && !rest_arr_ans.sites.is_empty());
    let rest_res_ans = oracle.query(rest_call_res, at);
    assert!(!rest_res_ans.has_unknown);
    assert_eq!(rest_res_ans.sites, oracle.query(kept_rest_arg, at).sites);
    assert!(
        !rest_res_ans
            .sites
            .intersects(&oracle.query(skipped_arg, at).sites)
    );

    // LoadGlobalObject
    let g_obj_ans = oracle.query(global_obj, at);
    assert!(g_obj_ans.has_unknown && g_obj_ans.sites.is_empty());
    let gp_ans = oracle.query(global_prop_loaded, at);
    assert!(!gp_ans.has_unknown);
    assert_eq!(gp_ans.sites, oracle.query(global_val, at).sites);
    let tgg_ans = oracle.query(try_get_global_loaded, at);
    assert!(tgg_ans.has_unknown);
    assert_eq!(tgg_ans.sites, oracle.query(global_val, at).sites);

    // Split-block ResumeGenerator
    let resume_ans = oracle.query(resumed_val, at);
    assert!(!resume_ans.has_unknown, "{resume_ans:?}");
    assert_eq!(resume_ans.sites, oracle.query(awaited_obj, at).sites);
}

#[test]
fn array_proto_mutator_preserves_own_named_method_shadow() {
    // `const a = []; a.push(x); a.pop = () => 7; a.pop()` (`e7-own-method-shadow`):
    // `a.push(x)` taints `a[Slot::Index]` (`a[0]` has `has_unknown == true` while
    // retaining `x`), without poisoning `Slot::Dynamic` or `Slot::Named("pop")`, so
    // `a.pop` resolves precisely (`has_unknown == false`, `resolution_complete == true`).
    let mut m = mk_module();
    let push_sym = intern(&mut m, "push");
    let pop_sym = intern(&mut m, "pop");

    let (shadow_pop, _) = add_static_func(&mut m, "shadow_pop", 0);
    {
        let b = entry_of(&m, shadow_pop);
        let seven = load_number(&mut m, b, 7.0);
        emit_void(&mut m, b, Op::Return { value: Some(seven) });
    }

    let main = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, main);
    let a = alloc_array(&mut m, b);
    let x = alloc_object(&mut m, b);

    let push_fn = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: a,
            name: push_sym,
        },
    );
    let _push_ret = emit(
        &mut m,
        b,
        Op::Call {
            callee: push_fn,
            this: Some(a),
            args: vec![x],
            kind: CallKind::Dynamic,
        },
    );

    let pop_clo = closure_of(&mut m, b, shadow_pop);
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: a,
            name: pop_sym,
            value: pop_clo,
        },
    );

    let pop_fn = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: a,
            name: pop_sym,
        },
    );
    let pop_call = push_inst(
        &mut m,
        b,
        Op::Call {
            callee: pop_fn,
            this: Some(a),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    let zero = load_number(&mut m, b, 0.0);
    let elem0 = emit(
        &mut m,
        b,
        Op::LoadPropIdx {
            object: a,
            index: zero,
        },
    );
    emit_void(&mut m, b, Op::Return { value: None });

    let out = run(&m);
    let pop_edge = out.graph().edge_at(pop_call).expect("pop call edge");
    assert_eq!(pop_edge.targets, CallTargets::Resolved(vec![shadow_pop]));
    assert!(
        pop_edge.resolution_complete,
        "own method shadow call must stay complete: {pop_edge:?}"
    );

    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let at = InstId::new(0);

    let elem_ans = oracle.query(elem0, at);
    assert!(
        elem_ans.has_unknown,
        "a[0] must stay conservative after a.push(x): {elem_ans:?}"
    );
    assert!(
        elem_ans.sites.intersects(&oracle.query(x, at).sites),
        "pushed argument x must flow into a[Slot::Index]: {elem_ans:?}"
    );

    let pop_ans = oracle.query(pop_fn, at);
    assert!(
        !pop_ans.has_unknown,
        "LoadProp(a, \"pop\") must resolve precisely: {pop_ans:?}"
    );
    assert_eq!(pop_ans.sites, oracle.query(pop_clo, at).sites);
}

#[test]
fn prototype_inheritance_super_unmapped_args_lex_compat_private_escapes_and_singleton_gate() {
    use crate::dataflow::heap::{UpdateKind, update_kind};

    let inst_of = |m: &Module, v: ValueId| -> InstId {
        match m.value(v).unwrap().def {
            abcd_ir::ValueDef::Inst(i) => i,
            other => panic!("expected inst: {other:?}"),
        }
    };

    let mut m = mk_module();
    let proto_sym = intern(&mut m, "prototype");
    let inh_sym = intern(&mut m, "inheritedMethod");
    let over_sym = intern(&mut m, "overridden");
    let stat_sym = intern(&mut m, "staticFactory");
    let late_sym = intern(&mut m, "lateProtoProp");
    let tag_sym = intern(&mut m, "tag");

    // 1. Prototype & static inheritance (`class Sub extends Base`):
    //    - `Base`: `inheritedMethod`, `overridden` (`Base` version), `static staticFactory`,
    //      plus `Base.prototype.lateProtoProp = late_obj` attached dynamically!
    //    - `Sub extends Base`: overrides `overridden` (calling `super.overridden()`),
    //      forwards `super()` in constructor.
    let (base_ctor, _) = add_static_func(&mut m, "Base", 0);
    {
        let b_bc = entry_of(&m, base_ctor);
        emit_void(&mut m, b_bc, Op::Return { value: None });
    }

    let (base_inh, _) = add_static_func(&mut m, "Base_inh", 0);
    let base_inh_obj = {
        let b_bi = entry_of(&m, base_inh);
        let o = alloc_object(&mut m, b_bi);
        emit_void(&mut m, b_bi, Op::Return { value: Some(o) });
        o
    };

    let (base_over, _) = add_static_func(&mut m, "Base_over", 0);
    let base_over_obj = {
        let b_bo = entry_of(&m, base_over);
        let o = alloc_object(&mut m, b_bo);
        emit_void(&mut m, b_bo, Op::Return { value: Some(o) });
        o
    };

    let (base_stat, _) = add_static_func(&mut m, "Base_stat", 0);
    let base_stat_obj = {
        let b_bs = entry_of(&m, base_stat);
        let o = alloc_object(&mut m, b_bs);
        emit_void(&mut m, b_bs, Op::Return { value: Some(o) });
        o
    };

    let (sub_ctor, sub_ctor_p) = add_static_func(&mut m, "Sub", 0);
    let call_super_ctor = {
        let b = entry_of(&m, sub_ctor);
        let c = push_inst(
            &mut m,
            b,
            Op::Call {
                callee: sub_ctor_p[0],
                this: None,
                args: Vec::new(),
                kind: CallKind::Super,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
        c
    };

    let (sub_over, sub_over_p) = add_static_func(&mut m, "Sub_over", 0);
    let (call_super_prop, super_ret_val) = {
        let b = entry_of(&m, sub_over);
        let sup_fn = emit(
            &mut m,
            b,
            Op::LoadSuper {
                key: abcd_ir::SuperKey::Name(over_sym),
                this_value: sub_over_p[2],
            },
        );
        let sr = emit(
            &mut m,
            b,
            Op::Call {
                callee: sup_fn,
                this: Some(sub_over_p[2]),
                args: Vec::new(),
                kind: CallKind::Dynamic,
            },
        );
        let call_sp = inst_of(&m, sr);
        emit_void(&mut m, b, Op::Return { value: Some(sr) });
        (call_sp, sr)
    };

    // 2. `GetUnmappedArgs` with ZERO declared formals receiving excess positional args!
    let (var_fn, _) = add_static_func(&mut m, "var_fn", 0);
    let var_elem_read = {
        let b = entry_of(&m, var_fn);
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
        elem
    };

    // 3. Lexical variable context/activation compatibility:
    //    - `set_lex(v)` is called ONLY internally (`set_lex(child_written_obj)`);
    //      its write into `func_main_0`'s `NewLexEnv` MUST NOT be dropped even though
    //      `func_main_0` has `recorded_funcs == false`, AND its phantom `None` base
    //      activation MUST NOT pollute `func_main_0`'s `GetLexVar` with `Obj::Unknown`!
    //    - `dead_lex_writer(p)` is NEVER called and NEVER escaped; its `PutLexVar(p)`
    //      MUST NOT pollute `func_main_0`'s `GetLexVar` with `Obj::Unknown`!
    let (set_lex, set_lex_p) = add_static_func(&mut m, "set_lex", 1);
    {
        let b = entry_of(&m, set_lex);
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: set_lex_p[3],
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let (dead_lex, dead_lex_p) = add_static_func(&mut m, "dead_lex", 1);
    {
        let b = entry_of(&m, dead_lex);
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: dead_lex_p[3],
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // 4. Private field closure & getter closure escape:
    //    - `priv_cb(p)` stored into private field `(0, 0)` on an `Obj::Unknown`
    //      host object -> `priv_cb` must be marked externally invocable (`p` is `Unknown`),
    //      while private field `(0, 1)` on a local `AllocObject` resolves precisely!
    //    - `getter_cb(p)` attached via `DefineGetterSetterByValue` on a local `AllocObject`
    //      -> `getter_cb` must ALSO be marked externally invocable!
    let (priv_cb, priv_cb_p) = add_static_func(&mut m, "priv_cb", 1);
    let priv_cb_param = {
        let b = entry_of(&m, priv_cb);
        emit_void(&mut m, b, Op::Return { value: None });
        priv_cb_p[3]
    };

    let (getter_cb, getter_cb_p) = add_static_func(&mut m, "getter_cb", 1);
    let getter_cb_param = {
        let b = entry_of(&m, getter_cb);
        emit_void(&mut m, b, Op::Return { value: None });
        getter_cb_p[3]
    };

    // 5. Multi-call helper allocating an object: `query` has `sites.len() == 1`,
    //    but `site_info_at` MUST gate strong updates (`UpdateKind::Weak`)!
    let (multi_alloc, _) = add_static_func(&mut m, "multi_alloc", 0);
    let multi_obj = {
        let b = entry_of(&m, multi_alloc);
        let o = alloc_object(&mut m, b);
        emit_void(&mut m, b, Op::Return { value: Some(o) });
        o
    };

    let main = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, main);

    let c_inh_s = m.consts.intern(Const::String(inh_sym));
    let c_inh_m = m.consts.intern(Const::method_ref(base_inh));
    let c_over_s = m.consts.intern(Const::String(over_sym));
    let c_bover_m = m.consts.intern(Const::method_ref(base_over));
    let c_stat_s = m.consts.intern(Const::String(stat_sym));
    let c_stat_m = m.consts.intern(Const::method_ref(base_stat));
    let base_mem = m.consts.push_array(vec![
        c_inh_s, c_inh_m, c_over_s, c_bover_m, c_stat_s, c_stat_m,
    ]);
    let base_cls = emit(
        &mut m,
        b,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: base_ctor,
            heritage: None,
            members: base_mem,
            member_attrs: vec![
                abcd_ir::MemberAttrs {
                    is_static: false,
                    kind: abcd_ir::FunctionKind::Function,
                },
                abcd_ir::MemberAttrs {
                    is_static: false,
                    kind: abcd_ir::FunctionKind::Function,
                },
                abcd_ir::MemberAttrs {
                    is_static: true,
                    kind: abcd_ir::FunctionKind::Function,
                },
            ],
            count: 2,
        })),
    );

    let c_sover_m = m.consts.intern(Const::method_ref(sub_over));
    let sub_mem = m.consts.push_array(vec![c_over_s, c_sover_m]);
    // Pass `base_cls` through a `Mov` to mimic dynamic expression evaluation.
    let heritage_val = emit(&mut m, b, Op::Mov { src: base_cls });
    let sub_cls = emit(
        &mut m,
        b,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: sub_ctor,
            heritage: Some(heritage_val),
            members: sub_mem,
            member_attrs: vec![abcd_ir::MemberAttrs {
                is_static: false,
                kind: abcd_ir::FunctionKind::Function,
            }],
            count: 1,
        })),
    );

    // Construct `new Sub()` BEFORE mutating `Base.prototype.lateProtoProp` to test
    // bucket re-arm propagation down `Base.prototype -> Sub.prototype -> sub_inst`!
    let sub_inst = emit(
        &mut m,
        b,
        Op::Call {
            callee: sub_cls,
            this: None,
            args: Vec::new(),
            kind: CallKind::New,
        },
    );
    let base_proto = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: base_cls,
            name: proto_sym,
        },
    );
    let late_obj = alloc_object(&mut m, b);
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: base_proto,
            name: late_sym,
            value: late_obj,
        },
    );

    let inh_callee = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: sub_inst,
            name: inh_sym,
        },
    );
    let inh_ret = emit(
        &mut m,
        b,
        Op::Call {
            callee: inh_callee,
            this: Some(sub_inst),
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );
    let call_inh = inst_of(&m, inh_ret);

    let over_callee = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: sub_inst,
            name: over_sym,
        },
    );
    let over_ret = emit(
        &mut m,
        b,
        Op::Call {
            callee: over_callee,
            this: Some(sub_inst),
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );
    let call_over = inst_of(&m, over_ret);

    let stat_callee = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: sub_cls,
            name: stat_sym,
        },
    );
    let stat_ret = emit(
        &mut m,
        b,
        Op::Call {
            callee: stat_callee,
            this: Some(sub_cls),
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );
    let call_stat = inst_of(&m, stat_ret);

    let late_read = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: sub_inst,
            name: late_sym,
        },
    );

    // Excess positional args into `var_fn(arg0, arg1)` (`0` declared formals).
    let var_clo = closure_of(&mut m, b, var_fn);
    let ex0 = alloc_object(&mut m, b);
    let ex1 = alloc_object(&mut m, b);
    let var_ret = emit(
        &mut m,
        b,
        Op::Call {
            callee: var_clo,
            this: None,
            args: vec![ex0, ex1],
            kind: CallKind::Dynamic,
        },
    );

    // Lexical environment in `func_main_0` written by `func_main_0` AND `set_lex`,
    // with `dead_lex` defined but never called.
    let _env = new_lex_env(&mut m, b);
    let lex_init_obj = alloc_object(&mut m, b);
    let lex_child_obj = alloc_object(&mut m, b);
    emit_void(
        &mut m,
        b,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: lex_init_obj,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let set_lex_clo = closure_of(&mut m, b, set_lex);
    let _dead_lex_clo = closure_of(&mut m, b, dead_lex);
    let _ = emit(
        &mut m,
        b,
        Op::Call {
            callee: set_lex_clo,
            this: None,
            args: vec![lex_child_obj],
            kind: CallKind::Dynamic,
        },
    );
    let lex_read = emit(
        &mut m,
        b,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );

    // Private fields & getter escapes.
    let host_unk = emit(
        &mut m,
        b,
        Op::TryGetGlobal {
            name: tag_sym,
            default: None,
        },
    );
    let priv_clo = closure_of(&mut m, b, priv_cb);
    let int_call_arg = alloc_object(&mut m, b);
    let _ = emit(
        &mut m,
        b,
        Op::Call {
            callee: priv_clo,
            this: None,
            args: vec![int_call_arg],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::StorePrivate {
            obj: host_unk,
            level: 0,
            slot: 0,
            value: priv_clo,
        },
    );

    let local_priv_holder = alloc_object(&mut m, b);
    let priv_val_obj = alloc_object(&mut m, b);
    emit_void(
        &mut m,
        b,
        Op::DefinePrivate {
            obj: local_priv_holder,
            level: 0,
            slot: 1,
            value: priv_val_obj,
        },
    );
    let priv_loaded = emit(
        &mut m,
        b,
        Op::LoadPrivate {
            obj: local_priv_holder,
            level: 0,
            slot: 1,
        },
    );

    let getter_clo = closure_of(&mut m, b, getter_cb);
    let _ = emit(
        &mut m,
        b,
        Op::Call {
            callee: getter_clo,
            this: None,
            args: vec![int_call_arg],
            kind: CallKind::Dynamic,
        },
    );
    let key_str = load_number(&mut m, b, 0.0);
    let _ = emit(
        &mut m,
        b,
        Op::DefineGetterSetterByValue {
            obj: local_priv_holder,
            key: key_str,
            getter: getter_clo,
            setter: key_str,
            set_name: key_str,
        },
    );

    // Call `multi_alloc` twice so `multi_obj` is NOT a concrete runtime singleton.
    let ma_clo = closure_of(&mut m, b, multi_alloc);
    let _ = emit(
        &mut m,
        b,
        Op::Call {
            callee: ma_clo,
            this: None,
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );
    let _ = emit(
        &mut m,
        b,
        Op::Call {
            callee: ma_clo,
            this: None,
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );
    let ret_iid = emit_void(&mut m, b, Op::Return { value: None });

    let out = run(&m);
    let cg = out.graph();

    // Inherited prototype method, subclass override (without Base pollution!),
    // `super.overridden()` -> `Base_over`, `Sub.staticFactory()` -> `Base_stat`,
    // and `super()` -> `Base`!
    assert_eq!(
        cg.edge_at(call_inh).unwrap().targets,
        CallTargets::Resolved(vec![base_inh])
    );
    assert_eq!(
        cg.edge_at(call_over).unwrap().targets,
        CallTargets::Resolved(vec![sub_over]),
        "Sub.overridden must shadow Base.overridden on Sub instances"
    );
    assert_eq!(
        cg.edge_at(call_super_prop).unwrap().targets,
        CallTargets::Resolved(vec![base_over])
    );
    assert_eq!(
        cg.edge_at(call_stat).unwrap().targets,
        CallTargets::Resolved(vec![base_stat])
    );
    assert_eq!(
        cg.edge_at(call_super_ctor).unwrap().targets,
        CallTargets::Resolved(vec![base_ctor])
    );

    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);

    assert_eq!(
        oracle.query(inh_ret, ret_iid).sites,
        oracle.query(base_inh_obj, ret_iid).sites
    );
    assert_eq!(
        oracle.query(super_ret_val, ret_iid).sites,
        oracle.query(base_over_obj, ret_iid).sites
    );
    assert_eq!(
        oracle.query(over_ret, ret_iid).sites,
        oracle.query(base_over_obj, ret_iid).sites
    );
    assert_eq!(
        oracle.query(stat_ret, ret_iid).sites,
        oracle.query(base_stat_obj, ret_iid).sites
    );
    assert_eq!(
        oracle.query(late_read, ret_iid).sites,
        oracle.query(late_obj, ret_iid).sites
    );

    // `GetUnmappedArgs` receives both excess actuals `{ex0, ex1}` with `has_unknown == false`!
    let var_ans = oracle.query(var_ret, ret_iid);
    assert!(!var_ans.has_unknown, "{var_ans:?}");
    let mut expected_var = oracle.query(ex0, ret_iid).sites;
    expected_var.union_with(&oracle.query(ex1, ret_iid).sites);
    assert_eq!(var_ans.sites, expected_var);
    assert_eq!(oracle.query(var_elem_read, ret_iid).sites, expected_var);

    // Lexical read sees `{lex_init_obj, lex_child_obj}` with `has_unknown == false`!
    let lex_ans = oracle.query(lex_read, ret_iid);
    assert!(
        !lex_ans.has_unknown,
        "lex read must exclude phantom/dead None activations: {lex_ans:?}"
    );
    let mut expected_lex = oracle.query(lex_init_obj, ret_iid).sites;
    expected_lex.union_with(&oracle.query(lex_child_obj, ret_iid).sites);
    assert_eq!(lex_ans.sites, expected_lex);

    // Private field on local object resolves precisely; closures escaping via
    // `StorePrivate` on `Obj::Unknown` or `DefineGetterSetterByValue` retain `has_unknown`.
    let priv_load_ans = oracle.query(priv_loaded, ret_iid);
    assert!(!priv_load_ans.has_unknown);
    assert_eq!(
        priv_load_ans.sites,
        oracle.query(priv_val_obj, ret_iid).sites
    );
    assert!(
        oracle.query(priv_cb_param, ret_iid).has_unknown,
        "closure stored into private field of Unknown object must be marked escaped"
    );
    assert!(
        oracle.query(getter_cb_param, ret_iid).has_unknown,
        "getter closure attached via DefineGetterSetterByValue must be marked escaped"
    );

    // Concrete-singleton strong-update gate (`D5`):
    // - `late_obj` in `func_main_0` top-level IS a concrete singleton -> `UpdateKind::Strong`!
    // - `multi_obj` in twice-called `multi_alloc` is single-site locally (`query.is_single_precise()`),
    //   but NOT a concrete runtime singleton -> `site_info_at` gates to `UpdateKind::Weak`!
    assert_eq!(
        update_kind(&oracle.site_info_at(late_obj, ret_iid)),
        UpdateKind::Strong
    );
    assert!(oracle.query(multi_obj, ret_iid).is_single_precise());
    assert!(
        oracle
            .query(multi_obj, ret_iid)
            .as_concrete_singleton(oracle.singletons())
            .is_none()
    );
    assert_eq!(
        update_kind(&oracle.site_info_at(multi_obj, ret_iid)),
        UpdateKind::Weak
    );
}
