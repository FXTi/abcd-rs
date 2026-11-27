//! Context sensitivity, per-object field buckets, delta propagation, phi joins,
//! determinism, packed representations, and budget/hop-cut edge completeness tests.

use super::*;

// ── Co-evolution fixed point + array elements (the c4 shape) ────────

#[test]
fn stored_closure_call_resolves_through_element_points_to() {
    let mut m = mk_module();
    let cb = add_func_named(&mut m, "cb");
    {
        let b = entry_of(&m, cb);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let main = add_func_named(&mut m, "main");
    let entry = entry_of(&m, main);
    let arr = alloc_array(&mut m, entry);
    let zero = load_number(&mut m, entry, 0.0);
    let clo = closure_of(&mut m, entry, cb);
    emit_void(
        &mut m,
        entry,
        Op::StorePropDyn {
            object: arr,
            key: zero,
            value: clo,
        },
    );
    let zero2 = load_number(&mut m, entry, 0.0);
    let f = emit(
        &mut m,
        entry,
        Op::LoadPropDyn {
            object: arr,
            key: zero2,
        },
    );
    let arg = load_number(&mut m, entry, 1.0);
    let call = push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: f,
            this: None,
            args: vec![arg],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let base = CallGraph::build(&m);
    assert_eq!(
        base.edge_at(call).unwrap().targets,
        CallTargets::UnknownCallees,
        "the base trace cannot see through the element store"
    );
    let out = analyze(&m, &base, &PtaConfig::default());
    let edge = out.graph().edge_at(call).expect("edge");
    assert_eq!(edge.edge_kind, CallEdgeKind::ResolvedValueFlow);
    assert_eq!(
        edge.targets,
        CallTargets::Resolved(vec![cb]),
        "the co-evolution resolves the stored closure"
    );
    assert!(
        edge.resolution_complete,
        "the callee set had no unknown — complete"
    );
    assert_eq!(out.graph().callers_of(cb), &[call]);
    assert!(!out.stats().capped);
}

// ── Global stores (the d4 shape) ────────────────────────────────────

#[test]
fn global_stored_function_call_resolves() {
    let mut m = mk_module();
    let boom = add_func_named(&mut m, "boom");
    {
        let b = entry_of(&m, boom);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let main = add_func_named(&mut m, "main");
    let entry = entry_of(&m, main);
    let boom_sym = intern(&mut m, "boom");
    let clo = closure_of(&mut m, entry, boom);
    emit_void(
        &mut m,
        entry,
        Op::StoreGlobal {
            name: boom_sym,
            value: clo,
        },
    );
    let g = emit(
        &mut m,
        entry,
        Op::TryGetGlobal {
            name: boom_sym,
            default: None,
        },
    );
    let call = push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: g,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let out = run(&m);
    let edge = out.graph().edge_at(call).expect("edge");
    assert_eq!(edge.targets, CallTargets::Resolved(vec![boom]));
    assert!(
        !edge.resolution_complete,
        "a global load is also host-bindable — partial"
    );
}

// ── Context keys (the 1-call-site witness) ──────────────────────────

#[test]
fn call_site_contexts_separate_factory_callers() {
    let mut m = mk_module();
    // id(x) { return x } — STATIC for precise binding.
    let (id, params) = add_static_func(&mut m, "id", 1);
    {
        let b = entry_of(&m, id);
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(params[3]),
            },
        );
    }
    let main = add_func_named(&mut m, "main");
    let entry = entry_of(&m, main);
    let id_clo = closure_of(&mut m, entry, id);
    let o1 = alloc_object(&mut m, entry);
    let r1 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: id_clo,
            this: None,
            args: vec![o1],
            kind: CallKind::Dynamic,
        },
    );
    let o2 = alloc_object(&mut m, entry);
    let r2 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: id_clo,
            this: None,
            args: vec![o2],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let a1 = oracle.query(r1, InstId::new(0));
    let a2 = oracle.query(r2, InstId::new(0));
    assert!(!a1.has_unknown && !a2.has_unknown, "precise: {a1:?} {a2:?}");
    assert_eq!(a1.sites.len(), 1);
    assert_eq!(a2.sites.len(), 1);
    assert!(
        a1.sites != a2.sites,
        "1-call-site contexts keep the two factory results apart"
    );
    // must-alias sees through the call (the a5 shape): both sides
    // single-precise with equal sites. (The oracle seam's must_alias
    // delegate was deleted as dead surface; same query composition here.)
    let (qa, qb) = (
        oracle.query(r1, InstId::new(0)),
        oracle.query(o1, InstId::new(0)),
    );
    assert!(qa.is_single_precise() && qb.is_single_precise() && qa.sites == qb.sites);
    let (qa, qb) = (
        oracle.query(r1, InstId::new(0)),
        oracle.query(o2, InstId::new(0)),
    );
    assert!(!(qa.is_single_precise() && qb.is_single_precise() && qa.sites == qb.sites));
}

// ── Field sensitivity (per abstract object, per bucket) ─────────────

#[test]
fn field_buckets_are_object_and_kind_sensitive() {
    let mut m = mk_module();
    let main = add_func_named(&mut m, "main");
    let entry = entry_of(&m, main);
    let a_sym = intern(&mut m, "a");
    let o1 = alloc_object(&mut m, entry);
    let o2 = alloc_object(&mut m, entry);
    let v1 = alloc_object(&mut m, entry);
    let v2 = alloc_object(&mut m, entry);
    // o1.a = v1; o2.a = v2 — same field, different objects.
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: o1,
            name: a_sym,
            value: v1,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: o2,
            name: a_sym,
            value: v2,
        },
    );
    let l1 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: o1,
            name: a_sym,
        },
    );
    let l2 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: o2,
            name: a_sym,
        },
    );
    // o1[0] = v2 — the Index bucket is separate from Named(a).
    let zero = load_number(&mut m, entry, 0.0);
    emit_void(
        &mut m,
        entry,
        Op::StorePropIdx {
            object: o1,
            index: zero,
            value: v2,
        },
    );
    let l3 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: o1,
            name: a_sym,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let one = |v: ValueId| {
        let a = oracle.query(v, InstId::new(0));
        assert!(!a.has_unknown, "precise: {a:?}");
        assert_eq!(a.sites.len(), 1, "single site: {a:?}");
        a.sites
    };
    assert_eq!(one(l1), one(v1), "o1.a is v1's site");
    assert_eq!(one(l2), one(v2), "o2.a is v2's site");
    assert_eq!(one(l3), one(v1), "the Index store does not reach o1.a");
}

/// A computed-key (Dynamic) store is visible to named and index reads
/// (the may-conservative bucket discipline).
#[test]
fn dynamic_store_reaches_named_and_index_reads() {
    let mut m = mk_module();
    let main = add_func_named(&mut m, "main");
    let entry = entry_of(&m, main);
    let a_sym = intern(&mut m, "a");
    let o = alloc_object(&mut m, entry);
    let k = load_number(&mut m, entry, 0.0);
    let v = alloc_object(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::StorePropDyn {
            object: o,
            key: k,
            value: v,
        },
    );
    let ln = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: o,
            name: a_sym,
        },
    );
    let zero = load_number(&mut m, entry, 0.0);
    let li = emit(
        &mut m,
        entry,
        Op::LoadPropIdx {
            object: o,
            index: zero,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    for x in [ln, li] {
        let a = oracle.query(x, InstId::new(0));
        assert!(!a.has_unknown);
        assert_eq!(a.sites, oracle.query(v, InstId::new(0)).sites);
    }
}

// ── Delta propagation (store through an interprocedural base) ───────
//
// The store/load handlers register on the call-result base BEFORE the
// callee's return object arrives; the late fact must still fire them
// (the delta discipline at the statement level).
#[test]
fn store_load_through_call_result_base() {
    let mut m = mk_module();
    let (mkobj, _) = add_static_func(&mut m, "mkobj", 0);
    {
        let b = entry_of(&m, mkobj);
        let o = alloc_object(&mut m, b);
        emit_void(&mut m, b, Op::Return { value: Some(o) });
    }
    let main = add_func_named(&mut m, "main");
    let entry = entry_of(&m, main);
    let f_sym = intern(&mut m, "f");
    let mk_clo = closure_of(&mut m, entry, mkobj);
    let o = emit(
        &mut m,
        entry,
        Op::Call {
            callee: mk_clo,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let v = alloc_object(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: o,
            name: f_sym,
            value: v,
        },
    );
    let x = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: o,
            name: f_sym,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let ans = oracle.query(x, InstId::new(0));
    assert!(!ans.has_unknown, "{ans:?}");
    assert_eq!(ans.sites, oracle.query(v, InstId::new(0)).sites);
}

// ── Phi unions + the strong-update flags ────────────────────────────

#[test]
fn phi_unions_sites_and_marks_has_phi() {
    let mut m = mk_module();
    let main = add_func_named(&mut m, "main");
    let entry = entry_of(&m, main);
    let t = add_block(&mut m, main);
    let e = add_block(&mut m, main);
    let join = add_block(&mut m, main);
    let cond = load_number(&mut m, entry, 1.0);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond,
            true_dest: t,
            false_dest: e,
        },
    );
    let a = alloc_object(&mut m, t);
    emit_void(&mut m, t, Op::Branch { dest: join });
    let b = alloc_object(&mut m, e);
    emit_void(&mut m, e, Op::Branch { dest: join });
    link(&mut m, entry, t);
    link(&mut m, entry, e);
    link(&mut m, t, join);
    link(&mut m, e, join);
    let phi = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    abcd_ir::Edge {
                        from: t,
                        kind: abcd_ir::EdgeKind::Normal,
                    },
                    a,
                ),
                (
                    abcd_ir::Edge {
                        from: e,
                        kind: abcd_ir::EdgeKind::Normal,
                    },
                    b,
                ),
            ],
        },
    );
    emit_void(&mut m, join, Op::Return { value: None });

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let ans = oracle.query(phi, InstId::new(0));
    assert_eq!(ans.sites.len(), 2);
    assert!(ans.has_phi, "the phi flag survives (weak updates stay)");
    assert!(!ans.has_unknown);
    // Keying-complete but not single-precise: site_info_at carries the
    // phi flag through, so update_kind stays Weak.
    let info = oracle.site_info_at(phi, InstId::new(0));
    assert!(info.has_phi && !info.has_unknown && info.sites.len() == 2);
    assert_eq!(
        crate::dataflow::heap::update_kind(&info),
        crate::dataflow::heap::UpdateKind::Weak
    );
}

// ── Budget cap ──────────────────────────────────────────────────────

#[test]
fn step_budget_cut_sets_capped() {
    let mut m = mk_module();
    let main = add_func_named(&mut m, "main");
    let entry = entry_of(&m, main);
    let o = alloc_object(&mut m, entry);
    let a_sym = intern(&mut m, "a");
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: o,
            name: a_sym,
            value: o,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let base = CallGraph::build(&m);
    let out = analyze(
        &m,
        &base,
        &PtaConfig {
            step_budget: 0,
            ..PtaConfig::default()
        },
    );
    assert!(out.stats().capped, "the tiny budget fires");
    // The oracle's answers carry the cap flag (consumers fall back).
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    assert!(oracle.query(o, InstId::new(0)).capped);
}

// ── Determinism (N20) ───────────────────────────────────────────────

#[test]
fn two_runs_are_identical() {
    let build = || {
        let mut m = mk_module();
        let cb = add_func_named(&mut m, "cb");
        {
            let b = entry_of(&m, cb);
            emit_void(&mut m, b, Op::Return { value: None });
        }
        let (id, params) = add_static_func(&mut m, "id", 1);
        {
            let b = entry_of(&m, id);
            emit_void(
                &mut m,
                b,
                Op::Return {
                    value: Some(params[3]),
                },
            );
        }
        let main = add_func_named(&mut m, "main");
        let entry = entry_of(&m, main);
        let arr = alloc_array(&mut m, entry);
        let zero = load_number(&mut m, entry, 0.0);
        let clo = closure_of(&mut m, entry, cb);
        emit_void(
            &mut m,
            entry,
            Op::StorePropDyn {
                object: arr,
                key: zero,
                value: clo,
            },
        );
        let g_sym = intern(&mut m, "cb");
        emit_void(
            &mut m,
            entry,
            Op::StoreGlobal {
                name: g_sym,
                value: clo,
            },
        );
        let id_clo = closure_of(&mut m, entry, id);
        let o = alloc_object(&mut m, entry);
        emit(
            &mut m,
            entry,
            Op::Call {
                callee: id_clo,
                this: None,
                args: vec![o],
                kind: CallKind::Dynamic,
            },
        );
        let zero2 = load_number(&mut m, entry, 0.0);
        let fv = emit(
            &mut m,
            entry,
            Op::LoadPropDyn {
                object: arr,
                key: zero2,
            },
        );
        push_inst(
            &mut m,
            entry,
            Op::Call {
                callee: fv,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        new_lex_env(&mut m, entry);
        emit_void(
            &mut m,
            entry,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: o,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, entry, Op::Return { value: None });
        m
    };
    let m = build();
    let a = run(&m);
    let b = run(&m);
    assert_eq!(a.graph(), b.graph(), "graphs identical");
    let (_, ta, sa) = a.into_parts();
    let (_, tb, sb) = b.into_parts();
    assert_eq!(ta, tb, "tables identical");
    assert_eq!(sa, sb, "stats identical");
}

#[test]
fn packed_ctx_sizes_order_isomorphism_sparse_answers_and_decoy_harness() {
    // 1. Verify compact `PackedCtx` / `PackedFunc` memory layout (`#84.3a`).
    assert_eq!(std::mem::size_of::<PackedCtx>(), 4);
    assert_eq!(std::mem::size_of::<ObjLoc>(), 12);
    assert_eq!(std::mem::size_of::<Slot>(), 12);
    assert_eq!(std::mem::size_of::<Obj>(), 16);
    assert_eq!(std::mem::size_of::<Ptr>(), 24);

    // Order isomorphism between `Option<InstId>` and `PackedCtx`.
    let opts: [Option<InstId>; 4] = [
        None,
        Some(InstId::new(0)),
        Some(InstId::new(1)),
        Some(InstId::new(u32::MAX - 1)),
    ];
    for i in 0..opts.len() {
        for j in 0..opts.len() {
            let pa = opts[i].map_or(PackedCtx::NONE, PackedCtx::some);
            let pb = opts[j].map_or(PackedCtx::NONE, PackedCtx::some);
            assert_eq!(opts[i].cmp(&opts[j]), pa.cmp(&pb));
        }
    }

    // 2. Decoy user function named `"__abcd_ohos_harness__"` (`#75`):
    //    When `PtaConfig { harness_func: None, .. }` runs in root-sliced mode
    //    with `[decoy_fn]` as root, `decoy_fn` MUST be treated as an ordinary
    //    user function (its zero-arg `LoadConst(MethodRef)` helper call IS wired
    //    and NOT filtered out as an inactive ViewPU harness call!).
    let mut m = mk_module();
    let helper = add_func_named(&mut m, "zero_arg_helper");
    let bh = entry_of(&m, helper);
    let helper_alloc = alloc_object(&mut m, bh);
    let helper_site = m.blocks[bh.index()].insts[0];
    emit_void(
        &mut m,
        bh,
        Op::Return {
            value: Some(helper_alloc),
        },
    );

    let decoy = add_func_named(&mut m, crate::ohos_lifecycle::OHOS_HARNESS_FUNC);
    let bd = entry_of(&m, decoy);
    let href = load_method_ref(&mut m, bd, helper);
    let call_res = emit(
        &mut m,
        bd,
        Op::Call {
            callee: href,
            this: None,
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    let ret_iid = emit_void(
        &mut m,
        bd,
        Op::Return {
            value: Some(call_res),
        },
    );

    // Add an unreached sibling function so `roots = Some(&[decoy])` is root-sliced,
    // plus a `ValueDef::Const` value to exercise `NON_HEAP_ANSWER_SLOT` and
    // unreached `INCOMPLETE_ANSWER_SLOT` in sparse `Rung2Tables` (`#78`).
    let unreached = add_func_named(&mut m, "unreached_fn");
    let bu = entry_of(&m, unreached);
    let unreached_obj = alloc_object(&mut m, bu);
    let const_undef = const_undefined(&mut m);
    emit_void(&mut m, bu, Op::Return { value: None });

    let links = ModuleLinkTable::build(&m);
    let base_cg = CallGraph::build_with_links(&m, &links);
    let out = analyze_with_links_and_roots(
        &m,
        &links,
        &base_cg,
        &PtaConfig {
            harness_func: None,
            ..PtaConfig::default()
        },
        Some(&[decoy]),
    );
    assert!(out.stats().root_sliced);
    let (_, tables, stats) = out.into_parts();
    assert_eq!(
        tables.answer_entries.len(),
        2,
        "only reached object-bearing values (`helper_alloc` and `call_res`) allocate entries in sparse `answer_entries`"
    );

    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let decoy_ans = oracle.query(call_res, ret_iid);
    assert!(
        !decoy_ans.has_unknown,
        "decoy user function named __abcd_ohos_harness__ must not be filtered as OHOS harness: {decoy_ans:?}"
    );
    assert_eq!(decoy_ans.sites, AllocSiteSet::one(helper_site));

    // `ValueDef::Const` decodes to `{ sites: empty, has_unknown: false }`;
    // unreached `AllocObject` decodes to `{ sites: empty, has_unknown: true }`.
    let const_ans = oracle.query(const_undef, ret_iid);
    assert!(const_ans.sites.is_empty() && !const_ans.has_unknown);
    let unreach_ans = oracle.query(unreached_obj, ret_iid);
    assert!(unreach_ans.sites.is_empty() && unreach_ans.has_unknown);
}

#[test]
fn capped_and_hop_cut_pta_preserve_syntactically_complete_base_edges() {
    let mut m = mk_module();

    let (closed_fn, closed_params) = add_static_func(&mut m, "closed_fn", 1);
    {
        let b = entry_of(&m, closed_fn);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let (heap_fn, _) = add_static_func(&mut m, "heap_fn", 0);
    {
        let b = entry_of(&m, heap_fn);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let (late_fn, _) = add_static_func(&mut m, "late_fn", 0);
    {
        let b = entry_of(&m, late_fn);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let main = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, main);

    // 1. Syntactically closed `DefineFunc` call (`base_edge.resolution_complete == true`).
    let def_closed = emit(
        &mut m,
        b,
        Op::DefineFunc {
            body: closed_fn,
            captures: Vec::new(),
            length: 1,
        },
    );
    let arg1 = alloc_object(&mut m, b);
    let direct_call = push_inst(
        &mut m,
        b,
        Op::Call {
            callee: def_closed,
            this: None,
            args: vec![arg1],
            kind: CallKind::Direct,
        },
    );

    // 2. PTA-resolved dynamic element call (`base_edge.targets == UnknownCallees`,
    //    resolved to `heap_fn` before `step_budget` fires).
    let arr1 = alloc_array(&mut m, b);
    let zero = load_number(&mut m, b, 0.0);
    let def_heap = emit(
        &mut m,
        b,
        Op::DefineFunc {
            body: heap_fn,
            captures: Vec::new(),
            length: 0,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::StorePropDyn {
            object: arr1,
            key: zero,
            value: def_heap,
        },
    );
    let loaded_heap = emit(
        &mut m,
        b,
        Op::LoadPropDyn {
            object: arr1,
            key: zero,
        },
    );
    let pta_call = push_inst(
        &mut m,
        b,
        Op::Call {
            callee: loaded_heap,
            this: None,
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );

    // Filler field stores on `holder2` (`ObjLoc::Site(holder2)` > `ObjLoc::Site(arr1)`)
    // so `step_budget` fires AFTER `pta_call` resolves `heap_fn` and BEFORE `arr3[0]` propagates.
    let holder2 = alloc_object(&mut m, b);
    let filler_val = alloc_object(&mut m, b);
    for idx in 0..16 {
        let p_sym = intern(&mut m, &format!("pad_{idx}"));
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: holder2,
                name: p_sym,
                value: filler_val,
            },
        );
    }

    // 3. Late PTA-dependent call (`arr3[0]`) that remains `UnknownCallees` when capped,
    //    plus a second closed call passing `loaded_late` into `closed_fn` to verify
    //    `compute_externally_invocable` keeps `closed_fn`'s parameter conservative under `capped`.
    let arr3 = alloc_array(&mut m, b);
    let def_late = emit(
        &mut m,
        b,
        Op::DefineFunc {
            body: late_fn,
            captures: Vec::new(),
            length: 0,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::StorePropDyn {
            object: arr3,
            key: zero,
            value: def_late,
        },
    );
    let loaded_late = emit(
        &mut m,
        b,
        Op::LoadPropDyn {
            object: arr3,
            key: zero,
        },
    );
    let unresolved_call = push_inst(
        &mut m,
        b,
        Op::Call {
            callee: loaded_late,
            this: None,
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );
    let direct_call_2 = push_inst(
        &mut m,
        b,
        Op::Call {
            callee: def_closed,
            this: None,
            args: vec![loaded_late],
            kind: CallKind::Direct,
        },
    );
    let ret_iid = emit_void(&mut m, b, Op::Return { value: None });

    let base = CallGraph::build(&m);
    assert!(base.edge_at(direct_call).unwrap().resolution_complete);
    assert!(!base.edge_at(pta_call).unwrap().resolution_complete);
    assert!(!base.edge_at(unresolved_call).unwrap().resolution_complete);

    let uncapped = analyze(&m, &base, &PtaConfig::default());
    assert!(!uncapped.stats().capped);
    let out = analyze(
        &m,
        &base,
        &PtaConfig {
            step_budget: uncapped.stats().facts - 10,
            ..PtaConfig::default()
        },
    );
    assert!(out.stats().capped, "step_budget must cap Pta::pump");

    let direct_edge = out.graph().edge_at(direct_call).expect("direct_call edge");
    assert_eq!(direct_edge.targets, CallTargets::Resolved(vec![closed_fn]));
    assert!(
        direct_edge.resolution_complete,
        "syntactically closed DefineFunc call must preserve resolution_complete == true under step_budget cap"
    );
    assert!(
        out.graph()
            .edge_at(direct_call_2)
            .expect("direct_call_2 edge")
            .resolution_complete
    );

    let pta_edge = out.graph().edge_at(pta_call).expect("pta_call edge");
    assert_eq!(pta_edge.targets, CallTargets::Resolved(vec![heap_fn]));
    assert!(
        !pta_edge.resolution_complete,
        "PTA-newly-resolved call must have resolution_complete == false when capped"
    );

    let unres_edge = out
        .graph()
        .edge_at(unresolved_call)
        .expect("unresolved_call edge");
    assert_eq!(unres_edge.targets, CallTargets::UnknownCallees);
    assert!(
        !unres_edge.resolution_complete,
        "unresolved PTA-dependent call must have resolution_complete == false when capped"
    );

    // Soundness check: even though `direct_call` and `direct_call_2` keep
    // `edge.resolution_complete == true`, `compute_externally_invocable` must
    // still retain `ctx = None` `has_unknown` on `closed_fn` when PTA capped
    // before `loaded_late` propagated into `closed_params[3]`.
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let param_ans = oracle.query(closed_params[3], ret_iid);
    assert!(param_ans.capped && param_ans.has_unknown, "{param_ans:?}");

    // Also verify `step_budget: 0` (immediate cap before any `Handler::Call` fires).
    let zero_out = analyze(
        &m,
        &base,
        &PtaConfig {
            step_budget: 0,
            ..PtaConfig::default()
        },
    );
    assert!(zero_out.stats().capped);
    assert!(
        zero_out
            .graph()
            .edge_at(direct_call)
            .unwrap()
            .resolution_complete
    );
    assert!(
        !zero_out
            .graph()
            .edge_at(pta_call)
            .unwrap()
            .resolution_complete
    );

    // Root-sliced `hop_cut_calls` (`!capped`): syntactically closed `DefineFunc`
    // call at hop 5 -> 6 keeps `resolution_complete == true`, while PTA-newly-resolved
    // call at hop 5 -> 6 keeps `resolution_complete == false`, and `h6`'s parameter
    // stays `has_unknown == true`.
    let mut mh = mk_module();
    let g_sym = intern(&mut mh, "ext");
    let mut chain = Vec::new();
    for idx in 0..6 {
        let (f, _) = add_static_func(&mut mh, &format!("hop_{idx}"), 0);
        chain.push(f);
    }
    let (h6, h6_params) = add_static_func(&mut mh, "hop_6", 1);
    {
        let b6 = entry_of(&mh, h6);
        emit_void(&mut mh, b6, Op::Return { value: None });
    }
    for idx in 0..5 {
        let bi = entry_of(&mh, chain[idx]);
        let next = chain[idx + 1];
        let def_next = emit(
            &mut mh,
            bi,
            Op::DefineFunc {
                body: next,
                captures: Vec::new(),
                length: 0,
            },
        );
        let _ = push_inst(
            &mut mh,
            bi,
            Op::Call {
                callee: def_next,
                this: None,
                args: Vec::new(),
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut mh, bi, Op::Return { value: None });
    }
    // `h5` (hop 5 == `MAX_SLICED_DYN_HOP`): both calls to `h6` exceed hop 5 (`hop_cut_calls`).
    let (hop_cut_direct, hop_cut_pta, h5_ret) = {
        let b5 = entry_of(&mh, chain[5]);
        let def_h6 = emit(
            &mut mh,
            b5,
            Op::DefineFunc {
                body: h6,
                captures: Vec::new(),
                length: 1,
            },
        );
        let unk_arg = emit(
            &mut mh,
            b5,
            Op::TryGetGlobal {
                name: g_sym,
                default: None,
            },
        );
        let c_dir = push_inst(
            &mut mh,
            b5,
            Op::Call {
                callee: def_h6,
                this: None,
                args: vec![unk_arg],
                kind: CallKind::Direct,
            },
        );
        let arr_h5 = alloc_array(&mut mh, b5);
        let z5 = load_number(&mut mh, b5, 0.0);
        emit_void(
            &mut mh,
            b5,
            Op::StorePropDyn {
                object: arr_h5,
                key: z5,
                value: def_h6,
            },
        );
        let dyn_h6 = emit(
            &mut mh,
            b5,
            Op::LoadPropDyn {
                object: arr_h5,
                key: z5,
            },
        );
        let c_pta = push_inst(
            &mut mh,
            b5,
            Op::Call {
                callee: dyn_h6,
                this: None,
                args: vec![unk_arg],
                kind: CallKind::Dynamic,
            },
        );
        let r = emit_void(&mut mh, b5, Op::Return { value: None });
        (c_dir, c_pta, r)
    };

    let mh_links = ModuleLinkTable::build(&mh);
    let mh_base = CallGraph::build_with_links(&mh, &mh_links);
    let hop_out = analyze_with_links_and_roots(
        &mh,
        &mh_links,
        &mh_base,
        &PtaConfig::default(),
        Some(&[chain[0]]),
    );
    assert!(!hop_out.stats().capped);
    assert!(
        hop_out
            .graph()
            .edge_at(hop_cut_direct)
            .unwrap()
            .resolution_complete,
        "syntactically closed call must stay resolution_complete == true under hop_cut_calls"
    );
    let hop_pta_edge = hop_out.graph().edge_at(hop_cut_pta).unwrap();
    assert_eq!(hop_pta_edge.targets, CallTargets::Resolved(vec![h6]));
    assert!(
        !hop_pta_edge.resolution_complete,
        "PTA-newly-resolved call must keep resolution_complete == false under hop_cut_calls"
    );
    let (_, hop_tables, hop_stats) = hop_out.into_parts();
    let hop_oracle = Rung2AliasOracle::new(&mh, hop_tables, hop_stats);
    assert!(
        hop_oracle.query(h6_params[3], h5_ret).has_unknown,
        "hop-cut unwired call to h6 must keep h6's parameter conservative"
    );
}
