//! Rung-1 engine tests — one per mechanism (the task's gate):
//! memoization, depth cap, interprocedural hop (both directions),
//! must-alias honesty, the balanced-parentheses discipline, unbalanced
//! fan-out marking, and determinism.

use super::*;
use crate::testutil::*;
use abcd_ir::{CallKind, Op};

/// The a4 shape: `p = mkobj()` where mkobj returns a fresh object —
/// the call result resolves through the callee's return to the callee's
/// alloc site (the interprocedural hop, forward-entry direction).
fn mk_call_result_module() -> (Module, FuncId, ValueId, InstId, InstId) {
    let mut m = mk_module();
    let mkobj = add_func_named(&mut m, "mkobj");
    let site;
    {
        let b = entry_of(&m, mkobj);
        m.func_mut(mkobj).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
        add_param(&mut m, mkobj, 0);
        add_param(&mut m, mkobj, 1);
        add_param(&mut m, mkobj, 2);
        site = alloc_object(&mut m, b);
        emit_void(&mut m, b, Op::Return { value: Some(site) });
    }
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let def = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: mkobj,
            captures: vec![],
            length: 0,
        },
    );
    let clo = emit(&mut m, entry, Op::AllocClosure { func: def });
    let call_inst = push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: clo,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let result = ValueId::new(m.values.len() as u32);
    m.values.push(abcd_ir::function::Value {
        def: ValueDef::Inst(call_inst),
        ty: abcd_ir::Ty::Any,
    });
    m.inst_mut(call_inst).unwrap().result = Some(result);
    emit_void(&mut m, entry, Op::Return { value: None });
    let site_iid = site.inst_of(&m);
    (m, caller, result, call_inst, site_iid)
}

/// Helper: the defining instruction of a value (test assertion aid).
trait InstOf {
    fn inst_of(&self, m: &Module) -> InstId;
}
impl InstOf for ValueId {
    fn inst_of(&self, m: &Module) -> InstId {
        match m.value(*self).unwrap().def {
            ValueDef::Inst(i) => i,
            _ => panic!("not inst-defined"),
        }
    }
}

#[test]
fn call_result_hops_into_callee_alloc_site() {
    let (m, _caller, result, call, site) = mk_call_result_module();
    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);

    let ans = oracle.query(result, call);
    assert_eq!(ans.sites.len(), 1);
    assert!(ans.sites.iter().eq([site]), "the callee's alloc site");
    assert!(ans.precise_for_keying(), "complete and balanced: {ans:?}");

    // site_info_at uses the refined answer (not the rung-0 empty set).
    let info = oracle.site_info_at(result, call);
    assert!(info.is_single_precise());
}

#[test]
fn memoization_serves_repeated_queries() {
    let (m, _caller, result, call, _site) = mk_call_result_module();
    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);

    let a = oracle.query(result, call);
    let b = oracle.query(result, call);
    assert_eq!(a, b);
    let stats = oracle.stats();
    assert_eq!(stats.queries, 2);
    assert!(
        stats.memo_hits >= 1,
        "the second query hit the memo: {stats:?}"
    );
}

/// The a5 shape with TWO call sites of the same identity callee:
/// `id(o1)` and `id(o2)` must resolve to DIFFERENT sites — the
/// balanced-parentheses discipline keeps the contexts apart (a
/// context-insensitive engine would union them).
#[test]
fn balanced_discipline_separates_call_sites() {
    let mut m = mk_module();
    let id = add_func_named(&mut m, "id");
    {
        let b = entry_of(&m, id);
        m.func_mut(id).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
        add_param(&mut m, id, 0);
        add_param(&mut m, id, 1);
        add_param(&mut m, id, 2);
        let x = add_param(&mut m, id, 3); // first formal (0xF default)
        emit_void(&mut m, b, Op::Return { value: Some(x) });
    }
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let def = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: id,
            captures: vec![],
            length: 1,
        },
    );
    let clo = emit(&mut m, entry, Op::AllocClosure { func: def });
    let o1 = alloc_object(&mut m, entry);
    let call1 = push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: clo,
            this: None,
            args: vec![o1],
            kind: CallKind::Dynamic,
        },
    );
    let r1 = ValueId::new(m.values.len() as u32);
    m.values.push(abcd_ir::function::Value {
        def: ValueDef::Inst(call1),
        ty: abcd_ir::Ty::Any,
    });
    m.inst_mut(call1).unwrap().result = Some(r1);
    let o2 = alloc_object(&mut m, entry);
    let call2 = push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: clo,
            this: None,
            args: vec![o2],
            kind: CallKind::Dynamic,
        },
    );
    let r2 = ValueId::new(m.values.len() as u32);
    m.values.push(abcd_ir::function::Value {
        def: ValueDef::Inst(call2),
        ty: abcd_ir::Ty::Any,
    });
    m.inst_mut(call2).unwrap().result = Some(r2);
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let a1 = oracle.query(r1, call1);
    let a2 = oracle.query(r2, call2);
    assert!(a1.is_single_precise() && a2.is_single_precise());
    assert!(
        !a1.sites.intersects(&a2.sites),
        "the contexts stay apart: {a1:?} vs {a2:?}"
    );
    assert_eq!(a1.sites.iter().next().unwrap(), o1.inst_of(&m));
    assert_eq!(a2.sites.iter().next().unwrap(), o2.inst_of(&m));

    // must-alias honesty: proven same-site (o1 through the call) is
    // must-alias; o1 vs o2 is not. (The oracle seam's must_alias
    // delegate was deleted as dead surface; same query composition here.)
    let (qa, qb) = (oracle.query(r1, call1), oracle.query(o1, call1));
    assert!(qa.is_single_precise() && qb.is_single_precise() && qa.sites == qb.sites);
    let (qa, qb) = (oracle.query(r1, call1), oracle.query(o2, call1));
    assert!(!(qa.is_single_precise() && qb.is_single_precise() && qa.sites == qb.sites));
    let (qa, qb) = (oracle.query(r1, call1), oracle.query(r2, call1));
    assert!(!(qa.is_single_precise() && qb.is_single_precise() && qa.sites == qb.sites));
}

/// Must-alias honesty: a phi merge of the same single site on both
/// sides is NOT must-alias (the phi kills the proof, rung-0 rule kept);
/// an unbalanced fan-out answer is never used for keying.
#[test]
fn must_alias_honesty_on_phi_and_unbalanced() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let join = add_block(&mut m, f);
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
    // Both phi entries are the SAME site — still a phi, so not
    // single-precise.
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
                    a,
                ),
            ],
        },
    );
    emit_void(&mut m, join, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(phi, InstId::new(0));
    assert_eq!(ans.sites.len(), 1, "one site through the phi");
    assert!(ans.has_phi);
    assert!(!ans.is_single_precise(), "phi kills single-precision");
    // Not must-alias: the phi side is not single-precise.
    let (qa, qb) = (
        oracle.query(phi, InstId::new(0)),
        oracle.query(a, InstId::new(0)),
    );
    assert!(!(qa.is_single_precise() && qb.is_single_precise() && qa.sites == qb.sites));
}

/// The b3 shape: a callee value that is a PARAMETER (`register(cb) {
/// cb(); }`) — the unbalanced fan-out resolves it through the recorded
/// caller's argument, marked unbalanced (may-direction only).
#[test]
fn param_callee_fanout_is_unbalanced_but_resolved() {
    let mut m = mk_module();
    let cb = add_func_named(&mut m, "cb");
    {
        let b = entry_of(&m, cb);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let register = add_func_named(&mut m, "register");
    let cb_param;
    let inner_call;
    {
        let b = entry_of(&m, register);
        m.func_mut(register).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
        add_param(&mut m, register, 0);
        add_param(&mut m, register, 1);
        add_param(&mut m, register, 2);
        cb_param = add_param(&mut m, register, 3);
        inner_call = push_inst(
            &mut m,
            b,
            Op::Call {
                callee: cb_param,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let caller = add_func_named(&mut m, "caller");
    {
        let b = entry_of(&m, caller);
        let def_reg = emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: register,
                captures: vec![],
                length: 1,
            },
        );
        let clo_reg = emit(&mut m, b, Op::AllocClosure { func: def_reg });
        let def_cb = emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: cb,
                captures: vec![],
                length: 0,
            },
        );
        let clo_cb = emit(&mut m, b, Op::AllocClosure { func: def_cb });
        push_inst(
            &mut m,
            b,
            Op::Call {
                callee: clo_reg,
                this: None,
                args: vec![clo_cb],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let graph = CallGraph::build(&m);
    // The inner call is unresolved at rung 0 (param callee).
    assert_eq!(
        graph.edge_at(inner_call).unwrap().targets,
        CallTargets::UnknownCallees
    );

    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(cb_param, inner_call);
    assert_eq!(ans.sites.len(), 1, "the caller's AllocClosure site");
    assert!(ans.unbalanced, "fan-out answers are marked");
    assert!(!ans.precise_for_keying(), "not usable for keying");
    assert!(
        ans.complete_for_resolution(),
        "usable for callee resolution"
    );

    // site_info_at must NOT use the unbalanced answer: it falls back to
    // rung 0 (param → empty + unknown).
    let info = oracle.site_info_at(cb_param, inner_call);
    assert!(info.sites.is_empty() && info.has_unknown);
}

/// The depth cap: a chain of functions `f_i(x) { return f_{i+1}(x); }`
/// nesting deeper than the cap cuts the walk — capped + unknown, and
/// site_info_at falls back to rung 0 (the sound over-approximation,
/// never silently wrong). (Sequential `id(id(...))` chains do NOT grow
/// the context stack: each entered call is popped before the next is
/// pushed — the call string stays balanced-flat, so this test uses true
/// nesting.)
#[test]
fn depth_cap_cuts_and_falls_back() {
    let mut m = mk_module();
    const N: u32 = 6;
    let mut funcs = Vec::new();
    for i in 0..N {
        let f = add_func_named(&mut m, &format!("f{i}"));
        m.func_mut(f).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
        funcs.push(f);
    }
    for (i, &f) in funcs.iter().enumerate() {
        let b = entry_of(&m, f);
        add_param(&mut m, f, 0);
        add_param(&mut m, f, 1);
        add_param(&mut m, f, 2);
        let x = add_param(&mut m, f, 3);
        if i + 1 < funcs.len() {
            let next = load_method_ref(&mut m, b, funcs[i + 1]);
            let r = emit(
                &mut m,
                b,
                Op::Call {
                    callee: next,
                    this: None,
                    args: vec![x],
                    kind: CallKind::Direct,
                },
            );
            emit_void(&mut m, b, Op::Return { value: Some(r) });
        } else {
            emit_void(&mut m, b, Op::Return { value: Some(x) });
        }
    }
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let obj = alloc_object(&mut m, entry);
    let site = obj.inst_of(&m);
    let f1 = load_method_ref(&mut m, entry, funcs[0]);
    let cur = emit(
        &mut m,
        entry,
        Op::Call {
            callee: f1,
            this: None,
            args: vec![obj],
            kind: CallKind::Direct,
        },
    );
    let outer_call = cur.inst_of(&m);
    emit_void(&mut m, entry, Op::Return { value: None });
    let graph = CallGraph::build(&m);

    // Depth 8 (the default): the 6-deep nesting resolves.
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(cur, outer_call);
    assert!(ans.is_single_precise(), "deep but under the cap: {ans:?}");
    assert_eq!(ans.sites.iter().next().unwrap(), site);

    // Depth 2: the nesting overruns the cap.
    let shallow = Rung1AliasOracle::with_depth(&m, &graph, 2);
    let ans = shallow.query(cur, outer_call);
    assert!(ans.capped && ans.has_unknown, "the cap cut: {ans:?}");
    assert!(!ans.precise_for_keying());
    assert!(shallow.stats().capped > 0);
    // The fallback is the rung-0 answer (call result → empty + unknown)
    // — sound, weak, never the precise-but-wrong one.
    let info = shallow.site_info_at(cur, outer_call);
    assert!(info.sites.is_empty() && info.has_unknown);
    // Not must-alias: a capped answer is not single-precise.
    let (qa, qb) = (
        shallow.query(cur, outer_call),
        shallow.query(cur, outer_call),
    );
    assert!(!(qa.is_single_precise() && qb.is_single_precise() && qa.sites == qb.sites));
}

/// Unresolved call targets are opaque; native (bodyless) callees too.
#[test]
fn unresolved_and_native_calls_are_unknown() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let g = try_get_global(&mut m, entry, "anything");
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
    let r = ValueId::new(m.values.len() as u32);
    m.values.push(abcd_ir::function::Value {
        def: ValueDef::Inst(call),
        ty: abcd_ir::Ty::Any,
    });
    m.inst_mut(call).unwrap().result = Some(r);
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(r, call);
    assert!(ans.has_unknown);
    assert_eq!(oracle.query(r, call).sites.len(), 0);
}

/// Determinism: two engines over the same module answer identically,
/// and repeated interleaved queries are stable.
#[test]
fn answers_are_deterministic() {
    let (m, _caller, result, call, _site) = mk_call_result_module();
    let graph = CallGraph::build(&m);
    let a = Rung1AliasOracle::new(&m, &graph);
    let b = Rung1AliasOracle::new(&m, &graph);
    assert_eq!(a.query(result, call), b.query(result, call));
    assert_eq!(a.site_info_at(result, call), b.site_info_at(result, call));
    // Interleaving does not change completed answers.
    let first = a.query(result, call);
    let _ = a.query(result, call);
    assert_eq!(a.query(result, call), first);
}

#[test]
fn new_constructor_includes_implicit_this_and_explicit_object_returns() {
    let mut m = mk_module();
    let ctor_void = add_func_named(&mut m, "CtorVoid");
    {
        let b = entry_of(&m, ctor_void);
        m.func_mut(ctor_void).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
        add_param(&mut m, ctor_void, 0);
        add_param(&mut m, ctor_void, 1);
        add_param(&mut m, ctor_void, 2);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let ctor_mixed = add_func_named(&mut m, "CtorMixed");
    let explicit_obj;
    {
        let b = entry_of(&m, ctor_mixed);
        m.func_mut(ctor_mixed).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
        let t = add_block(&mut m, ctor_mixed);
        let e = add_block(&mut m, ctor_mixed);
        add_param(&mut m, ctor_mixed, 0);
        add_param(&mut m, ctor_mixed, 1);
        add_param(&mut m, ctor_mixed, 2);
        let cond = load_number(&mut m, b, 1.0);
        emit_void(
            &mut m,
            b,
            Op::CondBranch {
                cond,
                true_dest: t,
                false_dest: e,
            },
        );
        explicit_obj = alloc_object(&mut m, t);
        emit_void(
            &mut m,
            t,
            Op::Return {
                value: Some(explicit_obj),
            },
        );
        emit_void(&mut m, e, Op::Return { value: None });
        link(&mut m, b, t);
        link(&mut m, b, e);
    }

    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let df_void = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: ctor_void,
            captures: vec![],
            length: 0,
        },
    );
    let clo_void = emit(&mut m, entry, Op::AllocClosure { func: df_void });
    let inst_void = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo_void,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    let new_void_iid = inst_void.inst_of(&m);

    let df_mixed = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: ctor_mixed,
            captures: vec![],
            length: 0,
        },
    );
    let clo_mixed = emit(&mut m, entry, Op::AllocClosure { func: df_mixed });
    let inst_mixed = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo_mixed,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    let new_mixed_iid = inst_mixed.inst_of(&m);
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);

    let ans_void = oracle.query(inst_void, new_void_iid);
    assert!(ans_void.is_single_precise(), "{ans_void:?}");
    assert_eq!(
        ans_void.sites.iter().collect::<Vec<_>>(),
        vec![new_void_iid]
    );

    let ans_mixed = oracle.query(inst_mixed, new_mixed_iid);
    assert!(ans_mixed.precise_for_keying() && ans_mixed.has_phi);
    let mut expected = vec![new_mixed_iid, explicit_obj.inst_of(&m)];
    expected.sort();
    assert_eq!(ans_mixed.sites.iter().collect::<Vec<_>>(), expected);
}

/// A `TryGetGlobal` helper for tests (the lifter's global-load shape).
fn try_get_global(m: &mut Module, b: abcd_ir::BlockId, name: &str) -> ValueId {
    let sym = m.sym.intern(name);
    emit(
        m,
        b,
        Op::TryGetGlobal {
            name: sym,
            default: None,
        },
    )
}

#[test]
fn out_of_bounds_ids_and_balanced_module_hop_context_preservation() {
    use abcd_ir::ClassId;
    use abcd_ir::module::{ClassData, EsModule, ExportDecl, ImportDecl, ModuleRequest};
    use abcd_ir::op::ModuleVarKind;

    // 1. Out-of-bounds ValueId / InstId / BlockId / FuncId never panic.
    let mut m_oob = mk_module();
    let f_oob = add_func_named(&mut m_oob, "oob");
    let b_oob = entry_of(&m_oob, f_oob);
    emit_void(&mut m_oob, b_oob, Op::Return { value: None });
    // Inject an out-of-bounds block/param reference on a synthetic function.
    m_oob.functions[f_oob.index()]
        .blocks
        .push(abcd_ir::BlockId::new(999));
    m_oob.functions[f_oob.index()]
        .params
        .push(ValueId::new(999));
    let g_oob = CallGraph::build(&m_oob);
    let r1_oob = Rung1AliasOracle::new(&m_oob, &g_oob);
    let ans_oob = r1_oob.query(ValueId::new(9999), InstId::new(9999));
    assert!(ans_oob.has_unknown);
    let info_oob = r1_oob.site_info_at(ValueId::new(9999), InstId::new(9999));
    assert!(info_oob.has_unknown);

    // 2. Balanced `ModuleHop`:
    //    - Record A (`Lmod_a;`): `id_fn(x) { return x; }`; `func_main_0` calls
    //      `id_fn(exported_obj)` AND `id_fn(decoy_obj)`, storing `id_fn(exported_obj)`
    //      into `StoreModuleVar(0)`.
    //    - Record B (`Lmod_b;`): `wrap(y)` loads `LoadModuleVar(External, 0)` (hopping
    //      across modules while `ctx = [call_wrap]` is non-empty!) AND returns a `Phi`
    //      of `(imported, y)` so `y` MUST still pop `call_wrap` from `ctx` AFTER
    //      `ModuleHop` finishes!
    let mut m = Module::new();
    let s_x = m.sym.intern("x");
    let req_a = m.sym.intern("./mod_a");

    let cid_a = ClassId::new(0);
    let mut cls_a = ClassData::new(m.sym.intern("Lmod_a;"), m.sym.intern("mod_a"));
    cls_a.es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![ExportDecl::Local {
            local_name: s_x,
            export_name: s_x,
        }],
        module_requests: Vec::new(),
    });
    m.classes.push(cls_a);

    let cid_b = ClassId::new(1);
    let mut cls_b = ClassData::new(m.sym.intern("Lmod_b;"), m.sym.intern("mod_b"));
    cls_b.es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: s_x,
            import_name: s_x,
            module_request: req_a,
        }],
        exports: Vec::new(),
        module_requests: vec![ModuleRequest {
            specifier: req_a,
            lazy: false,
        }],
    });
    m.classes.push(cls_b);

    let add_rec_fn = |m: &mut Module, cid: ClassId, name: &str, formals: u16| {
        let sym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = abcd_ir::FunctionData::new(cid, sym, abcd_ir::FunctionKind::Function);
        fd.modifiers = abcd_ir::Modifiers::STATIC;
        m.functions.push(fd);
        m.classes[cid.index()].methods.push(fid);
        let b = add_block(m, fid);
        let mut ps = Vec::new();
        for i in 0..(3 + formals) {
            ps.push(add_param(m, fid, i));
        }
        (fid, b, ps)
    };

    // `id_fn(x) { return x; }` in `mod_a`.
    let (id_fn, b_id, p_id) = add_rec_fn(&mut m, cid_a, "id_fn", 1);
    emit_void(
        &mut m,
        b_id,
        Op::Return {
            value: Some(p_id[3]),
        },
    );

    // `mod_a::func_main_0`: exports `id_fn(exp_obj)` and separately calls `id_fn(decoy_a)`.
    let (_, b_ma, _) = add_rec_fn(&mut m, cid_a, "func_main_0", 0);
    let exp_obj = alloc_object(&mut m, b_ma);
    let exp_site = exp_obj.inst_of(&m);
    let decoy_a = alloc_object(&mut m, b_ma);
    let id_ref1 = load_method_ref(&mut m, b_ma, id_fn);
    let exp_via_id = emit(
        &mut m,
        b_ma,
        Op::Call {
            callee: id_ref1,
            this: None,
            args: vec![exp_obj],
            kind: CallKind::Direct,
        },
    );
    let _ = emit(
        &mut m,
        b_ma,
        Op::Call {
            callee: id_ref1,
            this: None,
            args: vec![decoy_a],
            kind: CallKind::Direct,
        },
    );
    emit_void(
        &mut m,
        b_ma,
        Op::StoreModuleVar {
            index: 0,
            value: exp_via_id,
        },
    );
    emit_void(&mut m, b_ma, Op::Return { value: None });

    // `mod_b::wrap(y)`: merges `LoadModuleVar(External, 0)` AND parameter `y`.
    let (wrap_fn, b_w_entry, p_w) = add_rec_fn(&mut m, cid_b, "wrap", 1);
    let b_w_left = add_block(&mut m, wrap_fn);
    let b_w_right = add_block(&mut m, wrap_fn);
    let b_w_join = add_block(&mut m, wrap_fn);
    let cond = load_number(&mut m, b_w_entry, 1.0);
    emit_void(
        &mut m,
        b_w_entry,
        Op::CondBranch {
            cond,
            true_dest: b_w_left,
            false_dest: b_w_right,
        },
    );
    link(&mut m, b_w_entry, b_w_left);
    link(&mut m, b_w_entry, b_w_right);

    let imp_val = emit(
        &mut m,
        b_w_left,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    emit_void(&mut m, b_w_left, Op::Branch { dest: b_w_join });
    emit_void(&mut m, b_w_right, Op::Branch { dest: b_w_join });
    link(&mut m, b_w_left, b_w_join);
    link(&mut m, b_w_right, b_w_join);

    let merged = emit(
        &mut m,
        b_w_join,
        Op::Phi {
            entries: vec![
                (
                    abcd_ir::Edge {
                        from: b_w_left,
                        kind: abcd_ir::EdgeKind::Normal,
                    },
                    imp_val,
                ),
                (
                    abcd_ir::Edge {
                        from: b_w_right,
                        kind: abcd_ir::EdgeKind::Normal,
                    },
                    p_w[3],
                ),
            ],
        },
    );
    emit_void(
        &mut m,
        b_w_join,
        Op::Return {
            value: Some(merged),
        },
    );

    // `mod_b::func_main_0` calls `wrap(caller1_arg)` and `wrap(caller2_decoy)`:
    // querying `res1` MUST resolve `imp_val` to `{exp_site}` AND `p_w[3]` ONLY to
    // `{caller1_site}` (never `decoy_a` and never `caller2_decoy`)!
    let (_, b_mb, _) = add_rec_fn(&mut m, cid_b, "func_main_0", 0);
    let caller1_arg = alloc_object(&mut m, b_mb);
    let caller1_site = caller1_arg.inst_of(&m);
    let caller2_decoy = alloc_object(&mut m, b_mb);
    let wrap_ref = load_method_ref(&mut m, b_mb, wrap_fn);
    let res1 = emit(
        &mut m,
        b_mb,
        Op::Call {
            callee: wrap_ref,
            this: None,
            args: vec![caller1_arg],
            kind: CallKind::Direct,
        },
    );
    let call1_iid = res1.inst_of(&m);
    let _ = emit(
        &mut m,
        b_mb,
        Op::Call {
            callee: wrap_ref,
            this: None,
            args: vec![caller2_decoy],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, b_mb, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    let r1 = Rung1AliasOracle::new(&m, &cg);
    let ans = r1.query(res1, call1_iid);
    assert!(
        ans.precise_for_keying(),
        "balanced across ModuleHop: {ans:?}"
    );
    let mut expected = vec![exp_site, caller1_site];
    expected.sort();
    assert_eq!(ans.sites.iter().collect::<Vec<_>>(), expected);
}
