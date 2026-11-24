//! Rung-2 PTA unit tests, one per mechanism (the task's gate 4):
//! context keys, field sensitivity, delta propagation, the co-evolution
//! fixed point, env identity, array elements, globals, determinism, and
//! the depth/budget caps.

use super::*;
use crate::callgraph::CallTargets;
use crate::dataflow::ifds::CallGraphOracle;
use crate::testutil::*;
use abcd_ir::{BlockId, CallKind, Modifiers, Op};

/// Run the engine with the default config over `m`.
fn run(m: &Module) -> PtaOutcome {
    let base = CallGraph::build(m);
    analyze(m, &base, &PtaConfig::default())
}

/// A STATIC callee helper (the vendored 0xF frame-slot default applies,
/// so argument binding is precise — the es2abc shape).
fn add_static_func(m: &mut Module, name: &str, formals: u16) -> (FuncId, Vec<ValueId>) {
    let f = add_func_named(m, name);
    m.func_mut(f).unwrap().modifiers = Modifiers::STATIC;
    // func, newTarget, this, then the formals (N66).
    let mut params = Vec::new();
    for i in 0..(3 + formals) {
        params.push(add_param(m, f, i));
    }
    (f, params)
}

/// Define + allocate a closure of `body` in block `b`.
fn closure_of(m: &mut Module, b: BlockId, body: FuncId) -> ValueId {
    let def = emit(
        m,
        b,
        Op::DefineFunc {
            body,
            captures: vec![],
            length: 0,
        },
    );
    emit(m, b, Op::AllocClosure { func: def })
}

/// Emit a `NewLexEnv` with its result value wired (emit() asserts
/// has_result; NewLexEnv does produce the env).
fn new_lex_env(m: &mut Module, b: BlockId) -> InstId {
    emit(m, b, Op::NewLexEnv { num_vars: 1 });
    InstId::new(m.insts.len() as u32 - 1)
}

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
        super::super::heap::update_kind(&info),
        super::super::heap::UpdateKind::Weak
    );
}

// ── Lexical-environment identity (the b2 shape) ─────────────────────

/// The b2 module shape at IR level: two functions each with a
/// `NewLexEnv` and a slot-(0,0) capture; the two closures' `GetLexVar`
/// must resolve to their OWN function's environment.
#[test]
fn env_identity_separates_colliding_slots() {
    let mut m = mk_module();
    // f: GetLexVar(0,0); return it.
    let f = add_func_named(&mut m, "f");
    let get_in_f;
    {
        let b = entry_of(&m, f);
        let r = emit(&mut m, b, Op::GetLexVar { level: 0, slot: 0 });
        let ValueDef::Inst(i) = m.value(r).unwrap().def else {
            panic!()
        };
        get_in_f = i;
        emit_void(&mut m, b, Op::Return { value: Some(r) });
    }
    // g: same shape.
    let g = add_func_named(&mut m, "g");
    let get_in_g;
    {
        let b = entry_of(&m, g);
        let r = emit(&mut m, b, Op::GetLexVar { level: 0, slot: 0 });
        let ValueDef::Inst(i) = m.value(r).unwrap().def else {
            panic!()
        };
        get_in_g = i;
        emit_void(&mut m, b, Op::Return { value: Some(r) });
    }
    // main: env E1; E1[0] = taint; define f-closure; call it.
    let main = add_func_named(&mut m, "main");
    let env_main;
    {
        let b = entry_of(&m, main);
        env_main = new_lex_env(&mut m, b);
        let taint = load_string(&mut m, b, "tainted");
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: taint,
            },
        );
        let clo_f = closure_of(&mut m, b, f);
        push_inst(
            &mut m,
            b,
            Op::Call {
                callee: clo_f,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }
    // innocent: env E2; E2[0] = clean; define g-closure; call it.
    let innocent = add_func_named(&mut m, "innocent");
    let env_innocent;
    {
        let b = entry_of(&m, innocent);
        env_innocent = new_lex_env(&mut m, b);
        let clean = load_string(&mut m, b, "clean");
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: clean,
            },
        );
        let clo_g = closure_of(&mut m, b, g);
        push_inst(
            &mut m,
            b,
            Op::Call {
                callee: clo_g,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let ef = oracle.lex_env_at(get_in_f, 0);
    let eg = oracle.lex_env_at(get_in_g, 0);
    assert!(!ef.has_unknown, "{ef:?}");
    assert!(!eg.has_unknown, "{eg:?}");
    assert_eq!(ef.sites, AllocSiteSet::one(env_main));
    assert_eq!(eg.sites, AllocSiteSet::one(env_innocent));
    assert!(
        ef.sites != eg.sites,
        "the colliding (0,0) slots live in distinguishable environments"
    );
    assert!(oracle.is_env_site(env_main));
    assert!(oracle.is_env_site(env_innocent));
    let past = oracle.lex_env_at(get_in_f, 1);
    assert!(past.has_unknown, "a level past the chain is unknown");
}

// ── Env depth cap ───────────────────────────────────────────────────

#[test]
fn env_depth_cap_drops_outer_environments() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _e1 = new_lex_env(&mut m, b);
    let e2 = new_lex_env(&mut m, b);
    let g0 = emit(&mut m, b, Op::GetLexVar { level: 0, slot: 0 });
    let g1 = emit(&mut m, b, Op::GetLexVar { level: 1, slot: 0 });
    emit_void(&mut m, b, Op::Return { value: None });

    let base = CallGraph::build(&m);
    let out = analyze(
        &m,
        &base,
        &PtaConfig {
            max_env_depth: 1,
            ..PtaConfig::default()
        },
    );
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let inst_of = |v: ValueId| match m.value(v).unwrap().def {
        ValueDef::Inst(i) => i,
        _ => panic!(),
    };
    let a0 = oracle.lex_env_at(inst_of(g0), 0);
    assert_eq!(a0.sites, AllocSiteSet::one(e2), "the innermost survives");
    assert!(!a0.has_unknown);
    let a1 = oracle.lex_env_at(inst_of(g1), 1);
    assert!(
        a1.has_unknown,
        "the outer env was dropped by the cap — level 1 is unknown"
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
fn nested_closure_capture_propagates_through_lex_free_middle_function() {
    let mut m = mk_module();
    // inner: GetLexVar(0, 0) — captures outer's env through middle (which has no lex ops).
    let inner = add_func_named(&mut m, "inner");
    let get_in_inner;
    let inner_ret;
    {
        let b = entry_of(&m, inner);
        inner_ret = emit(&mut m, b, Op::GetLexVar { level: 0, slot: 0 });
        let ValueDef::Inst(i) = m.value(inner_ret).unwrap().def else {
            panic!()
        };
        get_in_inner = i;
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(inner_ret),
            },
        );
    }
    // middle: no NewLexEnv/PopLexEnv; defines and calls inner.
    let middle = add_func_named(&mut m, "middle");
    {
        let b = entry_of(&m, middle);
        let clo_inner = closure_of(&mut m, b, inner);
        push_inst(
            &mut m,
            b,
            Op::Call {
                callee: clo_inner,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }
    // outer: NewLexEnv; PutLexVar(0, 0, obj); defines and calls middle.
    let outer = add_func_named(&mut m, "outer");
    let env_outer;
    let stored_obj;
    {
        let b = entry_of(&m, outer);
        env_outer = new_lex_env(&mut m, b);
        stored_obj = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: stored_obj,
            },
        );
        let clo_mid = closure_of(&mut m, b, middle);
        push_inst(
            &mut m,
            b,
            Op::Call {
                callee: clo_mid,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let env = oracle.lex_env_at(get_in_inner, 0);
    assert!(!env.has_unknown);
    assert_eq!(env.sites, AllocSiteSet::one(env_outer));
    let ans = oracle.query(inner_ret, get_in_inner);
    assert!(!ans.has_unknown);
    assert_eq!(ans.sites, oracle.query(stored_obj, env_outer).sites);
}

fn add_record_fn(
    m: &mut Module,
    cid: ClassId,
    name: &str,
    formals: u16,
) -> (FuncId, BlockId, Vec<ValueId>) {
    let sym = m.sym.intern(name);
    let fid = FuncId::new(m.functions.len() as u32);
    let mut fd = abcd_ir::FunctionData::new(cid, sym, abcd_ir::FunctionKind::Function);
    fd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    let bid = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(abcd_ir::function::Block::default());
    fd.blocks.push(bid);
    let mut params = Vec::new();
    for i in 0..(3 + formals) {
        let vid = ValueId::new(m.values.len() as u32);
        m.values.push(abcd_ir::function::Value {
            def: ValueDef::Param(i),
            ty: abcd_ir::ty::Ty::Any,
        });
        fd.params.push(vid);
        params.push(vid);
    }
    m.functions.push(fd);
    m.classes[cid.index()].methods.push(fid);
    (fid, bid, params)
}

#[test]
fn define_class_methods_capture_enclosing_lexical_env() {
    let mut m = mk_module();
    let (ctor, ctor_b, _) = add_record_fn(&mut m, ClassId::new(0), "Cls", 0);
    let get_in_ctor = emit(&mut m, ctor_b, Op::GetLexVar { level: 0, slot: 0 });
    emit_void(&mut m, ctor_b, Op::Return { value: None });

    let (method, method_b, _) = add_record_fn(&mut m, ClassId::new(0), "work", 0);
    let get_in_method = emit(&mut m, method_b, Op::GetLexVar { level: 0, slot: 0 });
    let ValueDef::Inst(get_method_iid) = m.value(get_in_method).unwrap().def else {
        panic!()
    };
    emit_void(
        &mut m,
        method_b,
        Op::Return {
            value: Some(get_in_method),
        },
    );

    let main = add_func_named(&mut m, "main");
    let main_b = entry_of(&m, main);
    let env_site = new_lex_env(&mut m, main_b);
    let captured_obj = alloc_object(&mut m, main_b);
    emit_void(
        &mut m,
        main_b,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: captured_obj,
        },
    );
    let work_sym = intern(&mut m, "work");
    let members = m.consts.push(Const::ArrayLiteral(vec![
        Const::String(work_sym),
        Const::MethodRef(method),
        Const::number(1.0),
    ]));
    let cls_val = emit(
        &mut m,
        main_b,
        Op::DefineClass {
            ctor,
            heritage: None,
            members,
            member_attrs: Vec::new(),
            count: 0,
        },
    );
    let inst = emit(
        &mut m,
        main_b,
        Op::Call {
            callee: cls_val,
            this: None,
            args: Vec::new(),
            kind: CallKind::New,
        },
    );
    let m_val = emit(
        &mut m,
        main_b,
        Op::LoadProp {
            object: inst,
            name: work_sym,
        },
    );
    let _ = push_inst(
        &mut m,
        main_b,
        Op::Call {
            callee: m_val,
            this: Some(inst),
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, main_b, Op::Return { value: None });

    let links = ModuleLinkTable::build(&m);
    let base = CallGraph::build_with_links(&m, &links);
    let out = analyze_with_links_and_roots(&m, &links, &base, &PtaConfig::default(), Some(&[main]));
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);

    let env_ans = oracle.lex_env_at(get_method_iid, 0);
    assert!(!env_ans.has_unknown);
    assert_eq!(env_ans.sites, AllocSiteSet::one(env_site));
    for v in [get_in_ctor, get_in_method] {
        let q = oracle.query(v, get_method_iid);
        assert!(!q.has_unknown, "{q:?}");
        assert_eq!(q.sites, oracle.query(captured_obj, env_site).sites);
    }
}

#[test]
fn root_sliced_pta_skips_dead_functions_and_resolves_oop_imports_and_callbacks() {
    use abcd_ir::module::{ClassData, EsModule, ExportDecl, ImportDecl, ModuleRequest};
    use abcd_ir::op::ModuleVarKind;

    let mut m = Module::new();

    // Record 0: exporter (`export const sharedBox = { item: payload }`).
    let d0 = m.sym.intern("L@bundle:app/entry/ets/exporter;");
    let n0 = m.sym.intern("@bundle:app/entry/ets/exporter");
    let mut c0 = ClassData::new(d0, n0);
    let box_sym = m.sym.intern("sharedBox");
    c0.es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![ExportDecl::Local {
            local_name: box_sym,
            export_name: box_sym,
        }],
        module_requests: Vec::new(),
    });
    m.classes.push(c0);
    let cid_exporter = ClassId::new(0);

    // Record 1: unreferenced module + 25 dead functions.
    let d1 = m.sym.intern("L@bundle:app/entry/ets/unused;");
    let n1 = m.sym.intern("@bundle:app/entry/ets/unused");
    let mut c1 = ClassData::new(d1, n1);
    let unused_sym = m.sym.intern("unusedExport");
    c1.es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![ExportDecl::Local {
            local_name: unused_sym,
            export_name: unused_sym,
        }],
        module_requests: Vec::new(),
    });
    m.classes.push(c1);
    let cid_unused = ClassId::new(1);

    // Record 2: entry module importing `./exporter`.
    let d2 = m.sym.intern("L@bundle:app/entry/ets/entry;");
    let n2 = m.sym.intern("@bundle:app/entry/ets/entry");
    let req_exporter = m.sym.intern("./exporter");
    let mut c2 = ClassData::new(d2, n2);
    c2.es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: box_sym,
            import_name: box_sym,
            module_request: req_exporter,
        }],
        exports: Vec::new(),
        module_requests: vec![ModuleRequest {
            specifier: req_exporter,
            lazy: false,
        }],
    });
    m.classes.push(c2);
    let cid_entry = ClassId::new(2);

    let item_sym = intern(&mut m, "item");
    let field_sym = intern(&mut m, "field");
    let read_sym = intern(&mut m, "readField");

    // Exporter `func_main_0`: NOT in `roots`; should activate on demand via `LoadModuleVar`.
    let (_exporter_main, exp_b, _) = add_record_fn(&mut m, cid_exporter, "func_main_0", 0);
    let exported_box = alloc_object(&mut m, exp_b);
    let exported_payload = alloc_object(&mut m, exp_b);
    emit_void(
        &mut m,
        exp_b,
        Op::StoreProp {
            object: exported_box,
            name: item_sym,
            value: exported_payload,
        },
    );
    emit_void(
        &mut m,
        exp_b,
        Op::StoreModuleVar {
            index: 0,
            value: exported_box,
        },
    );
    emit_void(&mut m, exp_b, Op::Return { value: None });

    // Unused record `func_main_0` + 25 dead functions that must never be scanned.
    let (_unused_main, un_b, _) = add_record_fn(&mut m, cid_unused, "func_main_0", 0);
    let dead_val = alloc_object(&mut m, un_b);
    emit_void(
        &mut m,
        un_b,
        Op::StoreModuleVar {
            index: 0,
            value: dead_val,
        },
    );
    emit_void(&mut m, un_b, Op::Return { value: None });
    for idx in 0..25 {
        let (_, db, _) = add_record_fn(&mut m, cid_unused, &format!("dead_{idx}"), 0);
        let o = alloc_object(&mut m, db);
        emit_void(
            &mut m,
            db,
            Op::StoreProp {
                object: o,
                name: item_sym,
                value: o,
            },
        );
        emit_void(&mut m, db, Op::Return { value: None });
    }

    // External SDK registration stub `sdk_register(cb)`.
    let sdk_sym = m.sym.intern("sdk_register");
    let sdk_fn = FuncId::new(m.functions.len() as u32);
    let mut sdk_fd =
        abcd_ir::FunctionData::new(cid_entry, sdk_sym, abcd_ir::FunctionKind::Function);
    sdk_fd.is_external = true;
    m.functions.push(sdk_fd);
    m.classes[cid_entry.index()].methods.push(sdk_fn);

    // OOP class `Service`: `constructor(v) { this.field = v; }`, `readField() { return this.field; }`.
    let (svc_ctor, ctor_b, ctor_params) = add_record_fn(&mut m, cid_entry, "Service", 1);
    emit_void(
        &mut m,
        ctor_b,
        Op::StoreProp {
            object: ctor_params[2], // this
            name: field_sym,
            value: ctor_params[3], // formal 0
        },
    );
    emit_void(&mut m, ctor_b, Op::Return { value: None });

    let (svc_read, read_b, read_params) = add_record_fn(&mut m, cid_entry, "readField", 0);
    let loaded_this_field = emit(
        &mut m,
        read_b,
        Op::LoadProp {
            object: read_params[2], // this
            name: field_sym,
        },
    );
    emit_void(
        &mut m,
        read_b,
        Op::Return {
            value: Some(loaded_this_field),
        },
    );

    // Callback closure passed to external `sdk_register`: must be activated via `DefineFunc`.
    let (sdk_cb, cb_b, _) = add_record_fn(&mut m, cid_entry, "sdk_cb", 0);
    let cb_local_alloc = alloc_object(&mut m, cb_b);
    let cb_captured = emit(&mut m, cb_b, Op::GetLexVar { level: 0, slot: 0 });
    emit_void(&mut m, cb_b, Op::Return { value: None });

    // Entry function (the ONLY function in `roots`).
    let (entry_main, eb, _) = add_record_fn(&mut m, cid_entry, "entry_main", 0);
    let _env = new_lex_env(&mut m, eb);
    let lex_obj = alloc_object(&mut m, eb);
    emit_void(
        &mut m,
        eb,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: lex_obj,
        },
    );
    let members = m.consts.push(Const::ArrayLiteral(vec![
        Const::String(read_sym),
        Const::MethodRef(svc_read),
        Const::number(1.0),
    ]));
    let svc_cls = emit(
        &mut m,
        eb,
        Op::DefineClass {
            ctor: svc_ctor,
            heritage: None,
            members,
            member_attrs: Vec::new(),
            count: 1,
        },
    );
    let secret_obj = alloc_object(&mut m, eb);
    let svc_inst = emit(
        &mut m,
        eb,
        Op::Call {
            callee: svc_cls,
            this: None,
            args: vec![secret_obj],
            kind: CallKind::New,
        },
    );
    let read_m = emit(
        &mut m,
        eb,
        Op::LoadProp {
            object: svc_inst,
            name: read_sym,
        },
    );
    let _ = push_inst(
        &mut m,
        eb,
        Op::Call {
            callee: read_m,
            this: Some(svc_inst),
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    let imported_box = emit(
        &mut m,
        eb,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let imported_item = emit(
        &mut m,
        eb,
        Op::LoadProp {
            object: imported_box,
            name: item_sym,
        },
    );
    let cb_val = emit(
        &mut m,
        eb,
        Op::DefineFunc {
            body: sdk_cb,
            captures: Vec::new(),
            length: 0,
        },
    );
    let sdk_ref = load_method_ref(&mut m, eb, sdk_fn);
    let _ = push_inst(
        &mut m,
        eb,
        Op::Call {
            callee: sdk_ref,
            this: None,
            args: vec![cb_val],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, eb, Op::Return { value: None });

    let links = ModuleLinkTable::build(&m);
    let base = CallGraph::build_with_links(&m, &links);
    let full = analyze_with_links_and_roots(&m, &links, &base, &PtaConfig::default(), None);
    let sliced = analyze_with_links_and_roots(
        &m,
        &links,
        &base,
        &PtaConfig::default(),
        Some(&[entry_main]),
    );

    // Whole-module scans all 30+ internal functions; root-sliced scans only the
    // 5 reachable activations (`entry_main`, `exporter_main`, `svc_ctor`, `svc_read`, `sdk_cb`).
    assert!(full.stats().activations >= 30);
    assert_eq!(sliced.stats().activations, 5);

    let (_, tables, stats) = sliced.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);

    // OOP `this.field` inside `Service::readField` resolves single-precisely to `secret_obj`.
    let ans_field = oracle.query(loaded_this_field, InstId::new(0));
    assert!(!ans_field.has_unknown, "{ans_field:?}");
    assert_eq!(
        ans_field.sites,
        oracle.query(secret_obj, InstId::new(0)).sites
    );

    // Cross-module `LoadModuleVar` + `.item` resolves single-precisely to `exported_payload`.
    let ans_imp = oracle.query(imported_item, InstId::new(0));
    assert!(!ans_imp.has_unknown, "{ans_imp:?}");
    assert_eq!(
        ans_imp.sites,
        oracle.query(exported_payload, InstId::new(0)).sites
    );

    // Callback closure passed to external SDK function was scanned and captured `lex_obj`.
    let ans_cb_alloc = oracle.query(cb_local_alloc, InstId::new(0));
    assert!(ans_cb_alloc.is_single_precise());
    let ans_cb_lex = oracle.query(cb_captured, InstId::new(0));
    assert!(!ans_cb_lex.has_unknown, "{ans_cb_lex:?}");
    assert_eq!(
        ans_cb_lex.sites,
        oracle.query(lex_obj, InstId::new(0)).sites
    );
}

#[test]
fn root_sliced_pta_filters_ohos_harness_unrelated_inits_and_views() {
    use crate::ohos_lifecycle::synthesize_ohos_harness;
    use abcd_ir::module::ClassData;

    let mut m = Module::new();

    // Record 0: `EntryAbility extends UIAbility` + `RootedPage extends ViewPU`.
    let d0 = m
        .sym
        .intern("L@bundle:app/entry/ets/entryability/EntryAbility;");
    let n0 = m
        .sym
        .intern("@bundle:app/entry/ets/entryability/EntryAbility");
    m.classes.push(ClassData::new(d0, n0));
    let cid_ability = ClassId::new(0);

    let helper_sym = intern(&mut m, "helper");
    let state_sym = intern(&mut m, "stateObj");
    let on_create_sym = intern(&mut m, "onCreate");
    let initial_render_sym = intern(&mut m, "initialRender");
    let rerender_sym = intern(&mut m, "rerender");
    let ui_ability_sym = intern(&mut m, "UIAbility");
    let view_pu_sym = intern(&mut m, "ViewPU");

    let (ab_ctor, ab_ctor_b, ab_ctor_p) = add_record_fn(&mut m, cid_ability, "EntryAbility", 0);
    let ab_helper_alloc = alloc_object(&mut m, ab_ctor_b);
    emit_void(
        &mut m,
        ab_ctor_b,
        Op::StoreProp {
            object: ab_ctor_p[2],
            name: helper_sym,
            value: ab_helper_alloc,
        },
    );
    emit_void(&mut m, ab_ctor_b, Op::Return { value: None });

    let (ab_on_create, ab_oc_b, ab_oc_p) = add_record_fn(&mut m, cid_ability, "onCreate", 2);
    let ab_loaded_helper = emit(
        &mut m,
        ab_oc_b,
        Op::LoadProp {
            object: ab_oc_p[2],
            name: helper_sym,
        },
    );
    emit_void(&mut m, ab_oc_b, Op::Return { value: None });

    let (rv_ctor, rv_ctor_b, rv_ctor_p) = add_record_fn(&mut m, cid_ability, "RootedPage", 0);
    let rv_state_alloc = alloc_object(&mut m, rv_ctor_b);
    emit_void(
        &mut m,
        rv_ctor_b,
        Op::StoreProp {
            object: rv_ctor_p[2],
            name: state_sym,
            value: rv_state_alloc,
        },
    );
    emit_void(&mut m, rv_ctor_b, Op::Return { value: None });

    let (rv_render, rv_ren_b, rv_ren_p) = add_record_fn(&mut m, cid_ability, "initialRender", 0);
    let rv_loaded_state = emit(
        &mut m,
        rv_ren_b,
        Op::LoadProp {
            object: rv_ren_p[2],
            name: state_sym,
        },
    );
    emit_void(&mut m, rv_ren_b, Op::Return { value: None });

    let (rv_rerender, rv_rer_b, _) = add_record_fn(&mut m, cid_ability, "rerender", 0);
    emit_void(&mut m, rv_rer_b, Op::Return { value: None });

    let (_entry_init, ei_b, _) = add_record_fn(&mut m, cid_ability, "func_main_0", 0);
    let ui_base = emit(
        &mut m,
        ei_b,
        Op::TryGetGlobal {
            name: ui_ability_sym,
            default: None,
        },
    );
    let ab_members = m.consts.push(Const::ArrayLiteral(vec![
        Const::String(on_create_sym),
        Const::MethodRef(ab_on_create),
        Const::number(1.0),
    ]));
    let _ = emit(
        &mut m,
        ei_b,
        Op::DefineClass {
            ctor: ab_ctor,
            heritage: Some(ui_base),
            members: ab_members,
            member_attrs: Vec::new(),
            count: 0,
        },
    );
    let vp_base = emit(
        &mut m,
        ei_b,
        Op::TryGetGlobal {
            name: view_pu_sym,
            default: None,
        },
    );
    let rv_members = m.consts.push(Const::ArrayLiteral(vec![
        Const::String(initial_render_sym),
        Const::MethodRef(rv_render),
        Const::String(rerender_sym),
        Const::MethodRef(rv_rerender),
        Const::number(2.0),
    ]));
    let _ = emit(
        &mut m,
        ei_b,
        Op::DefineClass {
            ctor: rv_ctor,
            heritage: Some(vp_base),
            members: rv_members,
            member_attrs: Vec::new(),
            count: 0,
        },
    );
    emit_void(&mut m, ei_b, Op::Return { value: None });

    // 20 unrelated module records with `func_main_0` + `ViewPU` components (none in `roots`).
    for idx in 0..20 {
        let d = m
            .sym
            .intern(&format!("L@bundle:app/entry/ets/pages/Unrelated{idx};"));
        let n = m
            .sym
            .intern(&format!("@bundle:app/entry/ets/pages/Unrelated{idx}"));
        let cid = ClassId::new(m.classes.len() as u32);
        m.classes.push(ClassData::new(d, n));
        let (u_ctor, u_cb, _) = add_record_fn(&mut m, cid, "UnrelatedPage", 0);
        emit_void(&mut m, u_cb, Op::Return { value: None });
        let (u_ren, u_rb, _) = add_record_fn(&mut m, cid, "initialRender", 0);
        emit_void(&mut m, u_rb, Op::Return { value: None });
        let (u_rer, u_reb, _) = add_record_fn(&mut m, cid, "rerender", 0);
        emit_void(&mut m, u_reb, Op::Return { value: None });
        let (_, u_mb, _) = add_record_fn(&mut m, cid, "func_main_0", 0);
        let base_g = emit(
            &mut m,
            u_mb,
            Op::TryGetGlobal {
                name: view_pu_sym,
                default: None,
            },
        );
        let mem = m.consts.push(Const::ArrayLiteral(vec![
            Const::String(initial_render_sym),
            Const::MethodRef(u_ren),
            Const::String(rerender_sym),
            Const::MethodRef(u_rer),
            Const::number(2.0),
        ]));
        let _ = emit(
            &mut m,
            u_mb,
            Op::DefineClass {
                ctor: u_ctor,
                heritage: Some(base_g),
                members: mem,
                member_attrs: Vec::new(),
                count: 0,
            },
        );
        emit_void(&mut m, u_mb, Op::Return { value: None });
    }

    let (aug, harness_fid) = synthesize_ohos_harness(&m, None).expect("harness synthesized");
    let links = ModuleLinkTable::build(&aug);
    let base = CallGraph::build_with_links(&aug, &links);
    let out = analyze_with_links_and_roots(
        &aug,
        &links,
        &base,
        &PtaConfig::default(),
        Some(&[harness_fid, rv_render]),
    );

    // None of the 20 unrelated `func_main_0`s or 20 unrelated `ViewPU`s (80 functions)
    // are activated; only harness + EntryAbility(ctor, onCreate) + RootedPage(ctor, initialRender).
    assert!(
        out.stats().activations <= 8,
        "unexpected activations: {}",
        out.stats().activations
    );

    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&aug, tables, stats);

    let ab_ans = oracle.query(ab_loaded_helper, InstId::new(0));
    assert!(!ab_ans.has_unknown, "{ab_ans:?}");
    assert_eq!(
        ab_ans.sites,
        oracle.query(ab_helper_alloc, InstId::new(0)).sites
    );

    let rv_ans = oracle.query(rv_loaded_state, InstId::new(0));
    assert!(!rv_ans.has_unknown, "{rv_ans:?}");
    assert_eq!(
        rv_ans.sites,
        oracle.query(rv_state_alloc, InstId::new(0)).sites
    );
}

#[test]
fn root_sliced_pta_activates_namespace_exports_define_method_and_fits_256k_stack() {
    use abcd_ir::module::{ClassData, EsModule, ExportDecl, ModuleRequest};

    let builder = std::thread::Builder::new().stack_size(256 * 1024);
    builder
        .spawn(|| {
            let mut m = Module::new();

            let d0 = m.sym.intern("L@bundle:app/entry/ets/ns_mod;");
            let n0 = m.sym.intern("@bundle:app/entry/ets/ns_mod");
            let val_sym = m.sym.intern("nsVal");
            let mut c0 = ClassData::new(d0, n0);
            c0.es_module = Some(EsModule {
                imports: Vec::new(),
                exports: vec![ExportDecl::Local {
                    local_name: val_sym,
                    export_name: val_sym,
                }],
                module_requests: Vec::new(),
            });
            m.classes.push(c0);

            let d1 = m.sym.intern("L@bundle:app/entry/ets/main_mod;");
            let n1 = m.sym.intern("@bundle:app/entry/ets/main_mod");
            let req_ns = m.sym.intern("./ns_mod");
            let mut c1 = ClassData::new(d1, n1);
            c1.es_module = Some(EsModule {
                imports: Vec::new(),
                exports: Vec::new(),
                module_requests: vec![ModuleRequest {
                    specifier: req_ns,
                    lazy: false,
                }],
            });
            m.classes.push(c1);

            let (_ns_init, ns_b, _) = add_record_fn(&mut m, ClassId::new(0), "func_main_0", 0);
            let ns_exported_obj = alloc_object(&mut m, ns_b);
            emit_void(
                &mut m,
                ns_b,
                Op::StoreModuleVar {
                    index: 0,
                    value: ns_exported_obj,
                },
            );
            emit_void(&mut m, ns_b, Op::Return { value: None });

            let (dm_body, dm_b, _) = add_record_fn(&mut m, ClassId::new(1), "objMethod", 0);
            let dm_alloc = alloc_object(&mut m, dm_b);
            emit_void(&mut m, dm_b, Op::Return { value: None });

            let (entry_fn, eb, _) = add_record_fn(&mut m, ClassId::new(1), "entry", 0);
            // Deep Mov chain (1,500 hops) exercising iterative cycle-guarded helpers on 256 KiB stack.
            let mut chain_v = load_method_ref(&mut m, eb, dm_body);
            for _ in 0..1_500 {
                chain_v = emit(&mut m, eb, Op::Mov { src: chain_v });
            }
            let host = alloc_object(&mut m, eb);
            let m_sym = intern(&mut m, "m");
            let _ = emit(
                &mut m,
                eb,
                Op::DefineMethod {
                    object: host,
                    name: m_sym,
                    func: chain_v,
                    length: 0,
                },
            );
            let ns_obj = emit(&mut m, eb, Op::GetModuleNamespace { index: 0 });
            let loaded_ns_val = emit(
                &mut m,
                eb,
                Op::LoadProp {
                    object: ns_obj,
                    name: val_sym,
                },
            );
            emit_void(&mut m, eb, Op::Return { value: None });

            let links = ModuleLinkTable::build(&m);
            let base = CallGraph::build_with_links(&m, &links);
            let out = analyze_with_links_and_roots(
                &m,
                &links,
                &base,
                &PtaConfig::default(),
                Some(&[entry_fn]),
            );
            assert_eq!(out.stats().activations, 3);
            let (_, tables, stats) = out.into_parts();
            let oracle = Rung2AliasOracle::new(&m, tables, stats);

            let ans_ns = oracle.query(loaded_ns_val, InstId::new(0));
            assert!(!ans_ns.has_unknown, "{ans_ns:?}");
            assert_eq!(
                ans_ns.sites,
                oracle.query(ns_exported_obj, InstId::new(0)).sites
            );
            assert!(oracle.query(dm_alloc, InstId::new(0)).is_single_precise());
        })
        .unwrap()
        .join()
        .unwrap();
}
