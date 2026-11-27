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
    emit(
        m,
        b,
        Op::NewLexEnv {
            num_vars: 1,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
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
        let r = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
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
        let r = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
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
                kind: abcd_ir::LexEnvKind::Plain,
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
                kind: abcd_ir::LexEnvKind::Plain,
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
    let g0 = emit(
        &mut m,
        b,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let g1 = emit(
        &mut m,
        b,
        Op::GetLexVar {
            level: 1,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
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
fn nested_closure_capture_propagates_through_lex_free_middle_function() {
    let mut m = mk_module();
    // inner: GetLexVar(0, 0) — captures outer's env through middle (which has no lex ops).
    let inner = add_func_named(&mut m, "inner");
    let get_in_inner;
    let inner_ret;
    {
        let b = entry_of(&m, inner);
        inner_ret = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
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
                kind: abcd_ir::LexEnvKind::Plain,
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
    let get_in_ctor = emit(
        &mut m,
        ctor_b,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    emit_void(&mut m, ctor_b, Op::Return { value: None });

    let (method, method_b, _) = add_record_fn(&mut m, ClassId::new(0), "work", 0);
    let get_in_method = emit(
        &mut m,
        method_b,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
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
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let work_sym = intern(&mut m, "work");
    let c_work = m.consts.intern(Const::String(work_sym));
    let c_method = m.consts.intern(Const::method_ref(method));
    let c_one = m.consts.intern(Const::number(1.0));
    let members = m.consts.push_array(vec![c_work, c_method, c_one]);
    let cls_val = emit(
        &mut m,
        main_b,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor,
            heritage: None,
            members,
            member_attrs: Vec::new(),
            count: 0,
        })),
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
    let cb_captured = emit(
        &mut m,
        cb_b,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
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
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let c_read = m.consts.intern(Const::String(read_sym));
    let c_svc_read = m.consts.intern(Const::method_ref(svc_read));
    let c_one = m.consts.intern(Const::number(1.0));
    let members = m.consts.push_array(vec![c_read, c_svc_read, c_one]);
    let svc_cls = emit(
        &mut m,
        eb,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: svc_ctor,
            heritage: None,
            members,
            member_attrs: Vec::new(),
            count: 1,
        })),
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
    let c_oc = m.consts.intern(Const::String(on_create_sym));
    let c_ab_oc = m.consts.intern(Const::method_ref(ab_on_create));
    let c_one = m.consts.intern(Const::number(1.0));
    let ab_members = m.consts.push_array(vec![c_oc, c_ab_oc, c_one]);
    let _ = emit(
        &mut m,
        ei_b,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: ab_ctor,
            heritage: Some(ui_base),
            members: ab_members,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    let vp_base = emit(
        &mut m,
        ei_b,
        Op::TryGetGlobal {
            name: view_pu_sym,
            default: None,
        },
    );
    let c_ir = m.consts.intern(Const::String(initial_render_sym));
    let c_rv_ren = m.consts.intern(Const::method_ref(rv_render));
    let c_rr = m.consts.intern(Const::String(rerender_sym));
    let c_rv_rer = m.consts.intern(Const::method_ref(rv_rerender));
    let c_two = m.consts.intern(Const::number(2.0));
    let rv_members = m
        .consts
        .push_array(vec![c_ir, c_rv_ren, c_rr, c_rv_rer, c_two]);
    let _ = emit(
        &mut m,
        ei_b,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: rv_ctor,
            heritage: Some(vp_base),
            members: rv_members,
            member_attrs: Vec::new(),
            count: 0,
        })),
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
        let c_u_ren = m.consts.intern(Const::method_ref(u_ren));
        let c_u_rer = m.consts.intern(Const::method_ref(u_rer));
        let mem = m
            .consts
            .push_array(vec![c_ir, c_u_ren, c_rr, c_u_rer, c_two]);
        let _ = emit(
            &mut m,
            u_mb,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: u_ctor,
                heritage: Some(base_g),
                members: mem,
                member_attrs: Vec::new(),
                count: 0,
            })),
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

#[test]
fn patch_lex_vars_stay_isolated_and_new_spread_constructs_opaque_formals() {
    let mut m = mk_module();
    let f_sym = intern(&mut m, "f");
    let (ctor, ctor_b, ctor_p) = add_record_fn(&mut m, ClassId::new(0), "Box", 1);
    let own_alloc = alloc_object(&mut m, ctor_b);
    emit_void(
        &mut m,
        ctor_b,
        Op::StoreOwnPropName {
            object: ctor_p[2],
            name: f_sym,
            value: own_alloc,
            kind: abcd_ir::OwnStoreKind::ClassField,
        },
    );
    let formal_val = ctor_p[3];
    emit_void(&mut m, ctor_b, Op::Return { value: None });

    let main = add_func_named(&mut m, "main");
    let eb = entry_of(&m, main);
    let env_site = new_lex_env(&mut m, eb);
    let plain_obj = alloc_object(&mut m, eb);
    emit_void(
        &mut m,
        eb,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: plain_obj,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let patch_get = emit(
        &mut m,
        eb,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Patch,
        },
    );
    let ValueDef::Inst(patch_get_iid) = m.value(patch_get).unwrap().def else {
        panic!()
    };

    let empty_mem = m.consts.push_array(Vec::new());
    let cls = emit(
        &mut m,
        eb,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor,
            heritage: None,
            members: empty_mem,
            member_attrs: Vec::new(),
            count: 1,
        })),
    );
    let arr = alloc_array(&mut m, eb);
    let inst = emit(
        &mut m,
        eb,
        Op::Call {
            callee: cls,
            this: None,
            args: vec![arr],
            kind: CallKind::NewSpread,
        },
    );
    let loaded_f = emit(
        &mut m,
        eb,
        Op::LoadProp {
            object: inst,
            name: f_sym,
        },
    );
    emit_void(&mut m, eb, Op::Return { value: None });

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);

    // Patch lexical access never aliases the enclosing `NewLexEnv` slot.
    let patch_env = oracle.lex_env_at(patch_get_iid, 0);
    assert!(patch_env.has_unknown && patch_env.sites.is_empty());
    let patch_ans = oracle.query(patch_get, patch_get_iid);
    assert!(patch_ans.has_unknown && patch_ans.sites.is_empty());

    // `NewSpread` materializes the constructed receiver while keeping spread formals opaque.
    let f_ans = oracle.query(loaded_f, env_site);
    assert!(!f_ans.has_unknown);
    assert_eq!(f_ans.sites, oracle.query(own_alloc, env_site).sites);
    let formal_ans = oracle.query(formal_val, env_site);
    assert!(formal_ans.has_unknown);
}

// ── Sub-batch 1B regressions (R4-P1 / R4-P3 / R4-D4 / R4-H5) ─────────

#[test]
fn r4_p1_self_referencing_closure_with_pop_lex_env_terminates() {
    let mut m = mk_module();
    let (rec, _) = add_static_func(&mut m, "rec", 0);
    let rec_get_iid = {
        let b = entry_of(&m, rec);
        emit_void(&mut m, b, Op::PopLexEnv);
        let _self_clo = closure_of(&mut m, b, rec);
        let g = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(g) });
        match m.value(g).unwrap().def {
            ValueDef::Inst(i) => i,
            _ => panic!(),
        }
    };

    let main = add_func_named(&mut m, "func_main_0");
    {
        let b = entry_of(&m, main);
        let _outer_env = new_lex_env(&mut m, b);
        let obj = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: obj,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let clo = closure_of(&mut m, b, rec);
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: clo,
                this: None,
                args: Vec::new(),
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let base = CallGraph::build(&m);
    let out = analyze(&m, &base, &PtaConfig::default());
    assert!(!out.stats().capped);
    assert!(
        out.stats().env_rounds <= 4,
        "monotone lattice must converge in O(1) rounds, got {}",
        out.stats().env_rounds
    );
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let env_ans = oracle.lex_env_at(rec_get_iid, 0);
    assert!(
        env_ans.has_unknown,
        "after PopLexEnv + self-recapture, level 0 must be conservative: {env_ans:?}"
    );

    // Also build a multi-closure self-referencing PopLexEnv ring and verify
    // `step_budget = 10` halts immediately with `capped == true` and sound fallback.
    let mut big = mk_module();
    let mut ring_fns = Vec::new();
    for idx in 0..8 {
        let (f, _) = add_static_func(&mut big, &format!("ring_{idx}"), 0);
        ring_fns.push(f);
    }
    let mut probe_get_iid = InstId::new(0);
    for idx in 0..8 {
        let f = ring_fns[idx];
        let next = ring_fns[(idx + 1) % 8];
        let b = entry_of(&big, f);
        let _e = new_lex_env(&mut big, b);
        emit_void(&mut big, b, Op::PopLexEnv);
        let _self_c = closure_of(&mut big, b, f);
        let _next_c = closure_of(&mut big, b, next);
        let g = emit(
            &mut big,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        if idx == 0 {
            probe_get_iid = match big.value(g).unwrap().def {
                ValueDef::Inst(i) => i,
                _ => panic!(),
            };
        }
        emit_void(&mut big, b, Op::Return { value: Some(g) });
    }
    let big_base = CallGraph::build(&big);
    let capped_out = analyze(
        &big,
        &big_base,
        &PtaConfig {
            step_budget: 10,
            ..PtaConfig::default()
        },
    );
    assert!(capped_out.stats().capped);
    let (_, capped_tables, capped_stats) = capped_out.into_parts();
    let capped_oracle = Rung2AliasOracle::new(&big, capped_tables, capped_stats);
    assert!(capped_oracle.lex_env_at(probe_get_iid, 0).has_unknown);
}

#[test]
fn r4_p3_sendable_vs_plain_top_aligned_join_and_pre_throw_catch_env() {
    let inst_of = |m: &Module, v: ValueId| match m.value(v).unwrap().def {
        ValueDef::Inst(i) => i,
        _ => panic!(),
    };

    // 1. Direct unit check on top-aligned `join_chains`.
    let mut depth2 = EnvChain::default();
    depth2.push_site(InstId::new(10), 16); // outer (level 1)
    depth2.push_site(InstId::new(11), 16); // inner (level 0)
    let mut depth1 = EnvChain::default();
    depth1.push_site(InstId::new(20), 16); // inner (level 0)
    let joined = join_chains(&depth2, &depth1);
    let lvl0 = joined.at_level(0).expect("level 0");
    assert_eq!(
        lvl0.sites,
        BTreeSet::from([InstId::new(11), InstId::new(20)])
    );
    assert!(!lvl0.unknown, "both branches provide level 0");
    let lvl1 = joined.at_level(1).expect("level 1");
    assert_eq!(lvl1.sites, BTreeSet::from([InstId::new(10)]));
    assert!(lvl1.unknown, "only one branch provides level 1");

    // 2. End-to-end CFG check:
    //    (a) `Sendable` env survives `PopLexEnv` while `Plain` env is popped;
    //    (b) diamond CFG top-aligns `level = 0` (`!has_unknown`) and marks `level = 1` unknown;
    //    (c) catch handler joins pre-throw env states BEFORE `PopLexEnv` runs at try-block end.
    let mut m = mk_module();
    let (child_send, _) = add_static_func(&mut m, "child_send", 0);
    let child_send_get = {
        let b = entry_of(&m, child_send);
        let g = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Sendable,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(g) });
        g
    };

    let f_dual = add_func_named(&mut m, "dual_env");
    let (send_env_iid, send_obj, plain_obj, send_read, plain_read) = {
        let b = entry_of(&m, f_dual);
        let se_val = emit(
            &mut m,
            b,
            Op::NewLexEnv {
                num_vars: 1,
                kind: abcd_ir::LexEnvKind::Sendable,
            },
        );
        let se_iid = inst_of(&m, se_val);
        let s_obj = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: s_obj,
                kind: abcd_ir::LexEnvKind::Sendable,
            },
        );

        let _pe_iid = new_lex_env(&mut m, b);
        let p_obj = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: p_obj,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );

        // `PopLexEnv` pops ONLY the `Plain` frame; `Sendable` stays intact.
        emit_void(&mut m, b, Op::PopLexEnv);

        let s_read = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Sendable,
            },
        );
        let p_read = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let clo = closure_of(&mut m, b, child_send);
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: clo,
                this: None,
                args: Vec::new(),
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
        (se_iid, s_obj, p_obj, s_read, p_read)
    };

    // Diamond function testing top-aligned join in CFG.
    let f_diamond = add_func_named(&mut m, "diamond_env");
    let (outer_t, inner_t, inner_f, obj_t, obj_f, join_get0, join_get1) = {
        let entry = entry_of(&m, f_diamond);
        let bt = add_block(&mut m, f_diamond);
        let bf = add_block(&mut m, f_diamond);
        let bjoin = add_block(&mut m, f_diamond);
        let cond = load_number(&mut m, entry, 1.0);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond,
                true_dest: bt,
                false_dest: bf,
            },
        );

        let out_t = new_lex_env(&mut m, bt);
        let in_t = new_lex_env(&mut m, bt);
        let ot = alloc_object(&mut m, bt);
        emit_void(
            &mut m,
            bt,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: ot,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, bt, Op::Branch { dest: bjoin });

        let in_f = new_lex_env(&mut m, bf);
        let of_ = alloc_object(&mut m, bf);
        emit_void(
            &mut m,
            bf,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: of_,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, bf, Op::Branch { dest: bjoin });

        link(&mut m, entry, bt);
        link(&mut m, entry, bf);
        link(&mut m, bt, bjoin);
        link(&mut m, bf, bjoin);

        let g0 = emit(
            &mut m,
            bjoin,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let g1 = emit(
            &mut m,
            bjoin,
            Op::GetLexVar {
                level: 1,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, bjoin, Op::Return { value: None });
        (out_t, in_t, in_f, ot, of_, g0, g1)
    };

    // Try/catch function testing pre-throw env join inside a protected block
    // whose normal path pops `inner_try_env` before block exit.
    let f_try = add_func_named(&mut m, "try_catch_env");
    let (try_outer_env, try_inner_env, try_outer_obj, try_inner_obj, catch_get0, catch_get1) = {
        let entry = entry_of(&m, f_try);
        let btry = add_block(&mut m, f_try);
        let bcatch = add_block(&mut m, f_try);
        let bexit = add_block(&mut m, f_try);
        let prop_sym = intern(&mut m, "mayThrowProp");

        let outer_e = new_lex_env(&mut m, entry);
        let outer_o = alloc_object(&mut m, entry);
        emit_void(
            &mut m,
            entry,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: outer_o,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, entry, Op::Branch { dest: btry });

        // Throw point #1: `outer_e` is at level 0.
        let _ = emit(
            &mut m,
            btry,
            Op::LoadProp {
                object: outer_o,
                name: prop_sym,
            },
        );
        let inner_e = new_lex_env(&mut m, btry);
        let inner_o = alloc_object(&mut m, btry);
        emit_void(
            &mut m,
            btry,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: inner_o,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        // Throw point #2: `inner_e` is at level 0, `outer_e` is at level 1.
        let _ = emit(
            &mut m,
            btry,
            Op::LoadProp {
                object: inner_o,
                name: prop_sym,
            },
        );
        // Normal fallthrough pops `inner_e` before leaving `btry`!
        emit_void(&mut m, btry, Op::PopLexEnv);
        emit_void(&mut m, btry, Op::Branch { dest: bexit });

        let exc = add_exception_param(&mut m, bcatch);
        let cg0 = emit(
            &mut m,
            bcatch,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let cg1 = emit(
            &mut m,
            bcatch,
            Op::GetLexVar {
                level: 1,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let _ = exc;
        emit_void(&mut m, bcatch, Op::Branch { dest: bexit });
        emit_void(&mut m, bexit, Op::Return { value: None });

        link(&mut m, entry, btry);
        link(&mut m, btry, bexit);
        link(&mut m, bcatch, bexit);
        add_try(&mut m, f_try, vec![btry], bcatch, exc);

        (outer_e, inner_e, outer_o, inner_o, cg0, cg1)
    };

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);

    // Verify (a): Sendable vs Plain separation across PopLexEnv.
    let send_read_iid = inst_of(&m, send_read);
    let plain_read_iid = inst_of(&m, plain_read);
    let send_env_ans = oracle.lex_env_at(send_read_iid, 0);
    assert!(!send_env_ans.has_unknown);
    assert_eq!(send_env_ans.sites, AllocSiteSet::one(send_env_iid));
    assert_eq!(oracle.sendable_env_at(plain_read_iid, 0), send_env_ans);

    let send_val_ans = oracle.query(send_read, send_read_iid);
    assert!(!send_val_ans.has_unknown);
    assert_eq!(
        send_val_ans.sites,
        oracle.query(send_obj, send_read_iid).sites
    );
    assert_ne!(
        send_val_ans.sites,
        oracle.query(plain_obj, send_read_iid).sites
    );

    let child_send_iid = inst_of(&m, child_send_get);
    let child_send_ans = oracle.query(child_send_get, child_send_iid);
    assert!(!child_send_ans.has_unknown);
    assert_eq!(
        child_send_ans.sites,
        oracle.query(send_obj, send_read_iid).sites
    );

    let plain_env_ans = oracle.lex_env_at(plain_read_iid, 0);
    assert!(plain_env_ans.has_unknown && plain_env_ans.sites.is_empty());
    assert!(oracle.query(plain_read, plain_read_iid).has_unknown);

    // Verify (b): Diamond top-aligned join.
    let join_g0_iid = inst_of(&m, join_get0);
    let join_g1_iid = inst_of(&m, join_get1);
    let d_env0 = oracle.lex_env_at(join_g0_iid, 0);
    assert!(!d_env0.has_unknown, "{d_env0:?}");
    let mut expected_d0 = AllocSiteSet::one(inner_t);
    expected_d0.union_with(&AllocSiteSet::one(inner_f));
    assert_eq!(d_env0.sites, expected_d0);

    let d_val0 = oracle.query(join_get0, join_g0_iid);
    assert!(!d_val0.has_unknown);
    let mut expected_objs = oracle.query(obj_t, join_g0_iid).sites;
    expected_objs.union_with(&oracle.query(obj_f, join_g0_iid).sites);
    assert_eq!(d_val0.sites, expected_objs);

    let d_env1 = oracle.lex_env_at(join_g1_iid, 1);
    assert!(d_env1.has_unknown);
    assert_eq!(d_env1.sites, AllocSiteSet::one(outer_t));

    // Verify (c): Catch handler pre-throw join retains `try_inner_env` despite block-end `PopLexEnv`.
    let cg0_iid = inst_of(&m, catch_get0);
    let cg1_iid = inst_of(&m, catch_get1);
    let c_env0 = oracle.lex_env_at(cg0_iid, 0);
    assert!(!c_env0.has_unknown, "{c_env0:?}");
    let mut expected_catch0 = AllocSiteSet::one(try_outer_env);
    expected_catch0.union_with(&AllocSiteSet::one(try_inner_env));
    assert_eq!(c_env0.sites, expected_catch0);

    let c_val0 = oracle.query(catch_get0, cg0_iid);
    assert!(!c_val0.has_unknown);
    let mut expected_catch_objs = oracle.query(try_outer_obj, cg0_iid).sites;
    expected_catch_objs.union_with(&oracle.query(try_inner_obj, cg0_iid).sites);
    assert_eq!(c_val0.sites, expected_catch_objs);

    let c_env1 = oracle.lex_env_at(cg1_iid, 1);
    assert!(c_env1.has_unknown);
    assert_eq!(c_env1.sites, AllocSiteSet::one(try_outer_env));
}

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
