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
    // must_alias sees through the call (the a5 shape).
    assert!(AliasOracle::<()>::must_alias(&oracle, r1, o1, InstId::new(0)));
    assert!(!AliasOracle::<()>::must_alias(&oracle, r1, o2, InstId::new(0)));
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
