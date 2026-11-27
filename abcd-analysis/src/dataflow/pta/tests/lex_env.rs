//! Lexical-environment stack identity, nested/class captures, `Plain` vs `Sendable`
//! vs `Patch` stacks, top-aligned join, pre-throw catch edges, and `PopLexEnv` convergence.

use super::*;
use std::collections::BTreeSet;

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
