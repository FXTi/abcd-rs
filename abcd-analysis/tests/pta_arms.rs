//! Rung-2 PTA arm coverage (c-COV W10): synthetic modules for the
//! engine arms the corpus never drives — `closure_body` Mov/leaf/cycle
//! shapes, the non-callable callee pointer, external/dangling wired
//! callees, the no-slot-model `this` binding, `LoadFunction`/
//! `CreateGenerator` callables, result-less ops under the scan, the
//! dynamic-read bucket re-arm, and the lexical-environment dead/odd
//! shapes. Asserts are on exact points-to answers, graph edges, and
//! env answers.

mod common;

use abcd_analysis::callgraph::{CallGraph, CallTargets};
use abcd_analysis::dataflow::pta::{PtaConfig, Rung2AliasOracle, analyze};
use abcd_ir::{CallKind, Const, Edge, EdgeKind, FuncId, InstId, Op, ValueDef, ValueId};
use common::*;

/// Run the engine with the default config.
fn run(m: &abcd_ir::Module) -> abcd_analysis::dataflow::pta::PtaOutcome {
    let base = CallGraph::build(m);
    analyze(m, &base, &PtaConfig::default())
}

/// `closure_body` through a `Mov` (resolves), a non-`DefineFunc` leaf
/// (no body), and a Mov cycle (cut): the three uncovered def-chain arms.
#[test]
fn closure_body_mov_leaf_and_cycle() {
    let mut m = mk_module();
    let (body, _) = add_static_func(&mut m, "body", 0);
    {
        let b = entry_of(&m, body);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "main");
    let entry = entry_of(&m, f);
    // (a) AllocClosure(mov(DefineFunc(body))) — the Mov passes through.
    let def = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body,
            captures: vec![],
            length: 0,
        },
    );
    let mv = emit(&mut m, entry, Op::Mov { src: def });
    let clo_mov = emit(&mut m, entry, Op::AllocClosure { func: mv });
    let call_mov = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo_mov,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let call_mov = inst_of(&m, call_mov);
    // (b) AllocClosure(param) — the def chain bottoms at a non-Inst def.
    let p = add_param(&mut m, f, 0);
    let clo_param = emit(&mut m, entry, Op::AllocClosure { func: p });
    let call_param = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo_param,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let call_param = inst_of(&m, call_param);
    // (c) AllocClosure(mov-cycle) — the visiting cut.
    let v1 = ValueId::new(m.values.len() as u32);
    let v2 = ValueId::new(m.values.len() as u32 + 1);
    let m1 = push_inst(&mut m, entry, Op::Mov { src: v2 });
    m.values.push(abcd_ir::Value {
        def: ValueDef::Inst(m1),
        ty: abcd_ir::Ty::Any,
    });
    m.inst_mut(m1).unwrap().result = Some(v1);
    let m2 = push_inst(&mut m, entry, Op::Mov { src: v1 });
    m.values.push(abcd_ir::Value {
        def: ValueDef::Inst(m2),
        ty: abcd_ir::Ty::Any,
    });
    m.inst_mut(m2).unwrap().result = Some(v2);
    let _clo_cycle = emit(&mut m, entry, Op::AllocClosure { func: v1 });
    emit_void(&mut m, entry, Op::Return { value: None });

    let out = run(&m);
    // (a) resolved through the Mov.
    let edge = out.graph().edge_at(call_mov).expect("edge");
    assert_eq!(edge.targets, CallTargets::Resolved(vec![body]));
    // (b) the non-callable object at the callee pointer: no PTA edge.
    let edge = out.graph().edge_at(call_param).expect("edge");
    assert!(
        edge.targets != CallTargets::Resolved(vec![body]),
        "the param-bottomed closure is not callable: {:?}",
        edge.targets
    );
    assert!(!out.stats().capped);
}

/// `AllocClosure(LoadConst(MethodRef))` — the closure body trace does
/// not read the pooled method reference (a `_ => None` leaf), so the
/// PTA's object is non-callable; the BASE graph's own MethodRef trace
/// still resolves the edge.
#[test]
fn closure_over_methodref_leaf_is_not_pta_callable() {
    let mut m = mk_module();
    let (body, _) = add_static_func(&mut m, "body", 0);
    {
        let b = entry_of(&m, body);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "main");
    let entry = entry_of(&m, f);
    let mr = load_method_ref(&mut m, entry, body);
    let clo = emit(&mut m, entry, Op::AllocClosure { func: mr });
    let call = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let call = inst_of(&m, call);
    emit_void(&mut m, entry, Op::Return { value: None });

    let out = run(&m);
    // The base trace resolves the AllocClosure → MethodRef chain.
    let edge = out.graph().edge_at(call).expect("edge");
    assert_eq!(edge.targets, CallTargets::Resolved(vec![body]));
}

/// Wire attempts on callees without a body: an external function (via
/// `DefineFunc`) and a dangling `MethodRef` target. Both are recorded
/// as resolved targets but never activated.
#[test]
fn wire_call_external_and_dangling_callees() {
    let mut m = mk_module();
    let ext = add_external_func(&mut m, "ext");
    let f = add_func_named(&mut m, "main");
    let entry = entry_of(&m, f);
    let def_ext = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: ext,
            captures: vec![],
            length: 0,
        },
    );
    emit(
        &mut m,
        entry,
        Op::Call {
            callee: def_ext,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let ghost = load_method_ref(&mut m, entry, FuncId::new(999));
    emit(
        &mut m,
        entry,
        Op::Call {
            callee: ghost,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let out = run(&m);
    assert!(
        !out.stats().capped,
        "external/dangling wiring never hangs: {:?}",
        out.stats()
    );
}

/// The no-slot-model binding: a NON-STATIC callee without the callType
/// annotation over-approximates — every call operand (here: `this`)
/// reaches every parameter.
#[test]
fn no_slot_model_binds_this_to_every_param() {
    let mut m = mk_module();
    let callee = add_func_named(&mut m, "nostatic"); // no STATIC
    let p0 = add_param(&mut m, callee, 0);
    {
        let b = entry_of(&m, callee);
        emit_void(&mut m, b, Op::Return { value: Some(p0) });
    }
    let main = add_func_named(&mut m, "main");
    let entry = entry_of(&m, main);
    let clo = closure_of(&mut m, entry, callee);
    let obj = alloc_object(&mut m, entry);
    emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo,
            this: Some(obj),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let ans = oracle.query(p0, InstId::new(0));
    assert!(
        ans.sites.iter().any(|s| s == inst_of(&m, obj)),
        "the receiver reached the param: {ans:?}"
    );
}

/// `LoadFunction` (the function-self value) resolves a recursive call;
/// `CreateGenerator` resolves like a closure.
#[test]
fn loadfunction_and_creategenerator_are_callable() {
    let mut m = mk_module();
    let (f, _) = add_static_func(&mut m, "selfish", 0);
    let call_self;
    {
        let b = entry_of(&m, f);
        let lf = emit(&mut m, b, Op::LoadFunction);
        let r = emit(
            &mut m,
            b,
            Op::Call {
                callee: lf,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        call_self = inst_of(&m, r);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let (gen_body, _) = add_static_func(&mut m, "gen", 0);
    {
        let b = entry_of(&m, gen_body);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let main = add_func_named(&mut m, "main");
    let entry = entry_of(&m, main);
    let def = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: gen_body,
            captures: vec![],
            length: 0,
        },
    );
    let geno = emit(&mut m, entry, Op::CreateGenerator { func: def });
    let call_gen = emit(
        &mut m,
        entry,
        Op::Call {
            callee: geno,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let call_gen = inst_of(&m, call_gen);
    emit_void(&mut m, entry, Op::Return { value: None });

    let out = run(&m);
    assert_eq!(
        out.graph().edge_at(call_self).unwrap().targets,
        CallTargets::Resolved(vec![f]),
        "LoadFunction resolves the self-call"
    );
    assert_eq!(
        out.graph().edge_at(call_gen).unwrap().targets,
        CallTargets::Resolved(vec![gen_body]),
        "CreateGenerator resolves like a closure"
    );
}

/// A store through an unknown (parameter) base fires the Store handler
/// on `Obj::Unknown` (no field wiring); a call through an unknown callee
/// marks the site partial and poisons the result.
#[test]
fn unknown_base_store_and_param_callee() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "main");
    let entry = entry_of(&m, f);
    let p = add_param(&mut m, f, 0);
    let v = alloc_object(&mut m, entry);
    let x = intern(&mut m, "x");
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: p,
            name: x,
            value: v,
        },
    );
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: p,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let out = run(&m);
    assert!(out.stats().call_sites_partial >= 1, "the param callee");
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let ans = oracle.query(r, InstId::new(0));
    assert!(ans.has_unknown, "the unknown-callee result: {ans:?}");
    // The store through the unknown base did not wire a field, but the
    // stored value's own site still keys.
    let ans = oracle.query(v, InstId::new(0));
    assert_eq!(ans.sites.len(), 1);
}

/// The dynamic-read re-arm: a computed-key load fires on an object
/// BEFORE its named bucket exists; a later store through a call-result
/// alias notes the bucket and re-fires the read.
#[test]
fn dyn_read_rearmed_by_late_bucket() {
    let mut m = mk_module();
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
    let t = add_block(&mut m, main);
    let e = add_block(&mut m, main);
    let join = add_block(&mut m, main);
    let o = alloc_object(&mut m, entry);
    let o2 = alloc_object(&mut m, entry);
    let k = load_number(&mut m, entry, 0.0);
    // The dynamic read over a PHI of o and o2 (fires on both objects).
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
    emit_void(&mut m, t, Op::Branch { dest: join });
    emit_void(&mut m, e, Op::Branch { dest: join });
    link(&mut m, entry, t);
    link(&mut m, entry, e);
    link(&mut m, t, join);
    link(&mut m, e, join);
    let recv = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    o,
                ),
                (
                    Edge {
                        from: e,
                        kind: EdgeKind::Normal,
                    },
                    o2,
                ),
            ],
        },
    );
    let ld = emit(
        &mut m,
        join,
        Op::LoadPropDyn {
            object: recv,
            key: k,
        },
    );
    // The late store: through the call-result alias of o.
    let clo = closure_of(&mut m, join, id);
    let r = emit(
        &mut m,
        join,
        Op::Call {
            callee: clo,
            this: None,
            args: vec![o],
            kind: CallKind::Dynamic,
        },
    );
    let w = alloc_object(&mut m, join);
    let x = intern(&mut m, "x");
    emit_void(
        &mut m,
        join,
        Op::StoreProp {
            object: r,
            name: x,
            value: w,
        },
    );
    emit_void(&mut m, join, Op::Return { value: None });

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    let ld_sites = oracle.query(ld, InstId::new(0)).sites;
    let w_sites = oracle.query(w, InstId::new(0)).sites;
    assert_eq!(w_sites.len(), 1);
    assert!(
        ld_sites.intersects(&w_sites),
        "the re-armed dynamic read picked up the late bucket: {ld_sites:?} vs {w_sites:?}"
    );
}

/// Result-less ops under the scan (a result-less phi, result-less
/// loads), a self-edge Mov, and a duplicate edge: the guards hold.
#[test]
fn resultless_ops_and_edge_guards() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "main");
    let entry = entry_of(&m, f);
    let o = alloc_object(&mut m, entry);
    let x = intern(&mut m, "x");
    // Result-less loads (malformed but tolerated).
    let k = load_number(&mut m, entry, 0.0);
    push_inst(&mut m, entry, Op::LoadProp { object: o, name: x });
    push_inst(
        &mut m,
        entry,
        Op::LoadPropIdx {
            object: o,
            index: k,
        },
    );
    push_inst(&mut m, entry, Op::LoadPropDyn { object: o, key: k });
    // A phi without a result.
    push_inst(&mut m, entry, Op::Phi { entries: vec![] });
    // A self-edge: mov whose result IS its source value.
    let selfval = ValueId::new(m.values.len() as u32);
    let mv = push_inst(&mut m, entry, Op::Mov { src: selfval });
    m.values.push(abcd_ir::Value {
        def: ValueDef::Inst(mv),
        ty: abcd_ir::Ty::Any,
    });
    m.inst_mut(mv).unwrap().result = Some(selfval);
    // The same global store edge twice (the dedup arm).
    let g = intern(&mut m, "g");
    emit_void(&mut m, entry, Op::StoreGlobal { name: g, value: o });
    emit_void(&mut m, entry, Op::StoreGlobal { name: g, value: o });
    // A const-defined value (the value_answer const arm).
    let _cv = const_value(&mut m, Const::Null);
    emit_void(&mut m, entry, Op::Return { value: None });

    let out = run(&m);
    assert!(!out.stats().capped);
}

/// Dangling arena ids inside a function's block/inst lists are skipped
/// (the library's no-panics rule), and the analysis still terminates.
#[test]
fn dangling_block_and_inst_ids_are_skipped() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "main");
    let entry = entry_of(&m, f);
    let o = alloc_object(&mut m, entry);
    emit_void(&mut m, entry, Op::Return { value: None });
    // A dangling block in the function's block list and a dangling inst
    // in the entry block's list.
    m.func_mut(f)
        .unwrap()
        .blocks
        .push(abcd_ir::BlockId::new(9999));
    m.block_mut(entry).unwrap().insts.push(InstId::new(9999));

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    assert_eq!(oracle.query(o, InstId::new(0)).sites.len(), 1);
}

/// Lexical-environment oddities: a one-sided join (only one arm pushes
/// an env), a bare `PopLexEnv` (popping past the bottom), a bare
/// `DefineFunc` capture point, and a capture point in an unreachable
/// cycle (no computed stack).
#[test]
fn env_joins_pops_and_dead_capture_points() {
    let mut m = mk_module();
    // (a) One-sided join: only the `a` arm pushes a NewLexEnv.
    let f = add_func_named(&mut m, "main");
    let entry = entry_of(&m, f);
    let a = add_block(&mut m, f);
    let b = add_block(&mut m, f);
    let j = add_block(&mut m, f);
    let cond = load_number(&mut m, entry, 1.0);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond,
            true_dest: a,
            false_dest: b,
        },
    );
    emit(&mut m, a, Op::NewLexEnv { num_vars: 1 });
    emit_void(&mut m, a, Op::Branch { dest: j });
    emit_void(&mut m, b, Op::Branch { dest: j });
    link(&mut m, entry, a);
    link(&mut m, entry, b);
    link(&mut m, a, j);
    link(&mut m, b, j);
    let get_join = emit(&mut m, j, Op::GetLexVar { level: 0, slot: 0 });
    let get_join = inst_of(&m, get_join);
    emit_void(&mut m, j, Op::Return { value: None });
    // (b) Bare PopLexEnv (past the bottom) then a read.
    let g = add_func_named(&mut m, "popper");
    let pop_get;
    {
        let e = entry_of(&m, g);
        emit_void(&mut m, e, Op::PopLexEnv);
        let gg = emit(&mut m, e, Op::GetLexVar { level: 0, slot: 0 });
        pop_get = inst_of(&m, gg);
        emit_void(&mut m, e, Op::Return { value: None });
    }
    // (c) A bare DefineFunc (an unwrapped function value still captures).
    let (cap, _) = add_static_func(&mut m, "cap", 0);
    {
        let b = entry_of(&m, cap);
        let r = emit(&mut m, b, Op::GetLexVar { level: 0, slot: 0 });
        emit_void(&mut m, b, Op::Return { value: Some(r) });
    }
    let definer = add_func_named(&mut m, "definer");
    {
        let b = entry_of(&m, definer);
        emit(&mut m, b, Op::NewLexEnv { num_vars: 1 });
        emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: cap,
                captures: vec![],
                length: 0,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }
    // (d) An unreachable A <-> B cycle carrying a capture point and a
    // lex read (never computed by the stack dataflow).
    let dead = add_func_named(&mut m, "deadhost");
    let dead_entry = entry_of(&m, dead);
    let ba = add_block(&mut m, dead);
    let bb = add_block(&mut m, dead);
    emit_void(&mut m, dead_entry, Op::Return { value: None });
    let def_dead = emit(
        &mut m,
        ba,
        Op::DefineFunc {
            body: cap,
            captures: vec![],
            length: 0,
        },
    );
    emit(&mut m, ba, Op::AllocClosure { func: def_dead });
    let dead_get = emit(&mut m, ba, Op::GetLexVar { level: 0, slot: 0 });
    let dead_get = inst_of(&m, dead_get);
    emit_void(&mut m, ba, Op::Branch { dest: bb });
    emit_void(&mut m, bb, Op::Branch { dest: ba });
    link(&mut m, ba, bb);
    link(&mut m, bb, ba);

    let out = run(&m);
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    // (a) The join's level-0 entry is one-sided → unknown.
    let ans = oracle.lex_env_at(get_join, 0);
    assert!(ans.has_unknown, "one-sided join: {ans:?}");
    // (b) The popped-past-bottom entry is unknown.
    let ans = oracle.lex_env_at(pop_get, 0);
    assert!(ans.has_unknown, "the popped-past-bottom entry: {ans:?}");
    // (d) No stack was ever computed for the dead cycle.
    let ans = oracle.lex_env_at(dead_get, 0);
    assert!(ans.has_unknown, "dead capture point: {ans:?}");
}

/// The base-activation run skips external/bodyless functions (no scan).
#[test]
fn external_functions_get_no_base_activation() {
    let mut m = mk_module();
    let _ext = add_external_func(&mut m, "ext");
    let f = add_func_named(&mut m, "main");
    let entry = entry_of(&m, f);
    emit_void(&mut m, entry, Op::Return { value: None });
    let out = run(&m);
    assert!(!out.stats().capped);
}

/// Two closures of the SAME body phi-merged onto one callee pointer:
/// the second object's resolution is a no-op (the call-targets insert
/// dedups) and the wire is idempotent.
#[test]
fn phi_of_two_closures_same_body_resolves_once() {
    let mut m = mk_module();
    let (body, _) = add_static_func(&mut m, "body", 0);
    {
        let b = entry_of(&m, body);
        let o = alloc_object(&mut m, b);
        emit_void(&mut m, b, Op::Return { value: Some(o) });
    }
    let f = add_func_named(&mut m, "main");
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
    let c1 = closure_of(&mut m, t, body);
    emit_void(&mut m, t, Op::Branch { dest: join });
    let c2 = closure_of(&mut m, e, body);
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
                    Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    c1,
                ),
                (
                    Edge {
                        from: e,
                        kind: EdgeKind::Normal,
                    },
                    c2,
                ),
            ],
        },
    );
    let r = emit(
        &mut m,
        join,
        Op::Call {
            callee: phi,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let call = inst_of(&m, r);
    emit_void(&mut m, join, Op::Return { value: None });

    let out = run(&m);
    let edge = out.graph().edge_at(call).expect("edge");
    assert_eq!(edge.targets, CallTargets::Resolved(vec![body]));
    let (_, tables, stats) = out.into_parts();
    let oracle = Rung2AliasOracle::new(&m, tables, stats);
    // The oracle's module accessor (the rung-2 resolve seam; under
    // --release the trivial getter inlines into callers).
    assert!(std::ptr::eq(oracle.module(), &m));
    // The result points to the callee's alloc site.
    let body_alloc = m.block(entry_of(&m, body)).unwrap().insts[0];
    let ans = oracle.query(r, call);
    assert!(ans.sites.iter().eq([body_alloc]), "{ans:?}");
}

/// Result-less alloc/global-load shapes under the scan: the
/// `if let Some(r) = inst.result` guards skip them.
#[test]
fn resultless_alloc_and_load_shapes_are_skipped() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "main");
    let entry = entry_of(&m, f);
    let o = alloc_object(&mut m, entry);
    // Result-less variants of the result-bearing scan arms.
    push_inst(&mut m, entry, Op::AllocArray { shape: None });
    let gs = intern(&mut m, "g");
    push_inst(
        &mut m,
        entry,
        Op::TryGetGlobal {
            name: gs,
            default: None,
        },
    );
    push_inst(&mut m, entry, Op::LoadModuleVar { index: 0 });
    push_inst(&mut m, entry, Op::Mov { src: o });
    push_inst(&mut m, entry, Op::LoadFunction);
    emit_void(&mut m, entry, Op::Return { value: None });

    let out = run(&m);
    assert!(!out.stats().capped);
}
