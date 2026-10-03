//! Rung-1 alias-engine arm coverage (c-COV W10): direct engine queries
//! over hand-built modules, one test per SKIP-ARM the corpus suites
//! never query — Mov pass-through, ≥2-hop call results, ≥2-caller
//! unbalanced fan-outs, cycle cuts, exception/const params, the
//! implicit-slot bind table, and the partial/external/bodyless callee
//! hops. Every test asserts the exact `QueryAnswer`, not just
//! don't-panic.

mod common;

use abcd_analysis::callgraph::{CallGraph, CallTargets};
use abcd_analysis::dataflow::alias::Rung1AliasOracle;
use abcd_analysis::dataflow::heap::AliasOracle;
use abcd_ir::{CallKind, Const, Edge, EdgeKind, FuncId, InstId, Op, ValueDef, ValueId};
use common::*;

/// `o = {}; a = mov o; query(a)` — the Mov pass-through + Leave epilogue.
#[test]
fn mov_defined_value_passes_through() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let o = alloc_object(&mut m, entry);
    let site = inst_of(&m, o);
    let a = emit(&mut m, entry, Op::Mov { src: o });
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    // The module() getter is the oracle.rs rung-1 resolve seam.
    assert!(std::ptr::eq(oracle.module(), &m));
    let ans = oracle.query(a, InstId::new(0));
    assert_eq!(ans.sites.iter().collect::<Vec<_>>(), vec![site]);
    assert!(ans.precise_for_keying(), "{ans:?}");
}

/// A query on a func-less value (const-defined, owned by no function)
/// is unknown; a phi with a const incoming contributes nothing.
#[test]
fn const_values_are_not_heap_objects() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    let cv = const_value(&mut m, Const::Undefined);
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
    let site = inst_of(&m, a);
    emit_void(&mut m, t, Op::Branch { dest: join });
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
                    a,
                ),
                (
                    Edge {
                        from: e,
                        kind: EdgeKind::Normal,
                    },
                    cv,
                ),
            ],
        },
    );
    emit_void(&mut m, join, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    // Func-less (const-defined, unowned): unknown.
    let ans = oracle.query(cv, InstId::new(0));
    assert!(ans.has_unknown && ans.sites.is_empty(), "{ans:?}");
    // Phi with a const incoming: the alloc site, phi-flagged, no unknown.
    let ans = oracle.query(phi, InstId::new(0));
    assert_eq!(ans.sites.iter().collect::<Vec<_>>(), vec![site]);
    assert!(ans.has_phi && !ans.has_unknown, "{ans:?}");
}

/// An empty phi (`Phi { entries: [] }`) finishes precise-empty.
#[test]
fn empty_phi_is_precise_empty() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let phi = emit(&mut m, entry, Op::Phi { entries: vec![] });
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(phi, InstId::new(0));
    assert!(
        ans.has_phi && !ans.has_unknown && ans.sites.is_empty(),
        "{ans:?}"
    );
}

/// A value whose defining instruction id dangles: unknown (the
/// no-panics-on-data rule), not a crash.
#[test]
fn dangling_inst_def_is_unknown() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    // An instruction whose RESULT value claims a dangling definition.
    let bogus_val = ValueId::new(m.values.len() as u32);
    m.values.push(abcd_ir::Value {
        def: ValueDef::Inst(InstId::new(99999)),
        ty: abcd_ir::Ty::Any,
    });
    let inst = push_inst(&mut m, entry, Op::PopLexEnv);
    m.inst_mut(inst).unwrap().result = Some(bogus_val);
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(bogus_val, InstId::new(0));
    assert!(ans.has_unknown && ans.sites.is_empty(), "{ans:?}");
}

/// One callee, TWO returned values: the `QueryTask::Call` resume folds
/// the second hop (the ≥2-pending arm).
#[test]
fn call_result_two_return_hops() {
    let mut m = mk_module();
    let (pick, _) = add_static_func(&mut m, "pick", 1);
    let (ra, rb);
    {
        let entry = entry_of(&m, pick);
        let t = add_block(&mut m, pick);
        let e = add_block(&mut m, pick);
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
        ra = alloc_object(&mut m, t);
        emit_void(&mut m, t, Op::Return { value: Some(ra) });
        rb = alloc_object(&mut m, e);
        emit_void(&mut m, e, Op::Return { value: Some(rb) });
        link(&mut m, entry, t);
        link(&mut m, entry, e);
    }
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let clo = closure_of(&mut m, entry, pick);
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let call = inst_of(&m, r);
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(r, call);
    assert!(!ans.has_unknown && !ans.capped, "{ans:?}");
    let mut want = vec![inst_of(&m, ra), inst_of(&m, rb)];
    want.sort();
    assert_eq!(ans.sites.iter().collect::<Vec<_>>(), want);
}

/// One call site, TWO resolved callees (a phi of two closures): the
/// second callee hop exercises the same resume arm.
#[test]
fn call_result_two_callee_hops() {
    let mut m = mk_module();
    let (fa, _) = add_static_func(&mut m, "fa", 0);
    let (fb, _) = add_static_func(&mut m, "fb", 0);
    let (oa, ob);
    {
        let b = entry_of(&m, fa);
        oa = alloc_object(&mut m, b);
        emit_void(&mut m, b, Op::Return { value: Some(oa) });
    }
    {
        let b = entry_of(&m, fb);
        ob = alloc_object(&mut m, b);
        emit_void(&mut m, b, Op::Return { value: Some(ob) });
    }
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let t = add_block(&mut m, caller);
    let e = add_block(&mut m, caller);
    let join = add_block(&mut m, caller);
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
    let ca = closure_of(&mut m, t, fa);
    emit_void(&mut m, t, Op::Branch { dest: join });
    let cb = closure_of(&mut m, e, fb);
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
                    ca,
                ),
                (
                    Edge {
                        from: e,
                        kind: EdgeKind::Normal,
                    },
                    cb,
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

    let graph = CallGraph::build(&m);
    assert_eq!(
        graph.edge_at(call).unwrap().targets,
        CallTargets::Resolved(vec![fa, fb])
    );
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(r, call);
    assert!(!ans.has_unknown, "{ans:?}");
    let mut want = vec![inst_of(&m, oa), inst_of(&m, ob)];
    want.sort();
    assert_eq!(ans.sites.iter().collect::<Vec<_>>(), want);
}

/// The unbalanced fan-out over TWO recorded callers unions both
/// arguments (the `ParamUnbal` resume's schedule-next arm); a caller
/// passing FEWER args than formals contributes the precise-empty leaf.
#[test]
fn unbalanced_fanout_two_callers_and_short_args() {
    let mut m = mk_module();
    let (register, params) = add_static_func(&mut m, "register", 1);
    let cb_param = params[3];
    {
        let b = entry_of(&m, register);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let clo_reg = closure_of(&mut m, entry, register);
    let o1 = alloc_object(&mut m, entry);
    // Caller 1: passes o1.
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: clo_reg,
            this: None,
            args: vec![o1],
            kind: CallKind::Dynamic,
        },
    );
    let o2 = alloc_object(&mut m, entry);
    // Caller 2: passes o2.
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: clo_reg,
            this: None,
            args: vec![o2],
            kind: CallKind::Dynamic,
        },
    );
    // Caller 3: no args at all (formal is undefined — precise-empty).
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: clo_reg,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(cb_param, InstId::new(0));
    assert!(ans.unbalanced && !ans.has_unknown, "{ans:?}");
    let mut want = vec![inst_of(&m, o1), inst_of(&m, o2)];
    want.sort();
    assert_eq!(ans.sites.iter().collect::<Vec<_>>(), want);
}

/// A phi cycle (the loop-carried self-reference) is cut by the
/// in-progress guard and degrades to unknown.
#[test]
fn phi_self_cycle_is_cut() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let latch = add_block(&mut m, f);
    let o = alloc_object(&mut m, entry);
    let site = inst_of(&m, o);
    // The phi's own result value, referenced by its latch incoming.
    let phi_val = ValueId::new(m.values.len() as u32);
    let phi = emit(
        &mut m,
        entry,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: latch,
                        kind: EdgeKind::Normal,
                    },
                    phi_val,
                ),
                (
                    Edge {
                        from: entry,
                        kind: EdgeKind::Normal,
                    },
                    o,
                ),
            ],
        },
    );
    assert_eq!(phi, phi_val);
    emit_void(&mut m, entry, Op::Branch { dest: latch });
    emit_void(&mut m, latch, Op::Branch { dest: entry });
    link(&mut m, entry, latch);
    link(&mut m, latch, entry);

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(phi, InstId::new(0));
    assert!(ans.sites.iter().eq([site]), "the acyclic incoming survives");
    assert!(ans.has_unknown, "the cycle cut marks unknown: {ans:?}");
}

/// Exception params: the owner assignment in `with_depth` plus the
/// opaque answer.
#[test]
fn exception_param_is_owned_and_unknown() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let handler = add_block(&mut m, f);
    let may_throw = try_get_global(&mut m, entry, "g");
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: may_throw,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });
    let exc = add_exception_param(&mut m, handler);
    emit_void(&mut m, handler, Op::Return { value: Some(exc) });
    add_try(&mut m, f, vec![entry], handler, exc);

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    // Owned (via the exception-param owner pass) and opaque.
    let ans = oracle.query(exc, InstId::new(0));
    assert!(ans.has_unknown && ans.sites.is_empty(), "{ans:?}");
}

/// A call edge whose base trace gave up partway (resolved but
/// incomplete): the hops still happen, marked unknown.
#[test]
fn partially_resolved_edge_marks_unknown() {
    let mut m = mk_module();
    let (fa, _) = add_static_func(&mut m, "fa", 0);
    let oa;
    {
        let b = entry_of(&m, fa);
        oa = alloc_object(&mut m, b);
        emit_void(&mut m, b, Op::Return { value: Some(oa) });
    }
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let t = add_block(&mut m, caller);
    let e = add_block(&mut m, caller);
    let join = add_block(&mut m, caller);
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
    let ca = closure_of(&mut m, t, fa);
    emit_void(&mut m, t, Op::Branch { dest: join });
    // The else arm's callee value is an opaque global: the phi's trace
    // is resolved-but-incomplete.
    let g = try_get_global(&mut m, e, "maybe");
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
                    ca,
                ),
                (
                    Edge {
                        from: e,
                        kind: EdgeKind::Normal,
                    },
                    g,
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

    let graph = CallGraph::build(&m);
    let edge = graph.edge_at(call).unwrap();
    assert_eq!(edge.targets, CallTargets::Resolved(vec![fa]));
    assert!(!edge.resolution_complete, "the global dead-end is partial");
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(r, call);
    assert!(ans.has_unknown, "{ans:?}");
    assert_eq!(ans.sites.iter().collect::<Vec<_>>(), vec![inst_of(&m, oa)]);
}

/// A resolved callee missing from the module table (a dangling
/// MethodRef) and an external (bodyless) callee both fold to unknown
/// inside the hop.
#[test]
fn dangling_and_external_callees_are_unknown() {
    let mut m = mk_module();
    let ext = add_external_func(&mut m, "ext");
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let ghost = load_method_ref(&mut m, entry, FuncId::new(999));
    let r1 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: ghost,
            this: None,
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    let c1 = inst_of(&m, r1);
    let ext_val = load_method_ref(&mut m, entry, ext);
    let r2 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: ext_val,
            this: None,
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    let c2 = inst_of(&m, r2);
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let a1 = oracle.query(r1, c1);
    assert!(a1.has_unknown && a1.sites.is_empty(), "{a1:?}");
    let a2 = oracle.query(r2, c2);
    assert!(a2.has_unknown && a2.sites.is_empty(), "{a2:?}");
}

/// A callee that returns NOTHING (`Return` with no value): the hop set
/// is empty — precise-empty, not unknown.
#[test]
fn void_callee_is_precise_empty() {
    let mut m = mk_module();
    let (v, _) = add_static_func(&mut m, "v", 0);
    {
        let b = entry_of(&m, v);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let clo = closure_of(&mut m, entry, v);
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let call = inst_of(&m, r);
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(r, call);
    assert!(!ans.has_unknown && ans.sites.is_empty(), "{ans:?}");
}

/// The implicit-slot bind table (balanced hops): the func slot binds
/// the call's callee value, the this slot the explicit receiver (or
/// unknown when absent), newTarget is never an aliased heap value.
#[test]
fn implicit_slot_binds() {
    let mut m = mk_module();
    // Three callees returning params[0] (func), params[1] (newTarget),
    // params[2] (this) respectively.
    let mut calls = Vec::new();
    let mut results = Vec::new();
    for (name, slot) in [("f_func", 0u16), ("f_nt", 1u16), ("f_this", 2u16)] {
        let (g, params) = add_static_func(&mut m, name, 0);
        {
            let b = entry_of(&m, g);
            emit_void(
                &mut m,
                b,
                Op::Return {
                    value: Some(params[slot as usize]),
                },
            );
        }
        calls.push((g, slot));
        results.push(params[slot as usize]);
    }
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let mut rs = Vec::new();
    for (g, _) in &calls {
        let clo = closure_of(&mut m, entry, *g);
        let r = emit(
            &mut m,
            entry,
            Op::Call {
                callee: clo,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        rs.push((r, clo));
    }
    // f_this with an explicit receiver.
    let recv = alloc_object(&mut m, entry);
    let clo_this = closure_of(&mut m, entry, calls[2].0);
    let r_this = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo_this,
            this: Some(recv),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    // func slot → the call's closure value (an AllocClosure site).
    let ans = oracle.query(rs[0].0, inst_of(&m, rs[0].0));
    assert_eq!(
        ans.sites.iter().collect::<Vec<_>>(),
        vec![inst_of(&m, rs[0].1)],
        "the func slot binds the called closure"
    );
    assert!(!ans.has_unknown);
    // newTarget slot → unknown (constructed per call).
    let ans = oracle.query(rs[1].0, inst_of(&m, rs[1].0));
    assert!(ans.has_unknown && ans.sites.is_empty(), "{ans:?}");
    // this slot, no receiver → unknown; with a receiver → its site.
    let ans = oracle.query(rs[2].0, inst_of(&m, rs[2].0));
    assert!(ans.has_unknown, "{ans:?}");
    let ans = oracle.query(r_this, inst_of(&m, r_this));
    assert_eq!(
        ans.sites.iter().collect::<Vec<_>>(),
        vec![inst_of(&m, recv)]
    );
    assert!(!ans.has_unknown);
    let _ = results;
}

/// Reflective call kinds bind no formals (Apply/SuperSpread read an
/// argument array; SuperForwardAllArgs inherits the caller's frame):
/// the bind is a leaf-unknown.
#[test]
fn apply_and_super_kinds_bind_opaque() {
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
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let arr = alloc_array(&mut m, entry);
    let mut rs = Vec::new();
    for kind in [
        CallKind::Apply,
        CallKind::SuperSpread,
        CallKind::SuperForwardAllArgs,
    ] {
        let clo = closure_of(&mut m, entry, id);
        let r = emit(
            &mut m,
            entry,
            Op::Call {
                callee: clo,
                this: None,
                args: vec![arr],
                kind,
            },
        );
        rs.push(r);
    }
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    for r in rs {
        let ans = oracle.query(r, inst_of(&m, r));
        assert!(ans.has_unknown, "{ans:?}");
    }
}

/// Fewer args than formals: the unbound formal is precisely empty
/// (undefined is not a heap object).
#[test]
fn short_args_bind_precise_empty() {
    let mut m = mk_module();
    let (two, params) = add_static_func(&mut m, "two", 2);
    {
        let b = entry_of(&m, two);
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(params[4]), // the second formal
            },
        );
    }
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let clo = closure_of(&mut m, entry, two);
    let o = alloc_object(&mut m, entry);
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo,
            this: None,
            args: vec![o], // one arg for two formals
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(r, inst_of(&m, r));
    assert!(!ans.has_unknown && ans.sites.is_empty(), "{ans:?}");
}

/// A non-static callee without the callType annotation has NO reliable
/// slot model (the taint policy's conservative choice): its param bind
/// is a leaf-unknown.
#[test]
fn no_slot_model_is_leaf_unknown() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "nostatic"); // modifiers NONE
    let p0 = add_param(&mut m, f, 0);
    {
        let b = entry_of(&m, f);
        emit_void(&mut m, b, Op::Return { value: Some(p0) });
    }
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    let clo = closure_of(&mut m, entry, f);
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(r, inst_of(&m, r));
    assert!(ans.has_unknown && ans.sites.is_empty(), "{ans:?}");
}

/// The §5.2 calling-context seam: the rung-1 engine records the edge
/// (answers are per-query context stacks, so this changes nothing).
#[test]
fn inject_calling_context_records_without_changing_answers() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let o = alloc_object(&mut m, entry);
    let site = inst_of(&m, o);
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let mut oracle = Rung1AliasOracle::new(&m, &graph);
    AliasOracle::<()>::inject_calling_context(&mut oracle, InstId::new(0), f, &());
    AliasOracle::<()>::inject_calling_context(&mut oracle, InstId::new(0), f, &());
    let ans = oracle.query(o, InstId::new(0));
    assert_eq!(ans.sites.iter().collect::<Vec<_>>(), vec![site]);
    assert!(ans.is_single_precise());
}

/// Engine construction over a module with dangling inst ids in a
/// function's block list: the scan skips them (the no-panics rule).
#[test]
fn with_depth_skips_dangling_insts() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let o = alloc_object(&mut m, entry);
    let site = inst_of(&m, o);
    m.block_mut(entry).unwrap().insts.push(InstId::new(9999));
    emit_void(&mut m, entry, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);
    let ans = oracle.query(o, InstId::new(0));
    assert_eq!(ans.sites.iter().collect::<Vec<_>>(), vec![site]);
}
