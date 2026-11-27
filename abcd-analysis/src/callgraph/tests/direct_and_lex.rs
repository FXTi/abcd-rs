//! Direct calls, closures, SSA phi merges, lexical `this` capture, histograms,
//! determinism, and trace-budget completeness tests.

use super::*;

/// Direct call through `LoadConst(MethodRef)` resolves statically.
#[test]
fn direct_call_resolves() {
    let mut m = mk_module();
    let target = add_func_named(&mut m, "target");
    {
        let b = entry_of(&m, target);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let f = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, f);
    let callee = load_method_ref(&mut m, entry, target);
    let call = push_inst(
        &mut m,
        entry,
        Op::Call {
            callee,
            this: None,
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    let edge = cg.edge_at(call).expect("edge recorded");
    assert_eq!(edge.edge_kind, CallEdgeKind::Direct);
    assert_eq!(edge.targets, CallTargets::Resolved(vec![target]));
    assert_eq!(cg.callers_of(target), &[call]);
}

/// A closure stored and later called: `DefineFunc` → `AllocClosure` →
/// `Mov` → dynamic call. The closure blind spot does not exist for us.
#[test]
fn closure_value_call_resolves() {
    let mut m = mk_module();
    let body = add_func_named(&mut m, "lambda");
    {
        let b = entry_of(&m, body);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let f = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, f);
    let def = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body,
            captures: vec![],
            length: 0,
        },
    );
    let clo = emit(&mut m, entry, Op::AllocClosure { func: def });
    let alias = emit(&mut m, entry, Op::Mov { src: clo });
    let call = push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: alias,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    let edge = cg.edge_at(call).expect("edge recorded");
    assert_eq!(edge.edge_kind, CallEdgeKind::ResolvedValueFlow);
    assert_eq!(edge.targets, CallTargets::Resolved(vec![body]));
}

/// A phi of two closures resolves to both.
#[test]
fn phi_of_closures_resolves_to_both() {
    let mut m = mk_module();
    let g1 = add_func_named(&mut m, "g1");
    {
        let b = entry_of(&m, g1);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let g2 = add_func_named(&mut m, "g2");
    {
        let b = entry_of(&m, g2);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let f = add_func_named(&mut m, "caller");
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
    let d1 = emit(
        &mut m,
        t,
        Op::DefineFunc {
            body: g1,
            captures: vec![],
            length: 0,
        },
    );
    emit_void(&mut m, t, Op::Branch { dest: join });
    let d2 = emit(
        &mut m,
        e,
        Op::DefineFunc {
            body: g2,
            captures: vec![],
            length: 0,
        },
    );
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
                    d1,
                ),
                (
                    abcd_ir::Edge {
                        from: e,
                        kind: abcd_ir::EdgeKind::Normal,
                    },
                    d2,
                ),
            ],
        },
    );
    let call = push_inst(
        &mut m,
        join,
        Op::Call {
            callee: phi,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, join, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    let mut want = vec![g1, g2];
    want.sort();
    assert_eq!(
        cg.edge_at(call).expect("edge").targets,
        CallTargets::Resolved(want)
    );
}

/// A callee loaded from a property is explicitly UNKNOWN — never
/// dropped.
#[test]
fn property_callee_is_explicit_unknown() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, f);
    let obj = add_param(&mut m, f, 1);
    let name = intern(&mut m, "m");
    let callee = emit(&mut m, entry, Op::LoadProp { object: obj, name });
    let call = push_inst(
        &mut m,
        entry,
        Op::Call {
            callee,
            this: Some(obj),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    let edge = cg.edge_at(call).expect("the edge exists even when unknown");
    assert_eq!(edge.edge_kind, CallEdgeKind::UnknownCallees);
    assert_eq!(edge.targets, CallTargets::UnknownCallees);
    assert_eq!(cg.histogram(&m).unknown, 1);
    assert_eq!(cg.histogram(&m).total(), 1);
}

/// `New` resolves its constructor through the same trace; an external
/// target counts in the external bucket.
#[test]
fn new_and_external_histogram() {
    let mut m = mk_module();
    let ctor = add_func_named(&mut m, "C");
    {
        let b = entry_of(&m, ctor);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let mut fd = m.functions[ctor.index()].clone();
    fd.kind = FunctionKind::Constructor;
    m.functions[ctor.index()] = fd;

    let ext = {
        let sym = m.sym.intern("print");
        let id = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(ClassId::new(0), sym, FunctionKind::Function);
        fd.is_external = true;
        m.functions.push(fd);
        id
    };

    let f = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, f);
    let c = load_method_ref(&mut m, entry, ctor);
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: c,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    let p = load_method_ref(&mut m, entry, ext);
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: p,
            this: None,
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    let h = cg.histogram(&m);
    assert_eq!(h.resolved_internal, 1, "the `new C()` site");
    assert_eq!(h.resolved_external, 1, "the external `print` site");
    assert_eq!(h.unknown, 0);
}

/// Two builds over the same module are equal.
#[test]
fn build_is_deterministic() {
    let mut m = mk_module();
    let target = add_func_named(&mut m, "target");
    {
        let b = entry_of(&m, target);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, f);
    let callee = load_method_ref(&mut m, entry, target);
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee,
            this: None,
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    assert_eq!(CallGraph::build(&m), CallGraph::build(&m));
}

#[test]
fn arrow_closure_capturing_this_resolves_method_call() {
    let mut m = mk_module();
    let cid = ClassId::new(0);
    let s_on_tap = intern(&mut m, "onTap");
    let s_mount = intern(&mut m, "mount");

    let (view_ctor, b_vc, _) = add_method_fn(&mut m, cid, "MyView", FunctionKind::Constructor, 0);
    emit_void(&mut m, b_vc, Op::Return { value: None });

    let (on_tap_fn, b_ot, _) = add_method_fn(&mut m, cid, "onTap", FunctionKind::Function, 0);
    emit_void(&mut m, b_ot, Op::Return { value: None });

    let (arrow_fn, b_ar, _) = add_method_fn(&mut m, cid, "arrow", FunctionKind::Arrow, 0);
    let cap_this = emit(
        &mut m,
        b_ar,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let tap_callee = emit(
        &mut m,
        b_ar,
        Op::LoadProp {
            object: cap_this,
            name: s_on_tap,
        },
    );
    let arrow_tap_call = push_inst(
        &mut m,
        b_ar,
        Op::Call {
            callee: tap_callee,
            this: Some(cap_this),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_ar, Op::Return { value: None });

    // `mount()` captures `this` (`p_mo[2]`) into `NewLexEnv` slot 0 and creates `arrow_fn`.
    let (mount_fn, b_mo, p_mo) = add_method_fn(&mut m, cid, "mount", FunctionKind::Function, 0);
    let _ = emit(
        &mut m,
        b_mo,
        Op::NewLexEnv {
            num_vars: 1,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    emit_void(
        &mut m,
        b_mo,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: p_mo[2],
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let df_arrow = emit(
        &mut m,
        b_mo,
        Op::DefineFunc {
            body: arrow_fn,
            captures: vec![],
            length: 0,
        },
    );
    let _ = emit(&mut m, b_mo, Op::AllocClosure { func: df_arrow });
    emit_void(&mut m, b_mo, Op::PopLexEnv);
    emit_void(&mut m, b_mo, Op::Return { value: None });

    let (_, b_main, _) = add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
    let c_s_tap = m.consts.intern(Const::String(s_on_tap));
    let c_tap = m.consts.intern(Const::method_ref(on_tap_fn));
    let c_s_mount = m.consts.intern(Const::String(s_mount));
    let c_mount = m.consts.intern(Const::method_ref(mount_fn));
    let c_two = m.consts.intern(Const::number(2.0));
    let members = m
        .consts
        .push_array(vec![c_s_tap, c_tap, c_s_mount, c_mount, c_two]);
    let _ = emit(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: view_ctor,
            heritage: None,
            members,
            member_attrs: vec![],
            count: 2,
        })),
    );
    emit_void(&mut m, b_main, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    assert_eq!(
        cg.edge_at(arrow_tap_call).unwrap().targets,
        CallTargets::Resolved(vec![on_tap_fn])
    );
}

#[test]
fn capped_trace_chain_marks_resolution_incomplete() {
    let mut m = mk_module();
    let t1 = add_func_named(&mut m, "t1");
    let b_t1 = entry_of(&m, t1);
    emit_void(&mut m, b_t1, Op::Return { value: None });

    let f = add_func_named(&mut m, "deep_caller");
    let b = entry_of(&m, f);
    let mut cur = load_method_ref(&mut m, b, t1);
    for _ in 0..(MAX_TRACE_STEPS + 16) {
        cur = emit(&mut m, b, Op::Mov { src: cur });
    }
    let call_iid = push_inst(
        &mut m,
        b,
        Op::Call {
            callee: cur,
            this: None,
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    let edge = cg.edge_at(call_iid).expect("edge");
    assert!(
        !edge.resolution_complete,
        "budget-cut trace must never report resolution_complete == true"
    );
}
