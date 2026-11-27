//! Static and dynamic `DefineClass` / `DefineSendableClass` hierarchy, `super` calls,
//! prototype attachments, constructor field provenance, and 256 KiB stack tests.

use super::*;

#[test]
fn this_method_inherited_method_and_super_calls_resolve() {
    use abcd_ir::op::SuperKey;

    let mut m = mk_module();
    let cid = ClassId::new(0);

    let (base_ctor, b_bc, _) = add_method_fn(&mut m, cid, "Base", FunctionKind::Constructor, 0);
    emit_void(&mut m, b_bc, Op::Return { value: None });

    let (base_only, b_bo, _) = add_method_fn(&mut m, cid, "baseMethod", FunctionKind::Function, 0);
    emit_void(&mut m, b_bo, Op::Return { value: None });

    let (base_greet, b_bg, _) = add_method_fn(&mut m, cid, "Base.greet", FunctionKind::Function, 0);
    emit_void(&mut m, b_bg, Op::Return { value: None });

    let (sub_ctor, b_sc, p_sc) = add_method_fn(&mut m, cid, "Sub", FunctionKind::Constructor, 0);
    let super_ctor_call = push_inst(
        &mut m,
        b_sc,
        Op::Call {
            callee: p_sc[0],
            this: Some(p_sc[2]),
            args: vec![],
            kind: CallKind::Super,
        },
    );
    emit_void(
        &mut m,
        b_sc,
        Op::Return {
            value: Some(p_sc[2]),
        },
    );

    let (sub_helper, b_sh, _) = add_method_fn(&mut m, cid, "helper", FunctionKind::Function, 0);
    emit_void(&mut m, b_sh, Op::Return { value: None });

    let (sub_greet, b_sg, p_sg) =
        add_method_fn(&mut m, cid, "Sub.greet", FunctionKind::Function, 0);
    let s_helper = intern(&mut m, "helper");
    let s_base_m = intern(&mut m, "baseMethod");
    let s_greet = intern(&mut m, "greet");

    // 1) `this.helper()`
    let c_self = emit(
        &mut m,
        b_sg,
        Op::LoadProp {
            object: p_sg[2],
            name: s_helper,
        },
    );
    let self_call = push_inst(
        &mut m,
        b_sg,
        Op::Call {
            callee: c_self,
            this: Some(p_sg[2]),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    // 2) `this.baseMethod()` (inherited on miss)
    let c_inh = emit(
        &mut m,
        b_sg,
        Op::LoadProp {
            object: p_sg[2],
            name: s_base_m,
        },
    );
    let inh_call = push_inst(
        &mut m,
        b_sg,
        Op::Call {
            callee: c_inh,
            this: Some(p_sg[2]),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    // 3) `super.greet()` -> resolves to `Base.greet`, not `Sub.greet`!
    let c_sup = emit(
        &mut m,
        b_sg,
        Op::LoadSuper {
            this_value: p_sg[2],
            key: SuperKey::Name(s_greet),
        },
    );
    let sup_method_call = push_inst(
        &mut m,
        b_sg,
        Op::Call {
            callee: c_sup,
            this: Some(p_sg[2]),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_sg, Op::Return { value: None });

    // Define Base and Sub in `main`.
    let (_, b_main, _) = add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
    let c_s_base_m = m.consts.intern(Const::String(s_base_m));
    let c_base_only = m.consts.intern(Const::method_ref(base_only));
    let c_s_greet = m.consts.intern(Const::String(s_greet));
    let c_base_greet = m.consts.intern(Const::method_ref(base_greet));
    let c_two = m.consts.intern(Const::number(2.0));
    let base_members = m.consts.push_array(vec![
        c_s_base_m,
        c_base_only,
        c_s_greet,
        c_base_greet,
        c_two,
    ]);
    let base_cls = emit(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: base_ctor,
            heritage: None,
            members: base_members,
            member_attrs: vec![],
            count: 2,
        })),
    );
    let c_s_helper = m.consts.intern(Const::String(s_helper));
    let c_sub_helper = m.consts.intern(Const::method_ref(sub_helper));
    let c_sub_greet = m.consts.intern(Const::method_ref(sub_greet));
    let sub_members = m.consts.push_array(vec![
        c_s_helper,
        c_sub_helper,
        c_s_greet,
        c_sub_greet,
        c_two,
    ]);
    let _ = emit(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: sub_ctor,
            heritage: Some(base_cls),
            members: sub_members,
            member_attrs: vec![],
            count: 2,
        })),
    );
    emit_void(&mut m, b_main, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    let check = |call: InstId, target: FuncId| {
        let edge = cg.edge_at(call).expect("edge");
        assert_eq!(edge.edge_kind, CallEdgeKind::ResolvedValueFlow);
        assert_eq!(edge.targets, CallTargets::Resolved(vec![target]));
        assert!(!edge.resolution_complete);
    };
    check(super_ctor_call, base_ctor);
    check(self_call, sub_helper);
    check(inh_call, base_only);
    check(sup_method_call, base_greet);
}

#[test]
fn constructor_field_provenance_resolves_service_method() {
    let mut m = mk_module();
    let cid = ClassId::new(0);
    let s_do_work = intern(&mut m, "doWork");
    let s_service = intern(&mut m, "service");
    let s_svc_name = intern(&mut m, "Service");

    let (svc_ctor, b_sc, _) = add_method_fn(&mut m, cid, "Service", FunctionKind::Constructor, 0);
    emit_void(&mut m, b_sc, Op::Return { value: None });

    let (do_work, b_dw, _) = add_method_fn(&mut m, cid, "doWork", FunctionKind::Function, 0);
    emit_void(&mut m, b_dw, Op::Return { value: None });

    // Controller constructor: `this.service = new Service()` (via ArkTS lexical self-binding).
    let (ctrl_ctor, b_cc, p_cc) =
        add_method_fn(&mut m, cid, "Controller", FunctionKind::Constructor, 0);
    let svc_lex = emit(
        &mut m,
        b_cc,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    emit_void(
        &mut m,
        b_cc,
        Op::ThrowUndefinedIfHoleWithName {
            value: svc_lex,
            name: s_svc_name,
        },
    );
    let svc_inst = emit(
        &mut m,
        b_cc,
        Op::Call {
            callee: svc_lex,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    let new_svc_call = match m.value(svc_inst).unwrap().def {
        ValueDef::Inst(i) => i,
        _ => unreachable!(),
    };
    emit_void(
        &mut m,
        b_cc,
        Op::StoreProp {
            object: p_cc[2],
            name: s_service,
            value: svc_inst,
        },
    );
    emit_void(&mut m, b_cc, Op::Return { value: None });

    // Controller.run(): `this.service.doWork()`
    let (ctrl_run, b_cr, p_cr) = add_method_fn(&mut m, cid, "run", FunctionKind::Function, 0);
    let loaded_svc = emit(
        &mut m,
        b_cr,
        Op::LoadProp {
            object: p_cr[2],
            name: s_service,
        },
    );
    let loaded_dw = emit(
        &mut m,
        b_cr,
        Op::LoadProp {
            object: loaded_svc,
            name: s_do_work,
        },
    );
    let do_work_call = push_inst(
        &mut m,
        b_cr,
        Op::Call {
            callee: loaded_dw,
            this: Some(loaded_svc),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_cr, Op::Return { value: None });

    // `func_main_0`: lexical env storing `Service`, plus `DefineClass` for `Service` & `Controller`.
    let (_, b_main, _) = add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
    let _ = emit(
        &mut m,
        b_main,
        Op::NewLexEnv {
            num_vars: 1,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let c_s_dw = m.consts.intern(Const::String(s_do_work));
    let c_dw = m.consts.intern(Const::method_ref(do_work));
    let c_one = m.consts.intern(Const::number(1.0));
    let svc_members = m.consts.push_array(vec![c_s_dw, c_dw, c_one]);
    let svc_cls = emit(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: svc_ctor,
            heritage: None,
            members: svc_members,
            member_attrs: vec![],
            count: 1,
        })),
    );
    emit_void(
        &mut m,
        b_main,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: svc_cls,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let s_run = intern(&mut m, "run");
    let c_s_run = m.consts.intern(Const::String(s_run));
    let c_ctrl_run = m.consts.intern(Const::method_ref(ctrl_run));
    let ctrl_members = m.consts.push_array(vec![c_s_run, c_ctrl_run, c_one]);
    let _ = emit(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: ctrl_ctor,
            heritage: None,
            members: ctrl_members,
            member_attrs: vec![],
            count: 1,
        })),
    );
    emit_void(&mut m, b_main, Op::PopLexEnv);
    emit_void(&mut m, b_main, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    assert_eq!(
        cg.edge_at(new_svc_call).unwrap().targets,
        CallTargets::Resolved(vec![svc_ctor])
    );
    assert_eq!(
        cg.edge_at(do_work_call).unwrap().targets,
        CallTargets::Resolved(vec![do_work])
    );
}

#[test]
fn static_singleton_get_instance_fetch_resolves() {
    let mut m = mk_module();
    let cid = ClassId::new(0);
    let s_instance = intern(&mut m, "instance");
    let s_get_inst = intern(&mut m, "getInstance");
    let s_fetch = intern(&mut m, "fetch");

    let (repo_ctor, b_rc, _) = add_method_fn(&mut m, cid, "Repo", FunctionKind::Constructor, 0);
    emit_void(&mut m, b_rc, Op::Return { value: None });

    let (fetch_fn, b_fe, _) = add_method_fn(&mut m, cid, "fetch", FunctionKind::Function, 0);
    emit_void(&mut m, b_fe, Op::Return { value: None });

    // `static getInstance()`: `Repo.instance = new Repo(); return Repo.instance;`
    let (get_inst_fn, b_gi, _p_gi) =
        add_method_fn(&mut m, cid, "getInstance", FunctionKind::Function, 0);
    let repo_ref = emit(
        &mut m,
        b_gi,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let new_repo = emit(
        &mut m,
        b_gi,
        Op::Call {
            callee: repo_ref,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    emit_void(
        &mut m,
        b_gi,
        Op::StoreProp {
            object: repo_ref,
            name: s_instance,
            value: new_repo,
        },
    );
    let inst_field = emit(
        &mut m,
        b_gi,
        Op::LoadProp {
            object: repo_ref,
            name: s_instance,
        },
    );
    emit_void(
        &mut m,
        b_gi,
        Op::Return {
            value: Some(inst_field),
        },
    );

    // `caller()`: `Repo.getInstance().fetch()`
    let (caller_fn, b_ca, _) = add_method_fn(&mut m, cid, "caller", FunctionKind::Function, 0);
    let repo_in_caller = emit(
        &mut m,
        b_ca,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let gi_callee = emit(
        &mut m,
        b_ca,
        Op::LoadProp {
            object: repo_in_caller,
            name: s_get_inst,
        },
    );
    let singleton = emit(
        &mut m,
        b_ca,
        Op::Call {
            callee: gi_callee,
            this: Some(repo_in_caller),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let gi_call = match m.value(singleton).unwrap().def {
        ValueDef::Inst(i) => i,
        _ => unreachable!(),
    };
    let fetch_callee = emit(
        &mut m,
        b_ca,
        Op::LoadProp {
            object: singleton,
            name: s_fetch,
        },
    );
    let fetch_call = push_inst(
        &mut m,
        b_ca,
        Op::Call {
            callee: fetch_callee,
            this: Some(singleton),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_ca, Op::Return { value: None });

    // `func_main_0` defines `Repo` (1 instance method `fetch`, 1 static method `getInstance`)
    // and captures the lexical env into `caller_fn`.
    let (_, b_main, _) = add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
    let _ = emit(
        &mut m,
        b_main,
        Op::NewLexEnv {
            num_vars: 1,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let c_s_fetch = m.consts.intern(Const::String(s_fetch));
    let c_fetch = m.consts.intern(Const::method_ref(fetch_fn));
    let c_s_gi = m.consts.intern(Const::String(s_get_inst));
    let c_gi = m.consts.intern(Const::method_ref(get_inst_fn));
    let c_one = m.consts.intern(Const::number(1.0));
    let repo_members = m
        .consts
        .push_array(vec![c_s_fetch, c_fetch, c_s_gi, c_gi, c_one]);
    let repo_cls = emit(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: repo_ctor,
            heritage: None,
            members: repo_members,
            member_attrs: vec![],
            count: 1,
        })),
    );
    emit_void(
        &mut m,
        b_main,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: repo_cls,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let _ = emit(
        &mut m,
        b_main,
        Op::DefineFunc {
            body: caller_fn,
            captures: vec![],
            length: 0,
        },
    );
    emit_void(&mut m, b_main, Op::PopLexEnv);
    emit_void(&mut m, b_main, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    assert_eq!(
        cg.edge_at(gi_call).unwrap().targets,
        CallTargets::Resolved(vec![get_inst_fn])
    );
    assert_eq!(
        cg.edge_at(fetch_call).unwrap().targets,
        CallTargets::Resolved(vec![fetch_fn])
    );
}

#[test]
fn deep_500_inheritance_and_field_chain_runs_on_256k_stack() {
    const DEPTH: usize = 500;
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut m = mk_module();
            let cid = ClassId::new(0);
            let s_next = intern(&mut m, "next");
            let s_ping = intern(&mut m, "ping");

            let mut ctors = Vec::with_capacity(DEPTH);
            let mut ctor_blocks = Vec::with_capacity(DEPTH);
            let mut ctor_this = Vec::with_capacity(DEPTH);
            let (ping_fn, b_ping, _) =
                add_method_fn(&mut m, cid, "ping", FunctionKind::Function, 0);
            emit_void(&mut m, b_ping, Op::Return { value: None });

            for i in 0..DEPTH {
                let (ctor, b_c, p_c) =
                    add_method_fn(&mut m, cid, &format!("C{i}"), FunctionKind::Constructor, 0);
                ctors.push(ctor);
                ctor_blocks.push(b_c);
                ctor_this.push(p_c[2]);
            }

            let (_, b_main, _) =
                add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
            let _ = emit(
                &mut m,
                b_main,
                Op::NewLexEnv {
                    num_vars: DEPTH as u16,
                    kind: abcd_ir::LexEnvKind::Plain,
                },
            );
            let c_s_ping = m.consts.intern(Const::String(s_ping));
            let c_ping = m.consts.intern(Const::method_ref(ping_fn));
            let c_one = m.consts.intern(Const::number(1.0));
            let m0 = m.consts.push_array(vec![c_s_ping, c_ping, c_one]);
            let empty_mem = m.consts.push_array(vec![]);
            let mut prev_cls = emit(
                &mut m,
                b_main,
                Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                    ctor: ctors[0],
                    heritage: None,
                    members: m0,
                    member_attrs: vec![],
                    count: 1,
                })),
            );
            emit_void(
                &mut m,
                b_main,
                Op::PutLexVar {
                    level: 0,
                    slot: 0,
                    value: prev_cls,
                    kind: abcd_ir::LexEnvKind::Plain,
                },
            );
            emit_void(&mut m, ctor_blocks[0], Op::Return { value: None });

            for i in 1..DEPTH {
                prev_cls = emit(
                    &mut m,
                    b_main,
                    Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                        ctor: ctors[i],
                        heritage: Some(prev_cls),
                        members: empty_mem,
                        member_attrs: vec![],
                        count: 0,
                    })),
                );
                emit_void(
                    &mut m,
                    b_main,
                    Op::PutLexVar {
                        level: 0,
                        slot: i as u16,
                        value: prev_cls,
                        kind: abcd_ir::LexEnvKind::Plain,
                    },
                );
                let prev_lex = emit(
                    &mut m,
                    ctor_blocks[i],
                    Op::GetLexVar {
                        level: 0,
                        slot: (i - 1) as u16,
                        kind: abcd_ir::LexEnvKind::Plain,
                    },
                );
                let sub_inst = emit(
                    &mut m,
                    ctor_blocks[i],
                    Op::Call {
                        callee: prev_lex,
                        this: None,
                        args: vec![],
                        kind: CallKind::New,
                    },
                );
                emit_void(
                    &mut m,
                    ctor_blocks[i],
                    Op::StoreProp {
                        object: ctor_this[i],
                        name: s_next,
                        value: sub_inst,
                    },
                );
                emit_void(&mut m, ctor_blocks[i], Op::Return { value: None });
            }

            // 500-deep `LoadProp` chain on a constructed leaf instance (`inst.next.next...`).
            let leaf_inst = emit(
                &mut m,
                b_main,
                Op::Call {
                    callee: prev_cls,
                    this: None,
                    args: vec![],
                    kind: CallKind::New,
                },
            );
            let mut cur = leaf_inst;
            for _ in 0..DEPTH {
                cur = emit(
                    &mut m,
                    b_main,
                    Op::LoadProp {
                        object: cur,
                        name: s_next,
                    },
                );
            }
            let deep_callee = emit(
                &mut m,
                b_main,
                Op::LoadProp {
                    object: cur,
                    name: s_ping,
                },
            );
            let deep_call = push_inst(
                &mut m,
                b_main,
                Op::Call {
                    callee: deep_callee,
                    this: Some(cur),
                    args: vec![],
                    kind: CallKind::Dynamic,
                },
            );
            emit_void(&mut m, b_main, Op::Return { value: None });

            let cg = CallGraph::build(&m);
            // Bounded step cap cuts cleanly to `UnknownCallees` without stack overflow.
            assert_eq!(
                cg.edge_at(deep_call).unwrap().targets,
                CallTargets::UnknownCallees
            );
        })
        .expect("spawn 256k thread");
    handle.join().expect("256 KiB stack must not overflow");
}

#[test]
fn sendable_class_prototype_attachment_getter_and_object_literal_resolve() {
    use abcd_ir::op::ModuleVarKind;

    let mut m = mk_module();
    let cid = ClassId::new(0);
    let s_work = intern(&mut m, "work");
    let s_extra = intern(&mut m, "extra");
    let s_shared = intern(&mut m, "shared");
    let s_proto = intern(&mut m, "prototype");
    let s_lit_fn = intern(&mut m, "litFn");
    let s_prop_get = intern(&mut m, "worker");

    let (send_ctor, b_sc, _) =
        add_method_fn(&mut m, cid, "SendWorker", FunctionKind::Constructor, 0);
    emit_void(&mut m, b_sc, Op::Return { value: None });
    let (work_fn, b_wk, _) = add_method_fn(&mut m, cid, "work", FunctionKind::Function, 0);
    emit_void(&mut m, b_wk, Op::Return { value: None });
    let (extra_fn, b_ex, _) = add_method_fn(&mut m, cid, "extra", FunctionKind::Function, 0);
    emit_void(&mut m, b_ex, Op::Return { value: None });
    let (lit_fn, b_lf, _) = add_method_fn(&mut m, cid, "litFn", FunctionKind::Function, 0);
    emit_void(&mut m, b_lf, Op::Return { value: None });

    // `shared()` inside `SendWorker` loads its own sendable class via `ModuleVarKind::SendableClass`,
    // constructs an instance, and returns it.
    let (shared_fn, b_sh, _) = add_method_fn(&mut m, cid, "shared", FunctionKind::Function, 0);
    let self_send_cls = emit(
        &mut m,
        b_sh,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::SendableClass,
        },
    );
    let w_inst = emit(
        &mut m,
        b_sh,
        Op::Call {
            callee: self_send_cls,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    emit_void(
        &mut m,
        b_sh,
        Op::Return {
            value: Some(w_inst),
        },
    );

    // Getter `get worker()` calls `SendWorker.shared()` via `SendableClass`.
    let (getter_fn, b_gt, _) = add_method_fn(&mut m, cid, "worker", FunctionKind::Getter, 0);
    let cls_in_get = emit(
        &mut m,
        b_gt,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::SendableClass,
        },
    );
    let sh_callee = emit(
        &mut m,
        b_gt,
        Op::LoadProp {
            object: cls_in_get,
            name: s_shared,
        },
    );
    let sh_res = emit(
        &mut m,
        b_gt,
        Op::Call {
            callee: sh_callee,
            this: Some(cls_in_get),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(
        &mut m,
        b_gt,
        Op::Return {
            value: Some(sh_res),
        },
    );

    let (_, b_main, _) = add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
    let c_s_work = m.consts.intern(Const::String(s_work));
    let c_work = m.consts.intern(Const::method_ref(work_fn));
    let c_s_pget = m.consts.intern(Const::String(s_prop_get));
    let c_get = m.consts.intern(Const::method_ref(getter_fn));
    let c_s_shared = m.consts.intern(Const::String(s_shared));
    let c_shared = m.consts.intern(Const::method_ref(shared_fn));
    let c_two = m.consts.intern(Const::number(2.0));
    let send_members = m.consts.push_array(vec![
        c_s_work, c_work, c_s_pget, c_get, c_s_shared, c_shared, c_two,
    ]);
    let send_cls = emit(
        &mut m,
        b_main,
        Op::DefineSendableClass(Box::new(abcd_ir::DefineClassData {
            ctor: send_ctor,
            heritage: None,
            members: send_members,
            member_attrs: vec![],
            count: 2,
        })),
    );
    // Prototype attachment: `SendWorker.prototype.extra = extra_fn`
    let proto = emit(
        &mut m,
        b_main,
        Op::LoadProp {
            object: send_cls,
            name: s_proto,
        },
    );
    let df_extra = emit(
        &mut m,
        b_main,
        Op::DefineFunc {
            body: extra_fn,
            captures: vec![],
            length: 0,
        },
    );
    let cl_extra = emit(&mut m, b_main, Op::AllocClosure { func: df_extra });
    emit_void(
        &mut m,
        b_main,
        Op::StoreProp {
            object: proto,
            name: s_extra,
            value: cl_extra,
        },
    );

    let inst = emit(
        &mut m,
        b_main,
        Op::Call {
            callee: send_cls,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    let w_from_getter = emit(
        &mut m,
        b_main,
        Op::LoadProp {
            object: inst,
            name: s_prop_get,
        },
    );
    let extra_callee = emit(
        &mut m,
        b_main,
        Op::LoadProp {
            object: w_from_getter,
            name: s_extra,
        },
    );
    let call_extra = push_inst(
        &mut m,
        b_main,
        Op::Call {
            callee: extra_callee,
            this: Some(w_from_getter),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    // Object literal method resolution
    let c_s_lit = m.consts.intern(Const::String(s_lit_fn));
    let c_lit = m.consts.intern(Const::method_ref(lit_fn));
    let shape = m.consts.push_object(vec![c_s_lit], vec![c_lit]);
    let obj = emit(&mut m, b_main, Op::AllocObject { shape });
    let lit_callee = emit(
        &mut m,
        b_main,
        Op::LoadProp {
            object: obj,
            name: s_lit_fn,
        },
    );
    let call_lit = push_inst(
        &mut m,
        b_main,
        Op::Call {
            callee: lit_callee,
            this: Some(obj),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_main, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    assert_eq!(
        cg.edge_at(call_extra).unwrap().targets,
        CallTargets::Resolved(vec![extra_fn])
    );
    assert_eq!(
        cg.edge_at(call_lit).unwrap().targets,
        CallTargets::Resolved(vec![lit_fn])
    );
}

#[test]
fn async_generator_new_spread_and_super_arrow_resolve() {
    let mut m = mk_module();
    let cid = ClassId::new(0);
    let s_run = intern(&mut m, "run");

    let (base_ctor, b_bc, _) = add_method_fn(&mut m, cid, "Base", FunctionKind::Constructor, 0);
    emit_void(&mut m, b_bc, Op::Return { value: None });

    let (run_fn, b_run, _) = add_method_fn(&mut m, cid, "run", FunctionKind::Function, 0);
    emit_void(&mut m, b_run, Op::Return { value: None });

    // Arrow inside derived constructor calls `super(...)` via `CallKind::SuperArrow`.
    let (sup_arrow, b_sa, _) = add_method_fn(&mut m, cid, "supArrow", FunctionKind::Arrow, 0);
    let sup_cls_lex = emit(
        &mut m,
        b_sa,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let call_sup_arrow = push_inst(
        &mut m,
        b_sa,
        Op::Call {
            callee: sup_cls_lex,
            this: None,
            args: vec![],
            kind: CallKind::SuperArrow,
        },
    );
    emit_void(&mut m, b_sa, Op::Return { value: None });

    let (sub_ctor, b_sc, _) = add_method_fn(&mut m, cid, "Sub", FunctionKind::Constructor, 0);
    emit_void(&mut m, b_sc, Op::Return { value: None });

    let (agen_fn, b_ag, _) = add_method_fn(&mut m, cid, "agen", FunctionKind::AsyncGenerator, 0);
    emit_void(&mut m, b_ag, Op::Return { value: None });

    let (_, b_main, _) = add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
    let _ = emit(
        &mut m,
        b_main,
        Op::NewLexEnv {
            num_vars: 1,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let c_s_run = m.consts.intern(Const::String(s_run));
    let c_run = m.consts.intern(Const::method_ref(run_fn));
    let c_one = m.consts.intern(Const::Int32(1));
    let base_members = m.consts.push_array(vec![c_s_run, c_run, c_one]);
    let base_cls = emit(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: base_ctor,
            heritage: None,
            members: base_members,
            member_attrs: vec![],
            count: 1,
        })),
    );
    emit_void(
        &mut m,
        b_main,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: base_cls,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let _ = emit(
        &mut m,
        b_main,
        Op::DefineFunc {
            body: sup_arrow,
            captures: vec![],
            length: 0,
        },
    );
    let empty_mem = m.consts.push_array(vec![]);
    let sub_cls = emit(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: sub_ctor,
            heritage: Some(base_cls),
            members: empty_mem,
            member_attrs: vec![],
            count: 0,
        })),
    );
    let spread_args = alloc_array(&mut m, b_main);
    let sub_inst = emit(
        &mut m,
        b_main,
        Op::Call {
            callee: sub_cls,
            this: None,
            args: vec![spread_args],
            kind: CallKind::NewSpread,
        },
    );
    let call_new_spread = match m.value(sub_inst).unwrap().def {
        ValueDef::Inst(i) => i,
        _ => unreachable!(),
    };
    let run_callee = emit(
        &mut m,
        b_main,
        Op::LoadProp {
            object: sub_inst,
            name: s_run,
        },
    );
    let call_run = push_inst(
        &mut m,
        b_main,
        Op::Call {
            callee: run_callee,
            this: Some(sub_inst),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    let df_agen = emit(
        &mut m,
        b_main,
        Op::DefineFunc {
            body: agen_fn,
            captures: vec![],
            length: 0,
        },
    );
    let agen_obj = emit(&mut m, b_main, Op::CreateAsyncGenerator { func: df_agen });
    let call_agen = push_inst(
        &mut m,
        b_main,
        Op::Call {
            callee: agen_obj,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_main, Op::PopLexEnv);
    emit_void(&mut m, b_main, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    assert_eq!(
        cg.edge_at(call_sup_arrow).unwrap().targets,
        CallTargets::Resolved(vec![base_ctor])
    );
    assert_eq!(
        cg.edge_at(call_new_spread).unwrap().targets,
        CallTargets::Resolved(vec![sub_ctor])
    );
    assert_eq!(
        cg.edge_at(call_run).unwrap().targets,
        CallTargets::Resolved(vec![run_fn])
    );
    assert_eq!(
        cg.edge_at(call_agen).unwrap().targets,
        CallTargets::Resolved(vec![agen_fn])
    );
}

#[test]
fn super_forward_all_args_static_hierarchy_and_sendable_loop_lex_resolve() {
    use abcd_ir::module::{ClassData, SourceLang};
    use abcd_ir::op::LexEnvKind;
    use abcd_ir::ty::{StaticTy, Ty};

    let mut m = mk_module();
    let dyn_cid = ClassId::new(0);
    let s_greet = intern(&mut m, "greet");

    // 1) Dynamic `DefineClass` default derived ctor using `SuperForwardAllArgs`.
    let (dyn_base_ctor, b_dbc, _) =
        add_method_fn(&mut m, dyn_cid, "DynBase", FunctionKind::Constructor, 0);
    emit_void(&mut m, b_dbc, Op::Return { value: None });

    let (dyn_sub_ctor, b_dsc, p_dsc) =
        add_method_fn(&mut m, dyn_cid, "DynSub", FunctionKind::Constructor, 0);
    let call_dyn_fwd = push_inst(
        &mut m,
        b_dsc,
        Op::Call {
            callee: p_dsc[0],
            this: None,
            args: vec![p_dsc[0]],
            kind: CallKind::SuperForwardAllArgs,
        },
    );
    emit_void(&mut m, b_dsc, Op::Return { value: None });

    // 2) Static `ClassData::{super_class, interfaces}` (`SourceLang::ArkTS`) + `SuperForwardAllArgs`.
    let iface_cid = ClassId::new(m.classes.len() as u32);
    let mut iface_cls = ClassData::new(m.sym.intern("LIGreeter;"), m.sym.intern("IGreeter"));
    iface_cls.source_lang = SourceLang::ArkTS;
    iface_cls.modifiers = Modifiers::PUBLIC.union(Modifiers::INTERFACE);
    m.classes.push(iface_cls);

    let sbase_cid = ClassId::new(m.classes.len() as u32);
    let mut sbase_cls = ClassData::new(m.sym.intern("LStaticBase;"), m.sym.intern("StaticBase"));
    sbase_cls.source_lang = SourceLang::ArkTS;
    m.classes.push(sbase_cls);

    let ssub_cid = ClassId::new(m.classes.len() as u32);
    let mut ssub_cls = ClassData::new(m.sym.intern("LStaticSub;"), m.sym.intern("StaticSub"));
    ssub_cls.source_lang = SourceLang::ArkTS;
    ssub_cls.super_class = Some(sbase_cid);
    ssub_cls.interfaces = vec![iface_cid];
    m.classes.push(ssub_cls);

    let add_ark_fn = |m: &mut Module, cid: ClassId, name: &str, kind: FunctionKind| {
        let sym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(cid, sym, kind);
        fd.modifiers = Modifiers::PUBLIC;
        m.functions.push(fd);
        m.classes[cid.index()].methods.push(fid);
        let b = add_block(m, fid);
        let this_p = add_param(m, fid, 0);
        (fid, b, this_p)
    };

    let (sbase_ctor, b_sbc, _) = add_ark_fn(&mut m, sbase_cid, "<ctor>", FunctionKind::Constructor);
    emit_void(&mut m, b_sbc, Op::Return { value: None });

    let (_ssub_ctor, b_ssc, ssub_this) =
        add_ark_fn(&mut m, ssub_cid, "<ctor>", FunctionKind::Constructor);
    let call_static_fwd = push_inst(
        &mut m,
        b_ssc,
        Op::Call {
            callee: ssub_this,
            this: None,
            args: vec![ssub_this],
            kind: CallKind::SuperForwardAllArgs,
        },
    );
    emit_void(&mut m, b_ssc, Op::Return { value: None });

    let (ssub_greet, b_ssg, _) = add_ark_fn(&mut m, ssub_cid, "greet", FunctionKind::Function);
    emit_void(&mut m, b_ssg, Op::Return { value: None });

    // 3) Driver: `Sendable` env survives `PopLexEnv`, loop back-edge propagates `Plain` env,
    //    and `StaticTy::Reference(iface_cid)` resolves `IGreeter.greet` -> `StaticSub.greet`.
    let (driver_fn, b_entry, p_drv) =
        add_method_fn(&mut m, dyn_cid, "func_main_0", FunctionKind::Function, 1);
    m.values[p_drv[3].index()].ty = Ty::Static(StaticTy::Reference(iface_cid));
    let b_hdr = add_block(&mut m, driver_fn);
    let b_exit = add_block(&mut m, driver_fn);

    let empty_mem = m.consts.push_array(vec![]);
    let dyn_base = emit(
        &mut m,
        b_entry,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: dyn_base_ctor,
            heritage: None,
            members: empty_mem,
            member_attrs: vec![],
            count: 0,
        })),
    );
    let _ = emit(
        &mut m,
        b_entry,
        Op::NewLexEnv {
            num_vars: 1,
            kind: LexEnvKind::Sendable,
        },
    );
    emit_void(
        &mut m,
        b_entry,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: dyn_base,
            kind: LexEnvKind::Sendable,
        },
    );
    let _ = emit(
        &mut m,
        b_entry,
        Op::NewLexEnv {
            num_vars: 1,
            kind: LexEnvKind::Plain,
        },
    );
    emit_void(&mut m, b_entry, Op::PopLexEnv);
    emit_void(&mut m, b_entry, Op::Branch { dest: b_hdr });
    link(&mut m, b_entry, b_hdr);

    let base_from_sendable = emit(
        &mut m,
        b_hdr,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: LexEnvKind::Sendable,
        },
    );
    let _ = emit(
        &mut m,
        b_hdr,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: dyn_sub_ctor,
            heritage: Some(base_from_sendable),
            members: empty_mem,
            member_attrs: vec![],
            count: 0,
        })),
    );
    let cond = load_number(&mut m, b_hdr, 0.0);
    emit_void(
        &mut m,
        b_hdr,
        Op::CondBranch {
            cond,
            true_dest: b_hdr,
            false_dest: b_exit,
        },
    );
    link(&mut m, b_hdr, b_hdr);
    link(&mut m, b_hdr, b_exit);

    let iface_callee = emit(
        &mut m,
        b_exit,
        Op::LoadProp {
            object: p_drv[3],
            name: s_greet,
        },
    );
    let call_iface = push_inst(
        &mut m,
        b_exit,
        Op::Call {
            callee: iface_callee,
            this: Some(p_drv[3]),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_exit, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    assert_eq!(
        cg.edge_at(call_dyn_fwd).unwrap().targets,
        CallTargets::Resolved(vec![dyn_base_ctor])
    );
    assert_eq!(
        cg.edge_at(call_static_fwd).unwrap().targets,
        CallTargets::Resolved(vec![sbase_ctor])
    );
    assert_eq!(
        cg.edge_at(call_iface).unwrap().targets,
        CallTargets::Resolved(vec![ssub_greet])
    );
}

#[test]
fn dynamic_define_class_extends_resolves_subtype_overrides_and_marks_incomplete() {
    let mut m = mk_module();
    let cid = ClassId::new(0);
    let s_run = intern(&mut m, "run");

    let add_cls_fn = |m: &mut Module, name: &str, kind: FunctionKind| {
        let sym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(cid, sym, kind);
        fd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        m.functions.push(fd);
        m.classes[cid.index()].methods.push(fid);
        let b = add_block(m, fid);
        let p0 = add_param(m, fid, 0);
        let _ = add_param(m, fid, 1);
        let p_this = add_param(m, fid, 2);
        (fid, b, p0, p_this)
    };

    // `class Base { run() { ... }; dispatch() { return this.run(); } }`
    let (base_ctor, b_bc, _, _) = add_cls_fn(&mut m, "Base", FunctionKind::Constructor);
    emit_void(&mut m, b_bc, Op::Return { value: None });

    let (base_run, b_br, _, _) = add_cls_fn(&mut m, "Base_run", FunctionKind::Function);
    emit_void(&mut m, b_br, Op::Return { value: None });

    let (base_dispatch, b_bd, _, disp_this) =
        add_cls_fn(&mut m, "Base_dispatch", FunctionKind::Function);
    let callee_run = emit(
        &mut m,
        b_bd,
        Op::LoadProp {
            object: disp_this,
            name: s_run,
        },
    );
    let call_virtual = push_inst(
        &mut m,
        b_bd,
        Op::Call {
            callee: callee_run,
            this: Some(disp_this),
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_bd, Op::Return { value: None });

    // `class Sub extends Base { run() { ... } }`
    let (sub_ctor, b_sc, _, _) = add_cls_fn(&mut m, "Sub", FunctionKind::Constructor);
    emit_void(&mut m, b_sc, Op::Return { value: None });

    let (sub_run, b_sr, _, _) = add_cls_fn(&mut m, "Sub_run", FunctionKind::Function);
    emit_void(&mut m, b_sr, Op::Return { value: None });

    // `class UnresolvedSub extends dynamicBase() { constructor() { super(); } }`
    let (unres_ctor, b_uc, uc_p0, _) =
        add_cls_fn(&mut m, "UnresolvedSub", FunctionKind::Constructor);
    let call_unres_super = push_inst(
        &mut m,
        b_uc,
        Op::Call {
            callee: uc_p0,
            this: None,
            args: Vec::new(),
            kind: CallKind::Super,
        },
    );
    emit_void(&mut m, b_uc, Op::Return { value: None });

    let (_, b_main, _, _) = add_cls_fn(&mut m, "func_main_0", FunctionKind::Function);
    let s_disp = intern(&mut m, "dispatch");
    let c_s_run = m.consts.intern(Const::String(s_run));
    let c_s_disp = m.consts.intern(Const::String(s_disp));
    let c_br = m.consts.intern(Const::method_ref(base_run));
    let c_bd = m.consts.intern(Const::method_ref(base_dispatch));
    let c_sr = m.consts.intern(Const::method_ref(sub_run));
    let base_mem = m.consts.push_array(vec![c_s_run, c_br, c_s_disp, c_bd]);
    let sub_mem = m.consts.push_array(vec![c_s_run, c_sr]);
    let empty_mem = m.consts.push_array(Vec::new());

    let base_cls = emit(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: base_ctor,
            heritage: None,
            members: base_mem,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    let _ = emit(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: sub_ctor,
            heritage: Some(base_cls),
            members: sub_mem,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );

    let s_dyn = intern(&mut m, "getDynamicBase");
    let dyn_base = emit(
        &mut m,
        b_main,
        Op::TryGetGlobal {
            name: s_dyn,
            default: None,
        },
    );
    let _ = emit(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: unres_ctor,
            heritage: Some(dyn_base),
            members: empty_mem,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    emit_void(&mut m, b_main, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    let virt_edge = cg.edge_at(call_virtual).expect("virtual edge");
    let mut want = vec![base_run, sub_run];
    want.sort();
    assert_eq!(
        virt_edge.targets,
        CallTargets::Resolved(want),
        "dynamic DefineClass `extends` must include Sub.run override via sub_classes CHA"
    );
    assert!(
        !virt_edge.resolution_complete,
        "CHA virtual dispatch must mark resolution_complete == false"
    );

    let super_edge = cg.edge_at(call_unres_super).expect("unresolved super edge");
    assert_eq!(super_edge.targets, CallTargets::UnknownCallees);
    assert!(
        !super_edge.resolution_complete,
        "unresolved dynamic base expression must leave resolution_complete == false"
    );
}
