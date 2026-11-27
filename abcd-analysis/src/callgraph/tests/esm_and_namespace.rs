//! Cross-module `@bundle:` / dot-encoded ESM class resolution and `export * as ns`
//! namespace member call tests.

use super::*;

#[test]
fn cross_module_bundle_and_dot_encoded_imported_classes_resolve() {
    use abcd_ir::module::{ClassData, EsModule, ExportDecl, ImportDecl, ModuleRequest};
    use abcd_ir::op::{MemberAttrs, ModuleVarKind};

    let mut m = Module::new();

    // Record 0: `@bundle:` service record exporting `Auth`
    let d0 = m
        .sym
        .intern("L@bundle:com.demo.app/entry/ets/service/Auth;");
    let n0 = m.sym.intern("@bundle:com.demo.app/entry/ets/service/Auth");
    let cid0 = ClassId::new(0);
    let s_auth = m.sym.intern("Auth");
    let mut cls0 = ClassData::new(d0, n0);
    cls0.es_module = Some(EsModule {
        imports: vec![],
        exports: vec![ExportDecl::Local {
            export_name: s_auth,
            local_name: s_auth,
        }],
        module_requests: vec![],
    });
    m.classes.push(cls0);

    // Record 1: `@bundle:` page record importing `Auth` via `../service/Auth`
    let d1 = m.sym.intern("L@bundle:com.demo.app/entry/ets/pages/Login;");
    let n1 = m.sym.intern("@bundle:com.demo.app/entry/ets/pages/Login");
    let cid1 = ClassId::new(1);
    let s_req_auth = m.sym.intern("../service/Auth");
    let mut cls1 = ClassData::new(d1, n1);
    cls1.es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: s_auth,
            import_name: s_auth,
            module_request: s_req_auth,
        }],
        exports: vec![],
        module_requests: vec![ModuleRequest {
            specifier: s_req_auth,
            lazy: false,
        }],
    });
    m.classes.push(cls1);

    // Record 2: dot-encoded record exporting `Logger`
    let d2 = m.sym.intern("Lentry.src.main.ets.util.Logger;");
    let n2 = m.sym.intern("entry.src.main.ets.util.Logger");
    let cid2 = ClassId::new(2);
    let s_logger = m.sym.intern("Logger");
    let mut cls2 = ClassData::new(d2, n2);
    cls2.es_module = Some(EsModule {
        imports: vec![],
        exports: vec![ExportDecl::Local {
            export_name: s_logger,
            local_name: s_logger,
        }],
        module_requests: vec![],
    });
    m.classes.push(cls2);

    // Record 3: dot-encoded record importing `Logger` via `../util/Logger`
    let d3 = m.sym.intern("Lentry.src.main.ets.pages.Home;");
    let n3 = m.sym.intern("entry.src.main.ets.pages.Home");
    let cid3 = ClassId::new(3);
    let s_req_logger = m.sym.intern("../util/Logger");
    let mut cls3 = ClassData::new(d3, n3);
    cls3.es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: s_logger,
            import_name: s_logger,
            module_request: s_req_logger,
        }],
        exports: vec![],
        module_requests: vec![ModuleRequest {
            specifier: s_req_logger,
            lazy: false,
        }],
    });
    m.classes.push(cls3);

    // Populate Record 0 (`Auth`: static `verify`, instance `login`)
    let s_verify = intern(&mut m, "verify");
    let s_login = intern(&mut m, "login");
    let (auth_ctor, b_ac, _) = add_method_fn(&mut m, cid0, "Auth", FunctionKind::Constructor, 0);
    emit_void(&mut m, b_ac, Op::Return { value: None });
    let (auth_verify, b_av, _) = add_method_fn(&mut m, cid0, "verify", FunctionKind::Function, 0);
    emit_void(&mut m, b_av, Op::Return { value: None });
    let (auth_login, b_al, _) = add_method_fn(&mut m, cid0, "login", FunctionKind::Function, 0);
    emit_void(&mut m, b_al, Op::Return { value: None });

    let (_, b_m0, _) = add_method_fn(&mut m, cid0, "func_main_0", FunctionKind::Function, 0);
    let c_s_login = m.consts.intern(Const::String(s_login));
    let c_login = m.consts.intern(Const::method_ref(auth_login));
    let c_s_verify = m.consts.intern(Const::String(s_verify));
    let c_verify = m.consts.intern(Const::method_ref(auth_verify));
    let auth_members = m
        .consts
        .push_array(vec![c_s_login, c_login, c_s_verify, c_verify]);
    let auth_cls = emit(
        &mut m,
        b_m0,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: auth_ctor,
            heritage: None,
            members: auth_members,
            member_attrs: vec![
                MemberAttrs {
                    is_static: false,
                    kind: FunctionKind::Function,
                },
                MemberAttrs {
                    is_static: true,
                    kind: FunctionKind::Function,
                },
            ],
            count: 1,
        })),
    );
    emit_void(
        &mut m,
        b_m0,
        Op::StoreModuleVar {
            index: 0,
            value: auth_cls,
        },
    );
    emit_void(&mut m, b_m0, Op::Return { value: None });

    // Populate Record 1 (`Auth.verify()`, `new Auth().login()`)
    let (_, b_m1, _) = add_method_fn(&mut m, cid1, "func_main_0", FunctionKind::Function, 0);
    let imp_auth = emit(
        &mut m,
        b_m1,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let verify_callee = emit(
        &mut m,
        b_m1,
        Op::LoadProp {
            object: imp_auth,
            name: s_verify,
        },
    );
    let call_verify = push_inst(
        &mut m,
        b_m1,
        Op::Call {
            callee: verify_callee,
            this: Some(imp_auth),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let auth_inst = emit(
        &mut m,
        b_m1,
        Op::Call {
            callee: imp_auth,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    let call_new_auth = match m.value(auth_inst).unwrap().def {
        ValueDef::Inst(i) => i,
        _ => unreachable!(),
    };
    let login_callee = emit(
        &mut m,
        b_m1,
        Op::LoadProp {
            object: auth_inst,
            name: s_login,
        },
    );
    let call_login = push_inst(
        &mut m,
        b_m1,
        Op::Call {
            callee: login_callee,
            this: Some(auth_inst),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_m1, Op::Return { value: None });

    // Populate Record 2 (`Logger`: static `create` returning `new Logger()`, instance `info`)
    let s_create = intern(&mut m, "create");
    let s_info = intern(&mut m, "info");
    let (log_ctor, b_lc, _) = add_method_fn(&mut m, cid2, "Logger", FunctionKind::Constructor, 0);
    emit_void(&mut m, b_lc, Op::Return { value: None });
    let (log_info, b_li, _) = add_method_fn(&mut m, cid2, "info", FunctionKind::Function, 0);
    emit_void(&mut m, b_li, Op::Return { value: None });
    let (log_create, b_lcr, p_lcr) =
        add_method_fn(&mut m, cid2, "create", FunctionKind::Function, 0);
    let created_log = emit(
        &mut m,
        b_lcr,
        Op::Call {
            callee: p_lcr[2],
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    emit_void(
        &mut m,
        b_lcr,
        Op::Return {
            value: Some(created_log),
        },
    );

    let (_, b_m2, _) = add_method_fn(&mut m, cid2, "func_main_0", FunctionKind::Function, 0);
    let c_s_info = m.consts.intern(Const::String(s_info));
    let c_info = m.consts.intern(Const::method_ref(log_info));
    let c_s_create = m.consts.intern(Const::String(s_create));
    let c_create = m.consts.intern(Const::method_ref(log_create));
    let c_one = m.consts.intern(Const::number(1.0));
    let log_members = m
        .consts
        .push_array(vec![c_s_info, c_info, c_s_create, c_create, c_one]);
    let log_cls = emit(
        &mut m,
        b_m2,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: log_ctor,
            heritage: None,
            members: log_members,
            member_attrs: vec![],
            count: 1,
        })),
    );
    emit_void(
        &mut m,
        b_m2,
        Op::StoreModuleVar {
            index: 0,
            value: log_cls,
        },
    );
    emit_void(&mut m, b_m2, Op::Return { value: None });

    // Populate Record 3 (`Logger.create().info()`)
    let (_, b_m3, _) = add_method_fn(&mut m, cid3, "func_main_0", FunctionKind::Function, 0);
    let imp_log = emit(
        &mut m,
        b_m3,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let create_callee = emit(
        &mut m,
        b_m3,
        Op::LoadProp {
            object: imp_log,
            name: s_create,
        },
    );
    let log_inst = emit(
        &mut m,
        b_m3,
        Op::Call {
            callee: create_callee,
            this: Some(imp_log),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let call_create = match m.value(log_inst).unwrap().def {
        ValueDef::Inst(i) => i,
        _ => unreachable!(),
    };
    let info_callee = emit(
        &mut m,
        b_m3,
        Op::LoadProp {
            object: log_inst,
            name: s_info,
        },
    );
    let call_info = push_inst(
        &mut m,
        b_m3,
        Op::Call {
            callee: info_callee,
            this: Some(log_inst),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_m3, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    assert_eq!(
        cg.edge_at(call_verify).unwrap().targets,
        CallTargets::Resolved(vec![auth_verify])
    );
    assert_eq!(
        cg.edge_at(call_new_auth).unwrap().targets,
        CallTargets::Resolved(vec![auth_ctor])
    );
    assert_eq!(
        cg.edge_at(call_login).unwrap().targets,
        CallTargets::Resolved(vec![auth_login])
    );
    assert_eq!(
        cg.edge_at(call_create).unwrap().targets,
        CallTargets::Resolved(vec![log_create])
    );
    assert_eq!(
        cg.edge_at(call_info).unwrap().targets,
        CallTargets::Resolved(vec![log_info])
    );
}

#[test]
fn deep_mov_chain_over_20_hops_and_export_star_as_ns_resolve() {
    use abcd_ir::module::{ClassData, EsModule, ExportDecl, ImportDecl, ModuleRequest};
    use abcd_ir::op::ModuleVarKind;

    let mut m = Module::new();
    let s_ping = m.sym.intern("ping");
    let s_ns = m.sym.intern("ns");
    let s_star = m.sym.intern("*");
    let s_req_sub = m.sym.intern("./sub");
    let s_req_barrel = m.sym.intern("./barrel");

    // Record 0: `./sub` exporting `ping`
    let cid_sub = ClassId::new(0);
    let mut cls_sub = ClassData::new(
        m.sym.intern("L@bundle:com.demo/ets/sub;"),
        m.sym.intern("@bundle:com.demo/ets/sub"),
    );
    cls_sub.es_module = Some(EsModule {
        imports: vec![],
        exports: vec![ExportDecl::Local {
            export_name: s_ping,
            local_name: s_ping,
        }],
        module_requests: vec![],
    });
    m.classes.push(cls_sub);

    // Record 1: `./barrel` doing `export * as ns from "./sub"`
    let mut cls_barrel = ClassData::new(
        m.sym.intern("L@bundle:com.demo/ets/barrel;"),
        m.sym.intern("@bundle:com.demo/ets/barrel"),
    );
    cls_barrel.es_module = Some(EsModule {
        imports: vec![],
        exports: vec![ExportDecl::Indirect {
            export_name: s_ns,
            import_name: s_star,
            module_request: s_req_sub,
        }],
        module_requests: vec![ModuleRequest {
            specifier: s_req_sub,
            lazy: false,
        }],
    });
    m.classes.push(cls_barrel);

    // Record 2: `./main` importing `{ ns } from "./barrel"`
    let cid_main = ClassId::new(2);
    let mut cls_main = ClassData::new(
        m.sym.intern("L@bundle:com.demo/ets/main;"),
        m.sym.intern("@bundle:com.demo/ets/main"),
    );
    cls_main.es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: s_ns,
            import_name: s_ns,
            module_request: s_req_barrel,
        }],
        exports: vec![],
        module_requests: vec![ModuleRequest {
            specifier: s_req_barrel,
            lazy: false,
        }],
    });
    m.classes.push(cls_main);

    let (ping_fn, b_ping, _) = add_method_fn(&mut m, cid_sub, "ping", FunctionKind::Function, 0);
    emit_void(&mut m, b_ping, Op::Return { value: None });

    let (_, b_sub_main, _) =
        add_method_fn(&mut m, cid_sub, "func_main_0", FunctionKind::Function, 0);
    let df_ping = emit(
        &mut m,
        b_sub_main,
        Op::DefineFunc {
            body: ping_fn,
            captures: vec![],
            length: 0,
        },
    );
    let mut cur_ping = emit(&mut m, b_sub_main, Op::AllocClosure { func: df_ping });
    for _ in 0..25 {
        cur_ping = emit(&mut m, b_sub_main, Op::Mov { src: cur_ping });
    }
    emit_void(
        &mut m,
        b_sub_main,
        Op::StoreModuleVar {
            index: 0,
            value: cur_ping,
        },
    );
    emit_void(&mut m, b_sub_main, Op::Return { value: None });

    let (local_fn, b_loc, _) =
        add_method_fn(&mut m, cid_main, "localFn", FunctionKind::Function, 0);
    emit_void(&mut m, b_loc, Op::Return { value: None });

    let (_, b_main, _) = add_method_fn(&mut m, cid_main, "func_main_0", FunctionKind::Function, 0);
    let df_loc = emit(
        &mut m,
        b_main,
        Op::DefineFunc {
            body: local_fn,
            captures: vec![],
            length: 0,
        },
    );
    let mut clo_chain = emit(&mut m, b_main, Op::AllocClosure { func: df_loc });
    for _ in 0..25 {
        clo_chain = emit(&mut m, b_main, Op::Mov { src: clo_chain });
    }
    let call_mov_clo = push_inst(
        &mut m,
        b_main,
        Op::Call {
            callee: clo_chain,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    let mut ns_val = emit(
        &mut m,
        b_main,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    for _ in 0..25 {
        ns_val = emit(&mut m, b_main, Op::Mov { src: ns_val });
    }
    // Calling the namespace object itself resolves zero function targets -> complete == false.
    let call_ns_direct = push_inst(
        &mut m,
        b_main,
        Op::Call {
            callee: ns_val,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    // `ns.ping()` across `export * as ns` + 25-hop `Mov` chain resolves `ping_fn`.
    let ns_ping = emit(
        &mut m,
        b_main,
        Op::LoadProp {
            object: ns_val,
            name: s_ping,
        },
    );
    let call_ns_ping = push_inst(
        &mut m,
        b_main,
        Op::Call {
            callee: ns_ping,
            this: Some(ns_val),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_main, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    let e_clo = cg.edge_at(call_mov_clo).unwrap();
    assert_eq!(e_clo.targets, CallTargets::Resolved(vec![local_fn]));
    assert!(e_clo.resolution_complete);

    let e_ns_bad = cg.edge_at(call_ns_direct).unwrap();
    assert_eq!(e_ns_bad.targets, CallTargets::UnknownCallees);
    assert!(!e_ns_bad.resolution_complete);

    let e_ns_ping = cg.edge_at(call_ns_ping).unwrap();
    assert_eq!(e_ns_ping.targets, CallTargets::Resolved(vec![ping_fn]));
    assert!(e_ns_ping.resolution_complete);
}
