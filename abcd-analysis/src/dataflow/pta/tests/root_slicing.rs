//! Demand-driven root-sliced PTA, OpenHarmony harness filtering, namespace exports,
//! and 256 KiB stack tests.

use super::*;

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
    let links = ModuleLinkTable::build_with_harness(&aug, Some(harness_fid));
    let base = CallGraph::build_with_links(&aug, &links);
    let out = analyze_with_links_and_roots(
        &aug,
        &links,
        &base,
        &PtaConfig {
            harness_func: Some(harness_fid),
            ..PtaConfig::default()
        },
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
