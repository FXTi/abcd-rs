use super::*;

/// Probe 1 — Cross-module `export { tok as apiToken } from`, `export * from`
/// (with mutual `export *` cycle), `GetModuleNamespace`, and `@ohos.net.http`
/// two-step `createHttp().request(...)` sink.
#[test]
fn probe_ohos_01_cross_module_reexport_star_and_namespace() {
    let mut m = Module::new();
    let c_src = add_record(&mut m, "L@bundle:com.demo/entry/ets/source_mod;");
    let c_cyc = add_record(&mut m, "L@bundle:com.demo/entry/ets/cycle_mod;");
    let c_bar = add_record(&mut m, "L@bundle:com.demo/entry/ets/barrel_mod;");
    let c_snk = add_record(&mut m, "L@bundle:com.demo/entry/ets/sink_mod;");

    let s_oaid_mod = m.sym.intern("@ohos.identifier.oaid");
    let s_get_oaid = m.sym.intern("getOAID");
    let s_tok = m.sym.intern("tok");
    let s_clean = m.sym.intern("cleanVal");
    let s_api_tok = m.sym.intern("apiToken");
    let s_rel_src = m.sym.intern("./source_mod");
    let s_rel_cyc = m.sym.intern("./cycle_mod");
    let s_rel_bar = m.sym.intern("./barrel_mod");
    let s_ohm_bar = m.sym.intern("@bundle:com.demo/entry/ets/barrel_mod");
    let s_http_mod = m.sym.intern("@ohos.net.http");
    let s_default = m.sym.intern("default");
    let s_http = m.sym.intern("http");
    let s_ns = m.sym.intern("ns");

    m.classes[c_src.index()].es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: s_get_oaid,
            import_name: s_get_oaid,
            module_request: s_oaid_mod,
        }],
        exports: vec![
            ExportDecl::Local {
                local_name: s_tok,
                export_name: s_tok,
            },
            ExportDecl::Local {
                local_name: s_clean,
                export_name: s_clean,
            },
        ],
        module_requests: vec![ModuleRequest {
            specifier: s_oaid_mod,
            lazy: false,
        }],
    });

    m.classes[c_cyc.index()].es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![ExportDecl::Star {
            module_request: s_rel_bar,
        }],
        module_requests: vec![ModuleRequest {
            specifier: s_rel_bar,
            lazy: false,
        }],
    });

    m.classes[c_bar.index()].es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![
            ExportDecl::Indirect {
                export_name: s_api_tok,
                import_name: s_tok,
                module_request: s_rel_src,
            },
            ExportDecl::Star {
                module_request: s_rel_src,
            },
            ExportDecl::Star {
                module_request: s_rel_cyc,
            },
        ],
        module_requests: vec![
            ModuleRequest {
                specifier: s_rel_src,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_rel_cyc,
                lazy: false,
            },
        ],
    });

    m.classes[c_snk.index()].es_module = Some(EsModule {
        imports: vec![
            ImportDecl::Regular {
                local_name: s_api_tok,
                import_name: s_api_tok,
                module_request: s_ohm_bar,
            },
            ImportDecl::Regular {
                local_name: s_http,
                import_name: s_default,
                module_request: s_http_mod,
            },
            ImportDecl::Namespace {
                local_name: s_ns,
                module_request: s_ohm_bar,
            },
        ],
        exports: Vec::new(),
        module_requests: vec![
            ModuleRequest {
                specifier: s_ohm_bar,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_http_mod,
                lazy: false,
            },
        ],
    });

    // source_mod `func_main_0`: slot 0 = getOAID() (tainted), slot 1 = "public" (clean).
    let (_, b_src, _) = add_fn(&mut m, c_src, "func_main_0", FunctionKind::Function, 3);
    let oaid_fn = emit_val(
        &mut m,
        b_src,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let oaid_val = emit_val(
        &mut m,
        b_src,
        Op::Call {
            callee: oaid_fn,
            this: None,
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );
    emit_void(
        &mut m,
        b_src,
        Op::StoreModuleVar {
            index: 0,
            value: oaid_val,
        },
    );
    let clean_s = load_str(&mut m, b_src, "public");
    emit_void(
        &mut m,
        b_src,
        Op::StoreModuleVar {
            index: 1,
            value: clean_s,
        },
    );
    emit_void(&mut m, b_src, Op::Return { value: None });

    for c in [c_cyc, c_bar] {
        let (_, b, _) = add_fn(&mut m, c, "func_main_0", FunctionKind::Function, 3);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // sink_mod `func_main_0`:
    let (_, b_snk, _) = add_fn(&mut m, c_snk, "func_main_0", FunctionKind::Function, 3);
    let imp_api_tok = emit_val(
        &mut m,
        b_snk,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let http_mod = emit_val(
        &mut m,
        b_snk,
        Op::LoadModuleVar {
            index: 1,
            kind: ModuleVarKind::External,
        },
    );
    let create_http = load_prop(&mut m, b_snk, http_mod, "createHttp");
    let req_obj = emit_val(
        &mut m,
        b_snk,
        Op::Call {
            callee: create_http,
            this: Some(http_mod),
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    let req_fn = load_prop(&mut m, b_snk, req_obj, "request");

    // Line 101: TP (indirect re-export `apiToken`).
    let _ = emit_val_line(
        &mut m,
        b_snk,
        Op::Call {
            callee: req_fn,
            this: Some(req_obj),
            args: vec![imp_api_tok],
            kind: CallKind::Direct,
        },
        101,
    );

    // Namespace reads off `GetModuleNamespace(0)`: `ns.tok` (TP) vs `ns.cleanVal` (clean).
    let ns_obj = emit_val(&mut m, b_snk, Op::GetModuleNamespace { index: 0 });
    let ns_tok = load_prop(&mut m, b_snk, ns_obj, "tok");
    let ns_clean = load_prop(&mut m, b_snk, ns_obj, "cleanVal");

    let _ = emit_val_line(
        &mut m,
        b_snk,
        Op::Call {
            callee: req_fn,
            this: Some(req_obj),
            args: vec![ns_tok],
            kind: CallKind::Direct,
        },
        102,
    );
    let _ = emit_val_line(
        &mut m,
        b_snk,
        Op::Call {
            callee: req_fn,
            this: Some(req_obj),
            args: vec![ns_clean],
            kind: CallKind::Direct,
        },
        103,
    );
    emit_void(&mut m, b_snk, Op::Return { value: None });

    assert_ohos_probe(&m, "01-cross-module-reexport-star-ns", None, &[101, 102]);
}

/// Probe 2 — `@kit.*` canonical aliases (`@kit.BasicServicesKit` -> `@ohos.pasteboard`,
/// `@kit.PerformanceAnalysisKit` -> `@ohos.hilog`), cross-module `new SessionStore(v)`
/// instance field sensitivity, and cross-module `sendLeak(...)` closure invocation.
#[test]
fn probe_ohos_02_kit_imports_cross_module_closure_and_class_instance() {
    let mut m = Module::new();
    let c_svc = add_record(&mut m, "L@bundle:com.demo/entry/ets/service;");
    let c_page = add_record(&mut m, "L@bundle:com.demo/entry/ets/page;");

    let s_perf_kit = m.sym.intern("@kit.PerformanceAnalysisKit");
    let s_basic_kit = m.sym.intern("@kit.BasicServicesKit");
    let s_hilog = m.sym.intern("hilog");
    let s_pb = m.sym.intern("pasteboard");
    let s_send_leak = m.sym.intern("sendLeak");
    let s_sess = m.sym.intern("SessionStore");
    let s_rel_svc = m.sym.intern("./service");

    m.classes[c_svc.index()].es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: s_hilog,
            import_name: s_hilog,
            module_request: s_perf_kit,
        }],
        exports: vec![
            ExportDecl::Local {
                local_name: s_send_leak,
                export_name: s_send_leak,
            },
            ExportDecl::Local {
                local_name: s_sess,
                export_name: s_sess,
            },
        ],
        module_requests: vec![ModuleRequest {
            specifier: s_perf_kit,
            lazy: false,
        }],
    });

    m.classes[c_page.index()].es_module = Some(EsModule {
        imports: vec![
            ImportDecl::Regular {
                local_name: s_pb,
                import_name: s_pb,
                module_request: s_basic_kit,
            },
            ImportDecl::Regular {
                local_name: s_send_leak,
                import_name: s_send_leak,
                module_request: s_rel_svc,
            },
            ImportDecl::Regular {
                local_name: s_sess,
                import_name: s_sess,
                module_request: s_rel_svc,
            },
        ],
        exports: Vec::new(),
        module_requests: vec![
            ModuleRequest {
                specifier: s_basic_kit,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_rel_svc,
                lazy: false,
            },
        ],
    });

    // `service.ets`: `export function sendLeak(msg)` + `export class SessionStore { constructor(v) { this.secret = v; } }`.
    let (f_leak, b_leak, p_leak) = add_fn(&mut m, c_svc, "sendLeak", FunctionKind::Function, 4);
    let hilog_obj = emit_val(
        &mut m,
        b_leak,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let hilog_info = load_prop(&mut m, b_leak, hilog_obj, "info");
    let dom = load_num(&mut m, b_leak, 0.0);
    let tag = load_str(&mut m, b_leak, "Demo");
    let _ = emit_val_line(
        &mut m,
        b_leak,
        Op::Call {
            callee: hilog_info,
            this: Some(hilog_obj),
            args: vec![dom, tag, p_leak[3]],
            kind: CallKind::Direct,
        },
        201,
    );
    emit_void(&mut m, b_leak, Op::Return { value: None });

    let (f_ctor, b_ctor, p_ctor) =
        add_fn(&mut m, c_svc, "SessionStore", FunctionKind::Constructor, 4);
    store_prop(&mut m, b_ctor, p_ctor[2], "secret", p_ctor[3]);
    emit_void(&mut m, b_ctor, Op::Return { value: None });

    let (_, b_svc, _) = add_fn(&mut m, c_svc, "func_main_0", FunctionKind::Function, 3);
    let leak_clos = mk_closure(&mut m, b_svc, f_leak);
    emit_void(
        &mut m,
        b_svc,
        Op::StoreModuleVar {
            index: 0,
            value: leak_clos,
        },
    );
    let empty_mem = m.consts.push_array(Vec::new());
    let sess_cls = emit_val(
        &mut m,
        b_svc,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: f_ctor,
            heritage: None,
            members: empty_mem,
            member_attrs: Vec::new(),
            count: 1,
        })),
    );
    emit_void(
        &mut m,
        b_svc,
        Op::StoreModuleVar {
            index: 1,
            value: sess_cls,
        },
    );
    emit_void(&mut m, b_svc, Op::Return { value: None });

    // `page.ets`: reads clipboard primary text, wraps in `new SessionStore(clip)`,
    // and also constructs `new SessionStore("public")` calling `hilog.warn` directly (clean).
    let (_, b_page, _) = add_fn(&mut m, c_page, "func_main_0", FunctionKind::Function, 3);
    let pb_mod = emit_val(
        &mut m,
        b_page,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let get_sys_pb = load_prop(&mut m, b_page, pb_mod, "getSystemPasteboard");
    let sys_pb = emit_val(
        &mut m,
        b_page,
        Op::Call {
            callee: get_sys_pb,
            this: Some(pb_mod),
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    let get_data_sync = load_prop(&mut m, b_page, sys_pb, "getDataSync");
    let paste_data = emit_val(
        &mut m,
        b_page,
        Op::Call {
            callee: get_data_sync,
            this: Some(sys_pb),
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    let get_primary = load_prop(&mut m, b_page, paste_data, "getPrimaryText");
    let clip_text = emit_val(
        &mut m,
        b_page,
        Op::Call {
            callee: get_primary,
            this: Some(paste_data),
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );

    let imp_leak = emit_val(
        &mut m,
        b_page,
        Op::LoadModuleVar {
            index: 1,
            kind: ModuleVarKind::External,
        },
    );
    let imp_sess = emit_val(
        &mut m,
        b_page,
        Op::LoadModuleVar {
            index: 2,
            kind: ModuleVarKind::External,
        },
    );
    let tainted_sess = emit_val(
        &mut m,
        b_page,
        Op::Call {
            callee: imp_sess,
            this: None,
            args: vec![clip_text],
            kind: CallKind::New,
        },
    );
    let pub_str = load_str(&mut m, b_page, "public");
    let clean_sess = emit_val(
        &mut m,
        b_page,
        Op::Call {
            callee: imp_sess,
            this: None,
            args: vec![pub_str],
            kind: CallKind::New,
        },
    );
    let tainted_sec = load_prop(&mut m, b_page, tainted_sess, "secret");
    let clean_sec = load_prop(&mut m, b_page, clean_sess, "secret");

    // Calls `sendLeak(tainted_sess.secret)` -> hits line 201 inside `sendLeak`.
    let _ = emit_val(
        &mut m,
        b_page,
        Op::Call {
            callee: imp_leak,
            this: None,
            args: vec![tainted_sec],
            kind: CallKind::Dynamic,
        },
    );

    // Clean control sink on `clean_sess.secret` (must NOT hit because Rung 2 PTA
    // keys `tainted_sess` and `clean_sess` by distinct `New` call sites!).
    let hilog_svc_fn = {
        // Import hilog in svc? Let's call `@ohos.hilog.warn` via `TryGetGlobal` or `@ohos.hilog` import on page:
        // Add `@kit.PerformanceAnalysisKit` import slot 3 on `c_page`!
        m.classes[c_page.index()]
            .es_module
            .as_mut()
            .unwrap()
            .imports
            .push(ImportDecl::Regular {
                local_name: s_hilog,
                import_name: s_hilog,
                module_request: s_perf_kit,
            });
        m.classes[c_page.index()]
            .es_module
            .as_mut()
            .unwrap()
            .module_requests
            .push(ModuleRequest {
                specifier: s_perf_kit,
                lazy: false,
            });
        let hl = emit_val(
            &mut m,
            b_page,
            Op::LoadModuleVar {
                index: 3,
                kind: ModuleVarKind::External,
            },
        );
        let hw = load_prop(&mut m, b_page, hl, "warn");
        (hl, hw)
    };
    let d2 = load_num(&mut m, b_page, 0.0);
    let t2 = load_str(&mut m, b_page, "Clean");
    let _ = emit_val_line(
        &mut m,
        b_page,
        Op::Call {
            callee: hilog_svc_fn.1,
            this: Some(hilog_svc_fn.0),
            args: vec![d2, t2, clean_sec],
            kind: CallKind::Direct,
        },
        202,
    );
    emit_void(&mut m, b_page, Op::Return { value: None });

    assert_ohos_probe(&m, "02-kit-cross-module-closure-class", None, &[201]);
}

/// Probe 3 — Stage `UIAbility` lifecycle (`onCreate(want)` -> `this.deepLink = want.parameters.target`
/// -> `onForeground()` -> `this.context.startAbility(this.deepLink)`), paired with a
/// second `SettingsAbility` class to prove per-Ability receiver isolation (`fp = 0`).
#[test]
fn probe_ohos_03_uiability_want_lifecycle_and_receiver_isolation() {
    let mut m = Module::new();
    let cid = add_record(
        &mut m,
        "L@bundle:com.demo/entry/ets/entryability/EntryAbility;",
    );
    let s_kit_ab = m.sym.intern("@kit.AbilityKit");
    let s_uiab = m.sym.intern("UIAbility");
    m.classes[cid.index()].es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: s_uiab,
            import_name: s_uiab,
            module_request: s_kit_ab,
        }],
        exports: Vec::new(),
        module_requests: vec![ModuleRequest {
            specifier: s_kit_ab,
            lazy: false,
        }],
    });

    // EntryAbility: `onCreate(want, launchParam)` + `onForeground()`.
    let (ctor1, bc1, _) = add_fn(&mut m, cid, "EntryAbility", FunctionKind::Constructor, 3);
    emit_void(&mut m, bc1, Op::Return { value: None });

    let (oc1, boc1, poc1) = add_fn(&mut m, cid, "onCreate", FunctionKind::Function, 5);
    let params_obj = load_prop(&mut m, boc1, poc1[3], "parameters");
    let target_want = load_prop(&mut m, boc1, params_obj, "target");
    store_prop(&mut m, boc1, poc1[2], "deepLink", target_want);
    let safe_const = load_str(&mut m, boc1, "HomeAbility");
    store_prop(&mut m, boc1, poc1[2], "safeLink", safe_const);
    emit_void(&mut m, boc1, Op::Return { value: None });

    let (fg1, bfg1, pfg1) = add_fn(&mut m, cid, "onForeground", FunctionKind::Function, 3);
    let ctx1 = load_prop(&mut m, bfg1, pfg1[2], "context");
    let start_ab1 = load_prop(&mut m, bfg1, ctx1, "startAbility");
    let dl1 = load_prop(&mut m, bfg1, pfg1[2], "deepLink");
    let sl1 = load_prop(&mut m, bfg1, pfg1[2], "safeLink");
    let _ = emit_val_line(
        &mut m,
        bfg1,
        Op::Call {
            callee: start_ab1,
            this: Some(ctx1),
            args: vec![dl1],
            kind: CallKind::Direct,
        },
        301, // TP
    );
    let _ = emit_val_line(
        &mut m,
        bfg1,
        Op::Call {
            callee: start_ab1,
            this: Some(ctx1),
            args: vec![sl1],
            kind: CallKind::Direct,
        },
        302, // CLEAN
    );
    emit_void(&mut m, bfg1, Op::Return { value: None });

    // SettingsAbility: ignores `want`, sets `this.deepLink = "Settings"`, calls `startAbility`.
    let (ctor2, bc2, _) = add_fn(&mut m, cid, "SettingsAbility", FunctionKind::Constructor, 3);
    emit_void(&mut m, bc2, Op::Return { value: None });
    let (oc2, boc2, poc2) = add_fn(&mut m, cid, "onCreate2", FunctionKind::Function, 5);
    let clean_dl = load_str(&mut m, boc2, "Settings");
    store_prop(&mut m, boc2, poc2[2], "deepLink", clean_dl);
    emit_void(&mut m, boc2, Op::Return { value: None });
    let (fg2, bfg2, pfg2) = add_fn(&mut m, cid, "onForeground2", FunctionKind::Function, 3);
    let ctx2 = load_prop(&mut m, bfg2, pfg2[2], "context");
    let start_ab2 = load_prop(&mut m, bfg2, ctx2, "startAbility");
    let dl2 = load_prop(&mut m, bfg2, pfg2[2], "deepLink");
    let _ = emit_val_line(
        &mut m,
        bfg2,
        Op::Call {
            callee: start_ab2,
            this: Some(ctx2),
            args: vec![dl2],
            kind: CallKind::Direct,
        },
        303, // CLEAN (must NOT mix with EntryAbility.this!)
    );
    emit_void(&mut m, bfg2, Op::Return { value: None });

    // `func_main_0`: defines both UIAbility classes extending imported `UIAbility`.
    let (_, bmain, _) = add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
    let base_uiab = emit_val(
        &mut m,
        bmain,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let s_oc = m.sym.intern("onCreate");
    let s_fg = m.sym.intern("onForeground");
    let c_s_oc = m.consts.intern(Const::String(s_oc));
    let c_s_fg = m.consts.intern(Const::String(s_fg));
    let c_m_oc1 = m.consts.intern(Const::method_ref(oc1));
    let c_m_fg1 = m.consts.intern(Const::method_ref(fg1));
    let mem1 = m.consts.push_array(vec![c_s_oc, c_m_oc1, c_s_fg, c_m_fg1]);
    let _ = emit_val(
        &mut m,
        bmain,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: ctor1,
            heritage: Some(base_uiab),
            members: mem1,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    let c_m_oc2 = m.consts.intern(Const::method_ref(oc2));
    let c_m_fg2 = m.consts.intern(Const::method_ref(fg2));
    let mem2 = m.consts.push_array(vec![c_s_oc, c_m_oc2, c_s_fg, c_m_fg2]);
    let _ = emit_val(
        &mut m,
        bmain,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: ctor2,
            heritage: Some(base_uiab),
            members: mem2,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    emit_void(&mut m, bmain, Op::Return { value: None });

    assert_ohos_probe(&m, "03-uiability-want-receiver-isolation", None, &[301]);
}

/// Probe 4 — `*ExtensionAbility` discovered via `module.json` `srcEntry` +
/// `onAddForm(want)` writing `want.uri` to `@kit.CoreFileKit` `fileIo.writeSync`.
#[test]
fn probe_ohos_04_extension_ability_manifest_discovery_and_fs_sink() {
    let mut m = Module::new();
    let cid = add_record(&mut m, "L@bundle:com.demo/entry/ets/form/PayFormAbility;");
    let s_core_file = m.sym.intern("@kit.CoreFileKit");
    let s_file_io = m.sym.intern("fileIo");
    m.classes[cid.index()].es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: s_file_io,
            import_name: s_file_io,
            module_request: s_core_file,
        }],
        exports: Vec::new(),
        module_requests: vec![ModuleRequest {
            specifier: s_core_file,
            lazy: false,
        }],
    });

    let (ctor, bc, _) = add_fn(&mut m, cid, "PayFormAbility", FunctionKind::Constructor, 3);
    emit_void(&mut m, bc, Op::Return { value: None });

    let (on_add, ba, pa) = add_fn(&mut m, cid, "onAddForm", FunctionKind::Function, 4);
    let fs_mod = emit_val(
        &mut m,
        ba,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let write_sync = load_prop(&mut m, ba, fs_mod, "writeSync");
    let fd_num = load_num(&mut m, ba, 3.0);
    let want_uri = load_prop(&mut m, ba, pa[3], "uri");
    let banner = load_str(&mut m, ba, "static-header");
    let _ = emit_val_line(
        &mut m,
        ba,
        Op::Call {
            callee: write_sync,
            this: Some(fs_mod),
            args: vec![fd_num, want_uri],
            kind: CallKind::Direct,
        },
        401, // TP
    );
    let _ = emit_val_line(
        &mut m,
        ba,
        Op::Call {
            callee: write_sync,
            this: Some(fs_mod),
            args: vec![fd_num, banner],
            kind: CallKind::Direct,
        },
        402, // CLEAN
    );
    emit_void(&mut m, ba, Op::Return { value: None });

    // Define class WITHOUT heritage — relies on `manifest_json` `srcEntry` + `onAddForm`!
    let (_, bmain, _) = add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
    let s_af = m.sym.intern("onAddForm");
    let c_s_af = m.consts.intern(Const::String(s_af));
    let c_m_add = m.consts.intern(Const::method_ref(on_add));
    let mem = m.consts.push_array(vec![c_s_af, c_m_add]);
    let _ = emit_val(
        &mut m,
        bmain,
        Op::DefineClass(Box::new(DefineClassData {
            ctor,
            heritage: None,
            members: mem,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    emit_void(&mut m, bmain, Op::Return { value: None });

    let manifest =
        r#"{"module":{"extensionAbilities":[{"srcEntry":"./ets/form/PayFormAbility.ets"}]}}"#;
    assert_ohos_probe(
        &m,
        "04-extension-ability-manifest-fs",
        Some(manifest),
        &[401],
    );
}

/// Probe 5 — ArkUI `ViewPU` component (`aboutToAppear` -> `this.token = prefs.getSync(...)`
/// -> `initialRender` -> `NewLexEnv` + `PutLexVar` `this` capture -> `observeComponentCreation2`
/// -> `Button.onClick` -> `this.webCtrl.loadUrl(this.token)`), with a sibling `StaticBanner`
/// `ViewPU` component verifying zero cross-component `this` / `LexVar` leakage (`fp = 0`).
#[test]
fn probe_ohos_05_arkui_viewpu_lifecycle_lexenv_and_onclick_isolation() {
    let mut m = Module::new();
    let cid = add_record(&mut m, "L@bundle:com.demo/entry/ets/pages/ProfilePage;");
    let s_ark_data = m.sym.intern("@kit.ArkData");
    let s_ark_web = m.sym.intern("@kit.ArkWeb");
    let s_prefs = m.sym.intern("preferences");
    let s_webview = m.sym.intern("webview");
    m.classes[cid.index()].es_module = Some(EsModule {
        imports: vec![
            ImportDecl::Regular {
                local_name: s_prefs,
                import_name: s_prefs,
                module_request: s_ark_data,
            },
            ImportDecl::Regular {
                local_name: s_webview,
                import_name: s_webview,
                module_request: s_ark_web,
            },
        ],
        exports: Vec::new(),
        module_requests: vec![
            ModuleRequest {
                specifier: s_ark_data,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_ark_web,
                lazy: false,
            },
        ],
    });

    // Component 1: `ProfileCard extends ViewPU`
    let (ctor1, bc1, pc1) = add_fn(&mut m, cid, "ProfileCard", FunctionKind::Constructor, 3);
    let wv_mod1 = emit_val(
        &mut m,
        bc1,
        Op::LoadModuleVar {
            index: 1,
            kind: ModuleVarKind::External,
        },
    );
    let wv_ctor1 = load_prop(&mut m, bc1, wv_mod1, "WebviewController");
    let ctrl1 = emit_val(
        &mut m,
        bc1,
        Op::Call {
            callee: wv_ctor1,
            this: None,
            args: Vec::new(),
            kind: CallKind::New,
        },
    );
    store_prop(&mut m, bc1, pc1[2], "webCtrl", ctrl1);
    emit_void(&mut m, bc1, Op::Return { value: None });

    let (about1, bab1, pab1) = add_fn(&mut m, cid, "aboutToAppear", FunctionKind::Function, 3);
    let pr_mod = emit_val(
        &mut m,
        bab1,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let get_prefs = load_prop(&mut m, bab1, pr_mod, "getPreferencesSync");
    let prefs_inst = emit_val(
        &mut m,
        bab1,
        Op::Call {
            callee: get_prefs,
            this: Some(pr_mod),
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    let get_sync = load_prop(&mut m, bab1, prefs_inst, "getSync");
    let k_tok = load_str(&mut m, bab1, "auth_token");
    let tok_val = emit_val(
        &mut m,
        bab1,
        Op::Call {
            callee: get_sync,
            this: Some(prefs_inst),
            args: vec![k_tok],
            kind: CallKind::Direct,
        },
    );
    store_prop(&mut m, bab1, pab1[2], "token", tok_val);
    emit_void(&mut m, bab1, Op::Return { value: None });

    // `onClick` arrow closure inside `observeComponentCreation2` (reads `_this` via `GetLexVar(0, 0)`):
    let (click1, bclk1, _) = add_fn(&mut m, cid, "onClick_1", FunctionKind::Arrow, 3);
    let cap_this1 = emit_val(
        &mut m,
        bclk1,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let c1 = load_prop(&mut m, bclk1, cap_this1, "webCtrl");
    let load_url1 = load_prop(&mut m, bclk1, c1, "loadUrl");
    let t1 = load_prop(&mut m, bclk1, cap_this1, "token");
    let blank = load_str(&mut m, bclk1, "about:blank");
    let _ = emit_val_line(
        &mut m,
        bclk1,
        Op::Call {
            callee: load_url1,
            this: Some(c1),
            args: vec![t1],
            kind: CallKind::Direct,
        },
        501, // TP
    );
    let _ = emit_val_line(
        &mut m,
        bclk1,
        Op::Call {
            callee: load_url1,
            this: Some(c1),
            args: vec![blank],
            kind: CallKind::Direct,
        },
        502, // CLEAN
    );
    emit_void(&mut m, bclk1, Op::Return { value: None });

    let (obs_cb1, bobs1, _) = add_fn(&mut m, cid, "obs_1", FunctionKind::Arrow, 5);
    let btn1 = try_global(&mut m, bobs1, "Button");
    let on_click1 = load_prop(&mut m, bobs1, btn1, "onClick");
    let clk_clos1 = mk_closure(&mut m, bobs1, click1);
    let _ = emit_val(
        &mut m,
        bobs1,
        Op::Call {
            callee: on_click1,
            this: Some(btn1),
            args: vec![clk_clos1],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, bobs1, Op::Return { value: None });

    let (render1, brn1, prn1) = add_fn(&mut m, cid, "initialRender", FunctionKind::Function, 3);
    let _ = emit_val(
        &mut m,
        brn1,
        Op::NewLexEnv {
            num_vars: 1,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    emit_void(
        &mut m,
        brn1,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: prn1[2],
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let obs_fn1 = load_prop(&mut m, brn1, prn1[2], "observeComponentCreation2");
    let obs_clos1 = mk_closure(&mut m, brn1, obs_cb1);
    let btn_ref1 = try_global(&mut m, brn1, "Button");
    let _ = emit_val(
        &mut m,
        brn1,
        Op::Call {
            callee: obs_fn1,
            this: Some(prn1[2]),
            args: vec![obs_clos1, btn_ref1],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, brn1, Op::PopLexEnv);
    emit_void(&mut m, brn1, Op::Return { value: None });

    // Component 2: `StaticBanner extends ViewPU` (clean `this.token` — must NOT hit!)
    let (ctor2, bc2, pc2) = add_fn(&mut m, cid, "StaticBanner", FunctionKind::Constructor, 3);
    let wv_mod2 = emit_val(
        &mut m,
        bc2,
        Op::LoadModuleVar {
            index: 1,
            kind: ModuleVarKind::External,
        },
    );
    let wv_ctor2 = load_prop(&mut m, bc2, wv_mod2, "WebviewController");
    let ctrl2 = emit_val(
        &mut m,
        bc2,
        Op::Call {
            callee: wv_ctor2,
            this: None,
            args: Vec::new(),
            kind: CallKind::New,
        },
    );
    store_prop(&mut m, bc2, pc2[2], "webCtrl", ctrl2);
    emit_void(&mut m, bc2, Op::Return { value: None });

    let (about2, bab2, pab2) = add_fn(&mut m, cid, "aboutToAppear2", FunctionKind::Function, 3);
    let clean_tok = load_str(&mut m, bab2, "https://example.org/banner");
    store_prop(&mut m, bab2, pab2[2], "token", clean_tok);
    emit_void(&mut m, bab2, Op::Return { value: None });

    let (click2, bclk2, _) = add_fn(&mut m, cid, "onClick_2", FunctionKind::Arrow, 3);
    let cap_this2 = emit_val(
        &mut m,
        bclk2,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let c2 = load_prop(&mut m, bclk2, cap_this2, "webCtrl");
    let load_url2 = load_prop(&mut m, bclk2, c2, "loadUrl");
    let t2 = load_prop(&mut m, bclk2, cap_this2, "token");
    let _ = emit_val_line(
        &mut m,
        bclk2,
        Op::Call {
            callee: load_url2,
            this: Some(c2),
            args: vec![t2],
            kind: CallKind::Direct,
        },
        503, // CLEAN
    );
    emit_void(&mut m, bclk2, Op::Return { value: None });

    let (render2, brn2, prn2) = add_fn(&mut m, cid, "initialRender2", FunctionKind::Function, 3);
    let _ = emit_val(
        &mut m,
        brn2,
        Op::NewLexEnv {
            num_vars: 1,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    emit_void(
        &mut m,
        brn2,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: prn2[2],
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let btn2 = try_global(&mut m, brn2, "Button");
    let on_click2 = load_prop(&mut m, brn2, btn2, "onClick");
    let clk_clos2 = mk_closure(&mut m, brn2, click2);
    let _ = emit_val(
        &mut m,
        brn2,
        Op::Call {
            callee: on_click2,
            this: Some(btn2),
            args: vec![clk_clos2],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, brn2, Op::PopLexEnv);
    emit_void(&mut m, brn2, Op::Return { value: None });

    let (_, bmain, _) = add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
    let view_pu = try_global(&mut m, bmain, "ViewPU");
    let s_ata = m.sym.intern("aboutToAppear");
    let s_ir = m.sym.intern("initialRender");
    let c_s_ata = m.consts.intern(Const::String(s_ata));
    let c_s_ir = m.consts.intern(Const::String(s_ir));
    let c_m_about1 = m.consts.intern(Const::method_ref(about1));
    let c_m_render1 = m.consts.intern(Const::method_ref(render1));
    let mem1 = m
        .consts
        .push_array(vec![c_s_ata, c_m_about1, c_s_ir, c_m_render1]);
    let _ = emit_val(
        &mut m,
        bmain,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: ctor1,
            heritage: Some(view_pu),
            members: mem1,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    let c_m_about2 = m.consts.intern(Const::method_ref(about2));
    let c_m_render2 = m.consts.intern(Const::method_ref(render2));
    let mem2 = m
        .consts
        .push_array(vec![c_s_ata, c_m_about2, c_s_ir, c_m_render2]);
    let _ = emit_val(
        &mut m,
        bmain,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: ctor2,
            heritage: Some(view_pu),
            members: mem2,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    emit_void(&mut m, bmain, Op::Return { value: None });

    assert_ohos_probe(&m, "05-arkui-viewpu-lexenv-onclick", None, &[501]);
}
