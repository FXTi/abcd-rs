use super::*;

/// Probe 6 — OpenHarmony async patterns:
/// 1) `Promise.then`: `geoLocationManager.getCurrentLocation().then(loc => tcp.send(loc))` (601 TP, 602 clean);
/// 2) `async`/`await` (`AwaitUncaught` -> `SuspendGenerator` -> `ResumeGenerator`):
///    `const rdb = await relationalStore.getRdbStore(...); const rows = await rdb.querySql("SELECT ..."); rdb.executeSql(rows)`
///    (600 clean SQL query string does NOT self-trigger, 603 TP);
/// 3) `(err, data)` callback: `contact.selectContacts((err, list) => { hilog.error(err); hilog.info(list); })`
///    (604 `err` is CLEAN, 605 `list` is TP).
#[test]
fn probe_ohos_06_async_promise_then_await_and_err_data_callbacks() {
    let mut m = Module::new();
    let cid = add_record(&mut m, "L@bundle:com.demo/entry/ets/async_flow;");
    let s_loc = m.sym.intern("@ohos.geoLocationManager");
    let s_sock = m.sym.intern("@ohos.net.socket");
    let s_rdb = m.sym.intern("@ohos.data.relationalStore");
    let s_cnt = m.sym.intern("@ohos.contact");
    let s_hl = m.sym.intern("@ohos.hilog");
    let s_def = m.sym.intern("default");
    m.classes[cid.index()].es_module = Some(EsModule {
        imports: vec![
            ImportDecl::Regular {
                local_name: s_loc,
                import_name: s_def,
                module_request: s_loc,
            },
            ImportDecl::Regular {
                local_name: s_sock,
                import_name: s_def,
                module_request: s_sock,
            },
            ImportDecl::Regular {
                local_name: s_rdb,
                import_name: s_def,
                module_request: s_rdb,
            },
            ImportDecl::Regular {
                local_name: s_cnt,
                import_name: s_def,
                module_request: s_cnt,
            },
            ImportDecl::Regular {
                local_name: s_hl,
                import_name: s_def,
                module_request: s_hl,
            },
        ],
        exports: Vec::new(),
        module_requests: vec![
            ModuleRequest {
                specifier: s_loc,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_sock,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_rdb,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_cnt,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_hl,
                lazy: false,
            },
        ],
    });

    // 1. `then` callback `(loc) => { tcp.send(loc); tcp.send("ping"); }`.
    let (f_then, b_then, p_then) = add_fn(&mut m, cid, "onLoc", FunctionKind::Arrow, 4);
    let sock_mod = emit_val(
        &mut m,
        b_then,
        Op::LoadModuleVar {
            index: 1,
            kind: ModuleVarKind::External,
        },
    );
    let mk_tcp = load_prop(&mut m, b_then, sock_mod, "constructTCPSocketInstance");
    let tcp = emit_val(
        &mut m,
        b_then,
        Op::Call {
            callee: mk_tcp,
            this: Some(sock_mod),
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    let tcp_send = load_prop(&mut m, b_then, tcp, "send");
    let ping = load_str(&mut m, b_then, "ping");
    let _ = emit_val_line(
        &mut m,
        b_then,
        Op::Call {
            callee: tcp_send,
            this: Some(tcp),
            args: vec![p_then[3]],
            kind: CallKind::Direct,
        },
        601, // TP
    );
    let _ = emit_val_line(
        &mut m,
        b_then,
        Op::Call {
            callee: tcp_send,
            this: Some(tcp),
            args: vec![ping],
            kind: CallKind::Direct,
        },
        602, // CLEAN
    );
    emit_void(&mut m, b_then, Op::Return { value: None });

    // 2. `async` function using es2abc's exact `AsyncFunctionEnter` +
    //    `AwaitUncaught` -> `SuspendGenerator` -> `ResumeGenerator` pattern.
    let (f_async, b_async, _) = add_fn(&mut m, cid, "syncDb", FunctionKind::Async, 3);
    let fobj = emit_val(&mut m, b_async, Op::AsyncFunctionEnter);
    let rdb_mod = emit_val(
        &mut m,
        b_async,
        Op::LoadModuleVar {
            index: 2,
            kind: ModuleVarKind::External,
        },
    );
    let get_rdb = load_prop(&mut m, b_async, rdb_mod, "getRdbStore");
    let rdb_prom = emit_val(
        &mut m,
        b_async,
        Op::Call {
            callee: get_rdb,
            this: Some(rdb_mod),
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    let aw1 = emit_val(
        &mut m,
        b_async,
        Op::AwaitUncaught {
            funcobj: fobj,
            value: rdb_prom,
        },
    );
    let _ = emit_val(
        &mut m,
        b_async,
        Op::SuspendGenerator {
            genobj: fobj,
            value: aw1,
        },
    );
    let rdb_store = emit_val(&mut m, b_async, Op::ResumeGenerator { genobj: fobj });

    let query_sql = load_prop(&mut m, b_async, rdb_store, "querySql");
    let static_sql = load_str(&mut m, b_async, "SELECT token FROM accounts");
    let rows_prom = emit_val_line(
        &mut m,
        b_async,
        Op::Call {
            callee: query_sql,
            this: Some(rdb_store),
            args: vec![static_sql],
            kind: CallKind::Direct,
        },
        600, // CLEAN SQL query string (source call only, not SQLi!)
    );
    let aw2 = emit_val(
        &mut m,
        b_async,
        Op::AwaitUncaught {
            funcobj: fobj,
            value: rows_prom,
        },
    );
    let _ = emit_val(
        &mut m,
        b_async,
        Op::SuspendGenerator {
            genobj: fobj,
            value: aw2,
        },
    );
    let rows_val = emit_val(&mut m, b_async, Op::ResumeGenerator { genobj: fobj });

    let exec_sql = load_prop(&mut m, b_async, rdb_store, "executeSql");
    let _ = emit_val_line(
        &mut m,
        b_async,
        Op::Call {
            callee: exec_sql,
            this: Some(rdb_store),
            args: vec![rows_val],
            kind: CallKind::Direct,
        },
        603, // TP
    );
    emit_void(&mut m, b_async, Op::Return { value: None });

    // 3. `(err, contacts)` error-first callback: formal 0 (`err`) clean, formal 1 (`contacts`) tainted!
    let (f_cb, b_cb, p_cb) = add_fn(&mut m, cid, "onContacts", FunctionKind::Arrow, 5);
    let hl_mod = emit_val(
        &mut m,
        b_cb,
        Op::LoadModuleVar {
            index: 4,
            kind: ModuleVarKind::External,
        },
    );
    let hl_err = load_prop(&mut m, b_cb, hl_mod, "error");
    let hl_inf = load_prop(&mut m, b_cb, hl_mod, "info");
    let d0 = load_num(&mut m, b_cb, 0.0);
    let tg = load_str(&mut m, b_cb, "Cnt");
    let _ = emit_val_line(
        &mut m,
        b_cb,
        Op::Call {
            callee: hl_err,
            this: Some(hl_mod),
            args: vec![d0, tg, p_cb[3]], // `err` -> CLEAN
            kind: CallKind::Direct,
        },
        604,
    );
    let _ = emit_val_line(
        &mut m,
        b_cb,
        Op::Call {
            callee: hl_inf,
            this: Some(hl_mod),
            args: vec![d0, tg, p_cb[4]], // `contacts` -> TP
            kind: CallKind::Direct,
        },
        605,
    );
    emit_void(&mut m, b_cb, Op::Return { value: None });

    // `func_main_0` invokes all three async flows.
    let (_, bmain, _) = add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
    let loc_mod = emit_val(
        &mut m,
        bmain,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let get_loc = load_prop(&mut m, bmain, loc_mod, "getCurrentLocation");
    let loc_prom = emit_val(
        &mut m,
        bmain,
        Op::Call {
            callee: get_loc,
            this: Some(loc_mod),
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    let then_fn = load_prop(&mut m, bmain, loc_prom, "then");
    let then_clos = mk_closure(&mut m, bmain, f_then);
    let _ = emit_val(
        &mut m,
        bmain,
        Op::Call {
            callee: then_fn,
            this: Some(loc_prom),
            args: vec![then_clos],
            kind: CallKind::Direct,
        },
    );

    let async_clos = mk_closure(&mut m, bmain, f_async);
    let _ = emit_val(
        &mut m,
        bmain,
        Op::Call {
            callee: async_clos,
            this: None,
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );

    let cnt_mod = emit_val(
        &mut m,
        bmain,
        Op::LoadModuleVar {
            index: 3,
            kind: ModuleVarKind::External,
        },
    );
    let sel_cnt = load_prop(&mut m, bmain, cnt_mod, "selectContacts");
    let cnt_clos = mk_closure(&mut m, bmain, f_cb);
    let _ = emit_val(
        &mut m,
        bmain,
        Op::Call {
            callee: sel_cnt,
            this: Some(cnt_mod),
            args: vec![cnt_clos],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, bmain, Op::Return { value: None });

    assert_ohos_probe(
        &m,
        "06-async-promise-await-callback",
        None,
        &[601, 603, 605],
    );
}

/// Probe 7 — ArkWeb `WebviewController.registerJavaScriptProxy(bridge, "bridge", ["onWebCmd"])`:
/// whitelisted method `onWebCmd(cmd)` receives untrusted JS input (`701` TP),
/// while unexposed method `privateHelper(x)` is NOT seeded (`702` CLEAN).
#[test]
fn probe_ohos_07_webview_jsbridge_proxy_whitelist() {
    let mut m = Module::new();
    let cid = add_record(&mut m, "L@bundle:com.demo/entry/ets/bridge;");
    let s_wv = m.sym.intern("@ohos.web.webview");
    let s_def = m.sym.intern("default");
    m.classes[cid.index()].es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: s_wv,
            import_name: s_def,
            module_request: s_wv,
        }],
        exports: Vec::new(),
        module_requests: vec![ModuleRequest {
            specifier: s_wv,
            lazy: false,
        }],
    });

    let (f_exposed, b_exp, p_exp) = add_fn(&mut m, cid, "onWebCmd", FunctionKind::Function, 4);
    let wv_e = emit_val(
        &mut m,
        b_exp,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let wv_ctor_e = load_prop(&mut m, b_exp, wv_e, "WebviewController");
    let ctrl_e = emit_val(
        &mut m,
        b_exp,
        Op::Call {
            callee: wv_ctor_e,
            this: None,
            args: Vec::new(),
            kind: CallKind::New,
        },
    );
    let run_js_e = load_prop(&mut m, b_exp, ctrl_e, "runJavaScript");
    let _ = emit_val_line(
        &mut m,
        b_exp,
        Op::Call {
            callee: run_js_e,
            this: Some(ctrl_e),
            args: vec![p_exp[3]],
            kind: CallKind::Direct,
        },
        701, // TP
    );
    emit_void(&mut m, b_exp, Op::Return { value: None });

    let (f_priv, b_prv, p_prv) = add_fn(&mut m, cid, "privateHelper", FunctionKind::Function, 4);
    let wv_p = emit_val(
        &mut m,
        b_prv,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let wv_ctor_p = load_prop(&mut m, b_prv, wv_p, "WebviewController");
    let ctrl_p = emit_val(
        &mut m,
        b_prv,
        Op::Call {
            callee: wv_ctor_p,
            this: None,
            args: Vec::new(),
            kind: CallKind::New,
        },
    );
    let run_js_p = load_prop(&mut m, b_prv, ctrl_p, "runJavaScript");
    let _ = emit_val_line(
        &mut m,
        b_prv,
        Op::Call {
            callee: run_js_p,
            this: Some(ctrl_p),
            args: vec![p_prv[3]],
            kind: CallKind::Direct,
        },
        702, // CLEAN (not in method whitelist!)
    );
    emit_void(&mut m, b_prv, Op::Return { value: None });

    let (_, bmain, _) = add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
    let wv_mod = emit_val(
        &mut m,
        bmain,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let wv_ctor = load_prop(&mut m, bmain, wv_mod, "WebviewController");
    let ctrl = emit_val(
        &mut m,
        bmain,
        Op::Call {
            callee: wv_ctor,
            this: None,
            args: Vec::new(),
            kind: CallKind::New,
        },
    );
    let bridge = alloc_obj(&mut m, bmain);
    let c_exp = mk_closure(&mut m, bmain, f_exposed);
    let c_prv = mk_closure(&mut m, bmain, f_priv);
    store_prop(&mut m, bmain, bridge, "onWebCmd", c_exp);
    store_prop(&mut m, bmain, bridge, "privateHelper", c_prv);

    let s_on_web = m.sym.intern("onWebCmd");
    let c_s_on_web = m.consts.intern(Const::String(s_on_web));
    let list_shape = m.consts.push_array(vec![c_s_on_web]);
    let method_list = emit_val(
        &mut m,
        bmain,
        Op::AllocArray {
            shape: Some(list_shape),
        },
    );
    let proxy_name = load_str(&mut m, bmain, "nativeBridge");
    let reg_proxy = load_prop(&mut m, bmain, ctrl, "registerJavaScriptProxy");
    let _ = emit_val(
        &mut m,
        bmain,
        Op::Call {
            callee: reg_proxy,
            this: Some(ctrl),
            args: vec![bridge, proxy_name, method_list],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, bmain, Op::Return { value: None });

    assert_ohos_probe(&m, "07-webview-jsbridge-whitelist", None, &[701]);
}

/// Probe 8 — End-to-end `abcd_file::Builder` -> `decode` -> `lift_file` ->
/// `merge_ir_modules` -> `ohos_preset()` taint across two separate `.abc`
/// containers (`shared_hsp.abc` exporting `@ohos.identifier.oaid.getOAID()`
/// + `entry_hap.abc` importing `../shared_hsp` and sinking into `@ohos.hilog.info`).
#[test]
fn probe_ohos_08_real_bytecode_multi_abc_cross_container_taint() {
    let placeholder = EntityId(u16::MAX as u32);

    // 1. Build `shared_hsp.abc` (`L_GLOBAL;` standalone module exporting `oaidVal`).
    let hsp_bytes = {
        let mut b = Builder::new();
        b.set_api(12, "");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let es_rec = b.add_class("L_ESModuleRecord;");
        let es_field = b.class_add_field(es_rec, "SharedHsp", Type::U32, AccessFlags::PUBLIC);
        let req_oaid = b.add_string("@ohos.identifier.oaid");
        let s_get_oaid = b.add_string("getOAID");
        let s_oaid_val = b.add_string("oaidVal");
        let mod_la = b.add_literal_array("hsp_mod");
        b.literal_array_add_module_data(
            mod_la,
            &[req_oaid],
            &[
                ModuleRecordDef::RegularImport {
                    local_name: s_get_oaid,
                    import_name: s_get_oaid,
                    module_request_idx: 0,
                },
                ModuleRecordDef::LocalExport {
                    local_name: s_oaid_val,
                    export_name: s_oaid_val,
                },
            ],
        )
        .unwrap();
        b.field_set_value_literalarray(es_field, mod_la).unwrap();

        let proto = b.create_proto(Type::Void, &[]);
        let (code, _) = abcd_isa::encode(&[
            Bytecode::Ldexternalmodulevar(Imm(0)), // acc = getOAID
            Bytecode::Callarg0(Imm(0)),            // acc = getOAID()
            Bytecode::Stmodulevar(Imm(0)),         // slot 0 = oaidVal
            Bytecode::Returnundefined,
        ])
        .unwrap();
        b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 2, 3);
        b.deduplicate();
        b.finalize().expect("hsp finalize")
    };

    // 2. Build `entry_hap.abc` (`L_GLOBAL;` standalone module importing `oaidVal` from `../shared/hsp`).
    let hap_bytes = {
        let mut b = Builder::new();
        b.set_api(12, "");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let es_rec = b.add_class("L_ESModuleRecord;");
        let es_field = b.class_add_field(es_rec, "EntryHap", Type::U32, AccessFlags::PUBLIC);
        let req_hsp = b.add_string("../shared/hsp");
        let req_hl = b.add_string("@ohos.hilog");
        let s_oaid_val = b.add_string("oaidVal");
        let s_hilog = b.add_string("hilog");
        let s_default = b.add_string("default");
        let mod_la = b.add_literal_array("hap_mod");
        b.literal_array_add_module_data(
            mod_la,
            &[req_hsp, req_hl],
            &[
                ModuleRecordDef::RegularImport {
                    local_name: s_oaid_val,
                    import_name: s_oaid_val,
                    module_request_idx: 0,
                },
                ModuleRecordDef::RegularImport {
                    local_name: s_hilog,
                    import_name: s_default,
                    module_request_idx: 1,
                },
            ],
        )
        .unwrap();
        b.field_set_value_literalarray(es_field, mod_la).unwrap();

        let proto = b.create_proto(Type::Void, &[]);
        let (code, offsets) = abcd_isa::encode(&[
            Bytecode::Ldexternalmodulevar(Imm(0)),      // 0: acc = oaidVal
            Bytecode::Sta(Reg(0)),                      // 1: v0 = oaidVal
            Bytecode::Ldexternalmodulevar(Imm(1)),      // 2: acc = hilog
            Bytecode::Sta(Reg(1)),                      // 3: v1 = hilog
            Bytecode::Ldobjbyname(Imm(0), placeholder), // 4: acc = hilog.info
            Bytecode::Sta(Reg(2)),                      // 5: v2 = hilog.info
            Bytecode::Ldai(Imm(0)),                     // 6: domain = 0
            Bytecode::Sta(Reg(3)),                      // 7: v3 = 0
            Bytecode::LdaStr(placeholder),              // 8: tag = "T"
            Bytecode::Sta(Reg(4)),                      // 9: v4 = "T"
            Bytecode::Lda(Reg(2)),                      // 10: acc = hilog.info
            Bytecode::Callthis3(Imm(2), Reg(1), Reg(3), Reg(4), Reg(0)), // 11: hilog.info(0, "T", oaidVal)
            Bytecode::Returnundefined,                                   // 12
        ])
        .unwrap();
        let m_handle =
            b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 6, 3);
        let s_info = b.add_string("info");
        b.relocate_code_id(m_handle, offsets[4], 0, CodeEntity::String(s_info))
            .unwrap();
        let s_tag = b.add_string("T");
        b.relocate_code_id(m_handle, offsets[8], 0, CodeEntity::String(s_tag))
            .unwrap();
        b.deduplicate();
        b.finalize().expect("hap finalize")
    };

    let hsp_ir = abcd_lift::lift_file(&abcd_file::decode(&hsp_bytes).unwrap()).unwrap();
    let hap_ir = abcd_lift::lift_file(&abcd_file::decode(&hap_bytes).unwrap()).unwrap();
    let merged = merge_ir_modules(&[("shared/hsp", &hsp_ir), ("entry/index", &hap_ir)]);

    assert!(verify_module(&merged).errors.is_empty());
    let rep = run_taint(&merged, &ohos_preset());
    assert_eq!(rep.hits.len(), 1, "expected 1 cross-.abc hit: {rep:?}");
    assert_eq!(rep.hits[0].sink, "@ohos.hilog.info");
    assert_eq!(rep.hits[0].position, "arg 2");
}

/// Probe 9 — Multi-class OOP inheritance (`OAuthRepo extends BaseRepo`), static
/// singleton (`OAuthRepo.getInstance()`), constructor field-type dispatch
/// (`this.repo = OAuthRepo.getInstance()` -> `this.repo.forward(oaid)`), caller
/// `Local` survival across resolved `BodyStep` helper (`this.noop(tok)`), and
/// commercial 5-segment `@normalized:` cross-HAR import (`#34`).
#[test]
fn probe_ohos_09_oop_inheritance_singleton_field_dispatch_and_normalized_har() {
    use abcd_analysis::callgraph::CallGraph;
    use abcd_analysis::dataflow::ifds::CallGraphOracle;

    let mut m = Module::new();
    let c_har = add_record(
        &mut m,
        "L@normalized:N&har_net&com.demo.app/har_net/src/main/ets/NetRepo&1.0.0;",
    );
    let c_app = add_record(&mut m, "L@bundle:com.demo.app/entry/ets/AuthController;");

    let s_http_mod = m.sym.intern("@ohos.net.http");
    let s_oaid_mod = m.sym.intern("@ohos.identifier.oaid");
    let s_hilog_mod = m.sym.intern("@ohos.hilog");
    let s_default = m.sym.intern("default");
    let s_http = m.sym.intern("http");
    let s_get_oaid = m.sym.intern("getOAID");
    let s_hilog = m.sym.intern("hilog");
    let s_oauth_repo = m.sym.intern("OAuthRepo");
    let s_har_spec = m
        .sym
        .intern("@normalized:N&har_net&com.demo.app/har_net/src/main/ets/NetRepo&1.0.0");

    m.classes[c_har.index()].es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: s_http,
            import_name: s_default,
            module_request: s_http_mod,
        }],
        exports: vec![ExportDecl::Local {
            local_name: s_oauth_repo,
            export_name: s_oauth_repo,
        }],
        module_requests: vec![ModuleRequest {
            specifier: s_http_mod,
            lazy: false,
        }],
    });

    m.classes[c_app.index()].es_module = Some(EsModule {
        imports: vec![
            ImportDecl::Regular {
                local_name: s_oauth_repo,
                import_name: s_oauth_repo,
                module_request: s_har_spec,
            },
            ImportDecl::Regular {
                local_name: s_get_oaid,
                import_name: s_get_oaid,
                module_request: s_oaid_mod,
            },
            ImportDecl::Regular {
                local_name: s_hilog,
                import_name: s_default,
                module_request: s_hilog_mod,
            },
        ],
        exports: Vec::new(),
        module_requests: vec![
            ModuleRequest {
                specifier: s_har_spec,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_oaid_mod,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_hilog_mod,
                lazy: false,
            },
        ],
    });

    // BaseRepo: `noop(x)` + `send(payload)` -> `http.createHttp().request(payload)` (line 901 TP).
    let (base_ctor, b_bc, _) = add_fn(&mut m, c_har, "BaseRepo", FunctionKind::Constructor, 3);
    emit_void(&mut m, b_bc, Op::Return { value: None });

    let (base_noop, b_noop, _) = add_fn(&mut m, c_har, "noop", FunctionKind::Function, 4);
    emit_void(&mut m, b_noop, Op::Return { value: None });

    let (base_send, b_send, p_send) = add_fn(&mut m, c_har, "send", FunctionKind::Function, 4);
    let http_ext = emit_val(
        &mut m,
        b_send,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let create_http = load_prop(&mut m, b_send, http_ext, "createHttp");
    let client = emit_val(
        &mut m,
        b_send,
        Op::Call {
            callee: create_http,
            this: Some(http_ext),
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    let req_fn = load_prop(&mut m, b_send, client, "request");
    let _ = emit_val_line(
        &mut m,
        b_send,
        Op::Call {
            callee: req_fn,
            this: Some(client),
            args: vec![p_send[3]],
            kind: CallKind::Direct,
        },
        901,
    );
    emit_void(&mut m, b_send, Op::Return { value: None });

    // OAuthRepo extends BaseRepo: `forward(tok)` calls `this.noop(tok)` then inherited `this.send(tok)`.
    let (oauth_ctor, b_oc, _) = add_fn(&mut m, c_har, "OAuthRepo", FunctionKind::Constructor, 3);
    emit_void(&mut m, b_oc, Op::Return { value: None });

    let (oauth_fwd, b_fwd, p_fwd) = add_fn(&mut m, c_har, "forward", FunctionKind::Function, 4);
    let noop_m = load_prop(&mut m, b_fwd, p_fwd[2], "noop");
    let call_noop_val = emit_val(
        &mut m,
        b_fwd,
        Op::Call {
            callee: noop_m,
            this: Some(p_fwd[2]),
            args: vec![p_fwd[3]],
            kind: CallKind::Direct,
        },
    );
    let _ = call_noop_val;
    let send_m = load_prop(&mut m, b_fwd, p_fwd[2], "send");
    let send_call_vid = emit_val(
        &mut m,
        b_fwd,
        Op::Call {
            callee: send_m,
            this: Some(p_fwd[2]),
            args: vec![p_fwd[3]],
            kind: CallKind::Direct,
        },
    );
    let ValueDef::Inst(send_call_iid) = m.value(send_call_vid).unwrap().def else {
        panic!("expected inst");
    };
    emit_void(&mut m, b_fwd, Op::Return { value: None });

    // Static `OAuthRepo.getInstance()`: loads exported module slot 0 (`OAuthRepo`) and returns `new OAuthRepo()`.
    let (get_inst_fn, b_gi, _) = add_fn(&mut m, c_har, "getInstance", FunctionKind::Function, 3);
    let self_cls = emit_val(
        &mut m,
        b_gi,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::Local,
        },
    );
    let inst_repo = emit_val(
        &mut m,
        b_gi,
        Op::Call {
            callee: self_cls,
            this: None,
            args: Vec::new(),
            kind: CallKind::New,
        },
    );
    emit_void(
        &mut m,
        b_gi,
        Op::Return {
            value: Some(inst_repo),
        },
    );

    // HAR `func_main_0`: defines `BaseRepo`, `OAuthRepo extends BaseRepo`, attaches `getInstance`, exports slot 0.
    let (_, b_har_main, _) = add_fn(&mut m, c_har, "func_main_0", FunctionKind::Function, 3);
    let s_noop = m.sym.intern("noop");
    let s_send = m.sym.intern("send");
    let s_forward = m.sym.intern("forward");
    let c_s_noop = m.consts.intern(Const::String(s_noop));
    let c_m_noop = m.consts.intern(Const::method_ref(base_noop));
    let c_s_send = m.consts.intern(Const::String(s_send));
    let c_m_send = m.consts.intern(Const::method_ref(base_send));
    let c_n2 = m.consts.intern(Const::number(2.0));
    let base_mem = m
        .consts
        .push_array(vec![c_s_noop, c_m_noop, c_s_send, c_m_send, c_n2]);
    let base_cls_val = emit_val(
        &mut m,
        b_har_main,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: base_ctor,
            heritage: None,
            members: base_mem,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    let c_s_fwd = m.consts.intern(Const::String(s_forward));
    let c_m_fwd = m.consts.intern(Const::method_ref(oauth_fwd));
    let c_n1 = m.consts.intern(Const::number(1.0));
    let oauth_mem = m.consts.push_array(vec![c_s_fwd, c_m_fwd, c_n1]);
    let oauth_cls_val = emit_val(
        &mut m,
        b_har_main,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: oauth_ctor,
            heritage: Some(base_cls_val),
            members: oauth_mem,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    let gi_clo = mk_closure(&mut m, b_har_main, get_inst_fn);
    store_prop(&mut m, b_har_main, oauth_cls_val, "getInstance", gi_clo);
    emit_void(
        &mut m,
        b_har_main,
        Op::StoreModuleVar {
            index: 0,
            value: oauth_cls_val,
        },
    );
    emit_void(&mut m, b_har_main, Op::Return { value: None });

    // App record: `AuthService` stores `this.repo = OAuthRepo.getInstance()` in constructor
    // and dispatches `this.repo.forward(getOAID())` in `syncTainted()`.
    let (svc_ctor, b_sc, p_sc) = add_fn(&mut m, c_app, "AuthService", FunctionKind::Constructor, 3);
    let imp_repo = emit_val(
        &mut m,
        b_sc,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let gi_prop = load_prop(&mut m, b_sc, imp_repo, "getInstance");
    let repo_inst = emit_val(
        &mut m,
        b_sc,
        Op::Call {
            callee: gi_prop,
            this: Some(imp_repo),
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    store_prop(&mut m, b_sc, p_sc[2], "repo", repo_inst);
    emit_void(&mut m, b_sc, Op::Return { value: None });

    let (svc_sync, b_sy, p_sy) = add_fn(&mut m, c_app, "syncTainted", FunctionKind::Function, 3);
    let oaid_fn = emit_val(
        &mut m,
        b_sy,
        Op::LoadModuleVar {
            index: 1,
            kind: ModuleVarKind::External,
        },
    );
    let oaid_tok = emit_val(
        &mut m,
        b_sy,
        Op::Call {
            callee: oaid_fn,
            this: None,
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );
    let this_repo = load_prop(&mut m, b_sy, p_sy[2], "repo");
    let fwd_prop = load_prop(&mut m, b_sy, this_repo, "forward");
    let fwd_call_vid = emit_val(
        &mut m,
        b_sy,
        Op::Call {
            callee: fwd_prop,
            this: Some(this_repo),
            args: vec![oaid_tok],
            kind: CallKind::Direct,
        },
    );
    let ValueDef::Inst(fwd_call_iid) = m.value(fwd_call_vid).unwrap().def else {
        panic!("expected inst");
    };
    let hl_mod = emit_val(
        &mut m,
        b_sy,
        Op::LoadModuleVar {
            index: 2,
            kind: ModuleVarKind::External,
        },
    );
    let hl_info = load_prop(&mut m, b_sy, hl_mod, "info");
    let dom = load_num(&mut m, b_sy, 0.0);
    let tag = load_str(&mut m, b_sy, "Auth");
    let clean_msg = load_str(&mut m, b_sy, "ok");
    let _ = emit_val_line(
        &mut m,
        b_sy,
        Op::Call {
            callee: hl_info,
            this: Some(hl_mod),
            args: vec![dom, tag, clean_msg],
            kind: CallKind::Direct,
        },
        902, // CLEAN
    );
    emit_void(&mut m, b_sy, Op::Return { value: None });

    let (_, b_app_main, _) = add_fn(&mut m, c_app, "func_main_0", FunctionKind::Function, 3);
    let s_sync = m.sym.intern("syncTainted");
    let c_s_sync = m.consts.intern(Const::String(s_sync));
    let c_m_sync = m.consts.intern(Const::method_ref(svc_sync));
    let c_svc_n1 = m.consts.intern(Const::number(1.0));
    let svc_mem = m.consts.push_array(vec![c_s_sync, c_m_sync, c_svc_n1]);
    let svc_cls = emit_val(
        &mut m,
        b_app_main,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: svc_ctor,
            heritage: None,
            members: svc_mem,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    let svc_obj = emit_val(
        &mut m,
        b_app_main,
        Op::Call {
            callee: svc_cls,
            this: None,
            args: Vec::new(),
            kind: CallKind::New,
        },
    );
    let sync_fn = load_prop(&mut m, b_app_main, svc_obj, "syncTainted");
    let _ = emit_val(
        &mut m,
        b_app_main,
        Op::Call {
            callee: sync_fn,
            this: Some(svc_obj),
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, b_app_main, Op::Return { value: None });

    // Verify Rung 0.5 (`ClassHierarchyIndex`) resolves both `this.repo.forward(...)` across
    // `@normalized:` HAR and inherited `this.send(...)` before any PTA runs.
    let cg = CallGraph::build(&m);
    assert_eq!(cg.callees_of_call_at(fwd_call_iid), &[oauth_fwd]);
    assert_eq!(cg.callees_of_call_at(send_call_iid), &[base_send]);

    // Verify exact taint precision at both Rung 2 (default) and Rung 0!
    assert_ohos_probe(
        &m,
        "09-oop-inheritance-singleton-normalized-har",
        None,
        &[901],
    );
    let mut cfg_r0 = ohos_preset();
    cfg_r0.alias_rung = 0;
    let rep_r0 = run_taint(&m, &cfg_r0);
    let lines_r0: Vec<u32> = rep_r0
        .hits
        .iter()
        .filter_map(|h| h.loc.map(|l| l.line))
        .collect();
    assert_eq!(lines_r0, vec![901]);
}

/// Probe 10 — Demand-driven PTA root slicing & smart IFDS `Λ`-seeding on a
/// `650`-function (`> 512` threshold) multi-record bundle (`#34`): preserves
/// `k=1` `New`-site context sensitivity (`tp = 1, fp = 0`) while skipping
/// `640+` unrelated library/UI functions.
#[test]
fn probe_ohos_10_large_bundle_demand_driven_pta_and_ifds_scalability() {
    let mut m = Module::new();

    // 80 unrelated records x 8 functions = 640 unrelated functions with allocations & method calls.
    let s_item = m.sym.intern("item");
    let s_work = m.sym.intern("work");
    for r in 0..80 {
        let cid = add_record(
            &mut m,
            &format!("L@bundle:com.demo.app/entry/ets/lib/Mod{r};"),
        );
        let (ctor, bc, pc) = add_fn(&mut m, cid, "Widget", FunctionKind::Constructor, 3);
        let obj = alloc_obj(&mut m, bc);
        emit_void(
            &mut m,
            bc,
            Op::StoreProp {
                object: pc[2],
                name: s_item,
                value: obj,
            },
        );
        emit_void(&mut m, bc, Op::Return { value: None });

        let (wk, bw, pw) = add_fn(&mut m, cid, "work", FunctionKind::Function, 3);
        let _ = emit_val(
            &mut m,
            bw,
            Op::LoadProp {
                object: pw[2],
                name: s_item,
            },
        );
        emit_void(&mut m, bw, Op::Return { value: None });

        for h in 0..5 {
            let (_, bh, _) = add_fn(&mut m, cid, &format!("util_{h}"), FunctionKind::Function, 3);
            let _ = alloc_obj(&mut m, bh);
            emit_void(&mut m, bh, Op::Return { value: None });
        }

        let (_, bm, _) = add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
        let c_s_work = m.consts.intern(Const::String(s_work));
        let c_m_wk = m.consts.intern(Const::method_ref(wk));
        let c_wk_n1 = m.consts.intern(Const::number(1.0));
        let mem = m.consts.push_array(vec![c_s_work, c_m_wk, c_wk_n1]);
        let cls_v = emit_val(
            &mut m,
            bm,
            Op::DefineClass(Box::new(DefineClassData {
                ctor,
                heritage: None,
                members: mem,
                member_attrs: Vec::new(),
                count: 0,
            })),
        );
        let inst_v = emit_val(
            &mut m,
            bm,
            Op::Call {
                callee: cls_v,
                this: None,
                args: Vec::new(),
                kind: CallKind::New,
            },
        );
        let wk_fn = load_prop(&mut m, bm, inst_v, "work");
        let _ = emit_val(
            &mut m,
            bm,
            Op::Call {
                callee: wk_fn,
                this: Some(inst_v),
                args: Vec::new(),
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, bm, Op::Return { value: None });
    }

    // Bare-`&` commercial record exporting `secretTok` from `@ohos.identifier.oaid.getOAID()`.
    let c_src = add_record(&mut m, "L&shared_har/src/main/ets/DeviceStore&1.0.0;");
    let c_snk = add_record(&mut m, "L@bundle:com.demo.app/entry/ets/SinkPage;");
    let s_oaid_mod = m.sym.intern("@ohos.identifier.oaid");
    let s_get_oaid = m.sym.intern("getOAID");
    let s_secret = m.sym.intern("secretTok");
    let s_norm_src = m
        .sym
        .intern("@normalized:N&shared_har&com.demo.app/shared_har/src/main/ets/DeviceStore&1.0.0");
    let s_hilog_mod = m.sym.intern("@ohos.hilog");
    let s_default = m.sym.intern("default");
    let s_hilog = m.sym.intern("hilog");

    m.classes[c_src.index()].es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: s_get_oaid,
            import_name: s_get_oaid,
            module_request: s_oaid_mod,
        }],
        exports: vec![ExportDecl::Local {
            local_name: s_secret,
            export_name: s_secret,
        }],
        module_requests: vec![ModuleRequest {
            specifier: s_oaid_mod,
            lazy: false,
        }],
    });
    m.classes[c_snk.index()].es_module = Some(EsModule {
        imports: vec![
            ImportDecl::Regular {
                local_name: s_secret,
                import_name: s_secret,
                module_request: s_norm_src,
            },
            ImportDecl::Regular {
                local_name: s_hilog,
                import_name: s_default,
                module_request: s_hilog_mod,
            },
        ],
        exports: Vec::new(),
        module_requests: vec![
            ModuleRequest {
                specifier: s_norm_src,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_hilog_mod,
                lazy: false,
            },
        ],
    });

    let (_, b_src, _) = add_fn(&mut m, c_src, "func_main_0", FunctionKind::Function, 3);
    let oaid_fn = emit_val(
        &mut m,
        b_src,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let oaid_v = emit_val(
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
            value: oaid_v,
        },
    );
    emit_void(&mut m, b_src, Op::Return { value: None });

    // `VaultBox(v)` stores `this.payload = v`: tests Rung-2 `New`-site separation under root slicing!
    let (vbox_ctor, b_vb, p_vb) = add_fn(&mut m, c_snk, "VaultBox", FunctionKind::Constructor, 4);
    store_prop(&mut m, b_vb, p_vb[2], "payload", p_vb[3]);
    emit_void(&mut m, b_vb, Op::Return { value: None });

    let (_, b_snk, _) = add_fn(&mut m, c_snk, "func_main_0", FunctionKind::Function, 3);
    let c_vb_n0 = m.consts.intern(Const::number(0.0));
    let vb_mem = m.consts.push_array(vec![c_vb_n0]);
    let vb_cls = emit_val(
        &mut m,
        b_snk,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: vbox_ctor,
            heritage: None,
            members: vb_mem,
            member_attrs: Vec::new(),
            count: 1,
        })),
    );
    let imp_tok = emit_val(
        &mut m,
        b_snk,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let pub_tok = load_str(&mut m, b_snk, "public");
    let tainted_box = emit_val(
        &mut m,
        b_snk,
        Op::Call {
            callee: vb_cls,
            this: None,
            args: vec![imp_tok],
            kind: CallKind::New,
        },
    );
    let clean_box = emit_val(
        &mut m,
        b_snk,
        Op::Call {
            callee: vb_cls,
            this: None,
            args: vec![pub_tok],
            kind: CallKind::New,
        },
    );
    let tainted_pay = load_prop(&mut m, b_snk, tainted_box, "payload");
    let clean_pay = load_prop(&mut m, b_snk, clean_box, "payload");
    let hl_mod = emit_val(
        &mut m,
        b_snk,
        Op::LoadModuleVar {
            index: 1,
            kind: ModuleVarKind::External,
        },
    );
    let hl_info = load_prop(&mut m, b_snk, hl_mod, "info");
    let dom = load_num(&mut m, b_snk, 0.0);
    let tag = load_str(&mut m, b_snk, "Vault");
    let _ = emit_val_line(
        &mut m,
        b_snk,
        Op::Call {
            callee: hl_info,
            this: Some(hl_mod),
            args: vec![dom, tag, tainted_pay],
            kind: CallKind::Direct,
        },
        1001, // TP
    );
    let _ = emit_val_line(
        &mut m,
        b_snk,
        Op::Call {
            callee: hl_info,
            this: Some(hl_mod),
            args: vec![dom, tag, clean_pay],
            kind: CallKind::Direct,
        },
        1002, // CLEAN (must stay distinct under root-sliced Rung-2 PTA!)
    );
    emit_void(&mut m, b_snk, Op::Return { value: None });

    assert!(m.functions.len() > 640);
    assert!(verify_module(&m).errors.is_empty());
    let rep = run_taint(&m, &ohos_preset());
    assert_eq!(rep.alias_rung_used, 2, "must not hit PTA budget cap");
    let lines: Vec<u32> = rep
        .hits
        .iter()
        .filter_map(|h| h.loc.map(|l| l.line))
        .collect();
    assert_eq!(lines, vec![1001], "report={rep:?}");
    assert!(
        rep.path_edges < 600,
        "smart zero_needed seeding should skip 640 unrelated functions, got {} path_edges",
        rep.path_edges
    );
}
