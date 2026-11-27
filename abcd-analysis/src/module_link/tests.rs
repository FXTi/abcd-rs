//! Unit tests for cross-record ES module linking and IR module merging.

use super::*;
use crate::callgraph::CallGraph;
use crate::dataflow::Rung1AliasOracle;
use crate::dataflow::ifds::CallGraphOracle;
use crate::dataflow::pta::{PtaConfig, Rung2AliasOracle, analyze};
use abcd_ir::ValueDef;
use abcd_ir::function::{Block, Catch, FunctionData, Inst, TryRegion, Value};
use abcd_ir::module::{FieldData, FunctionKind, Modifiers, ModuleRequest};
use abcd_ir::op::{CallKind, ModuleVarKind};
use abcd_ir::ty::{StaticTy, Ty};
use abcd_ir::verify::verify_module;

fn push_fn_with_params(
    m: &mut Module,
    cid: ClassId,
    name: &str,
    kind: FunctionKind,
    total_params: u16,
) -> (FuncId, BlockId, Vec<ValueId>) {
    let nsym = m.sym.intern(name);
    let fid = FuncId::new(m.functions.len() as u32);
    let mut fd = FunctionData::new(cid, nsym, kind);
    fd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    let bid = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    fd.blocks.push(bid);
    let mut params = Vec::new();
    for i in 0..total_params {
        let vid = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Param(i),
            ty: Ty::Any,
        });
        fd.params.push(vid);
        params.push(vid);
    }
    m.functions.push(fd);
    m.classes[cid.index()].methods.push(fid);
    (fid, bid, params)
}

fn emit_val(m: &mut Module, b: BlockId, op: Op) -> (InstId, ValueId) {
    let iid = InstId::new(m.insts.len() as u32);
    let vid = ValueId::new(m.values.len() as u32);
    m.insts.push(Inst {
        op,
        result: Some(vid),
        block: b,
        loc: None,
    });
    m.values.push(Value {
        def: ValueDef::Inst(iid),
        ty: Ty::Any,
    });
    m.blocks[b.index()].insts.push(iid);
    (iid, vid)
}

fn emit_void(m: &mut Module, b: BlockId, op: Op) -> InstId {
    let iid = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op,
        result: None,
        block: b,
        loc: None,
    });
    m.blocks[b.index()].insts.push(iid);
    iid
}

#[test]
fn direct_indirect_star_json_and_cycle_guard() {
    let mut m = Module::new();

    // Record 0: leaf (`L@bundle:com.app/entry/ets/leaf;`)
    let d_leaf = m.sym.intern("L@bundle:com.app/entry/ets/leaf;");
    let n_leaf = m.sym.intern("@bundle:com.app/entry/ets/leaf");
    let c_leaf = ClassId::new(0);
    m.classes.push(ClassData::new(d_leaf, n_leaf));

    // Record 1: cycle (`L@bundle:com.app/entry/ets/cycle;`)
    let d_cycle = m.sym.intern("L@bundle:com.app/entry/ets/cycle;");
    let n_cycle = m.sym.intern("@bundle:com.app/entry/ets/cycle");
    let c_cycle = ClassId::new(1);
    m.classes.push(ClassData::new(d_cycle, n_cycle));

    // Record 2: barrel (`L@bundle:com.app/entry/ets/barrel;`)
    let d_barrel = m.sym.intern("L@bundle:com.app/entry/ets/barrel;");
    let n_barrel = m.sym.intern("@bundle:com.app/entry/ets/barrel");
    let c_barrel = ClassId::new(2);
    m.classes.push(ClassData::new(d_barrel, n_barrel));

    // Record 3: json (`L@bundle:com.app/entry/ets/assets/cfg;`)
    let d_json = m.sym.intern("L@bundle:com.app/entry/ets/assets/cfg;");
    let n_json = m.sym.intern("@bundle:com.app/entry/ets/assets/cfg");
    let mut json_cls = ClassData::new(d_json, n_json);
    let jpayload_sym = m.sym.intern(r#"{"api":"https://example.test"}"#);
    let jconst = m.consts.push(Const::String(jpayload_sym));
    let jfield_name = m.sym.intern("jsonFileContent");
    json_cls.fields.push(FieldData {
        name: jfield_name,
        ty: Ty::Any,
        modifiers: Modifiers::PUBLIC.union(Modifiers::STATIC),
        initial_value: Some(jconst),
        annotations: Vec::new(),
    });
    m.classes.push(json_cls);

    // Record 4: main (`L@bundle:com.app/entry/ets/main;`)
    let d_main = m.sym.intern("L@bundle:com.app/entry/ets/main;");
    let n_main = m.sym.intern("@bundle:com.app/entry/ets/main");
    let c_main = ClassId::new(4);
    m.classes.push(ClassData::new(d_main, n_main));

    // Populate ESM metadata:
    let s_secret = m.sym.intern("secret");
    let s_def_local = m.sym.intern("def_local");
    let s_default = m.sym.intern("default");
    m.classes[c_leaf.index()].es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![
            ExportDecl::Local {
                local_name: s_secret,
                export_name: s_secret,
            },
            ExportDecl::Local {
                local_name: s_def_local,
                export_name: s_default,
            },
        ],
        module_requests: Vec::new(),
    });

    let s_extra = m.sym.intern("extra");
    let s_rel_barrel = m.sym.intern("./barrel");
    m.classes[c_cycle.index()].es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![
            ExportDecl::Local {
                local_name: s_extra,
                export_name: s_extra,
            },
            ExportDecl::Star {
                module_request: s_rel_barrel,
            },
        ],
        module_requests: vec![ModuleRequest {
            specifier: s_rel_barrel,
            lazy: false,
        }],
    });

    let s_renamed = m.sym.intern("renamed");
    let s_rel_leaf = m.sym.intern("./leaf");
    let s_rel_cycle = m.sym.intern("./cycle");
    m.classes[c_barrel.index()].es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![
            ExportDecl::Indirect {
                export_name: s_renamed,
                import_name: s_secret,
                module_request: s_rel_leaf,
            },
            ExportDecl::Star {
                module_request: s_rel_leaf,
            },
            ExportDecl::Star {
                module_request: s_rel_cycle,
            },
        ],
        module_requests: vec![
            ModuleRequest {
                specifier: s_rel_leaf,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_rel_cycle,
                lazy: false,
            },
        ],
    });

    let s_ohm_barrel = m.sym.intern("@bundle:com.app/entry/ets/barrel");
    let s_rel_json = m.sym.intern("./assets/cfg.json");
    let s_ohos_http = m.sym.intern("@ohos.net.http");
    let s_create_http = m.sym.intern("createHttp");
    let s_ns = m.sym.intern("ns");
    m.classes[c_main.index()].es_module = Some(EsModule {
        imports: vec![
            ImportDecl::Regular {
                local_name: s_renamed,
                import_name: s_renamed,
                module_request: s_ohm_barrel,
            },
            ImportDecl::Regular {
                local_name: s_extra,
                import_name: s_extra,
                module_request: s_rel_barrel,
            },
            ImportDecl::Regular {
                local_name: s_default,
                import_name: s_default,
                module_request: s_rel_barrel,
            },
            ImportDecl::Regular {
                local_name: s_default,
                import_name: s_default,
                module_request: s_rel_json,
            },
            ImportDecl::Regular {
                local_name: s_create_http,
                import_name: s_create_http,
                module_request: s_ohos_http,
            },
            ImportDecl::Namespace {
                local_name: s_ns,
                module_request: s_ohm_barrel,
            },
        ],
        exports: Vec::new(),
        module_requests: vec![
            ModuleRequest {
                specifier: s_ohm_barrel,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_rel_json,
                lazy: false,
            },
            ModuleRequest {
                specifier: s_ohos_http,
                lazy: false,
            },
        ],
    });

    // Add `func_main_0` to leaf, cycle, barrel, and main.
    let (f_leaf, b_leaf, _) =
        push_fn_with_params(&mut m, c_leaf, "func_main_0", FunctionKind::Function, 3);
    let c42 = m.consts.push(Const::number(42.0));
    let (_, v42) = emit_val(&mut m, b_leaf, Op::LoadConst(c42));
    emit_void(
        &mut m,
        b_leaf,
        Op::StoreModuleVar {
            index: 0,
            value: v42,
        },
    );
    emit_void(&mut m, b_leaf, Op::Return { value: None });

    let (_, b_cycle, _) =
        push_fn_with_params(&mut m, c_cycle, "func_main_0", FunctionKind::Function, 3);
    let (_, b_cycle_val) = emit_val(&mut m, b_cycle, Op::LoadConst(c42));
    emit_void(
        &mut m,
        b_cycle,
        Op::StoreModuleVar {
            index: 0,
            value: b_cycle_val,
        },
    );
    emit_void(&mut m, b_cycle, Op::Return { value: None });

    let (f_barrel, b_barrel, _) =
        push_fn_with_params(&mut m, c_barrel, "func_main_0", FunctionKind::Function, 3);
    emit_void(&mut m, b_barrel, Op::Return { value: None });

    let (f_main, b_main, _) =
        push_fn_with_params(&mut m, c_main, "func_main_0", FunctionKind::Function, 3);
    emit_void(&mut m, b_main, Op::Return { value: None });

    assert!(verify_module(&m).errors.is_empty());

    let links = ModuleLinkTable::build(&m);
    assert!(links.has_multi_record_esm());

    // Slot 0 (`renamed` -> indirect to leaf's `secret` slot 0).
    let t0 = links.external_load(c_main, 0).expect("slot 0");
    assert!(!t0.unresolved_external);
    assert_eq!(
        t0.slots,
        vec![ModuleSlotRef {
            class_id: c_leaf,
            slot: 0
        }]
    );

    // Slot 1 (`extra` -> star through barrel -> cycle slot 0, cycle-safe).
    let t1 = links.external_load(c_main, 1).expect("slot 1");
    assert!(!t1.unresolved_external);
    assert_eq!(
        t1.slots,
        vec![ModuleSlotRef {
            class_id: c_cycle,
            slot: 0
        }]
    );

    // Slot 2 (`default` from barrel -> ECMA-262 `export *` must NOT forward `default`).
    let t2 = links.external_load(c_main, 2).expect("slot 2");
    assert!(t2.slots.is_empty());
    assert!(t2.unresolved_external);

    // Slot 3 (`default` from `./assets/cfg.json` -> JSON constant).
    let t3 = links.external_load(c_main, 3).expect("slot 3");
    assert!(!t3.unresolved_external);
    assert_eq!(t3.json_consts, vec![jconst]);

    // Slot 4 (`createHttp` from `@ohos.net.http` -> external SDK import).
    let t4 = links.external_load(c_main, 4).expect("slot 4");
    assert!(t4.unresolved_external);
    assert_eq!(t4.external_imports, vec![(s_ohos_http, s_create_http)]);

    // Namespace member resolution (`ns.renamed`, `ns.secret`, `ns.extra`; no `ns.default`).
    assert_eq!(
        links.resolve_namespace_member(c_main, 0, s_renamed),
        Some(
            [ModuleSlotRef {
                class_id: c_leaf,
                slot: 0
            }]
            .as_slice()
        )
    );
    assert!(
        links
            .resolve_namespace_member(c_main, 0, s_default)
            .is_none()
    );

    // Topological order: leaf and barrel initialize before main.
    let order = links.init_order();
    let pos_leaf = order.iter().position(|&f| f == f_leaf).expect("leaf");
    let pos_barrel = order.iter().position(|&f| f == f_barrel).expect("barrel");
    let pos_main = order.iter().position(|&f| f == f_main).expect("main");
    assert!(pos_leaf < pos_barrel);
    assert!(pos_barrel < pos_main);
}

#[test]
fn cross_module_callgraph_rung1_and_pta_resolve_closures_and_classes() {
    let mut m = Module::new();
    let d_lib = m.sym.intern("L@bundle:com.app/entry/ets/lib;");
    let n_lib = m.sym.intern("@bundle:com.app/entry/ets/lib");
    let c_lib = ClassId::new(0);
    m.classes.push(ClassData::new(d_lib, n_lib));

    let d_app = m.sym.intern("L@bundle:com.app/entry/ets/app;");
    let n_app = m.sym.intern("@bundle:com.app/entry/ets/app");
    let c_app = ClassId::new(1);
    m.classes.push(ClassData::new(d_app, n_app));

    let s_helper = m.sym.intern("helper");
    let s_box = m.sym.intern("ExportedBox");
    let s_shared = m.sym.intern("sharedObj");
    let s_payload = m.sym.intern("payload");
    let s_rel_lib = m.sym.intern("./lib");

    m.classes[c_lib.index()].es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![
            ExportDecl::Local {
                local_name: s_helper,
                export_name: s_helper,
            },
            ExportDecl::Local {
                local_name: s_box,
                export_name: s_box,
            },
            ExportDecl::Local {
                local_name: s_shared,
                export_name: s_shared,
            },
        ],
        module_requests: Vec::new(),
    });
    m.classes[c_app.index()].es_module = Some(EsModule {
        imports: vec![
            ImportDecl::Regular {
                local_name: s_helper,
                import_name: s_helper,
                module_request: s_rel_lib,
            },
            ImportDecl::Regular {
                local_name: s_box,
                import_name: s_box,
                module_request: s_rel_lib,
            },
            ImportDecl::Regular {
                local_name: s_shared,
                import_name: s_shared,
                module_request: s_rel_lib,
            },
        ],
        exports: Vec::new(),
        module_requests: vec![ModuleRequest {
            specifier: s_rel_lib,
            lazy: false,
        }],
    });

    // Helper closure body + ExportedBox constructor (`this.payload = arg0`).
    let (f_helper, b_helper, _) =
        push_fn_with_params(&mut m, c_lib, "helper", FunctionKind::Function, 3);
    emit_void(&mut m, b_helper, Op::Return { value: None });

    let (f_ctor, b_ctor, ctor_params) =
        push_fn_with_params(&mut m, c_lib, "ExportedBox", FunctionKind::Constructor, 4);
    emit_void(
        &mut m,
        b_ctor,
        Op::StoreProp {
            object: ctor_params[2], // `this`
            name: s_payload,
            value: ctor_params[3], // formal 0
        },
    );
    emit_void(&mut m, b_ctor, Op::Return { value: None });

    // lib `func_main_0` exports helper (slot 0), ExportedBox (slot 1), sharedObj (slot 2).
    let (_, b_lib, _) =
        push_fn_with_params(&mut m, c_lib, "func_main_0", FunctionKind::Function, 3);
    let empty_shape = m.consts.push(Const::ObjectLiteral {
        keys: Vec::new(),
        values: Vec::new(),
    });
    let empty_members = m.consts.push(Const::ArrayLiteral(Vec::new()));
    let (_, df_val) = emit_val(
        &mut m,
        b_lib,
        Op::DefineFunc {
            body: f_helper,
            captures: Vec::new(),
            length: 0,
        },
    );
    let (_, clos_val) = emit_val(&mut m, b_lib, Op::AllocClosure { func: df_val });
    emit_void(
        &mut m,
        b_lib,
        Op::StoreModuleVar {
            index: 0,
            value: clos_val,
        },
    );

    let (_, cls_val) = emit_val(
        &mut m,
        b_lib,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: f_ctor,
            heritage: None,
            members: empty_members,
            member_attrs: Vec::new(),
            count: 1,
        })),
    );
    emit_void(
        &mut m,
        b_lib,
        Op::StoreModuleVar {
            index: 1,
            value: cls_val,
        },
    );

    let (shared_alloc_iid, shared_val) =
        emit_val(&mut m, b_lib, Op::AllocObject { shape: empty_shape });
    emit_void(
        &mut m,
        b_lib,
        Op::StoreModuleVar {
            index: 2,
            value: shared_val,
        },
    );
    emit_void(&mut m, b_lib, Op::Return { value: None });

    // app `func_main_0`: imports and invokes helper, constructs ExportedBox(innerObj), reads .payload.
    let (_, b_app, _) =
        push_fn_with_params(&mut m, c_app, "func_main_0", FunctionKind::Function, 3);
    let (_, imp_helper) = emit_val(
        &mut m,
        b_app,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let (call_helper_iid, _) = emit_val(
        &mut m,
        b_app,
        Op::Call {
            callee: imp_helper,
            this: None,
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );

    let (_, imp_box) = emit_val(
        &mut m,
        b_app,
        Op::LoadModuleVar {
            index: 1,
            kind: ModuleVarKind::External,
        },
    );
    let (inner_alloc_iid, inner_obj) =
        emit_val(&mut m, b_app, Op::AllocObject { shape: empty_shape });
    let (new_box_iid, box_inst) = emit_val(
        &mut m,
        b_app,
        Op::Call {
            callee: imp_box,
            this: None,
            args: vec![inner_obj],
            kind: CallKind::New,
        },
    );
    let (load_payload_iid, loaded_payload) = emit_val(
        &mut m,
        b_app,
        Op::LoadProp {
            object: box_inst,
            name: s_payload,
        },
    );
    let (load_shared_iid, imp_shared) = emit_val(
        &mut m,
        b_app,
        Op::LoadModuleVar {
            index: 2,
            kind: ModuleVarKind::External,
        },
    );
    emit_void(&mut m, b_app, Op::Return { value: None });

    assert!(verify_module(&m).errors.is_empty());

    // Rung 0 CallGraph resolves both cross-module helper call and `new ExportedBox`.
    let cg = CallGraph::build(&m);
    assert_eq!(cg.callees_of_call_at(call_helper_iid), &[f_helper]);
    assert_eq!(cg.callees_of_call_at(new_box_iid), &[f_ctor]);

    // Rung 1 alias oracle resolves cross-module `sharedObj` allocation site.
    let r1 = Rung1AliasOracle::new(&m, &cg);
    let shared_ans = r1.query(imp_shared, load_shared_iid);
    assert!(shared_ans.precise_for_keying());
    assert_eq!(
        shared_ans.sites.iter().collect::<Vec<_>>(),
        vec![shared_alloc_iid]
    );

    // Rung 2 PTA resolves `box_inst.payload` across `new ExportedBox(inner_obj)`.
    let outcome = analyze(&m, &cg, &PtaConfig::default());
    let (_, tables, stats) = outcome.into_parts();
    let r2 = Rung2AliasOracle::new(&m, tables, stats);
    let payload_info = r2.site_info_at(loaded_payload, load_payload_iid);
    assert!(!payload_info.has_unknown);
    assert_eq!(
        payload_info.sites.iter().collect::<Vec<_>>(),
        vec![inner_alloc_iid]
    );
}

#[test]
fn merge_ir_modules_links_standalone_modules_and_verifies() {
    // Standalone module 1 (`lib/util`): exports `val`.
    let mut m1 = Module::new();
    let d_glob1 = m1.sym.intern("L_GLOBAL;");
    let n_glob1 = m1.sym.intern("_GLOBAL");
    m1.classes.push(ClassData::new(d_glob1, n_glob1));
    let s_val1 = m1.sym.intern("val");
    m1.exports.push(ExportDecl::Local {
        local_name: s_val1,
        export_name: s_val1,
    });
    let (_, b1, _) = push_fn_with_params(
        &mut m1,
        ClassId::new(0),
        "func_main_0",
        FunctionKind::Function,
        3,
    );
    let sh1 = m1.consts.push(Const::ObjectLiteral {
        keys: Vec::new(),
        values: Vec::new(),
    });
    let (_, v1) = emit_val(&mut m1, b1, Op::AllocObject { shape: sh1 });
    emit_void(
        &mut m1,
        b1,
        Op::StoreModuleVar {
            index: 0,
            value: v1,
        },
    );
    emit_void(&mut m1, b1, Op::Return { value: None });

    // Standalone module 2 (`entry/index`): imports `val` from `../lib/util`.
    let mut m2 = Module::new();
    let d_glob2 = m2.sym.intern("L_GLOBAL;");
    let n_glob2 = m2.sym.intern("_GLOBAL");
    m2.classes.push(ClassData::new(d_glob2, n_glob2));
    let s_val2 = m2.sym.intern("val");
    let s_req2 = m2.sym.intern("../lib/util");
    m2.imports.push(ImportDecl::Regular {
        local_name: s_val2,
        import_name: s_val2,
        module_request: s_req2,
    });
    m2.module_requests.push(ModuleRequest {
        specifier: s_req2,
        lazy: false,
    });
    let (_, b2, _) = push_fn_with_params(
        &mut m2,
        ClassId::new(0),
        "func_main_0",
        FunctionKind::Function,
        3,
    );
    let _ = emit_val(
        &mut m2,
        b2,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    emit_void(&mut m2, b2, Op::Return { value: None });

    let merged = merge_ir_modules(&[("lib/util", &m1), ("entry/index", &m2)]);
    let rep = verify_module(&merged);
    assert!(rep.errors.is_empty(), "verify errors: {:?}", rep.errors);

    let links = ModuleLinkTable::build(&merged);
    let t = links
        .external_load(ClassId::new(1), 0)
        .expect("merged import");
    assert!(!t.unresolved_external);
    assert_eq!(
        t.slots,
        vec![ModuleSlotRef {
            class_id: ClassId::new(0),
            slot: 0
        }]
    );
}

#[test]
fn deep_reexport_init_and_nested_remap_run_on_small_stack() {
    const DEPTH: usize = 300;
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut m1 = Module::new();
            let s_val = m1.sym.intern("val");
            for i in 0..DEPTH {
                let desc = m1.sym.intern(&format!("L@bundle:app/m{i};"));
                let name = m1.sym.intern(&format!("@bundle:app/m{i}"));
                let cid = ClassId::new(i as u32);
                m1.classes.push(ClassData::new(desc, name));
                let mut exports = Vec::new();
                let mut requests = Vec::new();
                let mut imports = Vec::new();
                if i == 0 {
                    exports.push(ExportDecl::Local {
                        local_name: s_val,
                        export_name: s_val,
                    });
                } else {
                    let prev = m1.sym.intern(&format!("@bundle:app/m{}", i - 1));
                    exports.push(ExportDecl::Star {
                        module_request: prev,
                    });
                    requests.push(ModuleRequest {
                        specifier: prev,
                        lazy: false,
                    });
                    if i + 1 == DEPTH {
                        imports.push(ImportDecl::Regular {
                            local_name: s_val,
                            import_name: s_val,
                            module_request: prev,
                        });
                    }
                }
                m1.classes[cid.index()].es_module = Some(EsModule {
                    imports,
                    exports,
                    module_requests: requests,
                });
                let (_, b, _) =
                    push_fn_with_params(&mut m1, cid, "func_main_0", FunctionKind::Function, 3);
                if i == 0 {
                    let c1 = m1.consts.push(Const::number(1.0));
                    let (_, v) = emit_val(&mut m1, b, Op::LoadConst(c1));
                    emit_void(&mut m1, b, Op::StoreModuleVar { index: 0, value: v });
                }
                emit_void(&mut m1, b, Op::Return { value: None });
            }

            // Deeply nested `Ty::Union` and `Const::ArrayLiteral` / `Const::ObjectLiteral`
            // plus `Int64` / `UInt64`, Round 3 literal tags, `TypedArrayLiteral`,
            // `LiteralBufferRef`, `Catch::type_class`, and a cyclic `ConstPool` entry.
            let mut deep_ty = Ty::Static(StaticTy::Reference(ClassId::new(0)));
            let c_key = m1.consts.intern(Const::String(s_val));
            let _ = m1.consts.push(Const::Int8(7));
            let c_i32 = m1.consts.push(Const::Int32(42));
            let _ = m1.consts.push(Const::float32(1.5));
            let _ = m1.consts.push(Const::Int64(-99));
            let _ = m1.consts.push(Const::UInt64(99));
            let _ = m1.consts.push(Const::Accessor(0));
            let _ = m1.consts.push(Const::MethodAffiliate(2));
            let _ = m1.consts.push(Const::BuiltinTypeIndex(3));
            let _ = m1.consts.push(Const::EtsImplements(s_val));
            let _ = m1.consts.push(Const::LitNull(0));
            let _ = m1.consts.push(Const::method_ref_with_kind(
                FuncId::new(0),
                abcd_ir::LitMethodKind::Getter,
            ));
            let tarr = m1.consts.push(Const::TypedArrayLiteral {
                tag: abcd_ir::TypedArrayTag::I32,
                items: vec![c_i32],
            });
            let _ = m1.consts.push(Const::LiteralBufferRef(tarr));
            let mut deep_cid = c_key;
            for _ in 0..DEPTH {
                deep_ty = Ty::union(vec![deep_ty]);
                let arr_cid = m1.consts.push_array(vec![deep_cid]);
                deep_cid = m1.consts.push_object(vec![c_key], vec![arr_cid]);
            }
            // Malformed self-referential `ArrayLiteral` cycle (`cyc_cid -> cyc_cid`).
            let cyc_cid = ConstId::new(m1.consts.len() as u32);
            let _ = m1.consts.push_array(vec![cyc_cid, deep_cid]);
            m1.values[0].ty = deep_ty;
            let h_bid = m1.functions[0].blocks[0];
            let exc_vid = ValueId::new(m1.values.len() as u32);
            m1.values.push(Value {
                def: ValueDef::ExceptionParam(h_bid),
                ty: Ty::Any,
            });
            m1.functions[0].try_regions.push(TryRegion {
                protected: vec![h_bid],
                catches: vec![Catch {
                    handler: h_bid,
                    exception: exc_vid,
                    type_class: Some(ClassId::new(1)),
                }],
            });

            let mut m2 = Module::new();
            let dg = m2.sym.intern("L_GLOBAL;");
            let ng = m2.sym.intern("_GLOBAL");
            m2.classes.push(ClassData::new(dg, ng));

            let merged = merge_ir_modules(&[("bundle", &m1), ("extra", &m2)]);
            let merged_owned =
                merge_ir_modules_owned([("bundle", m1.clone()), ("extra", m2.clone())]);
            abcd_ir::modules_structurally_eq(&merged, &merged_owned)
                .expect("merge_ir_modules_owned must match merge_ir_modules");

            // Also place the cyclic-const + deep-union module at index 1 so
            // `append_module_owned`'s iterative remappers run on the 256 KiB stack!
            let merged_rev_ref = merge_ir_modules(&[("extra", &m2), ("bundle", &m1)]);
            let merged_rev_owned = merge_ir_modules_owned([("extra", m2), ("bundle", m1)]);
            abcd_ir::modules_structurally_eq(&merged_rev_ref, &merged_rev_owned)
                .expect("reverse order structural equivalence");

            let links = ModuleLinkTable::build(&merged);
            assert_eq!(links.init_order().len(), DEPTH);
            let resolved = links
                .external_load(ClassId::new((DEPTH - 1) as u32), 0)
                .expect("leaf import");
            assert!(!resolved.unresolved_external);
            assert_eq!(
                resolved.slots,
                vec![ModuleSlotRef {
                    class_id: ClassId::new(0),
                    slot: 0
                }]
            );
        })
        .expect("spawn");
    handle.join().expect("small stack must not overflow");
}

fn add_exporting_record(m: &mut Module, raw_record: &str, export_names: &[&str]) -> ClassId {
    let desc = m.sym.intern(&format!("L{raw_record};"));
    let name = m.sym.intern(raw_record);
    let cid = ClassId::new(m.classes.len() as u32);
    m.classes.push(ClassData::new(desc, name));

    let exports: Vec<ExportDecl> = export_names
        .iter()
        .map(|ename| {
            let s = m.sym.intern(ename);
            ExportDecl::Local {
                local_name: s,
                export_name: s,
            }
        })
        .collect();
    m.classes[cid.index()].es_module = Some(EsModule {
        imports: Vec::new(),
        exports,
        module_requests: Vec::new(),
    });

    let (_, b, _) = push_fn_with_params(m, cid, "func_main_0", FunctionKind::Function, 3);
    let c1 = m.consts.push(Const::number(1.0));
    for idx in 0..export_names.len() {
        let (_, v) = emit_val(m, b, Op::LoadConst(c1));
        emit_void(
            m,
            b,
            Op::StoreModuleVar {
                index: idx as u32,
                value: v,
            },
        );
    }
    emit_void(m, b, Op::Return { value: None });
    cid
}

fn add_importing_record(
    m: &mut Module,
    raw_record: &str,
    specs: &[(&str, &str)],
) -> (ClassId, Vec<Sym>) {
    let desc = m.sym.intern(&format!("L{raw_record};"));
    let name = m.sym.intern(raw_record);
    let cid = ClassId::new(m.classes.len() as u32);
    m.classes.push(ClassData::new(desc, name));

    let mut imports = Vec::with_capacity(specs.len());
    let mut module_requests = Vec::with_capacity(specs.len());
    let mut req_syms = Vec::with_capacity(specs.len());
    for &(spec, imp_name) in specs {
        let s_req = m.sym.intern(spec);
        let s_imp = m.sym.intern(imp_name);
        imports.push(ImportDecl::Regular {
            local_name: s_imp,
            import_name: s_imp,
            module_request: s_req,
        });
        module_requests.push(ModuleRequest {
            specifier: s_req,
            lazy: false,
        });
        req_syms.push(s_req);
    }
    m.classes[cid.index()].es_module = Some(EsModule {
        imports,
        exports: Vec::new(),
        module_requests,
    });

    let (_, b, _) = push_fn_with_params(m, cid, "func_main_0", FunctionKind::Function, 3);
    emit_void(m, b, Op::Return { value: None });
    (cid, req_syms)
}

#[test]
fn bundle_and_infix_har_resolve_to_dot_encoded_records() {
    let mut m = Module::new();
    let c_main_ability = add_exporting_record(
        &mut m,
        "com.huawei.hmos.photos.phone_photos.ets.MainAbility.MainAbility",
        &["MainAbility"],
    );
    let c_drag_ctrl = add_exporting_record(
        &mut m,
        "com.huawei.hmos.photos.phone_photos@browserCommon.ets.default.controller.DragController",
        &["DragController"],
    );
    let (c_importer, _) = add_importing_record(
        &mut m,
        "com.huawei.hmos.photos.phone_photos.ets.pages.Gallery",
        &[
            (
                "@bundle:com.huawei.hmos.photos/phone_photos/ets/MainAbility/MainAbility",
                "MainAbility",
            ),
            (
                "@bundle:com.huawei.hmos.photos/phone_photos@browserCommon/ets/default/controller/DragController",
                "DragController",
            ),
        ],
    );

    assert!(verify_module(&m).errors.is_empty());
    let links = ModuleLinkTable::build(&m);

    let t0 = links.external_load(c_importer, 0).expect("slot 0");
    assert!(!t0.unresolved_external);
    assert_eq!(
        t0.slots,
        vec![ModuleSlotRef {
            class_id: c_main_ability,
            slot: 0,
        }]
    );
    assert_eq!(links.namespace_target(c_importer, 0), Some(c_main_ability));

    let t1 = links.external_load(c_importer, 1).expect("slot 1");
    assert!(!t1.unresolved_external);
    assert_eq!(
        t1.slots,
        vec![ModuleSlotRef {
            class_id: c_drag_ctrl,
            slot: 0,
        }]
    );
    assert_eq!(links.namespace_target(c_importer, 1), Some(c_drag_ctrl));
}

#[test]
fn package_ohpm_resolves_to_dot_encoded_records_and_index_fallbacks() {
    let mut m = Module::new();
    let c_clip = add_exporting_record(
        &mut m,
        "pkg_modules..ohpm.@hms-core+media@1.3.1.pkg_modules.@hms-core.media.src.main.ets.Clip",
        &["Clip"],
    );
    let c_media_index = add_exporting_record(
        &mut m,
        "pkg_modules..ohpm.@hms-core+media@1.3.1.pkg_modules.@hms-core.media.index",
        &["MediaHub"],
    );
    let c_slash_index = add_exporting_record(
        &mut m,
        "@package:pkg_modules/.ohpm/@ohos+axios@2.2.0/pkg_modules/@ohos/axios/index",
        &["axios"],
    );
    let c_stem_only = add_exporting_record(
        &mut m,
        "pkg_modules..ohpm.@ohos+crypto@1.0.0.pkg_modules.@ohos.crypto.Crypto",
        &["Crypto"],
    );

    let (c_importer, _) = add_importing_record(
        &mut m,
        "com.demo.entry.ets.pages.Index",
        &[
            (
                "@package:pkg_modules/.ohpm/@hms-core+media@1.3.1/pkg_modules/@hms-core/media/src/main/ets/Clip",
                "Clip",
            ),
            (
                "@package:pkg_modules/.ohpm/@hms-core+media@1.3.1/pkg_modules/@hms-core/media",
                "MediaHub",
            ),
            (
                "@package:pkg_modules/.ohpm/@ohos+axios@2.2.0/pkg_modules/@ohos/axios",
                "axios",
            ),
            (
                "@package:pkg_modules/.ohpm/@ohos+crypto@1.0.0/pkg_modules/@ohos/crypto/Crypto/index",
                "Crypto",
            ),
        ],
    );

    assert!(verify_module(&m).errors.is_empty());
    let links = ModuleLinkTable::build(&m);

    for (slot_idx, expected_cid) in [
        (0u32, c_clip),
        (1u32, c_media_index),
        (2u32, c_slash_index),
        (3u32, c_stem_only),
    ] {
        let t = links.external_load(c_importer, slot_idx).expect("slot");
        assert!(!t.unresolved_external, "slot {slot_idx} should resolve");
        assert_eq!(
            t.slots,
            vec![ModuleSlotRef {
                class_id: expected_cid,
                slot: 0,
            }]
        );
    }
}

#[test]
fn normalized_ohmurl_bare_ampersand_and_sdk_native_filters() {
    assert_eq!(
        parse_normalized_ohmurl("@normalized:N&entry&com.demo&entry/src/main/ets/Helper&1.0.0"),
        Some(("entry", "com.demo", "entry/src/main/ets/Helper"))
    );
    assert_eq!(
        parse_normalized_ohmurl("@normalized:N&har&com.demo/har/src/main/ets/Api&1.0.0"),
        Some(("har", "", "com.demo/har/src/main/ets/Api"))
    );
    assert_eq!(
        parse_normalized_ohmurl("@normalized:N&entry&&entry/src/main/ets/Helper"),
        Some(("entry", "", "entry/src/main/ets/Helper"))
    );
    assert_eq!(
        parse_normalized_ohmurl("@normalized:N&entry&entry/src/main/ets/Helper"),
        Some(("entry", "", "entry/src/main/ets/Helper"))
    );
    assert_eq!(
        parse_normalized_ohmurl("&entry&com.demo&entry/src/main/ets/Foo&1.0.0"),
        Some(("entry", "com.demo", "entry/src/main/ets/Foo"))
    );
    assert_eq!(
        parse_normalized_ohmurl("&har&com.demo/har/src/main/ets/Api&1.0.0"),
        Some(("har", "", "com.demo/har/src/main/ets/Api"))
    );
    assert_eq!(
        parse_normalized_ohmurl("&com.demo/entry/ets/Foo&1.0.0&"),
        Some(("", "", "com.demo/entry/ets/Foo"))
    );
    assert_eq!(
        parse_normalized_ohmurl("&entry/src/main/ets/Foo&"),
        Some(("", "", "entry/src/main/ets/Foo"))
    );

    let mut m = Module::new();
    // Bare `&` 4-field record matched by 5-field `@normalized:N&...` specifier.
    let c_helper = add_exporting_record(
        &mut m,
        "&entry&com.demo&entry/src/main/ets/Helper&1.0.0",
        &["Helper"],
    );
    // Dot-encoded record matched by 4-field `@normalized:N&har&...` specifier.
    let c_api = add_exporting_record(&mut m, "com.demo.har.src.main.ets.Api", &["callApi"]);
    // 5-field `@normalized:N&...` record matched by bare `&...` specifier.
    let c_model = add_exporting_record(
        &mut m,
        "@normalized:N&entry&com.demo&entry/src/main/ets/Model&1.0.0",
        &["Model"],
    );
    // Internal bundled `@app:` record resolves when present, while absent `@app:` marks external.
    let c_app_internal =
        add_exporting_record(&mut m, "@app:com.demo/entry/BundledLib", &["bundled"]);
    // Bare `&<mod>/<path>&<ver>` HAR record matched by 4-segment `@normalized:N&<mod>&<bundle>/<mod>/<path>&<ver>`.
    let c_shared_har = add_exporting_record(
        &mut m,
        "&shared_har/src/main/ets/DeviceStore&1.0.0",
        &["DeviceStore"],
    );

    let (c_importer, req_syms) = add_importing_record(
        &mut m,
        "&entry&com.demo&entry/src/main/ets/Main&1.0.0",
        &[
            (
                "@normalized:N&entry&com.demo&entry/src/main/ets/Helper&1.0.0",
                "Helper",
            ),
            (
                "@normalized:N&har&com.demo/har/src/main/ets/Api&1.0.0",
                "callApi",
            ),
            ("&entry&com.demo&entry/src/main/ets/Model&1.0.0", "Model"),
            ("@app:com.demo/entry/BundledLib", "bundled"),
            (
                "@normalized:N&shared_har&com.demo.app/shared_har/src/main/ets/DeviceStore&1.0.0",
                "DeviceStore",
            ),
            (
                "@normalized:Y&entry&com.demo&libentry.so&1.0.0",
                "nativeCall",
            ),
            ("@hms.core.push.pushService", "pushService"),
            ("@hms:core.account", "account"),
            ("@app:com.demo/entry/MissingNative", "missing"),
        ],
    );

    assert!(verify_module(&m).errors.is_empty());
    let links = ModuleLinkTable::build(&m);

    for (slot_idx, expected_cid) in [
        (0u32, c_helper),
        (1u32, c_api),
        (2u32, c_model),
        (3u32, c_app_internal),
        (4u32, c_shared_har),
    ] {
        let t = links.external_load(c_importer, slot_idx).expect("slot");
        assert!(!t.unresolved_external, "slot {slot_idx} should resolve");
        assert_eq!(
            t.slots,
            vec![ModuleSlotRef {
                class_id: expected_cid,
                slot: 0,
            }]
        );
    }

    for slot_idx in 5u32..=8u32 {
        let t = links.external_load(c_importer, slot_idx).expect("ext slot");
        assert!(
            t.unresolved_external,
            "slot {slot_idx} must mark unresolved_external"
        );
        assert!(t.slots.is_empty());
        assert_eq!(t.external_imports.len(), 1);
        assert_eq!(t.external_imports[0].0, req_syms[slot_idx as usize]);
    }
}

#[test]
fn dot_encoded_record_relative_imports() {
    let mut m = Module::new();
    let c_sibling = add_exporting_record(&mut m, "com.demo.entry.ets.pages.Sibling", &["Sibling"]);
    let c_util = add_exporting_record(&mut m, "com.demo.entry.ets.common.Util", &["util"]);
    let c_comp_idx = add_exporting_record(&mut m, "com.demo.entry.ets.components.index", &["Comp"]);
    let (c_home, _) = add_importing_record(
        &mut m,
        "com.demo.entry.ets.pages.Home",
        &[
            ("./Sibling", "Sibling"),
            ("../common/Util", "util"),
            ("../components", "Comp"),
        ],
    );

    assert!(verify_module(&m).errors.is_empty());
    let links = ModuleLinkTable::build(&m);

    for (slot_idx, expected_cid) in [(0u32, c_sibling), (1u32, c_util), (2u32, c_comp_idx)] {
        let t = links.external_load(c_home, slot_idx).expect("slot");
        assert!(!t.unresolved_external, "slot {slot_idx} should resolve");
        assert_eq!(
            t.slots,
            vec![ModuleSlotRef {
                class_id: expected_cid,
                slot: 0,
            }]
        );
    }
}

#[test]
fn cyclic_star_exports_preserve_monotone_unresolved_external() {
    let mut m = Module::new();

    // Leaf `c_leaf` defines local export `shared`.
    let d_leaf = m.sym.intern("Lapp/leaf;");
    let n_leaf = m.sym.intern("app/leaf");
    let s_shared = m.sym.intern("shared");
    let s_only_ext = m.sym.intern("onlyFromExt");
    let c_leaf = ClassId::new(m.classes.len() as u32);
    let mut cls_leaf = ClassData::new(d_leaf, n_leaf);
    cls_leaf.es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![ExportDecl::Local {
            local_name: s_shared,
            export_name: s_shared,
        }],
        module_requests: Vec::new(),
    });
    m.classes.push(cls_leaf);
    let (_, b_leaf, _) =
        push_fn_with_params(&mut m, c_leaf, "func_main_0", FunctionKind::Function, 3);
    let u_cid = m.consts.push(Const::Undefined);
    let (_, v_leaf) = emit_val(&mut m, b_leaf, Op::LoadConst(u_cid));
    emit_void(
        &mut m,
        b_leaf,
        Op::StoreModuleVar {
            index: 0,
            value: v_leaf,
        },
    );
    emit_void(&mut m, b_leaf, Op::Return { value: None });

    // `c_a` and `c_b` form an `export *` cycle (`./b` <-> `./a`), where:
    // - `c_a` has `export * from "./b"` followed by `export * from "./leaf"`
    // - `c_b` has `export * from "@ohos.net.http"` (external!) and `export * from "./a"`
    // Previously `StarAfterChild` overwrote `out.unresolved_external = saved_unres`,
    // losing `c_b`'s external star flag when `c_a` also matched `c_leaf`!
    let req_b = m.sym.intern("./b");
    let req_a = m.sym.intern("./a");
    let req_leaf = m.sym.intern("./leaf");
    let req_ext = m.sym.intern("@ohos.net.http");

    let d_a = m.sym.intern("Lapp/a;");
    let n_a = m.sym.intern("app/a");
    let c_a = ClassId::new(m.classes.len() as u32);
    let mut cls_a = ClassData::new(d_a, n_a);
    cls_a.es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![
            ExportDecl::Star {
                module_request: req_b,
            },
            ExportDecl::Star {
                module_request: req_leaf,
            },
        ],
        module_requests: vec![
            ModuleRequest {
                specifier: req_b,
                lazy: false,
            },
            ModuleRequest {
                specifier: req_leaf,
                lazy: false,
            },
        ],
    });
    m.classes.push(cls_a);
    let (_, b_a, _) = push_fn_with_params(&mut m, c_a, "func_main_0", FunctionKind::Function, 3);
    emit_void(&mut m, b_a, Op::Return { value: None });

    let d_b = m.sym.intern("Lapp/b;");
    let n_b = m.sym.intern("app/b");
    let c_b = ClassId::new(m.classes.len() as u32);
    let mut cls_b = ClassData::new(d_b, n_b);
    cls_b.es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![
            ExportDecl::Star {
                module_request: req_ext,
            },
            ExportDecl::Star {
                module_request: req_a,
            },
        ],
        module_requests: vec![
            ModuleRequest {
                specifier: req_ext,
                lazy: false,
            },
            ModuleRequest {
                specifier: req_a,
                lazy: false,
            },
        ],
    });
    m.classes.push(cls_b);
    let (_, b_b, _) = push_fn_with_params(&mut m, c_b, "func_main_0", FunctionKind::Function, 3);
    emit_void(&mut m, b_b, Op::Return { value: None });

    // Importer imports `shared` and `onlyFromExt` from BOTH `./a` and `./b`.
    let d_imp = m.sym.intern("Lapp/importer;");
    let n_imp = m.sym.intern("app/importer");
    let c_imp = ClassId::new(m.classes.len() as u32);
    let mut cls_imp = ClassData::new(d_imp, n_imp);
    cls_imp.es_module = Some(EsModule {
        imports: vec![
            ImportDecl::Regular {
                local_name: s_shared,
                import_name: s_shared,
                module_request: req_a,
            },
            ImportDecl::Regular {
                local_name: s_shared,
                import_name: s_shared,
                module_request: req_b,
            },
            ImportDecl::Regular {
                local_name: s_only_ext,
                import_name: s_only_ext,
                module_request: req_a,
            },
        ],
        exports: Vec::new(),
        module_requests: vec![
            ModuleRequest {
                specifier: req_a,
                lazy: false,
            },
            ModuleRequest {
                specifier: req_b,
                lazy: false,
            },
        ],
    });
    m.classes.push(cls_imp);
    let (_, b_imp, _) =
        push_fn_with_params(&mut m, c_imp, "func_main_0", FunctionKind::Function, 3);
    emit_void(&mut m, b_imp, Op::Return { value: None });

    assert!(verify_module(&m).errors.is_empty());
    let links = ModuleLinkTable::build(&m);
    assert!(links.has_unresolved_star(c_a));
    assert!(links.has_unresolved_star(c_b));
    assert!(!links.has_unresolved_star(c_leaf));

    for slot_idx in [0u32, 1u32] {
        let t = links.external_load(c_imp, slot_idx).expect("slot");
        assert_eq!(
            t.slots,
            vec![ModuleSlotRef {
                class_id: c_leaf,
                slot: 0,
            }]
        );
        assert!(
            t.unresolved_external,
            "slot {slot_idx}: cyclic `export * from '@ohos.net.http'` must stay monotonically unresolved"
        );
    }
    let t_ext = links.external_load(c_imp, 2).expect("ext-only slot");
    assert!(t_ext.slots.is_empty());
    assert!(t_ext.unresolved_external);
}

#[test]
fn merge_ir_modules_owned_streams_drops_and_matches_structural_eq() {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    // 0-element fast path.
    let empty_ref = merge_ir_modules(&[]);
    let empty_owned = merge_ir_modules_owned(Vec::<(&str, Module)>::new());
    abcd_ir::modules_structurally_eq(&empty_ref, &empty_owned).unwrap();

    // Build 3 standalone modules.
    let make_mod = |export_str: &str, import_from: Option<&str>| {
        let mut m = Module::new();
        let dg = m.sym.intern("L_GLOBAL;");
        let ng = m.sym.intern("_GLOBAL");
        m.classes.push(ClassData::new(dg, ng));
        let s_exp = m.sym.intern(export_str);
        m.exports.push(ExportDecl::Local {
            local_name: s_exp,
            export_name: s_exp,
        });
        if let Some(req) = import_from {
            let s_req = m.sym.intern(req);
            m.imports.push(ImportDecl::Regular {
                local_name: s_exp,
                import_name: s_exp,
                module_request: s_req,
            });
            m.module_requests.push(ModuleRequest {
                specifier: s_req,
                lazy: false,
            });
        }
        let (_, b, _) = push_fn_with_params(
            &mut m,
            ClassId::new(0),
            "func_main_0",
            FunctionKind::Function,
            3,
        );
        let c_num = m.consts.push(Const::number(7.0));
        let (_, v) = emit_val(&mut m, b, Op::LoadConst(c_num));
        emit_void(&mut m, b, Op::StoreModuleVar { index: 0, value: v });
        emit_void(&mut m, b, Op::Return { value: None });
        m
    };

    let m0 = make_mod("val", None);
    let m1 = make_mod("val", Some("../lib/a"));
    let m2 = make_mod("val", Some("../lib/b"));

    // 1-element standalone fast path.
    let single_ref = merge_ir_modules(&[("lib/a", &m0)]);
    let single_owned = merge_ir_modules_owned([("lib/a", m0.clone())]);
    abcd_ir::modules_structurally_eq(&single_ref, &single_owned).unwrap();

    // 1-element `--merge-abc` (`es_module.is_some()`) zero-clone fast path.
    let esm_ptr = single_owned.classes.as_ptr();
    let passthrough = merge_ir_modules_owned([("ignored", single_owned)]);
    assert_eq!(
        passthrough.classes.as_ptr(),
        esm_ptr,
        "single-element ESM module must return by value without cloning"
    );

    // Multi-module streaming path: verify each streamed guard drops BEFORE
    // the iterator produces the next item (except `m0` + `m1` peek pair).
    let live_guards = Arc::new(AtomicUsize::new(0));
    let max_live_guards = Arc::new(AtomicUsize::new(0));

    struct GuardedName {
        name: &'static str,
        live: Arc<AtomicUsize>,
    }
    impl AsRef<str> for GuardedName {
        fn as_ref(&self) -> &str {
            self.name
        }
    }
    impl Drop for GuardedName {
        fn drop(&mut self) {
            self.live.fetch_sub(1, Ordering::SeqCst);
        }
    }

    let raw_items = vec![
        ("lib/a", m0.clone()),
        ("lib/b", m1.clone()),
        ("entry/index", m2.clone()),
    ];
    let live_ref = Arc::clone(&live_guards);
    let max_ref = Arc::clone(&max_live_guards);
    let stream = raw_items.into_iter().map(move |(name, module)| {
        let cur = live_ref.fetch_add(1, Ordering::SeqCst) + 1;
        let _ = max_ref.fetch_max(cur, Ordering::SeqCst);
        (
            GuardedName {
                name,
                live: Arc::clone(&live_ref),
            },
            module,
        )
    });

    let multi_owned = merge_ir_modules_owned(stream);
    assert_eq!(live_guards.load(Ordering::SeqCst), 0);
    assert!(
        max_live_guards.load(Ordering::SeqCst) <= 2,
        "streaming merge must drop earlier items before pulling module 2..N"
    );
    let multi_ref = merge_ir_modules(&[("lib/a", &m0), ("lib/b", &m1), ("entry/index", &m2)]);
    abcd_ir::modules_structurally_eq(&multi_ref, &multi_owned).unwrap();
}

#[test]
fn lossy_export_syms_extend_appended_and_decoy_harness_check() {
    let mut m = Module::new();
    let d0 = m.sym.intern("L@bundle:app/exp;");
    let n0 = m.sym.intern("@bundle:app/exp");
    m.classes.push(ClassData::new(d0, n0));

    let d1 = m.sym.intern("L@bundle:app/imp;");
    let n1 = m.sym.intern("@bundle:app/imp");
    m.classes.push(ClassData::new(d1, n1));

    // Lone-surrogate export name (`0xD834` in MUTF-8: `ED A0 B4`).
    let s_lossy = m.sym.intern_raw_mutf8(&[0xED, 0xA0, 0xB4]);
    let s_rel = m.sym.intern("./exp");
    m.classes[0].es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![ExportDecl::Local {
            local_name: s_lossy,
            export_name: s_lossy,
        }],
        module_requests: Vec::new(),
    });
    m.classes[1].es_module = Some(EsModule {
        imports: Vec::new(),
        exports: Vec::new(),
        module_requests: vec![ModuleRequest {
            specifier: s_rel,
            lazy: false,
        }],
    });

    let (f0, b0, _) = push_fn_with_params(
        &mut m,
        ClassId::new(0),
        "func_main_0",
        FunctionKind::Function,
        3,
    );
    emit_void(&mut m, b0, Op::Return { value: None });

    let mut links = ModuleLinkTable::build(&m);
    assert_eq!(
        links.resolve_namespace_member(ClassId::new(1), 0, s_lossy),
        Some(
            [ModuleSlotRef {
                class_id: ClassId::new(0),
                slot: 0
            }]
            .as_slice()
        )
    );
    assert_eq!(links.func_of_block(b0), Some(f0));
    assert_eq!(links.block_func_slice(), &[Some(f0)]);

    // Append a new function and block after `build`, then `extend_appended`.
    let (f_extra, b_extra, _) = push_fn_with_params(
        &mut m,
        ClassId::new(1),
        crate::ohos_lifecycle::OHOS_HARNESS_FUNC,
        FunctionKind::Function,
        3,
    );
    let ret_iid = emit_void(&mut m, b_extra, Op::Return { value: None });
    links.extend_appended(&m);
    assert_eq!(links.func_class(f_extra), Some(ClassId::new(1)));
    assert_eq!(links.func_of_block(b_extra), Some(f_extra));
    assert_eq!(links.inst_func(&m, ret_iid), Some(f_extra));
    assert_eq!(links.block_func_slice(), &[Some(f0), Some(f_extra)]);
}
