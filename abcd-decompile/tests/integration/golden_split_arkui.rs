//! Golden and unit tests for `#26` Phase 2 (`--split-modules` multi-record
//! directory tree output & OHMUrl normalization) and Phase 3 (`--arkui`
//! OpenHarmony ArkUI declarative sugar recovery).

use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_decompile::split::{SplitFileKind, decompile_module_split, normalize_record_path};
use abcd_ir::consts::Const;
use abcd_ir::function::{Block, FunctionData, Inst, Value};
use abcd_ir::id::{BlockId, ClassId, FuncId, ValueId};
use abcd_ir::module::{
    ClassData, EsModule, ExportDecl, FieldData, FunctionKind, ImportDecl, Module, ModuleRequest,
};
use abcd_ir::op::{CallKind, CmpOp, ModuleVarKind, Op, UnOp};
use abcd_ir::ty::Ty;
use abcd_ir::{Edge, EdgeKind, ValueDef};

fn add_record_class(m: &mut Module, desc: &str) -> ClassId {
    let cid = ClassId::new(m.classes.len() as u32);
    let sym = m.sym.intern(desc);
    m.classes.push(ClassData::new(sym, sym));
    cid
}

fn add_fn_in_class(m: &mut Module, cid: ClassId, name: &str, kind: FunctionKind) -> FuncId {
    let sym = m.sym.intern(name);
    let fid = FuncId::new(m.functions.len() as u32);
    let mut fd = FunctionData::new(cid, sym, kind);
    fd.modifiers |= abcd_ir::Modifiers::STATIC;
    m.functions.push(fd);
    m.classes[cid.index()].methods.push(fid);
    let bid = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(fid).unwrap().blocks.push(bid);
    for _ in 0..3 {
        add_param(m, fid);
    }
    fid
}

fn add_param(m: &mut Module, fid: FuncId) -> ValueId {
    let idx = m.func(fid).unwrap().params.len() as u16;
    let vid = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Param(idx),
        ty: Ty::Any,
    });
    m.func_mut(fid).unwrap().params.push(vid);
    vid
}

fn add_block(m: &mut Module, fid: FuncId) -> BlockId {
    let bid = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(fid).unwrap().blocks.push(bid);
    bid
}

fn entry_of(m: &Module, fid: FuncId) -> BlockId {
    m.func(fid).unwrap().blocks[0]
}

fn emit_val(m: &mut Module, b: BlockId, op: Op) -> ValueId {
    assert!(op.has_result(), "{op:?} has no result");
    let iid = abcd_ir::InstId::new(m.insts.len() as u32);
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
    m.block_mut(b).unwrap().insts.push(iid);
    vid
}

fn emit_void(m: &mut Module, b: BlockId, op: Op) {
    assert!(!op.has_result(), "{op:?} has a result");
    let iid = abcd_ir::InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op,
        result: None,
        block: b,
        loc: None,
    });
    m.block_mut(b).unwrap().insts.push(iid);
}

fn load_str(m: &mut Module, b: BlockId, s: &str) -> ValueId {
    let sym = m.sym.intern(s);
    let cid = m.consts.push(Const::String(sym));
    emit_val(m, b, Op::LoadConst(cid))
}

fn load_num(m: &mut Module, b: BlockId, x: f64) -> ValueId {
    let cid = m.consts.push(Const::number(x));
    emit_val(m, b, Op::LoadConst(cid))
}

fn load_bool(m: &mut Module, b: BlockId, v: bool) -> ValueId {
    let cid = m.consts.push(Const::Bool(v));
    emit_val(m, b, Op::LoadConst(cid))
}

fn try_global(m: &mut Module, b: BlockId, name: &str) -> ValueId {
    let sym = m.sym.intern(name);
    let undef_cid = m.consts.push(Const::Undefined);
    let default = emit_val(m, b, Op::LoadConst(undef_cid));
    emit_val(
        m,
        b,
        Op::TryGetGlobal {
            name: sym,
            default: Some(default),
        },
    )
}

// ── Phase 2: Path normalization & `--split-modules` ───────────────────────

#[test]
fn normalize_record_path_handles_ohmurls_traversal_and_reserved_names() {
    assert_eq!(
        normalize_record_path(
            "L@bundle:com.example.app/entry/ets/pages/Index;",
            false,
            "ets"
        ),
        Some("com.example.app/entry/ets/pages/Index.ets".to_string())
    );
    assert_eq!(
        normalize_record_path(
            "L@package:pkg_modules/.ohpm/foo@1.0.0/src/index;",
            false,
            "js"
        ),
        Some("pkg_modules/.ohpm/foo@1.0.0/src/index.js".to_string())
    );
    assert_eq!(
        normalize_record_path(
            "L@normalized:N&entry&com.example.app&ets/pages/Home&1.0.0;",
            false,
            "ts"
        ),
        Some("ets/pages/Home.ts".to_string())
    );
    // Traversal stripping (`..` and leading `/`)
    assert_eq!(
        normalize_record_path("L/../../etc/../secret/main.js;", false, "js"),
        Some("etc/secret/main.js".to_string())
    );
    // Windows reserved basenames (`CON`, `nul`, `com1`)
    assert_eq!(
        normalize_record_path("LCON;", false, "js"),
        Some("CON_.js".to_string())
    );
    assert_eq!(
        normalize_record_path("Ldir/nul/com1.ts;", false, "js"),
        Some("dir/nul_/com1_.js".to_string())
    );
    // JSON extension override
    assert_eq!(
        normalize_record_path("Lcom.example.app/entry/cfg;", true, "js"),
        Some("com.example.app/entry/cfg.json".to_string())
    );
    // Synthetic and external SDK records return `None`
    assert_eq!(
        normalize_record_path("L_ESModuleRecord;", false, "js"),
        None
    );
    assert_eq!(
        normalize_record_path("L_ESSlotNumberAnnotation;", false, "js"),
        None
    );
    assert_eq!(normalize_record_path("L@ohos.net.http;", false, "js"), None);
    assert_eq!(normalize_record_path("L@kit.ArkUI;", false, "ets"), None);
}

#[test]
fn split_modules_isolates_per_record_slots_and_rewrites_ohmurl_and_json() {
    let mut m = Module::new();

    // Synthetic metadata class (must be skipped)
    let _synth = add_record_class(&mut m, "L_ESModuleRecord;");

    // Record 1: `Lcom.demo/entry/ets/pages/Main;`
    // Imports `{ calc }` from `@bundle:com.demo/entry/ets/util/Math` (External slot 0),
    // default `cfg` from `./config` (External slot 1), and `* as mathNs` (Namespace req 0).
    // Exports local `run` (Local slot 0).
    let cid_main = add_record_class(&mut m, "Lcom.demo/entry/ets/pages/Main;");
    let req_math = m.sym.intern("@bundle:com.demo/entry/ets/util/Math");
    let req_cfg = m.sym.intern("./config");
    let s_calc = m.sym.intern("calc");
    let s_cfg = m.sym.intern("cfg");
    let s_def = m.sym.intern("default");
    let s_ns = m.sym.intern("mathNs");
    let s_run = m.sym.intern("run");
    m.classes[cid_main.index()].es_module = Some(EsModule {
        module_requests: vec![
            ModuleRequest {
                specifier: req_math,
                lazy: false,
            },
            ModuleRequest {
                specifier: req_cfg,
                lazy: false,
            },
        ],
        imports: vec![
            ImportDecl::Regular {
                local_name: s_calc,
                import_name: s_calc,
                module_request: req_math,
            },
            ImportDecl::Regular {
                local_name: s_cfg,
                import_name: s_def,
                module_request: req_cfg,
            },
            ImportDecl::Namespace {
                local_name: s_ns,
                module_request: req_math,
            },
        ],
        exports: vec![ExportDecl::Local {
            local_name: s_run,
            export_name: s_run,
        }],
    });
    let f_main = add_fn_in_class(&mut m, cid_main, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, f_main);
        let ext_calc = emit_val(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let ext_cfg = emit_val(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 1,
                kind: ModuleVarKind::External,
            },
        );
        let ns = emit_val(&mut m, b, Op::GetModuleNamespace { index: 0 });
        let port_sym = m.sym.intern("port");
        let port = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: ext_cfg,
                name: port_sym,
            },
        );
        let sum = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: ext_calc,
                this: Some(ns),
                args: vec![port],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: sum,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Record 2: `Lcom.demo/entry/ets/util/Math;`
    // Also uses Local slot 0, but here Local slot 0 is `calc` (would collide
    // with `Main`'s slot 0 if module slots were not isolated per `ClassId`!).
    let cid_math = add_record_class(&mut m, "Lcom.demo/entry/ets/util/Math;");
    m.classes[cid_math.index()].es_module = Some(EsModule {
        module_requests: vec![],
        imports: vec![],
        exports: vec![ExportDecl::Local {
            local_name: s_calc,
            export_name: s_calc,
        }],
    });
    let f_calc_body = add_fn_in_class(&mut m, cid_math, "calc", FunctionKind::Function);
    {
        let x = add_param(&mut m, f_calc_body);
        let b = entry_of(&m, f_calc_body);
        emit_void(&mut m, b, Op::Return { value: Some(x) });
    }
    let f_math_main = add_fn_in_class(&mut m, cid_math, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, f_math_main);
        let df = emit_val(
            &mut m,
            b,
            Op::DefineFunc {
                body: f_calc_body,
                captures: vec![],
                length: 1,
            },
        );
        let cl = emit_val(&mut m, b, Op::AllocClosure { func: df });
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: cl,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Record 3: JSON asset `Lcom.demo/entry/ets/pages/config;`
    let cid_cfg = add_record_class(&mut m, "Lcom.demo/entry/ets/pages/config;");
    let json_name = m.sym.intern("jsonFileContent");
    let json_val = m.sym.intern("{\"port\":8080}");
    let json_const = m.consts.push(Const::String(json_val));
    m.classes[cid_cfg.index()].fields.push(FieldData {
        name: json_name,
        ty: Ty::Any,
        modifiers: abcd_ir::Modifiers::NONE,
        initial_value: Some(json_const),
        annotations: Vec::new(),
    });

    let split = decompile_module_split(&m, &EmitOptions::default());
    assert_eq!(split.files.len(), 3);

    let f0 = &split.files[0];
    assert_eq!(f0.rel_path, "com.demo/entry/ets/pages/Main.js");
    assert_eq!(f0.kind, SplitFileKind::Module);
    assert!(
        f0.text.contains("import { calc } from \"../util/Math\";"),
        "expected rewritten OHMUrl import in Main.js:\n{}",
        f0.text
    );
    assert!(
        f0.text.contains("import cfg from \"./config.json\";"),
        "expected rewritten .json import in Main.js:\n{}",
        f0.text
    );
    assert!(
        f0.text
            .contains("import * as mathNs from \"../util/Math\";"),
        "expected namespace import in Main.js:\n{}",
        f0.text
    );
    assert!(
        f0.text.contains("const calc$1 = calc;")
            && f0.text.contains("const mathNs$1 = mathNs;")
            && f0.text.contains("calc$1.call(mathNs$1,"),
        "expected External slot 0 -> calc & Namespace 0 -> mathNs:\n{}",
        f0.text
    );
    assert!(
        f0.text.contains("run = ") && f0.text.contains("export { run };"),
        "expected Local slot 0 -> run in Main.js:\n{}",
        f0.text
    );

    let f1 = &split.files[1];
    assert_eq!(f1.rel_path, "com.demo/entry/ets/util/Math.js");
    assert_eq!(f1.kind, SplitFileKind::Module);
    assert!(
        f1.text.contains("calc = function calc(") && f1.text.contains("export { calc };"),
        "expected Local slot 0 -> calc in Math.js:\n{}",
        f1.text
    );

    let f2 = &split.files[2];
    assert_eq!(f2.rel_path, "com.demo/entry/ets/pages/config.json");
    assert_eq!(f2.kind, SplitFileKind::Json);
    assert_eq!(f2.text, "{\"port\":8080}\n");
}

// ── Phase 3: OpenHarmony ArkUI declarative sugar (`--arkui`) ──────────────

#[test]
fn arkui_reconstructs_entry_struct_decorators_builders_and_ui_tree() {
    let mut m = Module::new();
    let cid = add_record_class(&mut m, "Lcom.demo/entry/ets/pages/CounterPage;");

    // Constructor of `CounterPage`: `@State count = 0`, `@Prop title`,
    // `@Link active`, `@Provide("themeKey") theme = "dark"`, `@Consume("bus") bus`,
    // `@StorageLink("token") token = "abc"`.
    let f_ctor = add_fn_in_class(&mut m, cid, "CounterPage", FunctionKind::Constructor);
    {
        let b = entry_of(&m, f_ctor);
        let this = m.func(f_ctor).unwrap().params[2];

        // @State count = 0
        let obs_cls = try_global(&mut m, b, "ObservedPropertySimplePU");
        let zero = load_num(&mut m, b, 0.0);
        let prop_count_s = load_str(&mut m, b, "count");
        let obs_count = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: obs_cls,
                this: None,
                args: vec![zero, this, prop_count_s],
                kind: CallKind::New,
            },
        );
        let k_count = m.sym.intern("__count");
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: this,
                name: k_count,
                value: obs_count,
            },
        );

        // @Prop title
        let prop_cls = try_global(&mut m, b, "SynchedPropertySimpleOneWayPU");
        let undef = m.consts.push(Const::Undefined);
        let v_undef = emit_val(&mut m, b, Op::LoadConst(undef));
        let s_title = load_str(&mut m, b, "title");
        let syn_title = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: prop_cls,
                this: None,
                args: vec![v_undef, this, s_title],
                kind: CallKind::New,
            },
        );
        let k_title = m.sym.intern("__title");
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: this,
                name: k_title,
                value: syn_title,
            },
        );

        // @Link active
        let link_cls = try_global(&mut m, b, "SynchedPropertySimpleTwoWayPU");
        let s_active = load_str(&mut m, b, "active");
        let syn_active = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: link_cls,
                this: None,
                args: vec![v_undef, this, s_active],
                kind: CallKind::New,
            },
        );
        let k_active = m.sym.intern("__active");
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: this,
                name: k_active,
                value: syn_active,
            },
        );

        // @Provide("themeKey") theme = "dark"
        let obs_cls2 = try_global(&mut m, b, "ObservedPropertySimplePU");
        let s_dark = load_str(&mut m, b, "dark");
        let s_theme = load_str(&mut m, b, "theme");
        let obs_theme = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: obs_cls2,
                this: None,
                args: vec![s_dark, this, s_theme],
                kind: CallKind::New,
            },
        );
        let k_theme = m.sym.intern("__theme");
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: this,
                name: k_theme,
                value: obs_theme,
            },
        );
        let add_prov_sym = m.sym.intern("addProvidedVar");
        let add_prov_fn = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: this,
                name: add_prov_sym,
            },
        );
        let alias_theme = load_str(&mut m, b, "themeKey");
        let read_theme = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: this,
                name: k_theme,
            },
        );
        let _ = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: add_prov_fn,
                this: Some(this),
                args: vec![alias_theme, read_theme],
                kind: CallKind::Dynamic,
            },
        );

        // @Consume("bus") bus
        let init_cons_sym = m.sym.intern("initializeConsume");
        let init_cons_fn = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: this,
                name: init_cons_sym,
            },
        );
        let s_bus = load_str(&mut m, b, "bus");
        let cons_val = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: init_cons_fn,
                this: Some(this),
                args: vec![s_bus, s_bus],
                kind: CallKind::Dynamic,
            },
        );
        let k_bus = m.sym.intern("__bus");
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: this,
                name: k_bus,
                value: cons_val,
            },
        );

        // @StorageLink("token") token = "abc"
        let csl_sym = m.sym.intern("createStorageLink");
        let csl_fn = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: this,
                name: csl_sym,
            },
        );
        let s_tok_key = load_str(&mut m, b, "token");
        let s_tok_def = load_str(&mut m, b, "abc");
        let tok_val = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: csl_fn,
                this: Some(this),
                args: vec![s_tok_key, s_tok_def, s_tok_key],
                kind: CallKind::Dynamic,
            },
        );
        let k_tok = m.sym.intern("__token");
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: this,
                name: k_tok,
                value: tok_val,
            },
        );

        emit_void(&mut m, b, Op::Return { value: Some(this) });
    }

    // Synthetic boilerplate `rerender` (must be elided under `--arkui`).
    let f_rerender = add_fn_in_class(&mut m, cid, "rerender", FunctionKind::Function);
    {
        let b = entry_of(&m, f_rerender);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // User lifecycle `aboutToAppear` (must be preserved).
    let f_appear = add_fn_in_class(&mut m, cid, "aboutToAppear", FunctionKind::Function);
    {
        let b = entry_of(&m, f_appear);
        let log_fn = try_global(&mut m, b, "print");
        let msg = load_str(&mut m, b, "mounted");
        let _ = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: log_fn,
                this: None,
                args: vec![msg],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Observe closure 1: `Column.create(); Column.width("100%");` (container, no `.pop()` inside).
    let f_col_obs = add_fn_in_class(&mut m, cid, "col_obs", FunctionKind::Function);
    {
        let _elmt = add_param(&mut m, f_col_obs);
        let _is_init = add_param(&mut m, f_col_obs);
        let b = entry_of(&m, f_col_obs);
        let col = try_global(&mut m, b, "Column");
        let create_sym = m.sym.intern("create");
        let create_fn = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: col,
                name: create_sym,
            },
        );
        let _ = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: create_fn,
                this: Some(col),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let width_sym = m.sym.intern("width");
        let width_fn = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: col,
                name: width_sym,
            },
        );
        let w_arg = load_str(&mut m, b, "100%");
        let _ = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: width_fn,
                this: Some(col),
                args: vec![w_arg],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Observe closure 2: `Text.create("Hello"); Text.fontSize(18); Text.pop();`
    let f_txt_obs = add_fn_in_class(&mut m, cid, "txt_obs", FunctionKind::Function);
    {
        let _elmt = add_param(&mut m, f_txt_obs);
        let _is_init = add_param(&mut m, f_txt_obs);
        let b = entry_of(&m, f_txt_obs);
        let txt = try_global(&mut m, b, "Text");
        let create_sym = m.sym.intern("create");
        let create_fn = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: txt,
                name: create_sym,
            },
        );
        let hello = load_str(&mut m, b, "Hello");
        let _ = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: create_fn,
                this: Some(txt),
                args: vec![hello],
                kind: CallKind::Dynamic,
            },
        );
        let fs_sym = m.sym.intern("fontSize");
        let fs_fn = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: txt,
                name: fs_sym,
            },
        );
        let eighteen = load_num(&mut m, b, 18.0);
        let _ = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: fs_fn,
                this: Some(txt),
                args: vec![eighteen],
                kind: CallKind::Dynamic,
            },
        );
        let pop_sym = m.sym.intern("pop");
        let pop_fn = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: txt,
                name: pop_sym,
            },
        );
        let _ = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: pop_fn,
                this: Some(txt),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Observe closure 3: Custom child `ChildBadge({ active: $active })`
    let f_child_obs = add_fn_in_class(&mut m, cid, "child_obs", FunctionKind::Function);
    {
        let _elmt = add_param(&mut m, f_child_obs);
        let _is_init = add_param(&mut m, f_child_obs);
        let b = entry_of(&m, f_child_obs);
        let this = m.func(f_child_obs).unwrap().params[2];
        let child_cls = try_global(&mut m, b, "ChildBadge");
        let empty_obj = m.consts.push(Const::ObjectLiteral {
            keys: vec![],
            values: vec![],
        });
        let props_obj = emit_val(&mut m, b, Op::AllocObject { shape: empty_obj });
        let k_active_backing = m.sym.intern("__active");
        let backing = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: this,
                name: k_active_backing,
            },
        );
        let k_active = m.sym.intern("active");
        emit_void(
            &mut m,
            b,
            Op::StoreOwnPropName {
                object: props_obj,
                name: k_active,
                value: backing,
            },
        );
        let child_inst = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: child_cls,
                this: None,
                args: vec![this, props_obj],
                kind: CallKind::New,
            },
        );
        let vpu = try_global(&mut m, b, "ViewPU");
        let create_sym = m.sym.intern("create");
        let create_fn = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: vpu,
                name: create_sym,
            },
        );
        let _ = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: create_fn,
                this: Some(vpu),
                args: vec![child_inst],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // `initialRender`: Column { Text("Hello").fontSize(18); ChildBadge({ active: $active }); }
    let f_render = add_fn_in_class(&mut m, cid, "initialRender", FunctionKind::Function);
    {
        let b = entry_of(&m, f_render);
        let this = m.func(f_render).unwrap().params[2];
        let obs_sym = m.sym.intern("observeComponentCreation2");

        for (obs_body, comp_global) in [
            (f_col_obs, Some("Column")),
            (f_txt_obs, Some("Text")),
            (f_child_obs, None),
        ] {
            let obs_fn = emit_val(
                &mut m,
                b,
                Op::LoadProp {
                    object: this,
                    name: obs_sym,
                },
            );
            let df = emit_val(
                &mut m,
                b,
                Op::DefineFunc {
                    body: obs_body,
                    captures: vec![],
                    length: 2,
                },
            );
            let cl = emit_val(&mut m, b, Op::AllocClosure { func: df });
            let mut call_args = vec![cl];
            if let Some(cg) = comp_global {
                call_args.push(try_global(&mut m, b, cg));
            }
            let _ = emit_val(
                &mut m,
                b,
                Op::Call {
                    callee: obs_fn,
                    this: Some(this),
                    args: call_args,
                    kind: CallKind::Dynamic,
                },
            );
        }

        // `Column.pop()`
        let col = try_global(&mut m, b, "Column");
        let pop_sym = m.sym.intern("pop");
        let pop_fn = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: col,
                name: pop_sym,
            },
        );
        let _ = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: pop_fn,
                this: Some(col),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Prototype-overflow `@Builder` method (`headerBuilder(label)`).
    let f_hdr_builder = add_fn_in_class(&mut m, cid, "headerBuilder", FunctionKind::Function);
    {
        let _label = add_param(&mut m, f_hdr_builder);
        let b = entry_of(&m, f_hdr_builder);
        let this = m.func(f_hdr_builder).unwrap().params[2];
        let obs_sym = m.sym.intern("observeComponentCreation2");
        let obs_fn = emit_val(
            &mut m,
            b,
            Op::LoadProp {
                object: this,
                name: obs_sym,
            },
        );
        let df = emit_val(
            &mut m,
            b,
            Op::DefineFunc {
                body: f_txt_obs,
                captures: vec![],
                length: 2,
            },
        );
        let cl = emit_val(&mut m, b, Op::AllocClosure { func: df });
        let txt_g = try_global(&mut m, b, "Text");
        let _ = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: obs_fn,
                this: Some(this),
                args: vec![cl, txt_g],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // `func_main_0`: finalizeConstruction polyfill + DefineClass + prototype-overflow
    // `headerBuilder` + `registerNamedRoute` entry registration.
    let f_main = add_fn_in_class(&mut m, cid, "func_main_0", FunctionKind::Function);
    {
        let b0 = entry_of(&m, f_main);
        let b_poly = add_block(&mut m, f_main);
        let b_join = add_block(&mut m, f_main);

        let fc_str = load_str(&mut m, b0, "finalizeConstruction");
        let vpu0 = try_global(&mut m, b0, "ViewPU");
        let proto_sym = m.sym.intern("prototype");
        let vpu_proto = emit_val(
            &mut m,
            b0,
            Op::LoadProp {
                object: vpu0,
                name: proto_sym,
            },
        );
        let has_fc = emit_val(
            &mut m,
            b0,
            Op::Compare {
                op: CmpOp::In,
                left: fc_str,
                right: vpu_proto,
            },
        );
        let not_fc = emit_val(
            &mut m,
            b0,
            Op::UnaryOp {
                op: UnOp::LogicalNot,
                operand: has_fc,
            },
        );
        emit_void(
            &mut m,
            b0,
            Op::CondBranch {
                cond: not_fc,
                true_dest: b_poly,
                false_dest: b_join,
            },
        );
        m.block_mut(b_poly).unwrap().preds.push(Edge {
            from: b0,
            kind: EdgeKind::Normal,
        });
        m.block_mut(b_join).unwrap().preds.push(Edge {
            from: b0,
            kind: EdgeKind::Normal,
        });

        let refl = try_global(&mut m, b_poly, "Reflect");
        let set_sym = m.sym.intern("set");
        let refl_set = emit_val(
            &mut m,
            b_poly,
            Op::LoadProp {
                object: refl,
                name: set_sym,
            },
        );
        let fc_str2 = load_str(&mut m, b_poly, "finalizeConstruction");
        let nop = load_bool(&mut m, b_poly, true);
        let _ = emit_val(
            &mut m,
            b_poly,
            Op::Call {
                callee: refl_set,
                this: Some(refl),
                args: vec![vpu_proto, fc_str2, nop],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_poly, Op::Branch { dest: b_join });
        m.block_mut(b_join).unwrap().preds.push(Edge {
            from: b_poly,
            kind: EdgeKind::Normal,
        });

        let vpu = try_global(&mut m, b_join, "ViewPU");
        let s_rerender = m.sym.intern("rerender");
        let s_appear = m.sym.intern("aboutToAppear");
        let s_render = m.sym.intern("initialRender");
        let members = m.consts.push(Const::ArrayLiteral(vec![
            Const::String(s_rerender),
            Const::MethodRef(f_rerender),
            Const::String(s_appear),
            Const::MethodRef(f_appear),
            Const::String(s_render),
            Const::MethodRef(f_render),
        ]));
        let cls_val = emit_val(
            &mut m,
            b_join,
            Op::DefineClass {
                ctor: f_ctor,
                heritage: Some(vpu),
                members,
                member_attrs: vec![],
                count: 3,
            },
        );
        let cls_proto = emit_val(
            &mut m,
            b_join,
            Op::LoadProp {
                object: cls_val,
                name: proto_sym,
            },
        );
        let df_hdr = emit_val(
            &mut m,
            b_join,
            Op::DefineFunc {
                body: f_hdr_builder,
                captures: vec![],
                length: 1,
            },
        );
        let cl_hdr = emit_val(&mut m, b_join, Op::AllocClosure { func: df_hdr });
        let hdr_sym = m.sym.intern("headerBuilder");
        emit_void(
            &mut m,
            b_join,
            Op::StoreOwnPropName {
                object: cls_proto,
                name: hdr_sym,
                value: cl_hdr,
            },
        );

        let reg_route = try_global(&mut m, b_join, "registerNamedRoute");
        let route_name = load_str(&mut m, b_join, "");
        let _ = emit_val(
            &mut m,
            b_join,
            Op::Call {
                callee: reg_route,
                this: None,
                args: vec![cls_val, route_name],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, b_join, Op::Return { value: None });
    }

    // 1. Default (`arkui: false`) keeps raw JS `class CounterPage extends ViewPU`
    let raw_js = decompile_module(&m, &EmitOptions::default());
    assert!(
        raw_js.text.contains("extends ViewPU"),
        "default mode must keep JS class output:\n{}",
        raw_js.text
    );
    assert!(!raw_js.text.contains("@Component"));

    // 2. Opt-in `--arkui` reconstructs `@Entry @Component struct CounterPage`
    let ark = decompile_module(
        &m,
        &EmitOptions {
            arkui: true,
            ..Default::default()
        },
    );
    let t = &ark.text;
    assert!(
        t.contains("@Entry\n@Component\nstruct CounterPage {"),
        "{t}"
    );
    assert!(t.contains("@State count: any = 0.0;"), "{t}");
    assert!(t.contains("@Prop title: any;"), "{t}");
    assert!(t.contains("@Link active: any;"), "{t}");
    assert!(
        t.contains("@Provide(\"themeKey\") theme: any = \"dark\";"),
        "{t}"
    );
    assert!(t.contains("@Consume bus: any;"), "{t}");
    assert!(
        t.contains("@StorageLink(\"token\") token: any = \"abc\";"),
        "{t}"
    );
    assert!(
        !t.contains("rerender("),
        "synthetic rerender must be elided:\n{t}"
    );
    assert!(
        !t.contains("finalizeConstruction"),
        "polyfill must be elided:\n{t}"
    );
    assert!(
        t.contains("aboutToAppear() {"),
        "lifecycle must survive:\n{t}"
    );
    assert!(
        t.contains("@Builder\n  headerBuilder("),
        "overflow @Builder:\n{t}"
    );
    assert!(t.contains("build() {"), "{t}");
    assert!(t.contains("Column() {"), "{t}");
    assert!(
        t.contains("Text(\"Hello\")\n        .fontSize(18.0)"),
        "{t}"
    );
    assert!(t.contains("ChildBadge({ active: $active })"), "{t}");
    assert!(t.contains(".width(\"100%\")"), "{t}");
}
