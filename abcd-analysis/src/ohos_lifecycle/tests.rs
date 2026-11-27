//! Unit tests for OpenHarmony component discovery and steady-state lifecycle harness synthesis.

use super::*;
use crate::callgraph::CallGraph;
use crate::dataflow::ifds::CallGraphOracle;
use crate::dataflow::pta::{PtaConfig, Rung2AliasOracle, analyze};
use abcd_ir::module::ClassData;
use abcd_ir::verify::verify_module;

fn add_fn(
    m: &mut Module,
    cid: ClassId,
    name: &str,
    kind: FunctionKind,
    total_params: u16,
) -> (FuncId, BlockId, Vec<ValueId>) {
    let sym = m.sym.intern(name);
    let fid = FuncId::new(m.functions.len() as u32);
    let mut fd = FunctionData::new(cid, sym, kind);
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

#[test]
fn plain_single_module_returns_none() {
    let mut m = Module::new();
    let d = m.sym.intern("L_GLOBAL;");
    let n = m.sym.intern("_GLOBAL");
    m.classes.push(ClassData::new(d, n));
    let (_, b, _) = add_fn(
        &mut m,
        ClassId::new(0),
        "func_main_0",
        FunctionKind::Function,
        3,
    );
    emit_inst_void(&mut m, b, Op::Return { value: None });
    assert!(synthesize_ohos_harness(&m, None).is_none());
}

#[test]
fn synthesize_harness_wires_ability_extension_and_viewpu_with_distinct_receivers() {
    let mut m = Module::new();
    let d = m
        .sym
        .intern("L@bundle:com.app/entry/ets/entryability/EntryAbility;");
    let n = m
        .sym
        .intern("@bundle:com.app/entry/ets/entryability/EntryAbility");
    let cid = ClassId::new(0);
    m.classes.push(ClassData::new(d, n));

    // Ability 1: EntryAbility (`ctor`, `onCreate`, `onForeground`)
    let (ctor1, b_c1, _) = add_fn(&mut m, cid, "EntryAbility", FunctionKind::Constructor, 3);
    emit_inst_void(&mut m, b_c1, Op::Return { value: None });
    let (on_create1, b_oc1, p_oc1) = add_fn(&mut m, cid, "onCreate", FunctionKind::Function, 5);
    let s_saved = m.sym.intern("savedWant");
    emit_inst_void(
        &mut m,
        b_oc1,
        Op::StoreProp {
            object: p_oc1[2],
            name: s_saved,
            value: p_oc1[3],
        },
    );
    emit_inst_void(&mut m, b_oc1, Op::Return { value: None });
    let (on_fg1, b_fg1, p_fg1) = add_fn(&mut m, cid, "onForeground", FunctionKind::Function, 3);
    emit_inst_void(&mut m, b_fg1, Op::Return { value: None });
    let fg1_last = m.blocks[b_fg1.index()].insts[0];

    // Ability 2: SecondAbility (`ctor`, `onForeground`) — distinct receiver check!
    let (ctor2, b_c2, _) = add_fn(&mut m, cid, "SecondAbility", FunctionKind::Constructor, 3);
    emit_inst_void(&mut m, b_c2, Op::Return { value: None });
    let (on_fg2, b_fg2, p_fg2) = add_fn(&mut m, cid, "onForeground2", FunctionKind::Function, 3);
    emit_inst_void(&mut m, b_fg2, Op::Return { value: None });
    let fg2_last = m.blocks[b_fg2.index()].insts[0];

    // ExtensionAbility: CardExt (`ctor`, `onAddForm`)
    let (ctor3, b_c3, _) = add_fn(&mut m, cid, "CardExt", FunctionKind::Constructor, 3);
    emit_inst_void(&mut m, b_c3, Op::Return { value: None });
    let (on_add, b_add, _) = add_fn(&mut m, cid, "onAddForm", FunctionKind::Function, 4);
    emit_inst_void(&mut m, b_add, Op::Return { value: None });

    // ArkUI ViewPU: HomePage (`ctor`, `aboutToAppear`, `initialRender`, overflow `@Builder`)
    let (ctor4, b_c4, _) = add_fn(&mut m, cid, "HomePage", FunctionKind::Constructor, 3);
    emit_inst_void(&mut m, b_c4, Op::Return { value: None });
    let (about, b_ab, _) = add_fn(&mut m, cid, "aboutToAppear", FunctionKind::Function, 3);
    emit_inst_void(&mut m, b_ab, Op::Return { value: None });
    let (render, b_rn, _) = add_fn(&mut m, cid, "initialRender", FunctionKind::Function, 3);
    emit_inst_void(&mut m, b_rn, Op::Return { value: None });
    let (builder, b_bd, p_bd) = add_fn(&mut m, cid, "HeaderBuilder", FunctionKind::Function, 3);
    let s_obs = m.sym.intern("observeComponentCreation2");
    let _ = emit_inst_val(
        &mut m,
        b_bd,
        Op::LoadProp {
            object: p_bd[2],
            name: s_obs,
        },
    );
    emit_inst_void(&mut m, b_bd, Op::Return { value: None });

    // `func_main_0` defines all 4 classes + attaches `HeaderBuilder` on `HomePage.prototype`.
    let (_, b_main, _) = add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
    let s_uiab = m.sym.intern("UIAbility");
    let s_form = m.sym.intern("FormExtensionAbility");
    let s_viewpu = m.sym.intern("ViewPU");
    let u_undef = m.consts.push(Const::Undefined);
    let undef = emit_inst_val(&mut m, b_main, Op::LoadConst(u_undef));
    let h_uiab = emit_inst_val(
        &mut m,
        b_main,
        Op::TryGetGlobal {
            name: s_uiab,
            default: Some(undef),
        },
    );
    let h_form = emit_inst_val(
        &mut m,
        b_main,
        Op::TryGetGlobal {
            name: s_form,
            default: Some(undef),
        },
    );
    let h_view = emit_inst_val(
        &mut m,
        b_main,
        Op::TryGetGlobal {
            name: s_viewpu,
            default: Some(undef),
        },
    );

    let s_oc = m.sym.intern("onCreate");
    let s_fg = m.sym.intern("onForeground");
    let s_af = m.sym.intern("onAddForm");
    let s_ata = m.sym.intern("aboutToAppear");
    let s_ir = m.sym.intern("initialRender");
    let s_proto = m.sym.intern("prototype");
    let s_hb = m.sym.intern("HeaderBuilder");

    let c_s_oc = m.consts.intern(Const::String(s_oc));
    let c_oc1 = m.consts.intern(Const::method_ref(on_create1));
    let c_s_fg = m.consts.intern(Const::String(s_fg));
    let c_fg1 = m.consts.intern(Const::method_ref(on_fg1));
    let mem1 = m.consts.push_array(vec![c_s_oc, c_oc1, c_s_fg, c_fg1]);
    let _ = emit_inst_val(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: ctor1,
            heritage: Some(h_uiab),
            members: mem1,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );

    let c_fg2 = m.consts.intern(Const::method_ref(on_fg2));
    let mem2 = m.consts.push_array(vec![c_s_fg, c_fg2]);
    let _ = emit_inst_val(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: ctor2,
            heritage: Some(h_uiab),
            members: mem2,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );

    let c_s_af = m.consts.intern(Const::String(s_af));
    let c_on_add = m.consts.intern(Const::method_ref(on_add));
    let mem3 = m.consts.push_array(vec![c_s_af, c_on_add]);
    let _ = emit_inst_val(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: ctor3,
            heritage: Some(h_form),
            members: mem3,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );

    let c_s_ata = m.consts.intern(Const::String(s_ata));
    let c_about = m.consts.intern(Const::method_ref(about));
    let c_s_ir = m.consts.intern(Const::String(s_ir));
    let c_render = m.consts.intern(Const::method_ref(render));
    let mem4 = m
        .consts
        .push_array(vec![c_s_ata, c_about, c_s_ir, c_render]);
    let home_cls = emit_inst_val(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: ctor4,
            heritage: Some(h_view),
            members: mem4,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    let home_proto = emit_inst_val(
        &mut m,
        b_main,
        Op::LoadProp {
            object: home_cls,
            name: s_proto,
        },
    );
    let df_bd = emit_inst_val(
        &mut m,
        b_main,
        Op::DefineFunc {
            body: builder,
            captures: Vec::new(),
            length: 0,
        },
    );
    let cl_bd = emit_inst_val(&mut m, b_main, Op::AllocClosure { func: df_bd });
    emit_inst_void(
        &mut m,
        b_main,
        Op::StoreProp {
            object: home_proto,
            name: s_hb,
            value: cl_bd,
        },
    );
    emit_inst_void(&mut m, b_main, Op::Return { value: None });

    let manifest =
        r#"{"module":{"abilities":[{"srcEntry":"./ets/entryability/EntryAbility.ets"}]}}"#;
    let entries = parse_manifest_src_entries(manifest);
    assert!(entries.contains("ets/entryability/EntryAbility"));

    let (aug, harness_fid) = synthesize_ohos_harness(&m, Some(manifest)).expect("harness");
    let rep = verify_module(&aug);
    assert!(rep.errors.is_empty(), "verify errors: {:?}", rep.errors);

    let cg = CallGraph::build(&aug);
    for target in [on_create1, on_fg1, on_fg2, on_add, about, render, builder] {
        assert!(
            !cg.callers_of(target).is_empty(),
            "expected harness to call {target:?}"
        );
    }

    // Verify Rung 2 PTA assigns non-overlapping concrete `AllocObject` sites
    // to `EntryAbility.this` vs `SecondAbility.this`.
    let outcome = analyze(
        &aug,
        &cg,
        &PtaConfig {
            harness_func: Some(harness_fid),
            ..PtaConfig::default()
        },
    );
    let (_, tables, stats) = outcome.into_parts();
    let r2 = Rung2AliasOracle::new(&aug, tables, stats);
    let this1 = r2.site_info_at(p_fg1[2], fg1_last);
    let this2 = r2.site_info_at(p_fg2[2], fg2_last);
    assert!(!this1.has_unknown && this1.sites.len() == 1);
    assert!(!this2.has_unknown && this2.sites.len() == 1);
    assert!(!this1.sites.intersects(&this2.sites));
}

#[test]
fn deep_and_cyclic_heritage_loadprop_runs_on_small_stack() {
    const DEPTH: usize = 500;
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut m = Module::new();
            let d = m.sym.intern("L@bundle:com.app/entry/ets/Deep;");
            let n = m.sym.intern("@bundle:com.app/entry/ets/Deep");
            let cid = ClassId::new(0);
            m.classes.push(ClassData::new(d, n));

            let (ctor_deep, b_cd, _) =
                add_fn(&mut m, cid, "DeepComp", FunctionKind::Constructor, 3);
            emit_inst_void(&mut m, b_cd, Op::Return { value: None });
            let (ctor_cyc, b_cc, _) =
                add_fn(&mut m, cid, "CyclicComp", FunctionKind::Constructor, 3);
            emit_inst_void(&mut m, b_cc, Op::Return { value: None });

            let (main_fid, b_main, _) =
                add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
            let s_uiab = m.sym.intern("UIAbility");
            let mut cur = emit_inst_val(
                &mut m,
                b_main,
                Op::TryGetGlobal {
                    name: s_uiab,
                    default: None,
                },
            );
            let s_seg = m.sym.intern("sub");
            for _ in 0..DEPTH {
                cur = emit_inst_val(
                    &mut m,
                    b_main,
                    Op::LoadProp {
                        object: cur,
                        name: s_seg,
                    },
                );
            }
            let deep_chain = cur;
            let deep_heritage = emit_inst_val(
                &mut m,
                b_main,
                Op::LoadProp {
                    object: cur,
                    name: s_uiab,
                },
            );
            let empty_mem = m.consts.push_array(Vec::new());
            let _ = emit_inst_val(
                &mut m,
                b_main,
                Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                    ctor: ctor_deep,
                    heritage: Some(deep_heritage),
                    members: empty_mem,
                    member_attrs: Vec::new(),
                    count: 0,
                })),
            );

            // Cyclic `LoadProp` chain (`v_cyc = LoadProp(v_cyc, "sub")`):
            // must terminate cleanly as `None` via the cycle guard.
            let cyc_iid = InstId::new(m.insts.len() as u32);
            let cyc_vid = ValueId::new(m.values.len() as u32);
            m.insts.push(Inst {
                op: Op::LoadProp {
                    object: cyc_vid,
                    name: s_seg,
                },
                result: Some(cyc_vid),
                block: b_main,
                loc: None,
            });
            m.values.push(Value {
                def: ValueDef::Inst(cyc_iid),
                ty: Ty::Any,
            });
            m.blocks[b_main.index()].insts.push(cyc_iid);
            let _ = emit_inst_val(
                &mut m,
                b_main,
                Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                    ctor: ctor_cyc,
                    heritage: Some(cyc_vid),
                    members: empty_mem,
                    member_attrs: Vec::new(),
                    count: 0,
                })),
            );
            emit_inst_void(&mut m, b_main, Op::Return { value: None });

            let links = ModuleLinkTable::build(&m);
            let full_name =
                resolve_heritage_name(&m, &links, main_fid, deep_chain).expect("deep chain");
            assert!(full_name.starts_with("UIAbility.sub."));
            assert_eq!(full_name.matches(".sub").count(), DEPTH);
            assert!(resolve_heritage_name(&m, &links, main_fid, cyc_vid).is_none());

            let comps = discover_components(&m, &links, None);
            assert_eq!(comps.len(), 1);
            assert_eq!(comps[0].ctor, ctor_deep);
            assert_eq!(comps[0].kind, OhosComponentKind::Ability);
        })
        .expect("spawn");
    handle.join().expect("small stack must not overflow");
}

#[test]
fn standalone_global_at_class1_with_stub_class0_preserves_esm_after_harness() {
    use abcd_ir::module::{ImportDecl, ModuleRequest};
    use abcd_ir::op::ModuleVarKind;

    let mut m = Module::new();
    // ClassId(0): empty stub class `"LA;"`
    let d_stub = m.sym.intern("LA;");
    let n_stub = m.sym.intern("A");
    m.classes.push(ClassData::new(d_stub, n_stub));

    // ClassId(1): standalone `"L_GLOBAL;"` with module-level SDK import
    let d_glob = m.sym.intern("L_GLOBAL;");
    let n_glob = m.sym.intern("_GLOBAL");
    let cid_glob = ClassId::new(1);
    m.classes.push(ClassData::new(d_glob, n_glob));

    let s_uiab = m.sym.intern("UIAbility");
    let s_kit = m.sym.intern("@kit.AbilityKit");
    m.imports.push(ImportDecl::Regular {
        local_name: s_uiab,
        import_name: s_uiab,
        module_request: s_kit,
    });
    m.module_requests.push(ModuleRequest {
        specifier: s_kit,
        lazy: false,
    });

    let (ctor, b_ctor, _) = add_fn(&mut m, cid_glob, "MyAbility", FunctionKind::Constructor, 3);
    emit_inst_void(&mut m, b_ctor, Op::Return { value: None });
    let (on_create, b_oc, _) = add_fn(&mut m, cid_glob, "onCreate", FunctionKind::Function, 5);
    emit_inst_void(&mut m, b_oc, Op::Return { value: None });

    let (_, b_main, _) = add_fn(&mut m, cid_glob, "func_main_0", FunctionKind::Function, 3);
    let h_uiab = emit_inst_val(
        &mut m,
        b_main,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let s_oc = m.sym.intern("onCreate");
    let c_s_oc = m.consts.intern(Const::String(s_oc));
    let c_oc = m.consts.intern(Const::method_ref(on_create));
    let mem = m.consts.push_array(vec![c_s_oc, c_oc]);
    let _ = emit_inst_val(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor,
            heritage: Some(h_uiab),
            members: mem,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    emit_inst_void(&mut m, b_main, Op::Return { value: None });

    let mut m_inplace = m.clone();
    let mut links_inplace = ModuleLinkTable::build(&m_inplace);
    assert!(links_inplace.external_load(cid_glob, 0).is_some());

    let (aug, harness_fid) = synthesize_ohos_harness(&m, None).expect("harness synthesized");
    assert_eq!(aug.func(harness_fid).unwrap().class_id, cid_glob);
    assert!(aug.classes[0].methods.is_empty());
    assert!(crate::module_link::is_standalone_single_module(
        &aug,
        Some(harness_fid)
    ));

    let links_after = ModuleLinkTable::build_with_harness(&aug, Some(harness_fid));
    let ext = links_after
        .external_load(cid_glob, 0)
        .expect("standalone ESM preserved on L_GLOBAL; after harness synthesis");
    assert_eq!(ext.external_imports, vec![(s_kit, s_uiab)]);

    // Also verify zero-clone two-phase `plan_entry_model` + `EntryPlan::append`
    // + `ModuleLinkTable::extend_appended` produces a structurally identical IR!
    let base_funcs = m_inplace.functions.len();
    let base_blocks = m_inplace.blocks.len();
    let base_insts = m_inplace.insts.len();
    let base_values = m_inplace.values.len();

    let plan = plan_entry_model(&m_inplace, &links_inplace, None);
    assert!(plan.needs_harness());
    let harness = plan.append(&mut m_inplace);
    links_inplace.extend_appended(&m_inplace);

    assert_eq!(harness.func, Some(harness_fid));
    assert_eq!(harness.base_funcs, base_funcs);
    assert_eq!(harness.base_blocks, base_blocks);
    assert_eq!(harness.base_insts, base_insts);
    assert_eq!(harness.base_values, base_values);
    assert_eq!(harness.entry_funcs, vec![harness_fid]);
    assert!(
        crate::module_link::is_standalone_single_module(&m_inplace, harness.func),
        "foreign LA; at ClassId(0) + L_GLOBAL; at ClassId(1) must stay standalone (#76)"
    );
    abcd_ir::modules_structurally_eq(&aug, &m_inplace)
        .expect("EntryPlan::append must match EntryModel::build structurally");
    assert_eq!(links_inplace.func_class(harness_fid), Some(cid_glob));
    assert_eq!(
        links_inplace
            .external_load(cid_glob, 0)
            .unwrap()
            .external_imports,
        vec![(s_kit, s_uiab)]
    );
}

#[test]
fn steady_state_lifecycle_loop_propagates_on_background_write_to_next_on_foreground_read() {
    use crate::dataflow::ifds::{IfdsConfig, IfdsProblem, IfdsSolver};

    let mut m = Module::new();
    let d = m
        .sym
        .intern("L@bundle:com.app/entry/ets/entryability/EntryAbility;");
    let n = m
        .sym
        .intern("@bundle:com.app/entry/ets/entryability/EntryAbility");
    let cid = ClassId::new(0);
    m.classes.push(ClassData::new(d, n));

    let s_cached = m.sym.intern("cachedSecret");
    let s_uiab = m.sym.intern("UIAbility");
    let s_bg = m.sym.intern("onBackground");
    let s_fg = m.sym.intern("onForeground");
    let s_destroy = m.sym.intern("onDestroy");

    let (ctor, b_c, _) = add_fn(&mut m, cid, "EntryAbility", FunctionKind::Constructor, 3);
    emit_inst_void(&mut m, b_c, Op::Return { value: None });

    // `onBackground`: `this.cachedSecret = "secret"`
    let (on_bg, b_bg, p_bg) = add_fn(&mut m, cid, "onBackground", FunctionKind::Function, 3);
    let s_secret = m.sym.intern("secret");
    let c_secret = m.consts.intern(Const::String(s_secret));
    let v_secret = emit_inst_val(&mut m, b_bg, Op::LoadConst(c_secret));
    let bg_store_iid = InstId::new(m.insts.len() as u32);
    emit_inst_void(
        &mut m,
        b_bg,
        Op::StoreProp {
            object: p_bg[2],
            name: s_cached,
            value: v_secret,
        },
    );
    emit_inst_void(&mut m, b_bg, Op::Return { value: None });

    // `onForeground`: `let x = this.cachedSecret; sink(x)`
    // In a single linear pass (`onForeground -> onBackground -> onDestroy`),
    // `onForeground` ran ONLY BEFORE `onBackground` and missed `this.cachedSecret`!
    let sink_sym = m.sym.intern("sink");
    let sink_fid = FuncId::new(m.functions.len() as u32);
    let mut sink_fd = FunctionData::new(cid, sink_sym, FunctionKind::Function);
    sink_fd.is_external = true;
    m.functions.push(sink_fd);
    m.classes[cid.index()].methods.push(sink_fid);

    let (on_fg, b_fg, p_fg) = add_fn(&mut m, cid, "onForeground", FunctionKind::Function, 3);
    let fg_load_iid = InstId::new(m.insts.len() as u32);
    let loaded = emit_inst_val(
        &mut m,
        b_fg,
        Op::LoadProp {
            object: p_fg[2],
            name: s_cached,
        },
    );
    let callee_sink = const_method_ref_val(&mut m, sink_fid);
    let sink_call = InstId::new(m.insts.len() as u32);
    let _ = emit_inst_val(
        &mut m,
        b_fg,
        Op::Call {
            callee: callee_sink,
            this: None,
            args: vec![loaded],
            kind: CallKind::Direct,
        },
    );
    emit_inst_void(&mut m, b_fg, Op::Return { value: None });

    // `onDestroy` teardown hook.
    let (on_destroy, b_dt, _) = add_fn(&mut m, cid, "onDestroy", FunctionKind::Function, 3);
    let dt_ret = InstId::new(m.insts.len() as u32);
    emit_inst_void(&mut m, b_dt, Op::Return { value: None });

    let (_, b_main, _) = add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
    let h_uiab = emit_inst_val(
        &mut m,
        b_main,
        Op::TryGetGlobal {
            name: s_uiab,
            default: None,
        },
    );
    let c_s_bg = m.consts.intern(Const::String(s_bg));
    let c_bg = m.consts.intern(Const::method_ref(on_bg));
    let c_s_fg = m.consts.intern(Const::String(s_fg));
    let c_fg = m.consts.intern(Const::method_ref(on_fg));
    let c_s_dt = m.consts.intern(Const::String(s_destroy));
    let c_dt = m.consts.intern(Const::method_ref(on_destroy));
    let mem = m
        .consts
        .push_array(vec![c_s_fg, c_fg, c_s_bg, c_bg, c_s_dt, c_dt]);
    let _ = emit_inst_val(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor,
            heritage: Some(h_uiab),
            members: mem,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    emit_inst_void(&mut m, b_main, Op::Return { value: None });

    let model = EntryModel::build(&m, None);
    let harness_fid = model.harness_func.expect("harness synthesized");
    assert_eq!(model.entry_funcs, vec![harness_fid]);
    let aug = model.augmented_module.as_ref().expect("augmented module");
    let rep = verify_module(aug);
    assert!(rep.errors.is_empty(), "verify errors: {:?}", rep.errors);

    let base_cg = CallGraph::build(aug);
    let (cg, tables, stats) = analyze(
        aug,
        &base_cg,
        &PtaConfig {
            harness_func: Some(harness_fid),
            ..PtaConfig::default()
        },
    )
    .into_parts();
    let r2 = Rung2AliasOracle::new(aug, tables, stats);
    let bg_sites = r2.query(p_bg[2], bg_store_iid).sites;
    let fg_sites = r2.query(p_fg[2], fg_load_iid).sites;
    assert_eq!(bg_sites.len(), 1);
    assert_eq!(bg_sites, fg_sites);
    let recv_site = bg_sites.iter().next().unwrap();

    // Run IFDS over the synthesized harness: `onBackground` taints
    // `(recv_site, cachedSecret)`, which loops around `while (*)` into the
    // next `onForeground` (`sink_call`) AND reaches `onDestroy` (`dt_ret`)!
    #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
    enum LfFact {
        Zero,
        Val(ValueId),
        HeapCached(InstId),
    }

    struct LfProblem {
        harness: FuncId,
        bg_store: InstId,
        fg_load: InstId,
        loaded_val: ValueId,
        recv_site: InstId,
    }

    impl IfdsProblem for LfProblem {
        type Fact = LfFact;

        fn zero(&self) -> LfFact {
            LfFact::Zero
        }

        fn initial_seeds(&self) -> Vec<(FuncId, LfFact)> {
            vec![(self.harness, LfFact::Zero)]
        }

        fn normal_flow(
            &self,
            _module: &Module,
            curr: InstId,
            _succ: InstId,
            source: &LfFact,
            out: &mut Vec<LfFact>,
        ) {
            match *source {
                LfFact::Zero => {
                    if curr == self.bg_store {
                        out.push(LfFact::HeapCached(self.recv_site));
                    }
                }
                LfFact::HeapCached(site) => {
                    out.push(LfFact::HeapCached(site));
                    if curr == self.fg_load && site == self.recv_site {
                        out.push(LfFact::Val(self.loaded_val));
                    }
                }
                LfFact::Val(v) => out.push(LfFact::Val(v)),
            }
        }

        fn call_flow(
            &self,
            _module: &Module,
            _call: InstId,
            _callee: FuncId,
            source: &LfFact,
            out: &mut Vec<LfFact>,
        ) {
            if let LfFact::HeapCached(s) = *source {
                out.push(LfFact::HeapCached(s));
            }
        }

        fn return_flow(
            &self,
            _module: &Module,
            _call_site: Option<InstId>,
            _callee: FuncId,
            _exit: InstId,
            _return_site: Option<InstId>,
            source: &LfFact,
            out: &mut Vec<LfFact>,
        ) {
            if let LfFact::HeapCached(s) = *source {
                out.push(LfFact::HeapCached(s));
            }
        }

        fn call_to_return_flow(
            &self,
            module: &Module,
            call: InstId,
            _return_site: InstId,
            source: &LfFact,
            out: &mut Vec<LfFact>,
        ) {
            match *source {
                LfFact::Zero => {}
                LfFact::Val(v) => out.push(LfFact::Val(v)),
                LfFact::HeapCached(s) => {
                    // Resolved internal calls propagate heap facts through callee;
                    // external `sink` bypasses.
                    let is_ext_call =
                        matches!(module.inst(call).map(|i| &i.op), Some(Op::Call { .. }))
                            && module
                                .inst(call)
                                .is_some_and(|_| call == InstId::new(999_999));
                    let _ = is_ext_call;
                    out.push(LfFact::HeapCached(s));
                }
            }
        }
    }

    let prob = LfProblem {
        harness: harness_fid,
        bg_store: bg_store_iid,
        fg_load: fg_load_iid,
        loaded_val: loaded,
        recv_site,
    };
    let res = IfdsSolver::new(aug, &prob, &cg, IfdsConfig::default()).solve();
    assert!(
        res.is_reached(sink_call, &LfFact::Val(loaded)),
        "state written in onBackground must flow around steady-state loop to next onForeground"
    );
    assert!(
        res.is_reached(dt_ret, &LfFact::HeapCached(recv_site)),
        "steady-state loop exit must reach teardown onDestroy"
    );
}

#[test]
fn out_of_bounds_class_and_func_ids_do_not_panic() {
    let mut m = Module::new();
    let d = m.sym.intern("L_GLOBAL;");
    let n = m.sym.intern("_GLOBAL");
    m.classes.push(ClassData::new(d, n));

    // Function with out-of-bounds `class_id = ClassId(999)` and `DefineClass`
    // referencing out-of-bounds `ctor = FuncId(999)`.
    let sym = m.sym.intern("func_main_0");
    let mut fd = FunctionData::new(ClassId::new(999), sym, FunctionKind::Function);
    let b = BlockId::new(0);
    m.blocks.push(Block::default());
    fd.blocks.push(b);
    m.functions.push(fd);

    let s_uiab = m.sym.intern("UIAbility");
    let h = emit_inst_val(
        &mut m,
        b,
        Op::TryGetGlobal {
            name: s_uiab,
            default: None,
        },
    );
    let empty_mem = m.consts.push_array(Vec::new());
    let _ = emit_inst_val(
        &mut m,
        b,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: FuncId::new(999),
            heritage: Some(h),
            members: empty_mem,
            member_attrs: Vec::new(),
            count: 0,
        })),
    );
    emit_inst_void(&mut m, b, Op::Return { value: None });

    let model = EntryModel::build(&m, Some(r#"{"srcEntry":"./ets/EntryAbility.ets"}"#));
    assert!(model.components.is_empty());
    assert!(synthesize_ohos_harness(&m, None).is_none());

    let links = ModuleLinkTable::build(&m);
    let plan = plan_entry_model(&m, &links, None);
    assert!(!plan.needs_harness());
    let noop = plan.into_noop_harness(&m);
    assert!(noop.func.is_none());
    assert_eq!(noop.base_funcs, m.functions.len());
    assert_eq!(noop.entry_funcs, model.entry_funcs);
}

#[test]
fn decoy_user_function_named_ohos_harness_does_not_spoof_entry_plan() {
    let mut m = Module::new();
    let d_glob = m.sym.intern("L_GLOBAL;");
    let n_glob = m.sym.intern("_GLOBAL");
    m.classes.push(ClassData::new(d_glob, n_glob));
    let d_user = m.sym.intern("LUserRecord;");
    let n_user = m.sym.intern("UserRecord");
    m.classes.push(ClassData::new(d_user, n_user));

    let (f_main, b_main, _) = add_fn(
        &mut m,
        ClassId::new(0),
        "func_main_0",
        FunctionKind::Function,
        3,
    );
    emit_inst_void(&mut m, b_main, Op::Return { value: None });

    // User-authored function literally named `"__abcd_ohos_harness__"` on `ClassId(1)`.
    let (f_decoy, b_decoy, _) = add_fn(
        &mut m,
        ClassId::new(1),
        OHOS_HARNESS_FUNC,
        FunctionKind::Function,
        3,
    );
    emit_inst_void(&mut m, b_decoy, Op::Return { value: None });

    assert!(
        !crate::module_link::is_standalone_single_module(&m, None),
        "decoy __abcd_ohos_harness__ on ClassId(1) is a real user method (#75)"
    );
    let links = ModuleLinkTable::build(&m);
    let plan = plan_entry_model(&m, &links, None);
    assert!(!plan.needs_harness());
    let noop = plan.into_noop_harness(&m);
    assert!(noop.func.is_none());
    assert_eq!(noop.entry_funcs, vec![f_main]);
    assert_eq!(links.func_class(f_decoy), Some(ClassId::new(1)));
}
