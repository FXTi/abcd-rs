//! Regression tests for Issue `#104` (`P3-ANA-1`..`P3-ANA-3`):
//! - `P3-ANA-1`: Root-sliced Rung-2 PTA soundness when a non-root helper may
//!   execute from an unrecorded caller (`!base_scanned[helper]`).
//! - `P3-ANA-2`: Rung-2 PTA numeric `Slot::Named` ↔ `Slot::Index` /
//!   `Ptr::GlobalDynamic` aliasing across all statement orderings.
//! - `P3-ANA-3`: `Rung0AliasOracle::with_links_and_graph` and
//!   `Rung1AliasOracle::with_links` after `module.sym.drop_index()` +
//!   `harness_func`, `Rung1` `new C()` returning `Phi(cachedObj, undefined)`,
//!   `CallGraph::refine_with_points_to` keeping class/object-literal methods
//!   open, barrel re-export pre-indexing, and 32-bit `EdgeCsr` `u32::MAX`
//!   bounds safety.

use crate::common::*;
use abcd_analysis::callgraph::{CallGraph, CallTargets};
use abcd_analysis::dataflow::alias::Rung1AliasOracle;
use abcd_analysis::dataflow::heap::Rung0AliasOracle;
use abcd_analysis::dataflow::ifds::{IfdsConfig, IfdsProblem, IfdsSolver};
use abcd_analysis::dataflow::pta::{PtaConfig, Rung2AliasOracle, analyze_with_links_and_roots};
use abcd_analysis::module_link::ModuleLinkTable;
use abcd_ir::module::{ClassData, EsModule, ExportDecl, FunctionKind, ImportDecl, ModuleRequest};
use abcd_ir::op::ModuleVarKind;
use abcd_ir::{
    CallKind, ClassId, Const, DefineClassData, Edge, EdgeKind, FuncId, InstId, LexEnvKind, Module,
    Op,
};

#[test]
fn root_sliced_pta_unscanned_base_ctx_soundness() {
    let mut m = mk_module();

    let (cb_root_fn, _) = add_static_func(&mut m, "cb_root", 0);
    {
        let b = entry_of(&m, cb_root_fn);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let (cb_unrec_fn, _) = add_static_func(&mut m, "cb_unrec", 0);
    {
        let b = entry_of(&m, cb_unrec_fn);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let (cb_closed_fn, _) = add_static_func(&mut m, "cb_closed", 0);
    {
        let b = entry_of(&m, cb_closed_fn);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Shared `helper(obj, cb)` called by BOTH `root` (in `roots`) and
    // `unrecorded_caller` (outside `roots`).
    let (helper, h_params) = add_static_func(&mut m, "helper", 2);
    let h_obj = h_params[3];
    let h_cb = h_params[4];
    let (h_lex_val, h_lex_iid, h_cb_call_iid);
    {
        let b = entry_of(&m, helper);
        let _ = emit(
            &mut m,
            b,
            Op::NewLexEnv {
                num_vars: 1,
                kind: LexEnvKind::Plain,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: h_obj,
                kind: LexEnvKind::Plain,
            },
        );
        h_lex_val = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: LexEnvKind::Plain,
            },
        );
        h_lex_iid = inst_of(&m, h_lex_val);
        let cb_res = emit(
            &mut m,
            b,
            Op::Call {
                callee: h_cb,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        h_cb_call_iid = inst_of(&m, cb_res);
        emit_void(&mut m, b, Op::PopLexEnv);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Control `closed_helper(obj, cb)` called ONLY by `root`.
    let (closed_helper, ch_params) = add_static_func(&mut m, "closed_helper", 2);
    let ch_obj = ch_params[3];
    let ch_cb = ch_params[4];
    let (ch_lex_val, ch_lex_iid, ch_cb_call_iid);
    {
        let b = entry_of(&m, closed_helper);
        let _ = emit(
            &mut m,
            b,
            Op::NewLexEnv {
                num_vars: 1,
                kind: LexEnvKind::Plain,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: ch_obj,
                kind: LexEnvKind::Plain,
            },
        );
        ch_lex_val = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: LexEnvKind::Plain,
            },
        );
        ch_lex_iid = inst_of(&m, ch_lex_val);
        let cb_res = emit(
            &mut m,
            b,
            Op::Call {
                callee: ch_cb,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        ch_cb_call_iid = inst_of(&m, cb_res);
        emit_void(&mut m, b, Op::PopLexEnv);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let (root, _) = add_static_func(&mut m, "root", 0);
    let root_obj;
    {
        let b = entry_of(&m, root);
        root_obj = alloc_object(&mut m, b);
        let cb1 = closure_of(&mut m, b, cb_root_fn);
        let h_ref = const_value(&mut m, Const::method_ref(helper));
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: h_ref,
                this: None,
                args: vec![root_obj, cb1],
                kind: CallKind::Direct,
            },
        );
        let closed_obj = alloc_object(&mut m, b);
        let cb_closed = closure_of(&mut m, b, cb_closed_fn);
        let ch_ref = const_value(&mut m, Const::method_ref(closed_helper));
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: ch_ref,
                this: None,
                args: vec![closed_obj, cb_closed],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Outside `roots`: calls `helper(other_obj, cb_unrec)`.
    let (unrecorded_caller, _) = add_static_func(&mut m, "unrecorded_caller", 0);
    {
        let b = entry_of(&m, unrecorded_caller);
        let other_obj = alloc_object(&mut m, b);
        let cb2 = closure_of(&mut m, b, cb_unrec_fn);
        let h_ref = const_value(&mut m, Const::method_ref(helper));
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: h_ref,
                this: None,
                args: vec![other_obj, cb2],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let links = ModuleLinkTable::build(&m);
    let base = CallGraph::build_with_links(&m, &links);
    let out = analyze_with_links_and_roots(&m, &links, &base, &PtaConfig::default(), Some(&[root]));
    let (graph, tables, stats) = out.into_parts();
    assert!(stats.root_sliced, "unrecorded_caller is outside roots");

    let oracle = Rung2AliasOracle::new(&m, tables, stats);

    // 1. Open `helper`: `(helper, PackedCtx::NONE)` never ran, while
    //    `unrecorded_caller` may invoke `helper` at runtime — `obj` and
    //    `GetLexVar` MUST report `has_unknown == true`, and `cb()` MUST report
    //    `resolution_complete == false`.
    assert!(oracle.query(h_obj, h_cb_call_iid).has_unknown);
    assert!(oracle.site_info_at(h_obj, h_cb_call_iid).has_unknown);
    assert!(oracle.query(h_lex_val, h_lex_iid).has_unknown);
    assert!(oracle.site_info_at(h_lex_val, h_lex_iid).has_unknown);

    let open_edge = graph.edge_at(h_cb_call_iid).expect("helper cb() edge");
    assert_eq!(open_edge.targets, CallTargets::Resolved(vec![cb_root_fn]));
    assert!(
        !open_edge.resolution_complete,
        "unscanned unrecorded caller must keep cb() incomplete: {open_edge:?}"
    );
    let _ = root_obj;

    // 2. Closed `closed_helper`: called exclusively from `root`, so precision
    //    is preserved (`has_unknown == false`, `resolution_complete == true`).
    assert!(!oracle.site_info_at(ch_obj, ch_cb_call_iid).has_unknown);
    assert!(!oracle.site_info_at(ch_lex_val, ch_lex_iid).has_unknown);
    let closed_edge = graph
        .edge_at(ch_cb_call_iid)
        .expect("closed_helper cb() edge");
    assert_eq!(
        closed_edge.targets,
        CallTargets::Resolved(vec![cb_closed_fn])
    );
    assert!(closed_edge.resolution_complete);
}

#[test]
fn rung2_pta_numeric_named_and_index_aliasing_all_combinations() {
    let mut m = mk_module();
    let mut target_fns = Vec::new();
    for i in 0..6 {
        let (f, _) = add_static_func(&mut m, &format!("fn_{i}"), 0);
        let b = entry_of(&m, f);
        emit_void(&mut m, b, Op::Return { value: None });
        target_fns.push(f);
    }
    let [f1, f2, f3, f_nan, f_neg, f_glob] = target_fns.try_into().expect("6 funcs");

    let (main, _) = add_static_func(&mut m, "func_main_0", 0);
    let b = entry_of(&m, main);
    let sym_zero = intern(&mut m, "0");
    let sym_foo = intern(&mut m, "foo");
    let sym_nan = intern(&mut m, "NaN");
    let sym_neg = intern(&mut m, "-1");
    let idx_zero = load_number(&mut m, b, 0.0);

    let c1 = closure_of(&mut m, b, f1);
    let c2 = closure_of(&mut m, b, f2);
    let c3 = closure_of(&mut m, b, f3);
    let c_nan = closure_of(&mut m, b, f_nan);
    let c_neg = closure_of(&mut m, b, f_neg);
    let c_glob = closure_of(&mut m, b, f_glob);

    let emit_dyn_call = |m: &mut Module, b, callee| {
        let r = emit(
            m,
            b,
            Op::Call {
                callee,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        inst_of(m, r)
    };

    // 1a. StoreProp("0", f1) -> LoadPropIdx(0)
    let o_a = alloc_object(&mut m, b);
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: o_a,
            name: sym_zero,
            value: c1,
        },
    );
    let l_a = emit(
        &mut m,
        b,
        Op::LoadPropIdx {
            object: o_a,
            index: idx_zero,
        },
    );
    let call_a = emit_dyn_call(&mut m, b, l_a);

    // 1b. Reverse registration order: LoadPropIdx(0) BEFORE StoreProp("0", f1)
    let o_a_rev = alloc_object(&mut m, b);
    let l_a_rev = emit(
        &mut m,
        b,
        Op::LoadPropIdx {
            object: o_a_rev,
            index: idx_zero,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: o_a_rev,
            name: sym_zero,
            value: c1,
        },
    );
    let call_a_rev = emit_dyn_call(&mut m, b, l_a_rev);

    // 2a. StorePropIdx(0, f2) -> LoadProp("0")
    let o_b = alloc_object(&mut m, b);
    emit_void(
        &mut m,
        b,
        Op::StorePropIdx {
            object: o_b,
            index: idx_zero,
            value: c2,
        },
    );
    let l_b = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: o_b,
            name: sym_zero,
        },
    );
    let call_b = emit_dyn_call(&mut m, b, l_b);

    // 2b. Reverse registration order: LoadProp("0") BEFORE StorePropIdx(0, f2)
    let o_b_rev = alloc_object(&mut m, b);
    let l_b_rev = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: o_b_rev,
            name: sym_zero,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::StorePropIdx {
            object: o_b_rev,
            index: idx_zero,
            value: c2,
        },
    );
    let call_b_rev = emit_dyn_call(&mut m, b, l_b_rev);

    // 3 & 4. Combined `obj["0"] = f1; obj[0] = f2; obj["foo"] = f3;`
    let o_mix = alloc_object(&mut m, b);
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: o_mix,
            name: sym_zero,
            value: c1,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::StorePropIdx {
            object: o_mix,
            index: idx_zero,
            value: c2,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: o_mix,
            name: sym_foo,
            value: c3,
        },
    );
    let l_mix_named = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: o_mix,
            name: sym_zero,
        },
    );
    let call_mix_named = emit_dyn_call(&mut m, b, l_mix_named);
    let l_mix_idx = emit(
        &mut m,
        b,
        Op::LoadPropIdx {
            object: o_mix,
            index: idx_zero,
        },
    );
    let call_mix_idx = emit_dyn_call(&mut m, b, l_mix_idx);
    let l_mix_foo = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: o_mix,
            name: sym_foo,
        },
    );
    let call_mix_foo = emit_dyn_call(&mut m, b, l_mix_foo);

    // 5. Special numeric keys (`"NaN"`, `"-1"`) and `globalThis["0"] -> globalThis[0]`.
    let o_spec = alloc_object(&mut m, b);
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: o_spec,
            name: sym_nan,
            value: c_nan,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: o_spec,
            name: sym_neg,
            value: c_neg,
        },
    );
    let l_spec_idx = emit(
        &mut m,
        b,
        Op::LoadPropIdx {
            object: o_spec,
            index: idx_zero,
        },
    );
    let call_spec_idx = emit_dyn_call(&mut m, b, l_spec_idx);

    let g_obj = emit(&mut m, b, Op::LoadGlobalObject);
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: g_obj,
            name: sym_zero,
            value: c_glob,
        },
    );
    let l_glob_idx = emit(
        &mut m,
        b,
        Op::LoadPropIdx {
            object: g_obj,
            index: idx_zero,
        },
    );
    let call_glob_idx = emit_dyn_call(&mut m, b, l_glob_idx);
    emit_void(&mut m, b, Op::Return { value: None });

    let links = ModuleLinkTable::build(&m);
    let base = CallGraph::build_with_links(&m, &links);
    let out = analyze_with_links_and_roots(&m, &links, &base, &PtaConfig::default(), None);
    let cg = out.graph();

    for cid in [call_a, call_a_rev] {
        let e = cg.edge_at(cid).unwrap();
        assert_eq!(e.targets, CallTargets::Resolved(vec![f1]));
        assert!(e.resolution_complete);
    }
    for cid in [call_b, call_b_rev] {
        let e = cg.edge_at(cid).unwrap();
        assert_eq!(e.targets, CallTargets::Resolved(vec![f2]));
        assert!(e.resolution_complete);
    }
    for cid in [call_mix_named, call_mix_idx] {
        let e = cg.edge_at(cid).unwrap();
        assert_eq!(e.targets, CallTargets::Resolved(vec![f1, f2]));
        assert!(e.resolution_complete);
    }
    let e_foo = cg.edge_at(call_mix_foo).unwrap();
    assert_eq!(e_foo.targets, CallTargets::Resolved(vec![f3]));
    assert!(e_foo.resolution_complete);

    let e_spec = cg.edge_at(call_spec_idx).unwrap();
    assert_eq!(e_spec.targets, CallTargets::Resolved(vec![f_nan, f_neg]));
    assert!(e_spec.resolution_complete);

    let e_glob = cg.edge_at(call_glob_idx).unwrap();
    assert_eq!(e_glob.targets, CallTargets::Resolved(vec![f_glob]));
    assert!(
        !e_glob.resolution_complete,
        "globalThis[0] keeps unknown floor"
    );
}

#[test]
fn with_links_constructors_after_drop_index_and_with_harness_func() {
    let mut m = Module::new();
    let s_shared = m.sym.intern("sharedObj");
    let req_a = m.sym.intern("./mod_a");

    let cid_a = ClassId::new(0);
    let mut cls_a = ClassData::new(m.sym.intern("Lmod_a;"), m.sym.intern("mod_a"));
    cls_a.es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![ExportDecl::Local {
            local_name: s_shared,
            export_name: s_shared,
        }],
        module_requests: Vec::new(),
    });
    m.classes.push(cls_a);

    let cid_b = ClassId::new(1);
    let mut cls_b = ClassData::new(m.sym.intern("Lmod_b;"), m.sym.intern("mod_b"));
    cls_b.es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: s_shared,
            import_name: s_shared,
            module_request: req_a,
        }],
        exports: Vec::new(),
        module_requests: vec![ModuleRequest {
            specifier: req_a,
            lazy: false,
        }],
    });
    m.classes.push(cls_b);

    let mk_rec_fn = |m: &mut Module, cid: ClassId, name: &str| {
        let sym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = abcd_ir::FunctionData::new(cid, sym, FunctionKind::Function);
        fd.modifiers = abcd_ir::Modifiers::STATIC;
        m.functions.push(fd);
        m.classes[cid.index()].methods.push(fid);
        let b = add_block(m, fid);
        for i in 0..3 {
            add_param(m, fid, i);
        }
        (fid, b)
    };

    let (main_a, b_a) = mk_rec_fn(&mut m, cid_a, "func_main_0");
    let exp_obj = alloc_object(&mut m, b_a);
    let exp_site = inst_of(&m, exp_obj);
    emit_void(
        &mut m,
        b_a,
        Op::StoreModuleVar {
            index: 0,
            value: exp_obj,
        },
    );
    emit_void(&mut m, b_a, Op::Return { value: None });

    let (main_b, b_b) = mk_rec_fn(&mut m, cid_b, "func_main_0");
    let imp_val = emit(
        &mut m,
        b_b,
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::External,
        },
    );
    let imp_iid = inst_of(&m, imp_val);
    emit_void(&mut m, b_b, Op::Return { value: None });

    // `steady_hook` called inside a `while (*)` loop of `harness_func`: its
    // allocation is NOT a concrete singleton when `harness_func` is honored,
    // whereas `once_helper` called once before the loop IS a concrete singleton.
    let (once_helper, b_once) = mk_rec_fn(&mut m, cid_b, "once_helper");
    let once_obj = alloc_object(&mut m, b_once);
    let once_site = inst_of(&m, once_obj);
    emit_void(&mut m, b_once, Op::Return { value: None });

    let (steady_hook, b_steady) = mk_rec_fn(&mut m, cid_b, "steady_hook");
    let steady_obj = alloc_object(&mut m, b_steady);
    let steady_site = inst_of(&m, steady_obj);
    emit_void(&mut m, b_steady, Op::Return { value: None });

    let (harness_func, b_h_entry) = mk_rec_fn(&mut m, cid_b, "__abcd_ohos_harness__");
    let b_h_loop = add_block(&mut m, harness_func);
    let b_h_exit = add_block(&mut m, harness_func);
    for init_fn in [main_a, main_b, once_helper] {
        let mr = load_method_ref(&mut m, b_h_entry, init_fn);
        let _ = emit(
            &mut m,
            b_h_entry,
            Op::Call {
                callee: mr,
                this: None,
                args: vec![],
                kind: CallKind::Direct,
            },
        );
    }
    emit_void(&mut m, b_h_entry, Op::Branch { dest: b_h_loop });
    link(&mut m, b_h_entry, b_h_loop);

    let mr_steady = load_method_ref(&mut m, b_h_loop, steady_hook);
    let _ = emit(
        &mut m,
        b_h_loop,
        Op::Call {
            callee: mr_steady,
            this: None,
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    let cond = load_number(&mut m, b_h_loop, 1.0);
    emit_void(
        &mut m,
        b_h_loop,
        Op::CondBranch {
            cond,
            true_dest: b_h_loop,
            false_dest: b_h_exit,
        },
    );
    link(&mut m, b_h_loop, b_h_loop);
    link(&mut m, b_h_loop, b_h_exit);
    emit_void(&mut m, b_h_exit, Op::Return { value: None });

    let links = ModuleLinkTable::build_with_harness(&m, Some(harness_func));
    let base = CallGraph::build_with_links(&m, &links);

    // Drop the symbol deduplication hash index BEFORE constructing Rung 0 & Rung 1.
    m.sym.drop_index();
    assert!(!m.sym.has_index());

    let r0 = Rung0AliasOracle::with_links_and_graph(&m, &links, &base, Some(harness_func));
    let r1 = Rung1AliasOracle::with_links(&m, &base, &links, Some(harness_func));
    let r1_bounded =
        Rung1AliasOracle::with_links_and_max_depth(&m, &base, &links, Some(harness_func), 4);
    assert!(!m.sym.has_index(), "no symbol-table index rebuild occurred");

    assert!(r0.is_concrete_singleton_site(exp_site));
    assert!(r0.is_concrete_singleton_site(once_site));
    assert!(!r0.is_concrete_singleton_site(steady_site));

    assert!(r1.is_concrete_singleton_site(exp_site));
    assert!(r1.is_concrete_singleton_site(once_site));
    assert!(!r1.is_concrete_singleton_site(steady_site));

    let imp_info = r1.site_info_at(imp_val, imp_iid);
    assert!(imp_info.is_single_precise(), "{imp_info:?}");
    assert_eq!(imp_info.sites.as_slice(), &[exp_site]);
    assert_eq!(r1_bounded.site_info_at(imp_val, imp_iid), imp_info);
}

#[test]
fn rung1_new_ctor_returning_phi_cached_and_undefined_retains_both_sites() {
    let mut m = mk_module();

    // Case 1: `CtorConst` returns `Phi(cached_obj, ValueDef::Const(Undefined))`.
    let (ctor_const, _) = add_static_func(&mut m, "CtorConst", 0);
    let cached_const_site;
    {
        let b_entry = entry_of(&m, ctor_const);
        let b_hit = add_block(&mut m, ctor_const);
        let b_miss = add_block(&mut m, ctor_const);
        let b_join = add_block(&mut m, ctor_const);
        let cond = load_number(&mut m, b_entry, 1.0);
        emit_void(
            &mut m,
            b_entry,
            Op::CondBranch {
                cond,
                true_dest: b_hit,
                false_dest: b_miss,
            },
        );
        let cached = alloc_object(&mut m, b_hit);
        cached_const_site = inst_of(&m, cached);
        let undef_cv = const_value(&mut m, Const::Undefined);
        emit_void(&mut m, b_hit, Op::Branch { dest: b_join });
        emit_void(&mut m, b_miss, Op::Branch { dest: b_join });
        link(&mut m, b_entry, b_hit);
        link(&mut m, b_entry, b_miss);
        link(&mut m, b_hit, b_join);
        link(&mut m, b_miss, b_join);
        let phi = emit(
            &mut m,
            b_join,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: b_hit,
                            kind: EdgeKind::Normal,
                        },
                        cached,
                    ),
                    (
                        Edge {
                            from: b_miss,
                            kind: EdgeKind::Normal,
                        },
                        undef_cv,
                    ),
                ],
            },
        );
        emit_void(&mut m, b_join, Op::Return { value: Some(phi) });
    }

    // Case 2: `CtorLoadConst` returns `Phi(cached_obj, LoadConst(Undefined))`.
    let (ctor_lc, _) = add_static_func(&mut m, "CtorLoadConst", 0);
    let cached_lc_site;
    {
        let b_entry = entry_of(&m, ctor_lc);
        let b_hit = add_block(&mut m, ctor_lc);
        let b_miss = add_block(&mut m, ctor_lc);
        let b_join = add_block(&mut m, ctor_lc);
        let cond = load_number(&mut m, b_entry, 1.0);
        emit_void(
            &mut m,
            b_entry,
            Op::CondBranch {
                cond,
                true_dest: b_hit,
                false_dest: b_miss,
            },
        );
        let cached = alloc_object(&mut m, b_hit);
        cached_lc_site = inst_of(&m, cached);
        let undef_cid = push_const(&mut m, Const::Undefined);
        let undef_lc = emit(&mut m, b_miss, Op::LoadConst(undef_cid));
        emit_void(&mut m, b_hit, Op::Branch { dest: b_join });
        emit_void(&mut m, b_miss, Op::Branch { dest: b_join });
        link(&mut m, b_entry, b_hit);
        link(&mut m, b_entry, b_miss);
        link(&mut m, b_hit, b_join);
        link(&mut m, b_miss, b_join);
        let phi = emit(
            &mut m,
            b_join,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: b_hit,
                            kind: EdgeKind::Normal,
                        },
                        cached,
                    ),
                    (
                        Edge {
                            from: b_miss,
                            kind: EdgeKind::Normal,
                        },
                        undef_lc,
                    ),
                ],
            },
        );
        emit_void(&mut m, b_join, Op::Return { value: Some(phi) });
    }

    // Case 3: `CtorViaHelper` returns `maybe_cached()`, where `maybe_cached`
    // has both `Return { value: Some(cached) }` and `Return { value: None }`.
    let (maybe_cached, _) = add_static_func(&mut m, "maybe_cached", 0);
    let cached_helper_site;
    {
        let b_entry = entry_of(&m, maybe_cached);
        let b_hit = add_block(&mut m, maybe_cached);
        let b_miss = add_block(&mut m, maybe_cached);
        let cond = load_number(&mut m, b_entry, 1.0);
        emit_void(
            &mut m,
            b_entry,
            Op::CondBranch {
                cond,
                true_dest: b_hit,
                false_dest: b_miss,
            },
        );
        let cached = alloc_object(&mut m, b_hit);
        cached_helper_site = inst_of(&m, cached);
        emit_void(
            &mut m,
            b_hit,
            Op::Return {
                value: Some(cached),
            },
        );
        emit_void(&mut m, b_miss, Op::Return { value: None });
        link(&mut m, b_entry, b_hit);
        link(&mut m, b_entry, b_miss);
    }
    let (ctor_helper, _) = add_static_func(&mut m, "CtorViaHelper", 0);
    {
        let b = entry_of(&m, ctor_helper);
        let mr = load_method_ref(&mut m, b, maybe_cached);
        let ret = emit(
            &mut m,
            b,
            Op::Call {
                callee: mr,
                this: None,
                args: vec![],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(ret) });
    }

    let (caller, _) = add_static_func(&mut m, "func_main_0", 0);
    let b = entry_of(&m, caller);
    let invoke_new = |m: &mut Module, b, ctor| {
        let clo = closure_of(m, b, ctor);
        let v = emit(
            m,
            b,
            Op::Call {
                callee: clo,
                this: None,
                args: vec![],
                kind: CallKind::New,
            },
        );
        (v, inst_of(m, v))
    };
    let (res1, new1) = invoke_new(&mut m, b, ctor_const);
    let (res2, new2) = invoke_new(&mut m, b, ctor_lc);
    let (res3, new3) = invoke_new(&mut m, b, ctor_helper);
    emit_void(&mut m, b, Op::Return { value: None });

    let graph = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &graph);

    for (res_val, new_site, cached_site) in [
        (res1, new1, cached_const_site),
        (res2, new2, cached_lc_site),
        (res3, new3, cached_helper_site),
    ] {
        let ans = oracle.query(res_val, new_site);
        let mut expected = vec![cached_site, new_site];
        expected.sort();
        assert_eq!(ans.sites.as_slice(), expected.as_slice(), "{ans:?}");
        assert!(ans.has_phi && ans.precise_for_keying(), "{ans:?}");
        assert!(
            !ans.may_be_non_object,
            "`new` itself always yields an Object"
        );
    }
}

#[test]
fn refine_with_points_to_keeps_class_and_object_literal_methods_open() {
    let mut m = mk_module();
    let (cb1_fn, _) = add_static_func(&mut m, "cb1", 0);
    let b_cb1 = entry_of(&m, cb1_fn);
    emit_void(&mut m, b_cb1, Op::Return { value: None });
    let (cb2_fn, _) = add_static_func(&mut m, "cb2", 0);
    let b_cb2 = entry_of(&m, cb2_fn);
    emit_void(&mut m, b_cb2, Op::Return { value: None });
    let (cb3_fn, _) = add_static_func(&mut m, "cb3", 0);
    let b_cb3 = entry_of(&m, cb3_fn);
    emit_void(&mut m, b_cb3, Op::Return { value: None });

    let (cls_ctor, _) = add_static_func(&mut m, "BoxCtor", 0);
    let b_ctor = entry_of(&m, cls_ctor);
    emit_void(&mut m, b_ctor, Op::Return { value: None });

    // 1. Class method referenced only in `DefineClass::members` (`Const::MethodRef`).
    let (cls_run, cls_params) = add_static_func(&mut m, "cls_run", 1);
    let cls_cb_call = {
        let b = entry_of(&m, cls_run);
        let r = emit(
            &mut m,
            b,
            Op::Call {
                callee: cls_params[3],
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
        inst_of(&m, r)
    };

    // 2. Object-literal method referenced only in `AllocObject::shape` (`Const::MethodRef`).
    let (lit_run, lit_params) = add_static_func(&mut m, "lit_run", 1);
    let lit_cb_call = {
        let b = entry_of(&m, lit_run);
        let r = emit(
            &mut m,
            b,
            Op::Call {
                callee: lit_params[3],
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
        inst_of(&m, r)
    };

    // 3. `FunctionKind::Generator` function invoked directly once.
    let (gen_run, gen_params) = add_static_func(&mut m, "gen_run", 1);
    m.func_mut(gen_run).unwrap().kind = FunctionKind::Generator;
    let gen_cb_call = {
        let b = entry_of(&m, gen_run);
        let r = emit(
            &mut m,
            b,
            Op::Call {
                callee: gen_params[3],
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
        inst_of(&m, r)
    };

    let (main, _) = add_static_func(&mut m, "func_main_0", 0);
    let b = entry_of(&m, main);
    let run_sym = intern(&mut m, "run");
    let k_run = push_const(&mut m, Const::String(run_sym));
    let v_cls_run = push_const(&mut m, Const::method_ref(cls_run));
    let c_one = push_const(&mut m, Const::number(1.0));
    let cls_members = push_const(&mut m, Const::ArrayLiteral(vec![k_run, v_cls_run, c_one]));
    let cls_val = emit(
        &mut m,
        b,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: cls_ctor,
            heritage: None,
            members: cls_members,
            member_attrs: Vec::new(),
            count: 1,
        })),
    );
    let box_inst = emit(
        &mut m,
        b,
        Op::Call {
            callee: cls_val,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    let cls_m = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: box_inst,
            name: run_sym,
        },
    );
    let cb1 = closure_of(&mut m, b, cb1_fn);
    let _ = emit(
        &mut m,
        b,
        Op::Call {
            callee: cls_m,
            this: Some(box_inst),
            args: vec![cb1],
            kind: CallKind::Dynamic,
        },
    );

    let v_lit_run = push_const(&mut m, Const::method_ref(lit_run));
    let lit_shape = push_const(
        &mut m,
        Const::ObjectLiteral {
            keys: vec![k_run],
            values: vec![v_lit_run],
        },
    );
    let _lit_obj = emit(&mut m, b, Op::AllocObject { shape: lit_shape });
    // Also record one direct call to `lit_run(cb2)` and `gen_run(cb3)` in `base`.
    let mr_lit = load_method_ref(&mut m, b, lit_run);
    let cb2 = closure_of(&mut m, b, cb2_fn);
    let _ = emit(
        &mut m,
        b,
        Op::Call {
            callee: mr_lit,
            this: None,
            args: vec![cb2],
            kind: CallKind::Direct,
        },
    );
    let mr_gen = load_method_ref(&mut m, b, gen_run);
    let cb3 = closure_of(&mut m, b, cb3_fn);
    let _ = emit(
        &mut m,
        b,
        Op::Call {
            callee: mr_gen,
            this: None,
            args: vec![cb3],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, b, Op::Return { value: None });

    let base = CallGraph::build(&m);
    let oracle = Rung1AliasOracle::new(&m, &base);
    let refined = CallGraph::refine_with_points_to(&m, &base, &oracle);

    for (call_iid, expected_fn) in [
        (cls_cb_call, cb1_fn),
        (lit_cb_call, cb2_fn),
        (gen_cb_call, cb3_fn),
    ] {
        let edge = refined.edge_at(call_iid).expect("bridged call edge");
        assert_eq!(edge.targets, CallTargets::Resolved(vec![expected_fn]));
        assert!(
            !edge.resolution_complete,
            "open method/generator caller must keep bridged edge incomplete: {edge:?}"
        );
    }
}

#[test]
fn ifds_edge_indices_at_u32_max_returns_empty_slice() {
    struct SeedOnlyProblem {
        entry: FuncId,
    }
    impl IfdsProblem for SeedOnlyProblem {
        type Fact = u8;
        fn zero(&self) -> u8 {
            0
        }
        fn initial_seeds(&self) -> Vec<(FuncId, u8)> {
            vec![(self.entry, 1)]
        }
        fn normal_flow(
            &self,
            _module: &Module,
            _curr: InstId,
            _succ: InstId,
            source: &u8,
            out: &mut Vec<u8>,
        ) {
            out.push(*source);
        }
    }

    let mut m = mk_module();
    let (f, _) = add_static_func(&mut m, "func_main_0", 0);
    let b = entry_of(&m, f);
    let _ = alloc_object(&mut m, b);
    let ret_iid = emit_void(&mut m, b, Op::Return { value: None });

    let cg = CallGraph::build(&m);
    let prob = SeedOnlyProblem { entry: f };
    let res = IfdsSolver::new(&m, &prob, &cg, IfdsConfig::default()).solve();

    assert!(!res.edge_indices_at(ret_iid).is_empty());
    assert!(res.edge_indices_at(InstId::new(u32::MAX)).is_empty());
    assert!(!res.has_any_fact_at(InstId::new(u32::MAX)));
}
