//! Issue #94 regressions: `globalThis` (`R7`), `#private` fields, `export * as ns` (`R8`),
//! captured `LexVar` level shifts (`R10`), DAG sharing, steady-state OHOS lifecycle (`D3`),
//! `Endpoint::parse` (`L6`), and `FlowSink` zero-copy parity (`D6`).

use std::cell::RefCell;
use std::collections::HashMap;

use crate::common::*;
use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::dataflow::Rung0AliasOracle;
use abcd_ir::consts::Const;
use abcd_ir::function::FunctionData;
use abcd_ir::module::{ClassData, EsModule, ExportDecl, FunctionKind, ImportDecl, ModuleRequest};
use abcd_ir::op::{DefineClassData, MemberAttrs, ModuleVarKind, SuperKey};
use abcd_ir::{
    CallKind, ClassId, Edge, EdgeKind, FuncId, LexEnvKind, LitMethodKind, Modifiers, Module, Op,
};
use abcd_taint::driver::run_taint;
use abcd_taint::fact::Fact;
use abcd_taint::names::{call_base_value, callee_name_candidates, normalize_sdk_specifier};
use abcd_taint::summary::Endpoint;
use abcd_taint::{
    Oracle, ProtoFamily, PrototypeResolver, SinkSpec, SourceSpec, SummaryRegistry, TaintConfig,
    ohos_preset,
};

use super::{emit_print, std_config_at};

/// `R7`: `globalThis` (`Op::LoadGlobalObject`) peeled through `Op::Mov` chains
/// writes `TaintBase::Global(name)`, passes the interprocedural global reader
/// cone when read ONLY via `globalThis.tok` (no `TryGetGlobal`), and reads back!
#[test]
fn r7_globalthis_load_store_mov_peel_and_interprocedural_reader_cone() {
    let mut m = mk_module();
    let tok_sym = intern(&mut m, "tok");
    let clean_sym = intern(&mut m, "cleanTok");

    let reader = add_func_named(&mut m, "readGlobalThisOnly");
    m.func_mut(reader).unwrap().modifiers = Modifiers::STATIC;
    let sink_hit_iid;
    let sink_clean_iid;
    {
        let b = entry_of(&m, reader);
        add_param(&mut m, reader, 0);
        add_param(&mut m, reader, 1);
        add_param(&mut m, reader, 2);
        let g0 = emit(&mut m, b, Op::LoadGlobalObject);
        let g1 = emit(&mut m, b, Op::Mov { src: g0 });
        let g2 = emit(&mut m, b, Op::Mov { src: g1 });
        let v = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: g2,
                name: tok_sym,
            },
        );
        let vc = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: g2,
                name: clean_sym,
            },
        );
        sink_hit_iid = emit_print(&mut m, b, v);
        sink_clean_iid = emit_print(&mut m, b, vc);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    add_param(&mut m, main_fn, 0);
    let secret = add_param(&mut m, main_fn, 1);

    let g_raw = emit(&mut m, entry, Op::LoadGlobalObject);
    let g_mov = emit(&mut m, entry, Op::Mov { src: g_raw });
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: g_mov,
            name: tok_sym,
            value: secret,
        },
    );
    let rref = load_method_ref(&mut m, entry, reader);
    let _ = emit(
        &mut m,
        entry,
        Op::Call {
            callee: rref,
            this: None,
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let report = run_taint(&m, &std_config_at(rung));
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_hit_iid),
            "rung {rung}: `globalThis.tok` read across interprocedural call must hit: {hit_calls:?}"
        );
        assert!(
            !hit_calls.contains(&sink_clean_iid),
            "rung {rung}: `globalThis.cleanTok` must remain clean: {hit_calls:?}"
        );
    }
}

/// `#private` fields (`StorePrivate`, `DefinePrivate`, `LoadPrivate`):
/// `this.#secret = source(); sink(this.#secret)` propagates across methods at all
/// rungs without colliding with `#clean` (`slot: 1`) or dynamic `this[dynKey]`.
#[test]
fn private_fields_load_store_define_slot_isolation_and_interprocedural() {
    let mut m = mk_module();

    let getter_fn = add_func_named(&mut m, "readPrivates");
    m.func_mut(getter_fn).unwrap().modifiers = Modifiers::STATIC;
    let sink_secret;
    let sink_clean_slot;
    let sink_dyn;
    {
        let b = entry_of(&m, getter_fn);
        add_param(&mut m, getter_fn, 0);
        add_param(&mut m, getter_fn, 1);
        let this_v = add_param(&mut m, getter_fn, 2);

        let v_sec = emit(
            &mut m,
            b,
            Op::LoadPrivate {
                level: 0,
                slot: 0,
                obj: this_v,
            },
        );
        let v_clean = emit(
            &mut m,
            b,
            Op::LoadPrivate {
                level: 0,
                slot: 1,
                obj: this_v,
            },
        );
        let dyn_k = try_get_global(&mut m, b, "DYN_KEY");
        let v_dyn = emit(
            &mut m,
            b,
            Op::LoadPropDyn {
                object: this_v,
                key: dyn_k,
            },
        );
        sink_secret = emit_print(&mut m, b, v_sec);
        sink_clean_slot = emit_print(&mut m, b, v_clean);
        sink_dyn = emit_print(&mut m, b, v_dyn);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    add_param(&mut m, main_fn, 0);
    let secret = add_param(&mut m, main_fn, 1);
    let clean = load_string(&mut m, entry, "clean");

    let inst = alloc_object(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::DefinePrivate {
            level: 0,
            slot: 0,
            obj: inst,
            value: secret,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::DefinePrivate {
            level: 0,
            slot: 1,
            obj: inst,
            value: clean,
        },
    );
    let gref = load_method_ref(&mut m, entry, getter_fn);
    let _ = emit(
        &mut m,
        entry,
        Op::Call {
            callee: gref,
            this: Some(inst),
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let report = run_taint(&m, &std_config_at(rung));
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_secret),
            "rung {rung}: `this.#secret` (slot 0) must propagate across method call: {hit_calls:?}"
        );
        assert!(
            !hit_calls.contains(&sink_clean_slot),
            "rung {rung}: `this.#clean` (slot 1) must NOT collide with slot 0: {hit_calls:?}"
        );
        assert!(
            !hit_calls.contains(&sink_dyn),
            "rung {rung}: `this[dynKey]` must NOT read `#private` slot 0: {hit_calls:?}"
        );
    }
}

/// `R8`: Cross-module `export * as sub from './sub'` (`import { sub } from './barrel'`)
/// and `GetModuleNamespace` (`import * as ns from './sub'`) propagate `ModuleVar`
/// taint AND resolve sink callee names across module boundaries.
#[test]
fn r8_export_star_as_ns_and_get_module_namespace_taint_and_callee_names() {
    let mut m = Module::new();

    let add_esm_record = |m: &mut Module, desc: &str, esm: EsModule| -> ClassId {
        let cid = ClassId::new(m.classes.len() as u32);
        let dsym = m.sym.intern(desc);
        let mut cls = ClassData::new(dsym, dsym);
        cls.es_module = Some(esm);
        m.classes.push(cls);
        cid
    };
    let add_fn_in = |m: &mut Module, cid: ClassId, name: &str| -> FuncId {
        let nsym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(cid, nsym, FunctionKind::Function);
        fd.modifiers = Modifiers::STATIC;
        m.functions.push(fd);
        m.classes[cid.index()].methods.push(fid);
        add_block(m, fid);
        fid
    };

    let sym_secret = m.sym.intern("secretVal");
    let sym_sink_fn = m.sym.intern("customSink");
    let sym_sub_req = m.sym.intern("./sub");
    let sym_barrel_req = m.sym.intern("./barrel");
    let sym_sub_ns = m.sym.intern("sub");
    let sym_star = m.sym.intern("*");

    // Record 0: `Lsub;` exports `secretVal` (slot 0) and `customSink` (slot 1).
    let sub_cid = add_esm_record(
        &mut m,
        "Lsub;",
        EsModule {
            imports: vec![],
            exports: vec![
                ExportDecl::Local {
                    export_name: sym_secret,
                    local_name: sym_secret,
                },
                ExportDecl::Local {
                    export_name: sym_sink_fn,
                    local_name: sym_sink_fn,
                },
            ],
            module_requests: vec![],
        },
    );
    // Record 1: `Lbarrel;` has `export * as sub from './sub'`.
    let barrel_cid = add_esm_record(
        &mut m,
        "Lbarrel;",
        EsModule {
            imports: vec![],
            exports: vec![ExportDecl::Indirect {
                export_name: sym_sub_ns,
                import_name: sym_star,
                module_request: sym_sub_req,
            }],
            module_requests: vec![ModuleRequest {
                specifier: sym_sub_req,
                lazy: false,
            }],
        },
    );
    // Record 2: `Lentry;` imports `{ sub } from './barrel'` AND `* as directNs from './sub'`.
    let entry_cid = add_esm_record(
        &mut m,
        "Lentry;",
        EsModule {
            imports: vec![ImportDecl::Regular {
                local_name: sym_sub_ns,
                import_name: sym_sub_ns,
                module_request: sym_barrel_req,
            }],
            exports: vec![],
            module_requests: vec![
                ModuleRequest {
                    specifier: sym_barrel_req,
                    lazy: false,
                },
                ModuleRequest {
                    specifier: sym_sub_req,
                    lazy: false,
                },
            ],
        },
    );

    // `Lsub::func_main_0`: stores tainted global into slot 0 and sink ref into slot 1.
    let sub_sink_fn = add_fn_in(&mut m, sub_cid, "realCustomSink");
    {
        let sb = entry_of(&m, sub_sink_fn);
        for i in 0..4 {
            add_param(&mut m, sub_sink_fn, i);
        }
        emit_void(&mut m, sb, Op::Return { value: None });
    }
    let sub_main = add_fn_in(&mut m, sub_cid, "func_main_0");
    {
        let b = entry_of(&m, sub_main);
        let src = try_get_global(&mut m, b, "ENV_SECRET");
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: src,
            },
        );
        let sref = load_method_ref(&mut m, b, sub_sink_fn);
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 1,
                value: sref,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let barrel_main = add_fn_in(&mut m, barrel_cid, "func_main_0");
    {
        let b = entry_of(&m, barrel_main);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let entry_main = add_fn_in(&mut m, entry_cid, "func_main_0");
    let call_via_barrel;
    let call_via_ns;
    {
        let b = entry_of(&m, entry_main);
        // Via `import { sub } from './barrel'`: `sub.customSink(sub.secretVal)`
        let sub_obj = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let val1 = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: sub_obj,
                name: sym_secret,
            },
        );
        let sink_callee1 = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: sub_obj,
                name: sym_sink_fn,
            },
        );
        call_via_barrel = push_inst(
            &mut m,
            b,
            Op::Call {
                callee: sink_callee1,
                this: Some(sub_obj),
                args: vec![val1],
                kind: CallKind::Dynamic,
            },
        );

        // Via `GetModuleNamespace(1)` (`./sub`): `directNs.customSink(directNs.secretVal)`
        let ns_obj = emit(&mut m, b, Op::GetModuleNamespace { index: 1 });
        let val2 = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: ns_obj,
                name: sym_secret,
            },
        );
        let sink_callee2 = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: ns_obj,
                name: sym_sink_fn,
            },
        );
        call_via_ns = push_inst(
            &mut m,
            b,
            Op::Call {
                callee: sink_callee2,
                this: Some(ns_obj),
                args: vec![val2],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    for rung in [0u8, 1, 2] {
        let cfg = TaintConfig {
            sources: vec![SourceSpec::GlobalLoad {
                name: "ENV_SECRET".to_owned(),
            }],
            sinks: vec![SinkSpec::Call {
                name: "realCustomSink".to_owned(),
            }],
            builtin_summaries: false,
            alias_rung: rung,
            ..TaintConfig::default()
        };
        let report = run_taint(&m, &cfg);
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&call_via_barrel),
            "rung {rung}: `export * as sub` namespace re-export must propagate taint & callee name: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&call_via_ns),
            "rung {rung}: `GetModuleNamespace` must propagate taint & callee name: {hit_calls:?}"
        );
    }
}

/// `R10`: At Rung 0 and Rung 1 (as well as Rung 2), `PutLexVar { level: 0, slot }`
/// in an outer function matches `GetLexVar { level: 1, slot }` inside a nested
/// closure that pushed its own `NewLexEnv` (and vice versa), without cross-slot
/// false positives.
#[test]
fn r10_rung0_and_rung1_captured_lexvar_level_shift_and_slot_isolation() {
    let mut m = mk_module();

    // `inner` pushes its own `NewLexEnv`, reads outer slot 2 (`level: 1, slot: 2`),
    // reads clean outer slot 9 (`level: 1, slot: 9`), and writes outer slot 3 (`level: 1, slot: 3`).
    let inner = add_func_named(&mut m, "innerClosure");
    m.func_mut(inner).unwrap().modifiers = Modifiers::STATIC;
    let sink_inner_hit;
    let sink_inner_clean;
    {
        let ib = entry_of(&m, inner);
        add_param(&mut m, inner, 0);
        add_param(&mut m, inner, 1);
        add_param(&mut m, inner, 2);
        let arg_sec = add_param(&mut m, inner, 3);
        let _ = emit(
            &mut m,
            ib,
            Op::NewLexEnv {
                num_vars: 2,
                kind: LexEnvKind::Plain,
            },
        );
        let from_outer = emit(
            &mut m,
            ib,
            Op::GetLexVar {
                level: 1,
                slot: 2,
                kind: LexEnvKind::Plain,
            },
        );
        let clean_outer = emit(
            &mut m,
            ib,
            Op::GetLexVar {
                level: 1,
                slot: 9,
                kind: LexEnvKind::Plain,
            },
        );
        sink_inner_hit = emit_print(&mut m, ib, from_outer);
        sink_inner_clean = emit_print(&mut m, ib, clean_outer);
        emit_void(
            &mut m,
            ib,
            Op::PutLexVar {
                level: 1,
                slot: 3,
                value: arg_sec,
                kind: LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, ib, Op::Return { value: None });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    add_param(&mut m, main_fn, 0);
    let secret = add_param(&mut m, main_fn, 1);
    let clean = load_string(&mut m, entry, "clean");

    let _ = emit(
        &mut m,
        entry,
        Op::NewLexEnv {
            num_vars: 10,
            kind: LexEnvKind::Plain,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::PutLexVar {
            level: 0,
            slot: 2,
            value: secret,
            kind: LexEnvKind::Plain,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::PutLexVar {
            level: 0,
            slot: 9,
            value: clean,
            kind: LexEnvKind::Plain,
        },
    );
    let clo = closure_of(&mut m, entry, inner);
    let _ = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo,
            this: None,
            args: vec![secret],
            kind: CallKind::Dynamic,
        },
    );
    // Outer reads slot 3 (`level: 0, slot: 3`) written by `inner` at `level: 1, slot: 3`!
    let back_in_outer = emit(
        &mut m,
        entry,
        Op::GetLexVar {
            level: 0,
            slot: 3,
            kind: LexEnvKind::Plain,
        },
    );
    let sink_outer_back = emit_print(&mut m, entry, back_in_outer);
    emit_void(&mut m, entry, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let report = run_taint(&m, &std_config_at(rung));
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_inner_hit),
            "rung {rung}: outer PutLexVar(0, 2) -> inner GetLexVar(1, 2) must hit: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_outer_back),
            "rung {rung}: inner PutLexVar(1, 3) -> outer GetLexVar(0, 3) must hit: {hit_calls:?}"
        );
        assert!(
            !hit_calls.contains(&sink_inner_clean),
            "rung {rung}: clean slot 9 must NOT be tainted by slot 2/3: {hit_calls:?}"
        );
    }
}

/// `names.rs` & `prototype.rs` diamond DAG sharing (`Phi(v, v)` and shared `v`
/// across two `LoadProp`s), `call_base_value` `Op::Mov` peeling across all member
/// load ops, `gap::resolve_callback_funcs` with `DefineMethod`, and `OhmUrl`.
#[test]
fn names_and_prototype_diamond_dag_sharing_and_call_base_mov_peeling() {
    let mut m = mk_module();
    let cb_fn = add_func_named(&mut m, "myMethodCb");
    {
        let cb_b = entry_of(&m, cb_fn);
        emit_void(&mut m, cb_b, Op::Return { value: None });
    }

    let f = add_func_named(&mut m, "func_main_0");
    let b0 = entry_of(&m, f);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let b_join = add_block(&mut m, f);

    // Shared root `v_glob = TryGetGlobal("console")` and `v_arr = AllocArray` across a diamond `Phi`.
    let v_glob = try_get_global(&mut m, b0, "console");
    let v_arr = alloc_array(&mut m, b0);
    let cond = load_number(&mut m, b0, 1.0);
    emit_void(
        &mut m,
        b0,
        Op::CondBranch {
            cond,
            true_dest: b1,
            false_dest: b2,
        },
    );
    link(&mut m, b0, b1);
    link(&mut m, b0, b2);

    let log_sym = intern(&mut m, "log");
    let warn_sym = intern(&mut m, "warn");
    let lp1 = emit(
        &mut m,
        b1,
        Op::LoadProp {
            object: v_glob,
            name: log_sym,
        },
    );
    let a1 = emit(&mut m, b1, Op::Mov { src: v_arr });
    emit_void(&mut m, b1, Op::Branch { dest: b_join });
    link(&mut m, b1, b_join);

    let lp2 = emit(
        &mut m,
        b2,
        Op::LoadProp {
            object: v_glob,
            name: warn_sym,
        },
    );
    let a2 = emit(&mut m, b2, Op::Mov { src: v_arr });
    emit_void(&mut m, b2, Op::Branch { dest: b_join });
    link(&mut m, b2, b_join);

    let phi_callee = emit(
        &mut m,
        b_join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b1,
                        kind: EdgeKind::Normal,
                    },
                    lp1,
                ),
                (
                    Edge {
                        from: b2,
                        kind: EdgeKind::Normal,
                    },
                    lp2,
                ),
            ],
        },
    );
    let phi_arr = emit(
        &mut m,
        b_join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b1,
                        kind: EdgeKind::Normal,
                    },
                    a1,
                ),
                (
                    Edge {
                        from: b2,
                        kind: EdgeKind::Normal,
                    },
                    a2,
                ),
            ],
        },
    );
    let iter_val = emit(&mut m, b_join, Op::GetIterator { obj: phi_arr });

    // `call_base_value` Mov peeling across LoadProp, LoadPropDyn, LoadPropIdx, LoadPrivate, LoadSuper, and `this`.
    let recv = alloc_object(&mut m, b_join);
    let recv_mov = emit(&mut m, b_join, Op::Mov { src: recv });
    let idx0 = load_number(&mut m, b_join, 0.0);

    let m_prop = emit(
        &mut m,
        b_join,
        Op::LoadProp {
            object: recv_mov,
            name: log_sym,
        },
    );
    let m_prop_mov = emit(&mut m, b_join, Op::Mov { src: m_prop });
    let c_prop = push_inst(
        &mut m,
        b_join,
        Op::Call {
            callee: m_prop_mov,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    let m_dyn = emit(
        &mut m,
        b_join,
        Op::LoadPropDyn {
            object: recv_mov,
            key: idx0,
        },
    );
    let m_dyn_mov = emit(&mut m, b_join, Op::Mov { src: m_dyn });
    let c_dyn = push_inst(
        &mut m,
        b_join,
        Op::Call {
            callee: m_dyn_mov,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    let m_idx = emit(
        &mut m,
        b_join,
        Op::LoadPropIdx {
            object: recv_mov,
            index: idx0,
        },
    );
    let m_idx_mov = emit(&mut m, b_join, Op::Mov { src: m_idx });
    let c_idx = push_inst(
        &mut m,
        b_join,
        Op::Call {
            callee: m_idx_mov,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    let m_priv = emit(
        &mut m,
        b_join,
        Op::LoadPrivate {
            level: 0,
            slot: 0,
            obj: recv_mov,
        },
    );
    let m_priv_mov = emit(&mut m, b_join, Op::Mov { src: m_priv });
    let c_priv = push_inst(
        &mut m,
        b_join,
        Op::Call {
            callee: m_priv_mov,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    let m_sup = emit(
        &mut m,
        b_join,
        Op::LoadSuper {
            key: SuperKey::Name(log_sym),
            this_value: recv_mov,
        },
    );
    let m_sup_mov = emit(&mut m, b_join, Op::Mov { src: m_sup });
    let c_sup = push_inst(
        &mut m,
        b_join,
        Op::Call {
            callee: m_sup_mov,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    let c_this = push_inst(
        &mut m,
        b_join,
        Op::Call {
            callee: v_glob,
            this: Some(recv_mov),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );

    // `DefineMethod` callback resolution via `gap::resolve_callback_funcs`.
    let def_cb = emit(
        &mut m,
        b_join,
        Op::DefineFunc {
            body: cb_fn,
            captures: vec![],
            length: 0,
        },
    );
    let dm_val = emit(
        &mut m,
        b_join,
        Op::DefineMethod {
            object: recv,
            name: log_sym,
            func: def_cb,
            length: 0,
        },
    );
    emit_void(&mut m, b_join, Op::Return { value: None });

    // 1. Both branches of the diamond `Phi` sharing `v_glob` resolve!
    let cands = callee_name_candidates(&m, phi_callee);
    assert!(
        cands.contains(&"console.log".to_owned()) && cands.contains(&"console.warn".to_owned()),
        "diamond DAG sharing `v_glob` must keep both candidates: {cands:?}"
    );

    // 2. Diamond `Phi(Mov(v_arr), Mov(v_arr))` -> `GetIterator` stays `Iterator` AND `precise == true`!
    let oracle = Oracle::Rung0(Rung0AliasOracle::new(&m));
    let memo = RefCell::new(HashMap::new());
    let resolver = PrototypeResolver::new(&m, &oracle, &memo);
    let fam_arr = resolver.families_of(phi_arr, c_prop);
    assert!(fam_arr.families.contains(&ProtoFamily::Array));
    assert!(
        fam_arr.precise,
        "acyclic diamond Phi(Mov(arr), Mov(arr)) must stay precise"
    );
    let fam_iter = resolver.families_of(iter_val, c_prop);
    assert!(
        fam_iter.families.contains(&ProtoFamily::Iterator),
        "GetIterator over diamond array must resolve Iterator: {fam_iter:?}"
    );

    // 3. `call_base_value` peels `Mov` on both `callee` and `this` across all 5 member-load ops!
    for cid in [c_prop, c_dyn, c_idx, c_priv, c_sup, c_this] {
        assert_eq!(
            call_base_value(&m, m.inst(cid).unwrap()),
            Some(recv),
            "call {cid:?} must recover peeled receiver `recv`"
        );
    }

    // 4. `gap::resolve_callback_funcs` resolves `DefineMethod`!
    let cbs = abcd_taint::gap::resolve_callback_funcs(&m, &oracle, dm_val, c_prop);
    assert_eq!(cbs, vec![cb_fn]);

    // 5. `OhmUrl`-backed `normalize_sdk_specifier`.
    assert_eq!(normalize_sdk_specifier("@ohos:net.http"), "@ohos.net.http");
    assert_eq!(
        normalize_sdk_specifier("@kit:NetworkKit"),
        "@kit.NetworkKit"
    );
    assert_eq!(normalize_sdk_specifier("@hms:core.push"), "@hms.core.push");
    assert_eq!(
        normalize_sdk_specifier("@normalized:N&entry&com.demo&entry/src/main/ets/Api&1.0.0"),
        "entry/src/main/ets/Api"
    );
}

/// `D3`: `EntryModel` steady-state `while (*)` OHOS lifecycle loop discovers
/// order-independent cross-callback taint flows (`onNewWant` / `onBackground`
/// writing `this.pendingWant = want` and `onForeground` reading `this.pendingWant`
/// into `@ohos.hilog.info`, even though `onForeground` precedes `onBackground`
/// in linear declaration order!).
#[test]
fn ohos_entry_model_steady_state_order_independent_lifecycle_flow() {
    let mut m = Module::new();
    let cid = ClassId::new(0);
    let desc = m.sym.intern("LEntryAbility;");
    let ui_ability_sym = m.sym.intern("UIAbility");
    let ability_spec = m.sym.intern("@ohos:app.ability.UIAbility");
    let hilog_spec = m.sym.intern("@ohos:hilog");
    let hilog_sym = m.sym.intern("hilog");
    let default_sym = m.sym.intern("default");
    let entry_sym = m.sym.intern("EntryAbility");
    let info_sym = m.sym.intern("info");
    let pending_sym = m.sym.intern("pendingWant");
    let on_fg_sym = m.sym.intern("onForeground");
    let on_bg_sym = m.sym.intern("onBackground");
    let on_nw_sym = m.sym.intern("onNewWant");

    let mut cls = ClassData::new(desc, desc);
    cls.es_module = Some(EsModule {
        imports: vec![
            ImportDecl::Regular {
                local_name: ui_ability_sym,
                import_name: default_sym,
                module_request: ability_spec,
            },
            ImportDecl::Regular {
                local_name: hilog_sym,
                import_name: default_sym,
                module_request: hilog_spec,
            },
        ],
        exports: vec![ExportDecl::Local {
            export_name: default_sym,
            local_name: entry_sym,
        }],
        module_requests: vec![
            ModuleRequest {
                specifier: ability_spec,
                lazy: false,
            },
            ModuleRequest {
                specifier: hilog_spec,
                lazy: false,
            },
        ],
    });
    m.classes.push(cls);

    let mk_fn = |m: &mut Module, name: &str, kind: FunctionKind| -> FuncId {
        let nsym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(cid, nsym, kind);
        fd.modifiers = Modifiers::STATIC;
        m.functions.push(fd);
        m.classes[0].methods.push(fid);
        add_block(m, fid);
        fid
    };

    let ctor = mk_fn(&mut m, "EntryAbility", FunctionKind::Constructor);
    {
        let b = entry_of(&m, ctor);
        add_param(&mut m, ctor, 0);
        add_param(&mut m, ctor, 1);
        let this_v = add_param(&mut m, ctor, 2);
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(this_v),
            },
        );
    }

    // `onForeground(this)` reads `this.pendingWant` and logs it via `hilog.info`.
    let on_fg = mk_fn(&mut m, "onForeground", FunctionKind::Function);
    let hilog_call_iid;
    {
        let b = entry_of(&m, on_fg);
        add_param(&mut m, on_fg, 0);
        add_param(&mut m, on_fg, 1);
        let this_v = add_param(&mut m, on_fg, 2);
        let pw = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: this_v,
                name: pending_sym,
            },
        );
        let hilog_mod = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 1,
                kind: ModuleVarKind::External,
            },
        );
        let info_fn = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: hilog_mod,
                name: info_sym,
            },
        );
        let dom = load_number(&mut m, b, 0.0);
        let tag = load_string(&mut m, b, "tag");
        hilog_call_iid = push_inst(
            &mut m,
            b,
            Op::Call {
                callee: info_fn,
                this: Some(hilog_mod),
                args: vec![dom, tag, pw],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // `onNewWant(want, launchParam)` runs LATER in linear order and stores `this.pendingWant = want`!
    let on_nw = mk_fn(&mut m, "onNewWant", FunctionKind::Function);
    {
        let b = entry_of(&m, on_nw);
        add_param(&mut m, on_nw, 0);
        add_param(&mut m, on_nw, 1);
        let this_v = add_param(&mut m, on_nw, 2);
        let want_v = add_param(&mut m, on_nw, 3);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: this_v,
                name: pending_sym,
                value: want_v,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let on_bg = mk_fn(&mut m, "onBackground", FunctionKind::Function);
    {
        let b = entry_of(&m, on_bg);
        add_param(&mut m, on_bg, 0);
        add_param(&mut m, on_bg, 1);
        add_param(&mut m, on_bg, 2);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let members_cid = {
        let k1 = push_const(&mut m, Const::String(on_fg_sym));
        let v1 = push_const(
            &mut m,
            Const::MethodRef {
                func: on_fg,
                kind: LitMethodKind::Method,
            },
        );
        let k2 = push_const(&mut m, Const::String(on_bg_sym));
        let v2 = push_const(
            &mut m,
            Const::MethodRef {
                func: on_bg,
                kind: LitMethodKind::Method,
            },
        );
        let k3 = push_const(&mut m, Const::String(on_nw_sym));
        let v3 = push_const(
            &mut m,
            Const::MethodRef {
                func: on_nw,
                kind: LitMethodKind::Method,
            },
        );
        let cnt = push_const(&mut m, Const::Int32(3));
        push_const(
            &mut m,
            Const::ArrayLiteral(vec![k1, v1, k2, v2, k3, v3, cnt]),
        )
    };

    let main_fn = mk_fn(&mut m, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, main_fn);
        let super_cls = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let cls_val = emit(
            &mut m,
            b,
            Op::DefineClass(Box::new(DefineClassData {
                ctor,
                heritage: Some(super_cls),
                members: members_cid,
                member_attrs: vec![
                    MemberAttrs {
                        is_static: false,
                        kind: FunctionKind::Function,
                    },
                    MemberAttrs {
                        is_static: false,
                        kind: FunctionKind::Function,
                    },
                    MemberAttrs {
                        is_static: false,
                        kind: FunctionKind::Function,
                    },
                ],
                count: 0,
            })),
        );
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: cls_val,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let cfg = ohos_preset();
    let report = run_taint(&m, &cfg);
    assert!(
        report.hits.iter().any(|h| h.call == hilog_call_iid),
        "steady-state EntryModel loop must propagate `onNewWant` -> `this.pendingWant` -> `onForeground` hilog sink: {:?}",
        report.hits
    );
}

/// `L6`: `abcd_taint::Endpoint::parse` & `Endpoint::is_valid_flow_source`
/// public crate-root API contract.
#[test]
fn endpoint_parse_reexported_api_contract() {
    let base = abcd_taint::Endpoint::parse("base").expect("base");
    let ret = abcd_taint::Endpoint::parse("return").expect("return");
    let p2 = abcd_taint::Endpoint::parse("param:2").expect("param:2");
    let var1 = abcd_taint::Endpoint::parse("any_param_from:1").expect("any_param_from:1");

    assert_eq!(base, Endpoint::Base);
    assert_eq!(ret, Endpoint::Return);
    assert_eq!(p2, Endpoint::Param(2));
    assert_eq!(var1, Endpoint::AnyParamFrom(1));

    assert!(base.is_valid_flow_source());
    assert!(p2.is_valid_flow_source());
    assert!(var1.is_valid_flow_source());
    assert!(!ret.is_valid_flow_source());
    assert!(abcd_taint::Endpoint::parse("invalid").is_err());
    assert!(abcd_taint::Endpoint::parse("param:99999").is_err());
}

/// `D6`: Direct unit check that `TaintProblem` `*_flow` wrappers and `*_flow_out`
/// zero-copy `FlowSink` produce 100% identical fact sets across normal, call,
/// return, call-to-return, and uncaught-exit edges.
#[test]
fn d6_flow_sink_zero_copy_matches_vec_flow_wrappers_bit_for_bit() {
    use abcd_analysis::dataflow::ifds::{FactId, FlowSink, IfdsProblem};

    let mut m = mk_module();
    let callee = add_func_named(&mut m, "calleeThrow");
    m.func_mut(callee).unwrap().modifiers = Modifiers::STATIC;
    let throw_iid;
    {
        let b = entry_of(&m, callee);
        add_param(&mut m, callee, 0);
        add_param(&mut m, callee, 1);
        add_param(&mut m, callee, 2);
        let p = add_param(&mut m, callee, 3);
        throw_iid = emit_void(&mut m, b, Op::Throw { value: p });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, main_fn);
    add_param(&mut m, main_fn, 0);
    let s = add_param(&mut m, main_fn, 1);
    let mov_s = emit(&mut m, b, Op::Mov { src: s });
    let cref = load_method_ref(&mut m, b, callee);
    let call_res = emit(
        &mut m,
        b,
        Op::Call {
            callee: cref,
            this: None,
            args: vec![mov_s],
            kind: CallKind::Direct,
        },
    );
    let ret_iid = emit_void(
        &mut m,
        b,
        Op::Return {
            value: Some(call_res),
        },
    );

    let cg = CallGraph::build(&m);
    let oracle = Oracle::Rung0(Rung0AliasOracle::new(&m));
    let reg = SummaryRegistry::with_builtins();
    let cfg = std_config_at(0);
    let problem = abcd_taint::TaintProblem::new(&m, &cg, oracle, &reg, &cfg);

    let abcd_ir::ValueDef::Inst(mov_iid) = m.value(mov_s).unwrap().def else {
        panic!("mov");
    };
    let abcd_ir::ValueDef::Inst(call_iid) = m.value(call_res).unwrap().def else {
        panic!("call");
    };

    let expand_sink = |src: &Fact, sink: &mut FlowSink<Fact>| -> Vec<Fact> {
        let mut v = Vec::new();
        if sink.has_pass_through() && !matches!(src, Fact::Zero) {
            v.push(src.clone());
        }
        v.append(sink.facts_mut());
        v
    };

    let src_fact = Fact::of(abcd_taint::TaintFact::local(s));
    let mut v1 = Vec::new();
    let mut s1 = FlowSink::new();
    problem.normal_flow(&m, mov_iid, call_iid, &src_fact, &mut v1);
    problem.normal_flow_out(&m, mov_iid, call_iid, FactId(1), &src_fact, &mut s1);
    assert!(
        s1.has_pass_through(),
        "live local `s` uses zero-copy pass_through"
    );
    assert_eq!(v1, expand_sink(&src_fact, &mut s1));

    let mov_fact = Fact::of(abcd_taint::TaintFact::local(mov_s));
    let mut vc = Vec::new();
    let mut sc = FlowSink::new();
    problem.call_flow(&m, call_iid, callee, &mov_fact, &mut vc);
    problem.call_flow_out(&m, call_iid, callee, FactId(2), &mov_fact, &mut sc);
    assert_eq!(vc, expand_sink(&mov_fact, &mut sc));

    let mut vctr = Vec::new();
    let mut sctr = FlowSink::new();
    problem.call_to_return_flow(&m, call_iid, ret_iid, &src_fact, &mut vctr);
    problem.call_to_return_flow_out(&m, call_iid, ret_iid, FactId(1), &src_fact, &mut sctr);
    assert_eq!(vctr, expand_sink(&src_fact, &mut sctr));

    let callee_p = m.func(callee).unwrap().params[3];
    let throw_fact = Fact::of(abcd_taint::TaintFact::local(callee_p));
    let mut vu = Vec::new();
    let mut su = FlowSink::new();
    problem.call_uncaught_exit_flow(&m, call_iid, callee, throw_iid, &throw_fact, &mut vu);
    problem.call_uncaught_exit_flow_out(
        &m,
        call_iid,
        callee,
        throw_iid,
        FactId(3),
        &throw_fact,
        &mut su,
    );
    assert_eq!(vu, expand_sink(&throw_fact, &mut su));
}
