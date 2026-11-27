//! Regression tests for GitHub Issue `#105` (`P3-TAINT-1`..`P3-TAINT-4`):
//! - `P3-TAINT-1`: Rung-2 `ClosedDispatchIndex` subset soundness (`prov ⊆ callees`),
//!   post-convergence provisional call-site invalidation, and `N20` determinism.
//! - `P3-TAINT-2`: Multi-symbol `StorePrivate` / `DefinePrivate` normal-edge weak updates.
//! - `P3-TAINT-3`: Multi-record ESM `Heap(∅)` unknown-base soundness (`sdk.getShared()`),
//!   unconditional `TryGetGlobal` / `LoadModuleVar` container propagation, and Rung-2
//!   `is_variadic_args_site` precision guard.
//! - `P3-TAINT-4`:
//!   - (a) Polymorphic `Phi(cleanSummarized, userIdentity)` `exclusive` summary handling;
//!   - (b) Memoized transitive `this` return (`helper() -> this.id() -> this`) &
//!     polymorphic `[A.m, B.m]` `defer_to_callee` preservation;
//!   - (c) `LocalLiveness` `Mov`-alias retention & `FuncAliasLoads` container ops;
//!   - (d) Narrow `ext_void` non-escape (`customStorage.putSync` vs `@ohos.hilog.info`);
//!   - (e) Signed & special canonical numeric property keys (`-1`, `NaN`, `Infinity`, `-Infinity`);
//!   - (f) `PreparedModule` after `drop_index()` running cleanly at `--alias-rung 0/1/2`.

use crate::common::*;
use abcd_ir::consts::Const;
use abcd_ir::function::FunctionData;
use abcd_ir::module::{ClassData, EsModule, ExportDecl, FunctionKind, ImportDecl, ModuleRequest};
use abcd_ir::op::{DefineClassData, MemberAttrs, ModuleVarKind};
use abcd_ir::{
    CallKind, ClassId, Edge, EdgeKind, FuncId, InstId, LexEnvKind, LitMethodKind, Modifiers,
    Module, Op, UnOp, ValueId,
};
use abcd_taint::summary::{Endpoint, Summary};
use abcd_taint::{
    PreparedModule, SinkSpec, SourceSpec, TaintConfig, ohos_preset, run_taint, run_taint_prepared,
};

fn cfg_at_rung(rung: u8) -> TaintConfig {
    TaintConfig {
        sources: vec![SourceSpec::FunctionParams {
            name: "func_main_0".to_owned(),
            params: None,
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        builtin_summaries: false,
        alias_rung: rung,
        ..TaintConfig::default()
    }
}

fn emit_print_sink(m: &mut Module, b: abcd_ir::BlockId, arg: ValueId) -> InstId {
    let p = try_get_global(m, b, "print");
    push_inst(
        m,
        b,
        Op::Call {
            callee: p,
            this: None,
            args: vec![arg],
            kind: CallKind::Dynamic,
        },
    )
}

fn add_esm_record(m: &mut Module, desc: &str, esm: EsModule) -> ClassId {
    let cid = ClassId::new(m.classes.len() as u32);
    let dsym = m.sym.intern(desc);
    let mut cls = ClassData::new(dsym, dsym);
    cls.es_module = Some(esm);
    m.classes.push(cls);
    cid
}

fn add_static_fn_in(m: &mut Module, cid: ClassId, name: &str, kind: FunctionKind) -> FuncId {
    let nsym = m.sym.intern(name);
    let fid = FuncId::new(m.functions.len() as u32);
    let mut fd = FunctionData::new(cid, nsym, kind);
    fd.modifiers = Modifiers::STATIC;
    m.functions.push(fd);
    m.classes[cid.index()].methods.push(fid);
    add_block(m, fid);
    fid
}

/// `P3-TAINT-1`: Under Rung 2, when `CallGraph` resolves `callees = [safeCb]`
/// (`edge.resolution_complete == false`) while `ClosedDispatchIndex` evaluates
/// `prov = {Callable(safeCb), Callable(idCb)}` (`callees ⊂ prov`), the call site
/// MUST NOT be certified closed (`prov ⊆ callees` fails because `idCb ∉ callees`).
#[test]
fn p3_taint_1_rung2_closed_dispatch_rejects_incomplete_callees_subset_of_prov() {
    let mut m = mk_module();

    // `safeCb(x)`: ignores `x`, returns `"clean"`.
    let safe_cb = add_func_named(&mut m, "safeCb");
    m.func_mut(safe_cb).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, safe_cb);
        for i in 0..4 {
            add_param(&mut m, safe_cb, i);
        }
        let clean = load_string(&mut m, b, "clean");
        emit_void(&mut m, b, Op::Return { value: Some(clean) });
    }

    // `idCb(x)`: returns `x`.
    let id_cb = add_func_named(&mut m, "idCb");
    m.func_mut(id_cb).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, id_cb);
        add_param(&mut m, id_cb, 0);
        add_param(&mut m, id_cb, 1);
        add_param(&mut m, id_cb, 2);
        let x = add_param(&mut m, id_cb, 3);
        emit_void(&mut m, b, Op::Return { value: Some(x) });
    }

    // `installLater()`: closure handed to unmodeled `registerHook(installLater)`.
    // PTA does not invoke `installLater`, so PTA's points-to for lex slot 0 is
    // `{safeCb}` + `has_unknown: true` (`callees = [safeCb]`, `resolution_complete = false`),
    // while `ClosedHarvest` sees both `PutLexVar` stores (`prov = {safeCb, idCb}`).
    let install_later = add_func_named(&mut m, "installLater");
    m.func_mut(install_later).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, install_later);
        for i in 0..3 {
            add_param(&mut m, install_later, i);
        }
        let _ = emit(
            &mut m,
            b,
            Op::NewLexEnv {
                num_vars: 1,
                kind: LexEnvKind::Plain,
            },
        );
        let id_clo = closure_of(&mut m, b, id_cb);
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 1,
                slot: 0,
                value: id_clo,
                kind: LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    m.func_mut(main_fn).unwrap().modifiers = Modifiers::STATIC;
    let sink_iid;
    {
        let b = entry_of(&m, main_fn);
        add_param(&mut m, main_fn, 0);
        add_param(&mut m, main_fn, 1);
        add_param(&mut m, main_fn, 2);
        let secret = add_param(&mut m, main_fn, 3);

        let _ = emit(
            &mut m,
            b,
            Op::NewLexEnv {
                num_vars: 1,
                kind: LexEnvKind::Plain,
            },
        );
        let safe_clo = closure_of(&mut m, b, safe_cb);
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: safe_clo,
                kind: LexEnvKind::Plain,
            },
        );
        let hook_clo = closure_of(&mut m, b, install_later);
        let reg_fn = try_get_global(&mut m, b, "registerExternalHook");
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: reg_fn,
                this: None,
                args: vec![hook_clo],
                kind: CallKind::Dynamic,
            },
        );
        let cb = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: LexEnvKind::Plain,
            },
        );
        let out_val = emit(
            &mut m,
            b,
            Op::Call {
                callee: cb,
                this: None,
                args: vec![secret],
                kind: CallKind::Dynamic,
            },
        );
        sink_iid = emit_print_sink(&mut m, b, out_val);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    for rung in [0u8, 1, 2] {
        let mut cfg = cfg_at_rung(rung);
        cfg.native_identity = true;
        let report = run_taint(&m, &cfg);
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_iid),
            "rung {rung}: incomplete `callees = [safeCb] ⊂ prov = {{safeCb, idCb}}` must NOT be certified closed: {hit_calls:?}"
        );
    }
}

/// `P3-TAINT-2`: Multi-symbol `StorePrivate` / `DefinePrivate` (`syms.len() >= 2`,
/// arising when two `NewLexEnv` frames merge into a block) must emit weak updates
/// onto every candidate `FieldKey::Named(psym)` on normal edges without strong-killing
/// pre-existing taint on either candidate symbol.
#[test]
fn p3_taint_2_multi_symbol_store_private_weak_update_propagates_and_preserves() {
    let mut m = mk_module();
    let main_fn = add_func_named(&mut m, "func_main_0");
    m.func_mut(main_fn).unwrap().modifiers = Modifiers::STATIC;

    let b_entry = entry_of(&m, main_fn);
    let b_cls_a = add_block(&mut m, main_fn);
    let b_cls_b = add_block(&mut m, main_fn);
    let b_merge = add_block(&mut m, main_fn);

    add_param(&mut m, main_fn, 0);
    add_param(&mut m, main_fn, 1);
    add_param(&mut m, main_fn, 2);
    let secret = add_param(&mut m, main_fn, 3);
    let cond = add_param(&mut m, main_fn, 4);

    let obj_tainted = alloc_object(&mut m, b_entry);
    let obj_kept = alloc_object(&mut m, b_entry);
    emit_void(
        &mut m,
        b_entry,
        Op::CondBranch {
            cond,
            true_dest: b_cls_a,
            false_dest: b_cls_b,
        },
    );
    link(&mut m, b_entry, b_cls_a);
    link(&mut m, b_entry, b_cls_b);

    // Branch A pushes lexical env A (`class A { #secret }`) and taints `obj_kept.#secret`.
    let _ = emit(
        &mut m,
        b_cls_a,
        Op::NewLexEnv {
            num_vars: 2,
            kind: LexEnvKind::Plain,
        },
    );
    emit_void(
        &mut m,
        b_cls_a,
        Op::DefinePrivate {
            level: 0,
            slot: 0,
            obj: obj_kept,
            value: secret,
        },
    );
    let read_in_a_fn = add_func_named(&mut m, "readInClassA");
    m.func_mut(read_in_a_fn).unwrap().modifiers = Modifiers::STATIC;
    let sink_from_multi_write;
    let sink_kept_after_weak_clean;
    {
        let rb = entry_of(&m, read_in_a_fn);
        add_param(&mut m, read_in_a_fn, 0);
        add_param(&mut m, read_in_a_fn, 1);
        add_param(&mut m, read_in_a_fn, 2);
        let p_tainted = add_param(&mut m, read_in_a_fn, 3);
        let p_kept = add_param(&mut m, read_in_a_fn, 4);
        let _ = emit(
            &mut m,
            rb,
            Op::NewLexEnv {
                num_vars: 1,
                kind: LexEnvKind::Plain,
            },
        );
        let v1 = emit(
            &mut m,
            rb,
            Op::LoadPrivate {
                level: 1,
                slot: 0,
                obj: p_tainted,
            },
        );
        let v2 = emit(
            &mut m,
            rb,
            Op::LoadPrivate {
                level: 1,
                slot: 0,
                obj: p_kept,
            },
        );
        sink_from_multi_write = emit_print_sink(&mut m, rb, v1);
        sink_kept_after_weak_clean = emit_print_sink(&mut m, rb, v2);
        emit_void(&mut m, rb, Op::Return { value: None });
    }
    let clo_a = closure_of(&mut m, b_cls_a, read_in_a_fn);
    emit_void(&mut m, b_cls_a, Op::Branch { dest: b_merge });
    link(&mut m, b_cls_a, b_merge);

    // Branch B pushes a second distinct lexical env B (`class B { #secret }`).
    let _ = emit(
        &mut m,
        b_cls_b,
        Op::NewLexEnv {
            num_vars: 2,
            kind: LexEnvKind::Plain,
        },
    );
    let clo_b = closure_of(&mut m, b_cls_b, read_in_a_fn);
    emit_void(&mut m, b_cls_b, Op::Branch { dest: b_merge });
    link(&mut m, b_cls_b, b_merge);

    // At `b_merge`, `explicit_sites_at` contains BOTH `NewLexEnv` sites (`syms.len() == 2`).
    let reader_phi = emit(
        &mut m,
        b_merge,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b_cls_a,
                        kind: EdgeKind::Normal,
                    },
                    clo_a,
                ),
                (
                    Edge {
                        from: b_cls_b,
                        kind: EdgeKind::Normal,
                    },
                    clo_b,
                ),
            ],
        },
    );
    // 1. Multi-symbol `StorePrivate` with tainted `secret` must propagate to `readInClassA`!
    emit_void(
        &mut m,
        b_merge,
        Op::StorePrivate {
            level: 0,
            slot: 0,
            obj: obj_tainted,
            value: secret,
        },
    );
    // 2. Multi-symbol `StorePrivate` with `"clean"` must be a WEAK update (must not kill `obj_kept`).
    let clean = load_string(&mut m, b_merge, "clean");
    emit_void(
        &mut m,
        b_merge,
        Op::StorePrivate {
            level: 0,
            slot: 0,
            obj: obj_kept,
            value: clean,
        },
    );
    let _ = emit(
        &mut m,
        b_merge,
        Op::Call {
            callee: reader_phi,
            this: None,
            args: vec![obj_tainted, obj_kept],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_merge, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let report = run_taint(&m, &cfg_at_rung(rung));
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_from_multi_write),
            "rung {rung}: multi-symbol StorePrivate must emit weak taint onto candidate private symbols: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_kept_after_weak_clean),
            "rung {rung}: multi-symbol StorePrivate with clean value must NOT strong-kill prior taint: {hit_calls:?}"
        );
    }
}

/// `P3-TAINT-3`: Multi-record ESM apps keep `Heap(∅)` unknown-base heap flow
/// (`const s = sdk.getShared(); s.token = src(); ... const t = sdk.getShared(); sink(t.token);`)
/// sound under Rung 2 while keeping `LoadModuleVar` / `TryGetGlobal` container
/// propagation unconditional across all rungs.
#[test]
fn p3_taint_3_multi_record_esm_unknown_base_empty_heap_and_container_stores() {
    let mut m = Module::new();
    let sym_sdk_req = m.sym.intern("@ext/sdk");
    let sym_default = m.sym.intern("default");
    let sym_sdk_local = m.sym.intern("sdk");
    let sym_get_shared = m.sym.intern("getShared");
    let sym_token = m.sym.intern("token");
    let sym_clean_prop = m.sym.intern("untouched");
    let sym_reader_req = m.sym.intern("./reader");
    let sym_run_reader = m.sym.intern("runReader");
    let sym_shared_cfg = m.sym.intern("sharedCfg");

    // Record 0 (`Lreader;`): imports `sdk` from `@ext/sdk`, exports `runReader` and `sharedCfg`.
    let reader_cid = add_esm_record(
        &mut m,
        "Lreader;",
        EsModule {
            imports: vec![ImportDecl::Regular {
                local_name: sym_sdk_local,
                import_name: sym_default,
                module_request: sym_sdk_req,
            }],
            exports: vec![
                ExportDecl::Local {
                    export_name: sym_run_reader,
                    local_name: sym_run_reader,
                },
                ExportDecl::Local {
                    export_name: sym_shared_cfg,
                    local_name: sym_shared_cfg,
                },
            ],
            module_requests: vec![ModuleRequest {
                specifier: sym_sdk_req,
                lazy: false,
            }],
        },
    );
    // Record 1 (`Lwriter;`): imports `sdk` from `@ext/sdk` and `{ runReader, sharedCfg }` from `./reader`.
    let writer_cid = add_esm_record(
        &mut m,
        "Lwriter;",
        EsModule {
            imports: vec![
                ImportDecl::Regular {
                    local_name: sym_sdk_local,
                    import_name: sym_default,
                    module_request: sym_sdk_req,
                },
                ImportDecl::Regular {
                    local_name: sym_run_reader,
                    import_name: sym_run_reader,
                    module_request: sym_reader_req,
                },
                ImportDecl::Regular {
                    local_name: sym_shared_cfg,
                    import_name: sym_shared_cfg,
                    module_request: sym_reader_req,
                },
            ],
            exports: vec![],
            module_requests: vec![
                ModuleRequest {
                    specifier: sym_sdk_req,
                    lazy: false,
                },
                ModuleRequest {
                    specifier: sym_reader_req,
                    lazy: false,
                },
            ],
        },
    );

    let run_reader_fn =
        add_static_fn_in(&mut m, reader_cid, "runReaderBody", FunctionKind::Function);
    let sink_shared_tok;
    let sink_shared_clean;
    let sink_mod_cfg_tok;
    {
        let b = entry_of(&m, run_reader_fn);
        for i in 0..3 {
            add_param(&mut m, run_reader_fn, i);
        }
        let sdk = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let get_sh = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: sdk,
                name: sym_get_shared,
            },
        );
        let t = emit(
            &mut m,
            b,
            Op::Call {
                callee: get_sh,
                this: Some(sdk),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let v_tok = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: t,
                name: sym_token,
            },
        );
        let v_clean = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: t,
                name: sym_clean_prop,
            },
        );
        let cfg_local = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 1,
                kind: ModuleVarKind::Local,
            },
        );
        let v_cfg_tok = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: cfg_local,
                name: sym_token,
            },
        );
        sink_shared_tok = emit_print_sink(&mut m, b, v_tok);
        sink_shared_clean = emit_print_sink(&mut m, b, v_clean);
        sink_mod_cfg_tok = emit_print_sink(&mut m, b, v_cfg_tok);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let reader_main = add_static_fn_in(&mut m, reader_cid, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, reader_main);
        let fn_ref = load_method_ref(&mut m, b, run_reader_fn);
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: fn_ref,
            },
        );
        let sdk = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let mk_cfg = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: sdk,
                name: sym_shared_cfg,
            },
        );
        let cfg_obj = emit(
            &mut m,
            b,
            Op::Call {
                callee: mk_cfg,
                this: Some(sdk),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 1,
                value: cfg_obj,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let writer_main = add_static_fn_in(&mut m, writer_cid, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, writer_main);
        let src = try_get_global(&mut m, b, "SECRET_SOURCE");
        let sdk = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let get_sh = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: sdk,
                name: sym_get_shared,
            },
        );
        let s = emit(
            &mut m,
            b,
            Op::Call {
                callee: get_sh,
                this: Some(sdk),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: s,
                name: sym_token,
                value: src,
            },
        );

        // Also mutate imported `sharedCfg.token = src` via `LoadModuleVar` container arm!
        let imp_cfg = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 2,
                kind: ModuleVarKind::External,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: imp_cfg,
                name: sym_token,
                value: src,
            },
        );

        let reader_callee = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 1,
                kind: ModuleVarKind::External,
            },
        );
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: reader_callee,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    for rung in [0u8, 1, 2] {
        let cfg = TaintConfig {
            sources: vec![SourceSpec::GlobalLoad {
                name: "SECRET_SOURCE".to_owned(),
            }],
            sinks: vec![SinkSpec::Call {
                name: "print".to_owned(),
            }],
            builtin_summaries: false,
            alias_rung: rung,
            ..TaintConfig::default()
        };
        let report = run_taint(&m, &cfg);
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_shared_tok),
            "rung {rung}: multi-record `sdk.getShared().token` unknown-base Heap(∅) flow must hit: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_mod_cfg_tok),
            "rung {rung}: LoadModuleVar container propagation `sharedCfg.token = src` must hit: {hit_calls:?}"
        );
        assert!(
            !hit_calls.contains(&sink_shared_clean),
            "rung {rung}: unrelated property `sdk.getShared().untouched` must stay clean: {hit_calls:?}"
        );
    }
}

/// `P3-TAINT-4(a)`: At a polymorphic call site `Phi(cleanSummarized, userIdentity)`,
/// `cleanSummarized`'s `exclusive: true` summary must NOT suppress IFDS body flow
/// through concrete sibling `userIdentity` (while monomorphic `cleanSummarized`
/// still honors `exclusive: true`).
#[test]
fn p3_taint_4a_polymorphic_exclusive_summary_preserves_sibling_user_body() {
    let mut m = mk_module();

    // `cleanSummarized(x)` has `{ return x; }` in IR, overridden by an `exclusive: true`
    // no-flow summary. Monomorphic calls must be clean; polymorphic calls with `userIdentity`
    // must still flow through `userIdentity(x) { return x; }`!
    let clean_fn = add_func_named(&mut m, "cleanSummarized");
    m.func_mut(clean_fn).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, clean_fn);
        add_param(&mut m, clean_fn, 0);
        add_param(&mut m, clean_fn, 1);
        add_param(&mut m, clean_fn, 2);
        let x = add_param(&mut m, clean_fn, 3);
        emit_void(&mut m, b, Op::Return { value: Some(x) });
    }

    let id_fn = add_func_named(&mut m, "userIdentity");
    m.func_mut(id_fn).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, id_fn);
        add_param(&mut m, id_fn, 0);
        add_param(&mut m, id_fn, 1);
        add_param(&mut m, id_fn, 2);
        let x = add_param(&mut m, id_fn, 3);
        emit_void(&mut m, b, Op::Return { value: Some(x) });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    m.func_mut(main_fn).unwrap().modifiers = Modifiers::STATIC;
    let b_entry = entry_of(&m, main_fn);
    let b_left = add_block(&mut m, main_fn);
    let b_right = add_block(&mut m, main_fn);
    let b_join = add_block(&mut m, main_fn);

    add_param(&mut m, main_fn, 0);
    add_param(&mut m, main_fn, 1);
    add_param(&mut m, main_fn, 2);
    let secret = add_param(&mut m, main_fn, 3);
    let cond = add_param(&mut m, main_fn, 4);

    let clean_clo_mono = closure_of(&mut m, b_entry, clean_fn);
    let mono_out = emit(
        &mut m,
        b_entry,
        Op::Call {
            callee: clean_clo_mono,
            this: None,
            args: vec![secret],
            kind: CallKind::Dynamic,
        },
    );
    let sink_mono_clean = emit_print_sink(&mut m, b_entry, mono_out);

    let secret2 = try_get_global(&mut m, b_entry, "SECOND_SECRET");
    emit_void(
        &mut m,
        b_entry,
        Op::CondBranch {
            cond,
            true_dest: b_left,
            false_dest: b_right,
        },
    );
    link(&mut m, b_entry, b_left);
    link(&mut m, b_entry, b_right);

    let clo_left = closure_of(&mut m, b_left, clean_fn);
    emit_void(&mut m, b_left, Op::Branch { dest: b_join });
    link(&mut m, b_left, b_join);

    let clo_right = closure_of(&mut m, b_right, id_fn);
    emit_void(&mut m, b_right, Op::Branch { dest: b_join });
    link(&mut m, b_right, b_join);

    let poly_callee = emit(
        &mut m,
        b_join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b_left,
                        kind: EdgeKind::Normal,
                    },
                    clo_left,
                ),
                (
                    Edge {
                        from: b_right,
                        kind: EdgeKind::Normal,
                    },
                    clo_right,
                ),
            ],
        },
    );
    let poly_out = emit(
        &mut m,
        b_join,
        Op::Call {
            callee: poly_callee,
            this: None,
            args: vec![secret2],
            kind: CallKind::Dynamic,
        },
    );
    let sink_poly_out = emit_print_sink(&mut m, b_join, poly_out);
    let sink_secret2_after = emit_print_sink(&mut m, b_join, secret2);
    emit_void(&mut m, b_join, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let mut cfg = cfg_at_rung(rung);
        cfg.sources.push(SourceSpec::GlobalLoad {
            name: "SECOND_SECRET".to_owned(),
        });
        cfg.extra_summaries.push((
            "cleanSummarized".to_owned(),
            Some(1),
            Summary::new("exclusive sanitizer")
                .clear(Endpoint::Param(0))
                .exclusive(),
        ));
        let report = run_taint(&m, &cfg);
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            !hit_calls.contains(&sink_mono_clean),
            "rung {rung}: monomorphic `cleanSummarized` must still suppress body via `exclusive: true`: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_poly_out),
            "rung {rung}: polymorphic `Phi(cleanSummarized, userIdentity)` must flow through `userIdentity`: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_secret2_after),
            "rung {rung}: polymorphic `Phi(cleanSummarized, userIdentity)` must NOT clear caller arg along `userIdentity` path: {hit_calls:?}"
        );
    }
}

/// `P3-TAINT-4(b)`:
/// 1. Memoized transitive `this` return (`helper() { return this.id(); } id() { return this; }`)
///    propagates `Local(x).secret` onto `y = x.helper()`.
/// 2. Polymorphic `[A.m, B.m]` where `A.m` overwrites `this.secret = ""` and `B.m`
///    does not touch `secret` preserves `Local(x).secret` across `x.m()`.
#[test]
fn p3_taint_4b_transitive_this_return_and_polymorphic_defer_to_callee() {
    let mut m = mk_module();
    let sym_secret = intern(&mut m, "secret");
    let sym_id = intern(&mut m, "id");
    let sym_helper = intern(&mut m, "helper");
    let sym_m = intern(&mut m, "m");

    let mk_class = |m: &mut Module,
                    b: abcd_ir::BlockId,
                    cls_name: &str,
                    methods: &[(abcd_ir::Sym, FuncId)]|
     -> ValueId {
        let ctor = add_func_named(m, &format!("{cls_name}_ctor"));
        m.func_mut(ctor).unwrap().kind = FunctionKind::Constructor;
        m.func_mut(ctor).unwrap().modifiers = Modifiers::STATIC;
        {
            let cb = entry_of(m, ctor);
            for i in 0..3 {
                add_param(m, ctor, i);
            }
            emit_void(m, cb, Op::Return { value: None });
        }
        let mut items = Vec::new();
        let mut attrs = Vec::new();
        for &(msym, mfid) in methods {
            items.push(m.consts.push(Const::String(msym)));
            items.push(m.consts.push(Const::MethodRef {
                func: mfid,
                kind: LitMethodKind::Method,
            }));
            attrs.push(MemberAttrs {
                is_static: false,
                kind: FunctionKind::Function,
            });
        }
        items.push(m.consts.push(Const::Int32(methods.len() as u32)));
        let members_cid = m.consts.push(Const::ArrayLiteral(items));
        emit(
            m,
            b,
            Op::DefineClass(Box::new(DefineClassData {
                ctor,
                members: members_cid,
                count: 0,
                heritage: None,
                member_attrs: attrs,
            })),
        )
    };

    // `Box.id() { return this; }` and `Box.helper() { return this.id(); }`
    let box_id = add_func_named(&mut m, "Box_id");
    m.func_mut(box_id).unwrap().kind = FunctionKind::Function;
    m.func_mut(box_id).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, box_id);
        add_param(&mut m, box_id, 0);
        add_param(&mut m, box_id, 1);
        let this_v = add_param(&mut m, box_id, 2);
        let mov_this = emit(&mut m, b, Op::Mov { src: this_v });
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(mov_this),
            },
        );
    }
    let box_helper = add_func_named(&mut m, "Box_helper");
    m.func_mut(box_helper).unwrap().kind = FunctionKind::Function;
    m.func_mut(box_helper).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, box_helper);
        add_param(&mut m, box_helper, 0);
        add_param(&mut m, box_helper, 1);
        let this_v = add_param(&mut m, box_helper, 2);
        let id_cal = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: this_v,
                name: sym_id,
            },
        );
        let ret = emit(
            &mut m,
            b,
            Op::Call {
                callee: id_cal,
                this: Some(this_v),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(ret) });
    }

    // `A.m() { this.secret = "clean"; return 1; }` and `B.m() { return 2; }`
    let a_m = add_func_named(&mut m, "A_m");
    m.func_mut(a_m).unwrap().kind = FunctionKind::Function;
    m.func_mut(a_m).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, a_m);
        add_param(&mut m, a_m, 0);
        add_param(&mut m, a_m, 1);
        let this_v = add_param(&mut m, a_m, 2);
        let clean = load_string(&mut m, b, "");
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: this_v,
                name: sym_secret,
                value: clean,
            },
        );
        let one = load_number(&mut m, b, 1.0);
        emit_void(&mut m, b, Op::Return { value: Some(one) });
    }
    let b_m = add_func_named(&mut m, "B_m");
    m.func_mut(b_m).unwrap().kind = FunctionKind::Function;
    m.func_mut(b_m).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, b_m);
        for i in 0..3 {
            add_param(&mut m, b_m, i);
        }
        let two = load_number(&mut m, b, 2.0);
        emit_void(&mut m, b, Op::Return { value: Some(two) });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    m.func_mut(main_fn).unwrap().modifiers = Modifiers::STATIC;
    let b_entry = entry_of(&m, main_fn);
    let b_a = add_block(&mut m, main_fn);
    let b_b = add_block(&mut m, main_fn);
    let b_join = add_block(&mut m, main_fn);

    add_param(&mut m, main_fn, 0);
    add_param(&mut m, main_fn, 1);
    add_param(&mut m, main_fn, 2);
    let secret = add_param(&mut m, main_fn, 3);
    let cond = add_param(&mut m, main_fn, 4);

    // 1. Transitive `this` return: `y = box_inst.helper(); sink(y.secret)`
    let box_cls = mk_class(
        &mut m,
        b_entry,
        "Box",
        &[(sym_id, box_id), (sym_helper, box_helper)],
    );
    let box_inst = emit(
        &mut m,
        b_entry,
        Op::Call {
            callee: box_cls,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    emit_void(
        &mut m,
        b_entry,
        Op::StoreProp {
            object: box_inst,
            name: sym_secret,
            value: secret,
        },
    );
    let h_cal = emit(
        &mut m,
        b_entry,
        Op::LoadProp {
            object: box_inst,
            name: sym_helper,
        },
    );
    let y = emit(
        &mut m,
        b_entry,
        Op::Call {
            callee: h_cal,
            this: Some(box_inst),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let y_sec = emit(
        &mut m,
        b_entry,
        Op::LoadProp {
            object: y,
            name: sym_secret,
        },
    );
    let sink_trans_this = emit_print_sink(&mut m, b_entry, y_sec);

    // 2. Polymorphic `[A.m, B.m]`: `x = Phi(new A(), new B()); x.secret = secret; x.m(); sink(x.secret)`
    // Make `x` come from a fresh summary call on the `Local(x)` channel as well as `new A / new B`!
    let cls_a = mk_class(&mut m, b_entry, "A", &[(sym_m, a_m)]);
    let cls_b = mk_class(&mut m, b_entry, "B", &[(sym_m, b_m)]);
    emit_void(
        &mut m,
        b_entry,
        Op::CondBranch {
            cond,
            true_dest: b_a,
            false_dest: b_b,
        },
    );
    link(&mut m, b_entry, b_a);
    link(&mut m, b_entry, b_b);

    let inst_a = emit(
        &mut m,
        b_a,
        Op::Call {
            callee: cls_a,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    emit_void(&mut m, b_a, Op::Branch { dest: b_join });
    link(&mut m, b_a, b_join);

    let inst_b = emit(
        &mut m,
        b_b,
        Op::Call {
            callee: cls_b,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    emit_void(&mut m, b_b, Op::Branch { dest: b_join });
    link(&mut m, b_b, b_join);

    let x = emit(
        &mut m,
        b_join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b_a,
                        kind: EdgeKind::Normal,
                    },
                    inst_a,
                ),
                (
                    Edge {
                        from: b_b,
                        kind: EdgeKind::Normal,
                    },
                    inst_b,
                ),
            ],
        },
    );
    emit_void(
        &mut m,
        b_join,
        Op::StoreProp {
            object: x,
            name: sym_secret,
            value: secret,
        },
    );
    let m_cal = emit(
        &mut m,
        b_join,
        Op::LoadProp {
            object: x,
            name: sym_m,
        },
    );
    let _ = emit(
        &mut m,
        b_join,
        Op::Call {
            callee: m_cal,
            this: Some(x),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    // Also test a pure unknown-site `Local(u).secret` passed into `[A.m, B.m]` via direct `Phi(A_m, B_m)`
    // so `Heap` sites cannot mask a `Local(u).secret` drop!
    let u_fresh = {
        let fcal = try_get_global(&mut m, b_join, "freshContainer");
        emit(
            &mut m,
            b_join,
            Op::Call {
                callee: fcal,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        )
    };
    emit_void(
        &mut m,
        b_join,
        Op::StoreProp {
            object: u_fresh,
            name: sym_secret,
            value: secret,
        },
    );
    let _ = emit(
        &mut m,
        b_join,
        Op::Call {
            callee: m_cal,
            this: Some(u_fresh),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let x_sec = emit(
        &mut m,
        b_join,
        Op::LoadProp {
            object: x,
            name: sym_secret,
        },
    );
    let u_sec = emit(
        &mut m,
        b_join,
        Op::LoadProp {
            object: u_fresh,
            name: sym_secret,
        },
    );
    let sink_poly_x = emit_print_sink(&mut m, b_join, x_sec);
    let sink_poly_u = emit_print_sink(&mut m, b_join, u_sec);
    emit_void(&mut m, b_join, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let mut cfg = cfg_at_rung(rung);
        cfg.extra_summaries.push((
            "freshContainer".to_owned(),
            Some(0),
            Summary::new("allocates fresh empty container").exclusive(),
        ));
        let report = run_taint(&m, &cfg);
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_trans_this),
            "rung {rung}: transitive `this` return `helper() -> this.id() -> this` must hit: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_poly_x),
            "rung {rung}: polymorphic `[A.m, B.m]` must preserve `x.secret` along `B.m`: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_poly_u),
            "rung {rung}: polymorphic `[A.m, B.m]` must preserve `Local(u_fresh).secret` along `B.m`: {hit_calls:?}"
        );
    }
}

/// `P3-TAINT-4(c)`: `should_retain_local_at` retains `Local(v2)` across `nop` when
/// `v2 = Mov(v1)` dies at `nop` while `v1` (`peel_movs` root) remains live at
/// `sink(v1.secret)` (even when `site_info_at` has empty sites via a fresh summary
/// call so `Heap(∅)` cannot rescue the dropped `Local` fact), AND `FuncAliasLoads`
/// retains `Local` facts read via `CopyDataProps` / `CreateObjectWithExcludedKeys`.
#[test]
fn p3_taint_4c_mov_aliased_local_liveness_and_func_alias_loads_containers() {
    let mut m = mk_module();
    let sym_secret = intern(&mut m, "secret");
    let sym_other = intern(&mut m, "other");

    // Identity helper returning an object whose site set is `{alloc_iid}` + `has_unknown`
    // (when merged with an unknown branch) so `Local(alias)` is exercised across `CopyDataProps`.
    let main_fn = add_func_named(&mut m, "func_main_0");
    m.func_mut(main_fn).unwrap().modifiers = Modifiers::STATIC;
    let b_entry = entry_of(&m, main_fn);
    let b_k = add_block(&mut m, main_fn);
    let b_u = add_block(&mut m, main_fn);
    let b_join = add_block(&mut m, main_fn);

    add_param(&mut m, main_fn, 0);
    add_param(&mut m, main_fn, 1);
    add_param(&mut m, main_fn, 2);
    let secret = add_param(&mut m, main_fn, 3);
    let cond = add_param(&mut m, main_fn, 4);

    // Case 1: `v1 = freshSummaryCall(); v2 = Mov(v1); v2.secret = secret; nop; sink(v1.secret);`
    // At Rung 2, `fresh_result_site(v1) == Some(fresh_iid)` rejects `Heap(∅)`, so ONLY
    // `Local(v2).secret` carries taint to `v1.secret`!
    let fresh_cal = try_get_global(&mut m, b_entry, "freshBox");
    let v1 = emit(
        &mut m,
        b_entry,
        Op::Call {
            callee: fresh_cal,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let v2 = emit(&mut m, b_entry, Op::Mov { src: v1 });
    emit_void(
        &mut m,
        b_entry,
        Op::StoreProp {
            object: v2,
            name: sym_secret,
            value: secret,
        },
    );
    let _nop1 = load_number(&mut m, b_entry, 0.0);
    let read_v1 = emit(
        &mut m,
        b_entry,
        Op::LoadProp {
            object: v1,
            name: sym_secret,
        },
    );
    let sink_mov_root_read = emit_print_sink(&mut m, b_entry, read_v1);

    // Symmetric Case 1b: `w2 = Mov(w1); w1.secret = secret; nop; sink(w2.secret);`
    let w1 = emit(
        &mut m,
        b_entry,
        Op::Call {
            callee: fresh_cal,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let w2 = emit(&mut m, b_entry, Op::Mov { src: w1 });
    emit_void(
        &mut m,
        b_entry,
        Op::StoreProp {
            object: w1,
            name: sym_secret,
            value: secret,
        },
    );
    let _nop2 = load_number(&mut m, b_entry, 0.0);
    let read_w2 = emit(
        &mut m,
        b_entry,
        Op::LoadProp {
            object: w2,
            name: sym_secret,
        },
    );
    let sink_mov_alias_read = emit_print_sink(&mut m, b_entry, read_w2);

    // Case 2: `FuncAliasLoads` over `CreateObjectWithExcludedKeys`:
    // `base_obj` is allocated in `b_entry`, merged with `unk` in `Phi` -> `alias_phi`
    // (`sites = {base_obj_site}`, `has_unknown = true`). `alias_phi.secret = secret`,
    // `alias_phi` dies at `nop`, then `rest = CreateObjectWithExcludedKeys(base_obj, ["other"])`!
    let base_obj = alloc_object(&mut m, b_entry);
    emit_void(
        &mut m,
        b_entry,
        Op::CondBranch {
            cond,
            true_dest: b_k,
            false_dest: b_u,
        },
    );
    link(&mut m, b_entry, b_k);
    link(&mut m, b_entry, b_u);

    let k_mov = emit(&mut m, b_k, Op::Mov { src: base_obj });
    emit_void(&mut m, b_k, Op::Branch { dest: b_join });
    link(&mut m, b_k, b_join);

    let u_cal = try_get_global(&mut m, b_u, "unknownObj");
    let u_obj = emit(
        &mut m,
        b_u,
        Op::Call {
            callee: u_cal,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_u, Op::Branch { dest: b_join });
    link(&mut m, b_u, b_join);

    let alias_phi = emit(
        &mut m,
        b_join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b_k,
                        kind: EdgeKind::Normal,
                    },
                    k_mov,
                ),
                (
                    Edge {
                        from: b_u,
                        kind: EdgeKind::Normal,
                    },
                    u_obj,
                ),
            ],
        },
    );
    emit_void(
        &mut m,
        b_join,
        Op::StoreProp {
            object: alias_phi,
            name: sym_secret,
            value: secret,
        },
    );
    let _nop3 = load_number(&mut m, b_join, 1.0);
    let key_other = load_string(&mut m, b_join, "other");
    let _ = sym_other;
    let rest_obj = emit(
        &mut m,
        b_join,
        Op::CreateObjectWithExcludedKeys {
            obj: base_obj,
            keys: vec![key_other],
        },
    );
    let rest_sec = emit(
        &mut m,
        b_join,
        Op::LoadProp {
            object: rest_obj,
            name: sym_secret,
        },
    );
    let sink_excl = emit_print_sink(&mut m, b_join, rest_sec);
    emit_void(&mut m, b_join, Op::Return { value: None });

    for rung in [0u8, 1, 2] {
        let mut cfg = cfg_at_rung(rung);
        cfg.extra_summaries.push((
            "freshBox".to_owned(),
            Some(0),
            Summary::new("returns fresh unkeyed object").exclusive(),
        ));
        let report = run_taint(&m, &cfg);
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_mov_root_read),
            "rung {rung}: `v2 = Mov(v1); v2.secret = src(); nop; sink(v1.secret)` must hit: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_mov_alias_read),
            "rung {rung}: `w2 = Mov(w1); w1.secret = src(); nop; sink(w2.secret)` must hit: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_excl),
            "rung {rung}: `CreateObjectWithExcludedKeys` alias load must retain taint: {hit_calls:?}"
        );
    }
}

/// `P3-TAINT-4(d)`: Under Rung 2 on a multi-record ESM module, passing a local
/// allocation `box` to an unmodeled external void call (`customStorage.putSync("k", box)`)
/// MUST mark `box` as escaped so `got = customStorage.getSync("k"); sink(got.secret)` hits,
/// whereas passing `cleanLoggedBox` only to `@ohos.hilog.info` does NOT escape it!
#[test]
fn p3_taint_4d_narrow_ext_void_custom_storage_escapes_while_hilog_does_not() {
    let mut m = Module::new();
    let sym_storage_req = m.sym.intern("@my/customStorage");
    let sym_hilog_req = m.sym.intern("@ohos.hilog");
    let sym_default = m.sym.intern("default");
    let sym_storage = m.sym.intern("customStorage");
    let sym_hilog = m.sym.intern("hilog");
    let sym_put = m.sym.intern("putSync");
    let sym_get = m.sym.intern("getSync");
    let sym_info = m.sym.intern("info");
    let sym_secret = m.sym.intern("secret");
    let sym_logged_only = m.sym.intern("loggedOnly");
    let sym_helper_req = m.sym.intern("./helper");
    let sym_read_back = m.sym.intern("readBack");

    let helper_cid = add_esm_record(
        &mut m,
        "Lhelper;",
        EsModule {
            imports: vec![ImportDecl::Regular {
                local_name: sym_storage,
                import_name: sym_default,
                module_request: sym_storage_req,
            }],
            exports: vec![ExportDecl::Local {
                export_name: sym_read_back,
                local_name: sym_read_back,
            }],
            module_requests: vec![ModuleRequest {
                specifier: sym_storage_req,
                lazy: false,
            }],
        },
    );
    let entry_cid = add_esm_record(
        &mut m,
        "Lentry;",
        EsModule {
            imports: vec![
                ImportDecl::Regular {
                    local_name: sym_storage,
                    import_name: sym_default,
                    module_request: sym_storage_req,
                },
                ImportDecl::Regular {
                    local_name: sym_hilog,
                    import_name: sym_default,
                    module_request: sym_hilog_req,
                },
                ImportDecl::Regular {
                    local_name: sym_read_back,
                    import_name: sym_read_back,
                    module_request: sym_helper_req,
                },
            ],
            exports: vec![],
            module_requests: vec![
                ModuleRequest {
                    specifier: sym_storage_req,
                    lazy: false,
                },
                ModuleRequest {
                    specifier: sym_hilog_req,
                    lazy: false,
                },
                ModuleRequest {
                    specifier: sym_helper_req,
                    lazy: false,
                },
            ],
        },
    );

    let read_back_fn = add_static_fn_in(&mut m, helper_cid, "readBackBody", FunctionKind::Function);
    let sink_stored;
    let sink_logged_only;
    {
        let b = entry_of(&m, read_back_fn);
        for i in 0..3 {
            add_param(&mut m, read_back_fn, i);
        }
        let st = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let get_fn = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: st,
                name: sym_get,
            },
        );
        let key = load_string(&mut m, b, "k");
        let got = emit(
            &mut m,
            b,
            Op::Call {
                callee: get_fn,
                this: Some(st),
                args: vec![key],
                kind: CallKind::Dynamic,
            },
        );
        let v_sec = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: got,
                name: sym_secret,
            },
        );
        let v_log = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: got,
                name: sym_logged_only,
            },
        );
        sink_stored = emit_print_sink(&mut m, b, v_sec);
        sink_logged_only = emit_print_sink(&mut m, b, v_log);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let helper_main = add_static_fn_in(&mut m, helper_cid, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, helper_main);
        let fref = load_method_ref(&mut m, b, read_back_fn);
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: fref,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let store_worker = add_static_fn_in(&mut m, entry_cid, "storeWorker", FunctionKind::Function);
    {
        let b = entry_of(&m, store_worker);
        for i in 0..3 {
            add_param(&mut m, store_worker, i);
        }
        let src = add_param(&mut m, store_worker, 3);

        // `stored_box` passed to `customStorage.putSync("k", stored_box)` (unused result!).
        let stored_box = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: stored_box,
                name: sym_secret,
                value: src,
            },
        );
        let st = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let put_fn = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: st,
                name: sym_put,
            },
        );
        let k_str = load_string(&mut m, b, "k");
        let _unused = emit(
            &mut m,
            b,
            Op::Call {
                callee: put_fn,
                this: Some(st),
                args: vec![k_str, stored_box],
                kind: CallKind::Dynamic,
            },
        );

        // `logged_box` passed ONLY to `@ohos.hilog.info(...)` (non-escaping logging sink!).
        let logged_box = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: logged_box,
                name: sym_logged_only,
                value: src,
            },
        );
        let hl = emit(
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
                object: hl,
                name: sym_info,
            },
        );
        let dom = load_number(&mut m, b, 0.0);
        let tag = load_string(&mut m, b, "tag");
        let _unused_log = emit(
            &mut m,
            b,
            Op::Call {
                callee: info_fn,
                this: Some(hl),
                args: vec![dom, tag, logged_box],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let entry_main = add_static_fn_in(&mut m, entry_cid, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, entry_main);
        let src = try_get_global(&mut m, b, "SECRET_TOKEN");
        let sw_ref = load_method_ref(&mut m, b, store_worker);
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: sw_ref,
                this: None,
                args: vec![src],
                kind: CallKind::Direct,
            },
        );
        let rb = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 2,
                kind: ModuleVarKind::External,
            },
        );
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: rb,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let cfg = TaintConfig {
        sources: vec![SourceSpec::GlobalLoad {
            name: "SECRET_TOKEN".to_owned(),
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        builtin_summaries: false,
        alias_rung: 2,
        ..TaintConfig::default()
    };
    let report = run_taint(&m, &cfg);
    let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
    assert!(
        hit_calls.contains(&sink_stored),
        "Rung 2: unmodeled external void call `customStorage.putSync` must escape `stored_box`: {hit_calls:?}"
    );
    assert!(
        !hit_calls.contains(&sink_logged_only),
        "Rung 2: `@ohos.hilog.info` must NOT mark `logged_box` as escaped into `customStorage`: {hit_calls:?}"
    );
}

/// `P3-TAINT-4(e)`: Signed and special canonical numeric property keys (`"-1"`,
/// `"NaN"`, `"Infinity"`, `"-Infinity"`) are `AnyIndex`-compatible so
/// `o[-1] = src; sink(o["-1"])` preserves heap taint while `o["-foo"]` stays clean.
#[test]
fn p3_taint_4e_signed_and_special_numeric_property_keys() {
    let mut m = mk_module();
    let sym_neg1 = intern(&mut m, "-1");
    let sym_nan = intern(&mut m, "NaN");
    let sym_inf = intern(&mut m, "Infinity");
    let sym_ninf = intern(&mut m, "-Infinity");
    let sym_neg_foo = intern(&mut m, "-foo");

    let reader_fn = add_func_named(&mut m, "readNumericProps");
    m.func_mut(reader_fn).unwrap().modifiers = Modifiers::STATIC;
    let sink_neg1;
    let sink_nan;
    let sink_inf;
    let sink_ninf;
    let sink_neg_foo;
    {
        let b = entry_of(&m, reader_fn);
        add_param(&mut m, reader_fn, 0);
        add_param(&mut m, reader_fn, 1);
        add_param(&mut m, reader_fn, 2);
        let obj = add_param(&mut m, reader_fn, 3);

        let k_neg1 = load_string(&mut m, b, "-1");
        let v_neg1 = emit(
            &mut m,
            b,
            Op::LoadPropDyn {
                object: obj,
                key: k_neg1,
            },
        );
        let v_nan = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: obj,
                name: sym_nan,
            },
        );
        let v_inf = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: obj,
                name: sym_inf,
            },
        );
        let v_ninf = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: obj,
                name: sym_ninf,
            },
        );
        let v_neg_foo = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: obj,
                name: sym_neg_foo,
            },
        );
        let _ = sym_neg1;
        sink_neg1 = emit_print_sink(&mut m, b, v_neg1);
        sink_nan = emit_print_sink(&mut m, b, v_nan);
        sink_inf = emit_print_sink(&mut m, b, v_inf);
        sink_ninf = emit_print_sink(&mut m, b, v_ninf);
        sink_neg_foo = emit_print_sink(&mut m, b, v_neg_foo);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    m.func_mut(main_fn).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, main_fn);
        add_param(&mut m, main_fn, 0);
        add_param(&mut m, main_fn, 1);
        add_param(&mut m, main_fn, 2);
        let secret = add_param(&mut m, main_fn, 3);

        let obj = alloc_object(&mut m, b);
        let one = load_number(&mut m, b, 1.0);
        let minus_one = emit(
            &mut m,
            b,
            Op::UnaryOp {
                op: UnOp::Minus,
                operand: one,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StorePropDyn {
                object: obj,
                key: minus_one,
                value: secret,
            },
        );
        let rref = load_method_ref(&mut m, b, reader_fn);
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: rref,
                this: None,
                args: vec![obj],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    for rung in [0u8, 1, 2] {
        let report = run_taint(&m, &cfg_at_rung(rung));
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_neg1),
            "rung {rung}: `o[-1] = src; sink(o[\"-1\"])` must hit: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_nan),
            "rung {rung}: `AnyIndex` store must match `o.NaN`: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_inf),
            "rung {rung}: `AnyIndex` store must match `o.Infinity`: {hit_calls:?}"
        );
        assert!(
            hit_calls.contains(&sink_ninf),
            "rung {rung}: `AnyIndex` store must match `o[\"-Infinity\"]`: {hit_calls:?}"
        );
        assert!(
            !hit_calls.contains(&sink_neg_foo),
            "rung {rung}: non-numeric `o[\"-foo\"]` must NOT match `AnyIndex`: {hit_calls:?}"
        );
    }
}

/// `P3-TAINT-4(f)`: `PreparedModule::owned` (which calls `module.sym.drop_index()`
/// and `module.consts.drop_index()`) runs cleanly at `--alias-rung 0`, `1`, and `2`
/// without rebuilding `ModuleLinkTable` over a dropped-index `SymbolTable` and
/// honoring `harness_fid` across multi-record ESM + OHOS Ability lifecycle!
#[test]
fn p3_taint_4f_prepared_module_dropped_index_runs_cleanly_at_rungs_0_1_2() {
    let mut m = Module::new();
    let sym_ability_kit = m.sym.intern("@kit.AbilityKit");
    let sym_hilog_req = m.sym.intern("@ohos.hilog");
    let sym_helper_req = m.sym.intern("./helper");
    let sym_ui_ability = m.sym.intern("UIAbility");
    let sym_default = m.sym.intern("default");
    let sym_hilog = m.sym.intern("hilog");
    let sym_forward = m.sym.intern("forwardUri");
    let sym_on_create = m.sym.intern("onCreate");
    let sym_uri = m.sym.intern("uri");
    let sym_tok = m.sym.intern("tok");
    let sym_info = m.sym.intern("info");

    // Record 0 (`Lhelper;`): exports `forwardUri(want)` which stores into a concrete
    // singleton object, reads back, and logs via `@ohos.hilog.info` (exercising
    // `SingletonSiteClassifier` + witness-path replay at Rungs 0, 1, 2!).
    let helper_cid = add_esm_record(
        &mut m,
        "Lhelper;",
        EsModule {
            imports: vec![ImportDecl::Regular {
                local_name: sym_hilog,
                import_name: sym_default,
                module_request: sym_hilog_req,
            }],
            exports: vec![ExportDecl::Local {
                export_name: sym_forward,
                local_name: sym_forward,
            }],
            module_requests: vec![ModuleRequest {
                specifier: sym_hilog_req,
                lazy: false,
            }],
        },
    );
    let entry_cid = add_esm_record(
        &mut m,
        "Lentry;",
        EsModule {
            imports: vec![
                ImportDecl::Regular {
                    local_name: sym_ui_ability,
                    import_name: sym_ui_ability,
                    module_request: sym_ability_kit,
                },
                ImportDecl::Regular {
                    local_name: sym_forward,
                    import_name: sym_forward,
                    module_request: sym_helper_req,
                },
            ],
            exports: vec![],
            module_requests: vec![
                ModuleRequest {
                    specifier: sym_ability_kit,
                    lazy: false,
                },
                ModuleRequest {
                    specifier: sym_helper_req,
                    lazy: false,
                },
            ],
        },
    );

    let forward_fn = add_static_fn_in(&mut m, helper_cid, "forwardUriImpl", FunctionKind::Function);
    let sink_hilog;
    {
        let b = entry_of(&m, forward_fn);
        add_param(&mut m, forward_fn, 0);
        add_param(&mut m, forward_fn, 1);
        add_param(&mut m, forward_fn, 2);
        let want_p = add_param(&mut m, forward_fn, 3);

        let uri_v = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: want_p,
                name: sym_uri,
            },
        );
        let box_obj = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: box_obj,
                name: sym_tok,
                value: uri_v,
            },
        );
        let loaded = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: box_obj,
                name: sym_tok,
            },
        );
        let hl = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let info_fn = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: hl,
                name: sym_info,
            },
        );
        let dom = load_number(&mut m, b, 0.0);
        let tag = load_string(&mut m, b, "prep");
        sink_hilog = push_inst(
            &mut m,
            b,
            Op::Call {
                callee: info_fn,
                this: Some(hl),
                args: vec![dom, tag, loaded],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let helper_main = add_static_fn_in(&mut m, helper_cid, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, helper_main);
        let fref = load_method_ref(&mut m, b, forward_fn);
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: fref,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let ability_ctor =
        add_static_fn_in(&mut m, entry_cid, "EntryAbility", FunctionKind::Constructor);
    {
        let b = entry_of(&m, ability_ctor);
        for i in 0..3 {
            add_param(&mut m, ability_ctor, i);
        }
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let on_create_fn = add_static_fn_in(&mut m, entry_cid, "onCreate", FunctionKind::Function);
    {
        let b = entry_of(&m, on_create_fn);
        add_param(&mut m, on_create_fn, 0);
        add_param(&mut m, on_create_fn, 1);
        add_param(&mut m, on_create_fn, 2);
        let want_arg = add_param(&mut m, on_create_fn, 3);
        let fwd = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 1,
                kind: ModuleVarKind::External,
            },
        );
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: fwd,
                this: None,
                args: vec![want_arg],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let entry_main = add_static_fn_in(&mut m, entry_cid, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, entry_main);
        let base_cls = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let c_name = m.consts.push(Const::String(sym_on_create));
        let c_mref = m.consts.push(Const::MethodRef {
            func: on_create_fn,
            kind: LitMethodKind::Method,
        });
        let c_cnt = m.consts.push(Const::Int32(1));
        let members = m
            .consts
            .push(Const::ArrayLiteral(vec![c_name, c_mref, c_cnt]));
        let _ = emit(
            &mut m,
            b,
            Op::DefineClass(Box::new(DefineClassData {
                ctor: ability_ctor,
                members,
                count: 0,
                heritage: Some(base_cls),
                member_attrs: vec![MemberAttrs {
                    is_static: false,
                    kind: FunctionKind::Function,
                }],
            })),
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let base_cfg = ohos_preset();
    let prepared = PreparedModule::owned(m, &base_cfg);

    for rung in [0u8, 1, 2] {
        let mut cfg = ohos_preset();
        cfg.alias_rung = rung;
        cfg.pta_step_budget = Some(100_000);
        let report = run_taint_prepared(&prepared, &cfg);
        assert_eq!(report.alias_rung_used, rung);
        let hit = report
            .hits
            .iter()
            .find(|h| h.call == sink_hilog)
            .unwrap_or_else(|| {
                panic!(
                    "rung {rung}: PreparedModule after drop_index() must resolve cross-module ESM + OHOS harness flow: {:?}",
                    report.hits
                )
            });
        assert!(
            !hit.path.is_empty(),
            "rung {rung}: witness path replay must succeed on dropped-index PreparedModule"
        );
    }
}

/// `P3-TAINT-1` (post-convergence certifying): When `class Sub extends getBase()`
/// only links to `Base` after `getBase()`'s `func_ret_prov` resolves in Round 0 Step 6,
/// `Sub`'s unsealed instance (`Object.defineProperty(subInst, ...)`) unseals `Base` in
/// Round 1 Step 4 and MUST invalidate `Base.dispatch`'s provisional Round-0
/// `this.run(x)` closed-call certification.
#[test]
fn p3_taint_1_post_convergence_certifying_drops_provisional_closed_call() {
    let mut m = mk_module();
    let sym_run = intern(&mut m, "run");
    let sym_dispatch = intern(&mut m, "dispatch");
    let sym_def_prop = intern(&mut m, "defineProperty");

    let base_ctor = add_func_named(&mut m, "Base_ctor");
    m.func_mut(base_ctor).unwrap().kind = FunctionKind::Constructor;
    m.func_mut(base_ctor).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, base_ctor);
        for i in 0..3 {
            add_param(&mut m, base_ctor, i);
        }
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let base_run = add_func_named(&mut m, "Base_run");
    m.func_mut(base_run).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, base_run);
        for i in 0..4 {
            add_param(&mut m, base_run, i);
        }
        let clean = load_string(&mut m, b, "clean");
        emit_void(&mut m, b, Op::Return { value: Some(clean) });
    }
    let base_dispatch = add_func_named(&mut m, "Base_dispatch");
    m.func_mut(base_dispatch).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, base_dispatch);
        add_param(&mut m, base_dispatch, 0);
        add_param(&mut m, base_dispatch, 1);
        let this_v = add_param(&mut m, base_dispatch, 2);
        let x = add_param(&mut m, base_dispatch, 3);
        let rcal = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: this_v,
                name: sym_run,
            },
        );
        let r = emit(
            &mut m,
            b,
            Op::Call {
                callee: rcal,
                this: Some(this_v),
                args: vec![x],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(r) });
    }

    let get_base_fn = add_func_named(&mut m, "getBase");
    m.func_mut(get_base_fn).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, get_base_fn);
        for i in 0..3 {
            add_param(&mut m, get_base_fn, i);
        }
        let _ = emit(
            &mut m,
            b,
            Op::NewLexEnv {
                num_vars: 1,
                kind: LexEnvKind::Plain,
            },
        );
        let cls_v = emit(
            &mut m,
            b,
            Op::GetLexVar {
                level: 1,
                slot: 0,
                kind: LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(cls_v) });
    }

    let sub_ctor = add_func_named(&mut m, "Sub_ctor");
    m.func_mut(sub_ctor).unwrap().kind = FunctionKind::Constructor;
    m.func_mut(sub_ctor).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, sub_ctor);
        for i in 0..3 {
            add_param(&mut m, sub_ctor, i);
        }
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    m.func_mut(main_fn).unwrap().modifiers = Modifiers::STATIC;
    let sink_iid;
    {
        let b = entry_of(&m, main_fn);
        add_param(&mut m, main_fn, 0);
        add_param(&mut m, main_fn, 1);
        add_param(&mut m, main_fn, 2);
        let secret = add_param(&mut m, main_fn, 3);

        let _ = emit(
            &mut m,
            b,
            Op::NewLexEnv {
                num_vars: 1,
                kind: LexEnvKind::Plain,
            },
        );
        let base_items = vec![
            m.consts.push(Const::String(sym_run)),
            m.consts.push(Const::MethodRef {
                func: base_run,
                kind: LitMethodKind::Method,
            }),
            m.consts.push(Const::String(sym_dispatch)),
            m.consts.push(Const::MethodRef {
                func: base_dispatch,
                kind: LitMethodKind::Method,
            }),
            m.consts.push(Const::Int32(2)),
        ];
        let base_members = m.consts.push(Const::ArrayLiteral(base_items));
        let base_cls = emit(
            &mut m,
            b,
            Op::DefineClass(Box::new(DefineClassData {
                ctor: base_ctor,
                members: base_members,
                count: 0,
                heritage: None,
                member_attrs: vec![
                    MemberAttrs {
                        is_static: false,
                        kind: FunctionKind::Function,
                    },
                    MemberAttrs {
                        is_static: false,
                        kind: FunctionKind::Function,
                    },
                ],
            })),
        );
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: base_cls,
                kind: LexEnvKind::Plain,
            },
        );

        let gb_clo = closure_of(&mut m, b, get_base_fn);
        let sup_val = emit(
            &mut m,
            b,
            Op::Call {
                callee: gb_clo,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let zero_cnt = m.consts.push(Const::Int32(0));
        let sub_members = m.consts.push(Const::ArrayLiteral(vec![zero_cnt]));
        let sub_cls = emit(
            &mut m,
            b,
            Op::DefineClass(Box::new(DefineClassData {
                ctor: sub_ctor,
                members: sub_members,
                count: 0,
                heritage: Some(sup_val),
                member_attrs: vec![],
            })),
        );
        let sub_inst = emit(
            &mut m,
            b,
            Op::Call {
                callee: sub_cls,
                this: None,
                args: vec![],
                kind: CallKind::New,
            },
        );
        // Monkey-patch `sub_inst` via `Object.defineProperty(sub_inst, "run", desc)` so `Sub` is unsealed!
        let obj_glob = try_get_global(&mut m, b, "Object");
        let def_prop = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: obj_glob,
                name: sym_def_prop,
            },
        );
        let k_run = load_string(&mut m, b, "run");
        let desc = alloc_object(&mut m, b);
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: def_prop,
                this: Some(obj_glob),
                args: vec![sub_inst, k_run, desc],
                kind: CallKind::Dynamic,
            },
        );

        let dcal = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: sub_inst,
                name: sym_dispatch,
            },
        );
        let out_v = emit(
            &mut m,
            b,
            Op::Call {
                callee: dcal,
                this: Some(sub_inst),
                args: vec![secret],
                kind: CallKind::Dynamic,
            },
        );
        sink_iid = emit_print_sink(&mut m, b, out_v);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    for rung in [0u8, 1, 2] {
        let mut cfg = cfg_at_rung(rung);
        cfg.native_identity = true;
        let report = run_taint(&m, &cfg);
        let hit_calls: Vec<_> = report.hits.iter().map(|h| h.call).collect();
        assert!(
            hit_calls.contains(&sink_iid),
            "rung {rung}: Round-0 provisional closed call in `Base.dispatch` must be invalidated once `Sub extends getBase()` unseals `Base`: {hit_calls:?}"
        );
    }
}
