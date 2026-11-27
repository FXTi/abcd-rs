use super::*;
use abcd_analysis::dataflow::heap::FieldKey;
use abcd_analysis::ohos_lifecycle::{OHOS_CONTEXT_GLOBAL, OHOS_HARNESS_FUNC, OHOS_WANT_GLOBAL};
use abcd_ir::consts::Const;
use abcd_ir::function::{Block, FunctionData, Inst, Value};
use abcd_ir::module::{ClassData, FunctionKind, Modifiers};
use abcd_ir::ty::Ty;
use abcd_ir::{CallKind, ClassId, DefineClassData, ValueDef, ValueId};

fn add_fn(
    m: &mut Module,
    cid: ClassId,
    name: &str,
    kind: FunctionKind,
    num_params: u16,
) -> (FuncId, BlockId, Vec<ValueId>) {
    let sym = m.sym.intern(name);
    let fid = FuncId::new(m.functions.len() as u32);
    let mut fd = FunctionData::new(cid, sym, kind);
    fd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    let bid = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    fd.blocks.push(bid);
    let mut params = Vec::with_capacity(num_params as usize);
    for idx in 0..num_params {
        let vid = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Param(idx),
            ty: Ty::Any,
        });
        params.push(vid);
    }
    fd.params.clone_from(&params);
    m.functions.push(fd);
    m.classes[cid.index()].methods.push(fid);
    (fid, bid, params)
}

fn emit_val(m: &mut Module, block: BlockId, op: Op) -> ValueId {
    let iid = InstId::new(m.insts.len() as u32);
    let vid = ValueId::new(m.values.len() as u32);
    m.insts.push(Inst {
        op,
        result: Some(vid),
        block,
        loc: None,
    });
    m.values.push(Value {
        def: ValueDef::Inst(iid),
        ty: Ty::Any,
    });
    m.blocks[block.index()].insts.push(iid);
    vid
}

fn emit_void(m: &mut Module, block: BlockId, op: Op) -> InstId {
    let iid = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op,
        result: None,
        block,
        loc: None,
    });
    m.blocks[block.index()].insts.push(iid);
    iid
}

/// `#73`: Verify `report.hits` sorts strictly by `(call, position, fact, sink)`
/// when multiple distinct `TaintFact`s and matching `SinkSpec`s collide on the
/// exact same `(call, position)`.
#[test]
fn hits_sort_strictly_by_fact_and_sink_at_same_call_and_position() {
    let mut m = Module::new();
    let d_glob = m.sym.intern("L_GLOBAL;");
    let n_glob = m.sym.intern("_GLOBAL");
    let cid = ClassId::new(0);
    m.classes.push(ClassData::new(d_glob, n_glob));

    // Intern `first_prop` before `second_prop` so `Sym(first_prop) < Sym(second_prop)`.
    let sym_first = m.sym.intern("first_prop");
    let sym_second = m.sym.intern("second_prop");
    assert!(sym_first < sym_second);

    // Internal sink body named `"alpha_sink"` loaded via `LoadConst(MethodRef)` and
    // stored on `globalThis.zeta_sink` so callee-name resolution yields BOTH
    // `"zeta_sink"` and `"alpha_sink"` at the exact same call site.
    let (sink_fn, b_sink, _) = add_fn(&mut m, cid, "alpha_sink", FunctionKind::Function, 4);
    emit_void(&mut m, b_sink, Op::Return { value: None });

    let (_main_fn, b_main, _) = add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
    let src_sym = m.sym.intern("TAINT_SRC");
    let taint = emit_val(
        &mut m,
        b_main,
        Op::TryGetGlobal {
            name: src_sym,
            default: None,
        },
    );
    let empty_shape = m.consts.push_object(Vec::new(), Vec::new());
    let obj = emit_val(&mut m, b_main, Op::AllocObject { shape: empty_shape });

    // Store `second_prop` FIRST and `first_prop` SECOND so solver arrival order
    // at the sink is `[second_prop, first_prop]` (`fact[0] > fact[1]` prior to sort).
    emit_void(
        &mut m,
        b_main,
        Op::StoreProp {
            object: obj,
            name: sym_second,
            value: taint,
        },
    );
    emit_void(
        &mut m,
        b_main,
        Op::StoreProp {
            object: obj,
            name: sym_first,
            value: taint,
        },
    );

    let zeta_sym = m.sym.intern("zeta_sink");
    let sink_ref_cid = m.consts.push(Const::method_ref(sink_fn));
    let sink_ref_v = emit_val(&mut m, b_main, Op::LoadConst(sink_ref_cid));
    emit_void(
        &mut m,
        b_main,
        Op::StoreGlobal {
            name: zeta_sym,
            value: sink_ref_v,
        },
    );
    let dyn_callee = emit_val(
        &mut m,
        b_main,
        Op::TryGetGlobal {
            name: zeta_sym,
            default: None,
        },
    );
    // Phi merges `dyn_callee` (`TryGetGlobal("zeta_sink")`) and `sink_ref_v` (`alpha_sink`)
    // in a straight-line block? Simpler: call `sink_ref_v` directly while registering
    // duplicate/distinct sinks? Better: `DefineClass` / `TryGetGlobal`: a direct call to
    // `dyn_callee` when `Rung2` resolves `StoreGlobal`? Let's pass `sink_ref_v` via `Mov`
    // or test two `SinkSpec::Call`s matching `"console.log"` vs `"Console.log"` or
    // `TryGetGlobal("zeta_sink")` resolved via module var!
    let _ = dyn_callee;
    let mod_slot = 0u32;
    emit_void(
        &mut m,
        b_main,
        Op::StoreModuleVar {
            index: mod_slot,
            value: sink_ref_v,
        },
    );
    // Calling `sink_ref_v` directly resolves `FunctionData::name` == `"alpha_sink"`;
    // calling a `LoadProp` on `TryGetGlobal("zeta_ns")` that PTA resolves to `sink_fn`
    // yields BOTH `"zeta_ns.run"` (from global load chain) and `"alpha_sink"` (from
    // resolved callee `FunctionData::name`)!
    let ns_sym = m.sym.intern("zeta_ns");
    let run_sym = m.sym.intern("run");
    let ns_obj = emit_val(&mut m, b_main, Op::AllocObject { shape: empty_shape });
    emit_void(
        &mut m,
        b_main,
        Op::StoreProp {
            object: ns_obj,
            name: run_sym,
            value: sink_ref_v,
        },
    );
    emit_void(
        &mut m,
        b_main,
        Op::StoreGlobal {
            name: ns_sym,
            value: ns_obj,
        },
    );
    let ns_loaded = emit_val(
        &mut m,
        b_main,
        Op::TryGetGlobal {
            name: ns_sym,
            default: None,
        },
    );
    let callee_v = emit_val(
        &mut m,
        b_main,
        Op::LoadProp {
            object: ns_loaded,
            name: run_sym,
        },
    );
    let sink_call = InstId::new(m.insts.len() as u32);
    let _ = emit_val(
        &mut m,
        b_main,
        Op::Call {
            callee: callee_v,
            this: Some(ns_loaded),
            args: vec![obj],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b_main, Op::Return { value: None });

    let cfg = TaintConfig {
        sources: vec![SourceSpec::GlobalLoad {
            name: "TAINT_SRC".to_owned(),
        }],
        // Intentionally list `"zeta_ns.run"` BEFORE `"alpha_sink"`.
        sinks: vec![
            SinkSpec::Call {
                name: "zeta_ns.run".to_owned(),
            },
            SinkSpec::Call {
                name: "alpha_sink".to_owned(),
            },
        ],
        ohos_lifecycle: false,
        ..TaintConfig::default()
    };

    let rep = run_taint(&m, &cfg);
    let arg0_hits: Vec<&SinkHit> = rep
        .hits
        .iter()
        .filter(|h| h.call == sink_call && h.position == "arg 0")
        .collect();
    assert!(
        arg0_hits.len() >= 4,
        "expected >= 4 hits (2 field facts x 2 sink names), got {}",
        arg0_hits.len()
    );
    for pair in arg0_hits.windows(2) {
        let lhs = (
            pair[0].call,
            &pair[0].position,
            &pair[0].fact,
            &pair[0].sink,
        );
        let rhs = (
            pair[1].call,
            &pair[1].position,
            &pair[1].fact,
            &pair[1].sink,
        );
        assert!(
            lhs <= rhs,
            "SinkHit slice must be strictly sorted by (call, position, fact, sink): {lhs:?} > {rhs:?}"
        );
    }
    // Verify `sym_first` appears strictly before `sym_second` among field-bearing hits,
    // and `"alpha_sink"` appears before `"zeta_ns.run"` for identical facts.
    let named_hits: Vec<(abcd_ir::Sym, &str)> = arg0_hits
        .iter()
        .filter_map(|h| match h.fact.fields.elements() {
            [FieldKey::Named(s)] => Some((*s, h.sink.as_str())),
            _ => None,
        })
        .collect();
    assert!(named_hits.contains(&(sym_first, "alpha_sink")));
    assert!(named_hits.contains(&(sym_first, "zeta_ns.run")));
    assert!(named_hits.contains(&(sym_second, "alpha_sink")));
    assert!(named_hits.contains(&(sym_second, "zeta_ns.run")));
    for w in named_hits.windows(2) {
        assert!(w[0] <= w[1], "unsorted (field_sym, sink): {w:?}");
    }
}

/// `#71` & `#74`: Ability module WITHOUT `"context"` pre-interned in `module.sym`:
/// `PreparedModule::owned` synthesizes the harness in-place, drops hash indexes,
/// resolves `"context"` without `<sym N>`, and matches `run_taint(&orig, &cfg)`.
#[test]
fn prepared_module_owned_and_borrowed_preserve_harness_context_sym_and_parity() {
    let mut m = Module::new();
    let d_glob = m.sym.intern("L_GLOBAL;");
    let n_glob = m.sym.intern("_GLOBAL");
    let cid = ClassId::new(0);
    m.classes.push(ClassData::new(d_glob, n_glob));

    let (ctor, b_ctor, _) = add_fn(&mut m, cid, "EntryAbility", FunctionKind::Constructor, 3);
    emit_void(&mut m, b_ctor, Op::Return { value: None });

    // `onCreate(this, want)` forwards `this` (whose `.context` slot is initialized
    // by `__abcd_ohos_harness__`) directly to `sink(this)` WITHOUT mentioning `"context"`!
    let (on_create, b_oc, p_oc) = add_fn(&mut m, cid, "onCreate", FunctionKind::Function, 5);
    let s_sink = m.sym.intern("sink");
    let sink_callee = emit_val(
        &mut m,
        b_oc,
        Op::TryGetGlobal {
            name: s_sink,
            default: None,
        },
    );
    let _ = emit_val(
        &mut m,
        b_oc,
        Op::Call {
            callee: sink_callee,
            this: None,
            args: vec![p_oc[2]],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, b_oc, Op::Return { value: None });

    let (_main_fn, b_main, _) = add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
    let s_uiab = m.sym.intern("UIAbility");
    let uiab = emit_val(
        &mut m,
        b_main,
        Op::TryGetGlobal {
            name: s_uiab,
            default: None,
        },
    );
    let s_oc = m.sym.intern("onCreate");
    let c_oc_name = m.consts.push(Const::String(s_oc));
    let c_oc_ref = m.consts.push(Const::method_ref(on_create));
    let c_aff = m.consts.push(Const::Int32(2));
    let c_cnt = m.consts.push(Const::Int32(1));
    let members = m.consts.push_array(vec![c_oc_name, c_oc_ref, c_aff, c_cnt]);
    let _ = emit_val(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(DefineClassData {
            ctor,
            heritage: Some(uiab),
            members,
            member_attrs: Vec::new(),
            count: 1,
        })),
    );
    emit_void(&mut m, b_main, Op::Return { value: None });

    // Precondition: `"context"` is NOT interned in `m.sym` prior to preparation!
    assert_eq!(m.sym.get("context"), None);

    let cfg = TaintConfig {
        sources: vec![SourceSpec::GlobalLoad {
            name: OHOS_CONTEXT_GLOBAL.to_owned(),
        }],
        sinks: vec![SinkSpec::Call {
            name: "sink".to_owned(),
        }],
        ohos_lifecycle: true,
        ..TaintConfig::default()
    };

    let orig_rep = run_taint(&m, &cfg);
    let borrowed_prep = PreparedModule::borrowed(&m, &cfg);
    let borrowed_rep = run_taint_prepared(&borrowed_prep, &cfg);

    let owned_prep = PreparedModule::owned(m.clone(), &cfg);
    assert!(owned_prep.harness().and_then(|h| h.func).is_some());
    assert!(!owned_prep.module().sym.has_index());
    assert!(!owned_prep.module().consts.has_index());
    let owned_rep = run_taint_prepared(&owned_prep, &cfg);

    assert!(
        !owned_rep.hits.is_empty(),
        "expected tainted this.context hit"
    );
    assert_eq!(owned_rep.hits, orig_rep.hits);
    assert_eq!(owned_rep.hits, borrowed_rep.hits);
    assert_eq!(owned_rep.path_edges, orig_rep.path_edges);
    assert_eq!(owned_rep.alias_rung_used, orig_rep.alias_rung_used);

    let mut saw_context_field = false;
    for hit in &owned_rep.hits {
        for key in hit.fact.fields.elements() {
            if let FieldKey::Named(sym) = key {
                let resolved_owned = owned_prep.module().sym.resolve(*sym);
                let resolved_borrowed = borrowed_prep.module().sym.resolve(*sym);
                assert!(
                    resolved_owned.is_some(),
                    "Sym {sym:?} must resolve on PreparedModule::module() (no <sym N>)"
                );
                assert_eq!(resolved_owned, resolved_borrowed);
                if resolved_owned == Some("context") {
                    saw_context_field = true;
                }
            }
        }
    }
    assert!(
        saw_context_field,
        "expected TaintFact carrying harness-interned `.context` field"
    );

    // Also verify `PreparedModule::borrowed` on a plain non-OHOS module does ZERO clone.
    let mut plain = Module::new();
    let pd = plain.sym.intern("L_GLOBAL;");
    let pn = plain.sym.intern("_GLOBAL");
    plain.classes.push(ClassData::new(pd, pn));
    let (_, pb, _) = add_fn(
        &mut plain,
        ClassId::new(0),
        "func_main_0",
        FunctionKind::Function,
        3,
    );
    emit_void(&mut plain, pb, Op::Return { value: None });
    let plain_prep = PreparedModule::borrowed(&plain, &cfg);
    assert!(plain_prep.harness().is_some_and(|h| h.func.is_none()));
    assert!(
        std::ptr::eq(plain_prep.module(), &plain),
        "PreparedModule::borrowed must borrow in-place when !plan.needs_harness()"
    );
}

/// `#75`: A user function literally named `"__abcd_ohos_harness__"` must never be
/// suppressed or scrubbed, both standalone and alongside a genuine synthesized
/// OpenHarmony Ability harness.
#[test]
fn decoy_user_func_named_ohos_harness_is_never_suppressed_or_scrubbed() {
    let build_module = |with_real_ability: bool| -> (Module, FuncId) {
        let mut m = Module::new();
        let d_glob = m.sym.intern("L_GLOBAL;");
        let n_glob = m.sym.intern("_GLOBAL");
        let cid = ClassId::new(0);
        m.classes.push(ClassData::new(d_glob, n_glob));

        // User decoy function literally named `"__abcd_ohos_harness__"` reading a global
        // source AND a stored global, forwarding to `sink`.
        let (decoy_fn, b_decoy, _) =
            add_fn(&mut m, cid, OHOS_HARNESS_FUNC, FunctionKind::Function, 3);
        let s_src = m.sym.intern("USER_SECRET");
        let s_sink = m.sym.intern("sink");
        let secret = emit_val(
            &mut m,
            b_decoy,
            Op::TryGetGlobal {
                name: s_src,
                default: None,
            },
        );
        let sink_fn = emit_val(
            &mut m,
            b_decoy,
            Op::TryGetGlobal {
                name: s_sink,
                default: None,
            },
        );
        let _ = emit_val(
            &mut m,
            b_decoy,
            Op::Call {
                callee: sink_fn,
                this: None,
                args: vec![secret],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, b_decoy, Op::Return { value: None });

        if with_real_ability {
            let (ctor, b_ctor, _) =
                add_fn(&mut m, cid, "RealAbility", FunctionKind::Constructor, 3);
            emit_void(&mut m, b_ctor, Op::Return { value: None });

            let (on_create, b_oc, p_oc) =
                add_fn(&mut m, cid, "onCreate", FunctionKind::Function, 5);
            let sink_oc = emit_val(
                &mut m,
                b_oc,
                Op::TryGetGlobal {
                    name: s_sink,
                    default: None,
                },
            );
            let _ = emit_val(
                &mut m,
                b_oc,
                Op::Call {
                    callee: sink_oc,
                    this: None,
                    args: vec![p_oc[3]],
                    kind: CallKind::Direct,
                },
            );
            emit_void(&mut m, b_oc, Op::Return { value: None });

            let (_main_fn, b_main, _) =
                add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
            let s_uiab = m.sym.intern("UIAbility");
            let uiab = emit_val(
                &mut m,
                b_main,
                Op::TryGetGlobal {
                    name: s_uiab,
                    default: None,
                },
            );
            let s_oc = m.sym.intern("onCreate");
            let c_oc_name = m.consts.push(Const::String(s_oc));
            let c_oc_ref = m.consts.push(Const::method_ref(on_create));
            let c_aff = m.consts.push(Const::Int32(2));
            let c_cnt = m.consts.push(Const::Int32(1));
            let members = m.consts.push_array(vec![c_oc_name, c_oc_ref, c_aff, c_cnt]);
            let _ = emit_val(
                &mut m,
                b_main,
                Op::DefineClass(Box::new(DefineClassData {
                    ctor,
                    heritage: Some(uiab),
                    members,
                    member_attrs: Vec::new(),
                    count: 1,
                })),
            );
            // Invoke user's decoy `__abcd_ohos_harness__` from `func_main_0`.
            let decoy_ref_cid = m.consts.push(Const::method_ref(decoy_fn));
            let decoy_callee = emit_val(&mut m, b_main, Op::LoadConst(decoy_ref_cid));
            let _ = emit_val(
                &mut m,
                b_main,
                Op::Call {
                    callee: decoy_callee,
                    this: None,
                    args: Vec::new(),
                    kind: CallKind::Direct,
                },
            );
            emit_void(&mut m, b_main, Op::Return { value: None });
        } else {
            let (_main_fn, b_main, _) =
                add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
            let decoy_ref_cid = m.consts.push(Const::method_ref(decoy_fn));
            let decoy_callee = emit_val(&mut m, b_main, Op::LoadConst(decoy_ref_cid));
            let _ = emit_val(
                &mut m,
                b_main,
                Op::Call {
                    callee: decoy_callee,
                    this: None,
                    args: Vec::new(),
                    kind: CallKind::Direct,
                },
            );
            emit_void(&mut m, b_main, Op::Return { value: None });
        }

        (m, decoy_fn)
    };

    let cfg = TaintConfig {
        sources: vec![
            SourceSpec::GlobalLoad {
                name: "USER_SECRET".to_owned(),
            },
            SourceSpec::GlobalLoad {
                name: OHOS_WANT_GLOBAL.to_owned(),
            },
        ],
        sinks: vec![SinkSpec::Call {
            name: "sink".to_owned(),
        }],
        ohos_lifecycle: true,
        ..TaintConfig::default()
    };

    // 1. Standalone module with decoy `"__abcd_ohos_harness__"`.
    let (m_standalone, decoy_standalone) = build_module(false);
    let prep_standalone = PreparedModule::owned(m_standalone, &cfg);
    assert!(prep_standalone.harness().is_some_and(|h| h.func.is_none()));
    let rep_standalone = run_taint_prepared(&prep_standalone, &cfg);
    assert!(
        rep_standalone
            .hits
            .iter()
            .any(|h| h.seed.0 == decoy_standalone),
        "standalone decoy __abcd_ohos_harness__ hit must not be suppressed: {:?}",
        rep_standalone.hits
    );

    // 2. Module with BOTH user decoy `"__abcd_ohos_harness__"` AND a real Ability
    //    (so a genuine synthetic harness is ALSO synthesized at `FuncId(base_funcs)`).
    let (m_both, decoy_both) = build_module(true);
    let prep_both = PreparedModule::owned(m_both, &cfg);
    let synth_fid = prep_both
        .harness()
        .and_then(|h| h.func)
        .expect("genuine harness synthesized");
    assert_ne!(synth_fid, decoy_both);
    let rep_both = run_taint_prepared(&prep_both, &cfg);
    assert!(
        rep_both.hits.iter().any(|h| h.seed.0 == decoy_both),
        "user decoy __abcd_ohos_harness__ hit must survive alongside synthetic harness: {:?}",
        rep_both.hits
    );
    assert!(
        rep_both.hits.len() >= 2,
        "both decoy USER_SECRET flow and Ability onCreate(want) flow must fire"
    );
    assert!(
        rep_both.hits.iter().all(|h| h.seed.0 != synth_fid),
        "synthetic harness FuncId must still be scrubbed from user-facing seeds"
    );
}
