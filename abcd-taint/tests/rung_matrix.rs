//! Rung-matrix + driver arm coverage (c-COV W10): the `ABCD_TAINT_RUNG`
//! env only feeds `#[ignore]`d root-package suites, so the rung-0/1
//! oracle arms are covered IN-CRATE by constructing
//! `TaintConfig { alias_rung: 0/1/2, .. }` directly and running
//! mechanism fixtures through `run_taint`/`run_taint_full`. Also: the
//! `TaintConfig::default` path, the rung-2 → rung-1 budget degrade (via
//! the new `pta_step_budget` knob), the sink-position arms, the
//! block-terminal-call return sites, the throw-exit path detour, and
//! the unbalanced-return arm.

mod common;

use abcd_ir::{CallKind, Op};
use abcd_taint::driver::run_taint;
use abcd_taint::{SinkSpec, SourceSpec, TaintConfig};
use common::*;

/// The standard config (mechanisms.rs parity): all `func_main_0`
/// params are sources, `print` is the sink, no builtin summaries.
fn std_config() -> TaintConfig {
    TaintConfig {
        sources: vec![SourceSpec::FunctionParams {
            name: "func_main_0".to_owned(),
            params: None,
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        builtin_summaries: false,
        ..TaintConfig::default()
    }
}

/// `print(...)` call in block `b`; returns the call inst.
fn print_call(m: &mut abcd_ir::Module, b: abcd_ir::BlockId, args: Vec<abcd_ir::ValueId>) {
    let print = try_get_global(m, b, "print");
    push_inst(
        m,
        b,
        Op::Call {
            callee: print,
            this: None,
            args,
            kind: CallKind::Dynamic,
        },
    );
}

/// The default config's exact shape (the driver's default path feeds
/// the corpus smoke and the probe runner's non-matrix runs).
#[test]
fn taint_config_default_is_pinned() {
    let d = TaintConfig::default();
    assert!(d.sources.is_empty() && d.sinks.is_empty());
    assert!(d.builtin_summaries);
    assert!(d.extra_summaries.is_empty());
    assert!(d.seed_all_functions);
    assert!(d.follow_returns_past_seeds);
    assert!(d.native_identity);
    assert_eq!(
        d.max_field_chain,
        abcd_analysis::dataflow::heap::DEFAULT_MAX_FIELD_CHAIN
    );
    assert_eq!(d.alias_rung, 2);
    assert_eq!(d.pta_step_budget, None);
    // The default path runs end to end (an empty module analyzes).
    let m = mk_module();
    let report = run_taint(&m, &d);
    assert_eq!(report.alias_rung_used, 2);
    assert!(report.hits.is_empty());
}

/// Rung 0: a store through an unknown base keys by the empty-site
/// wildcard and reads back (the rung-0 heap model).
#[test]
fn rung0_unknown_base_store_reads_back() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let o = try_get_global(&mut m, entry, "o");
    let k = intern(&mut m, "k");
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: o,
            name: k,
            value: p,
        },
    );
    let x = emit(&mut m, entry, Op::LoadProp { object: o, name: k });
    print_call(&mut m, entry, vec![x]);
    // A method-style call: the prototype path runs `may_sites_at`
    // (the rung-0 arm answers with the local def-chain walk).
    let g = try_get_global(&mut m, entry, "gg");
    let pop = intern(&mut m, "pop");
    let gp = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: g,
            name: pop,
        },
    );
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: gp,
            this: Some(g),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let config = TaintConfig {
        alias_rung: 0,
        builtin_summaries: true,
        ..std_config()
    };
    let report = run_taint(&m, &config);
    assert_eq!(report.alias_rung_used, 0);
    assert_eq!(
        report.hits.len(),
        1,
        "the wildcard reads back: {:?}",
        report.hits
    );
}

/// Rung 1 over one module: the demand-driven engine's arms — the
// imprecise-store `aliases_of_store` bail, the may-answer fallback on
// an opaque receiver, the complete may-answer on a param receiver with
// recorded callers (the prototype may-arm, rung-1-exclusive), and the
// calling-context injection on a resolved body-step.
#[test]
fn rung1_engine_arms() {
    let mut m = mk_module();
    // helper(recv) { recv.pop(); } — the param receiver's unbalanced
    // fan-out answer is complete for RESOLUTION (the may-arm).
    let helper = add_func_named(&mut m, "helper");
    m.func_mut(helper).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    {
        let b = entry_of(&m, helper);
        add_param(&mut m, helper, 0);
        add_param(&mut m, helper, 1);
        add_param(&mut m, helper, 2);
        let recv = add_param(&mut m, helper, 3);
        let pop = intern(&mut m, "pop");
        let callee = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: recv,
                name: pop,
            },
        );
        push_inst(
            &mut m,
            b,
            Op::Call {
                callee,
                this: Some(recv),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // The imprecise store: a global-loaded base (engine: unknown).
    let o = try_get_global(&mut m, entry, "o");
    let k = intern(&mut m, "k");
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: o,
            name: k,
            value: p,
        },
    );
    let x = emit(&mut m, entry, Op::LoadProp { object: o, name: k });
    print_call(&mut m, entry, vec![x]);
    // The opaque receiver for the may-answer fallback.
    let g = try_get_global(&mut m, entry, "gg");
    let pop = intern(&mut m, "pop");
    let gpop = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: g,
            name: pop,
        },
    );
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: gpop,
            this: Some(g),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    // The unbalanced receiver: helper(a) with a an AllocArray.
    let a = alloc_array(&mut m, entry);
    let idx = load_number(&mut m, entry, 0.0);
    emit_void(
        &mut m,
        entry,
        Op::StorePropIdx {
            object: a,
            index: idx,
            value: p,
        },
    );
    let h = load_method_ref(&mut m, entry, helper);
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: h,
            this: None,
            args: vec![a],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let config = TaintConfig {
        alias_rung: 1,
        builtin_summaries: true,
        ..std_config()
    };
    let report = run_taint(&m, &config);
    assert_eq!(report.alias_rung_used, 1);
    // The imprecise store fell back to the rung-0 keying (the wildcard
    // reads back).
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(x)),
        "the store's baseline re-key carried the flow: {:?}",
        report.hits
    );
    // The unbalanced receiver typed Array through the may-arm: the
    // prototype summary applied.
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Array.prototype.pop"),
        "the rung-1-exclusive may-arm typed the param receiver: {:?}",
        report.summaries_applied
    );
    // The opaque receiver produced NO prototype candidate (the fallback
    // answer is empty), only the named miss.
    assert!(report.summary_misses.contains_key("gg.pop"));
    assert!(
        !report
            .summaries_applied
            .iter()
            .any(|(_, n)| n.contains("prototype") && n.contains("gg")),
        "no invented family: {:?}",
        report.summaries_applied
    );
}

/// Rung 2 with a zero PTA step budget: the capped engine degrades
/// loudly to the rung-1 pipeline (alias_rung_used == 1) and the flow
/// is still found (sound degradation, never silent).
#[test]
fn rung2_budget_cut_degrades_to_rung1() {
    let build = || {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "func_main_0");
        let entry = entry_of(&m, f);
        add_param(&mut m, f, 0);
        let p = add_param(&mut m, f, 1);
        let o = alloc_object(&mut m, entry);
        let k = intern(&mut m, "k");
        emit_void(
            &mut m,
            entry,
            Op::StoreProp {
                object: o,
                name: k,
                value: p,
            },
        );
        let x = emit(&mut m, entry, Op::LoadProp { object: o, name: k });
        print_call(&mut m, entry, vec![x]);
        emit_void(&mut m, entry, Op::Return { value: None });
        m
    };
    let capped = run_taint(
        &build(),
        &TaintConfig {
            alias_rung: 2,
            pta_step_budget: Some(0),
            ..std_config()
        },
    );
    assert_eq!(capped.alias_rung_used, 1, "the cut degrades to rung 1");
    assert_eq!(capped.hits.len(), 1, "the flow survives the degrade");
    let control = run_taint(
        &build(),
        &TaintConfig {
            alias_rung: 2,
            pta_step_budget: None,
            ..std_config()
        },
    );
    assert_eq!(
        control.alias_rung_used, 2,
        "the default budget holds rung 2"
    );
    assert_eq!(control.hits.len(), 1);
}

/// The legacy lexical channel (rungs 0 and 1): `PutLexVar` keys by
/// `(level, slot)` and `GetLexVar` reads it back.
#[test]
fn lexvar_legacy_channel_rungs_0_and_1() {
    let build = || {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "func_main_0");
        let entry = entry_of(&m, f);
        add_param(&mut m, f, 0);
        let p = add_param(&mut m, f, 1);
        emit_void(
            &mut m,
            entry,
            Op::PutLexVar {
                level: 0,
                slot: 2,
                value: p,
            },
        );
        let x = emit(&mut m, entry, Op::GetLexVar { level: 0, slot: 2 });
        print_call(&mut m, entry, vec![x]);
        emit_void(&mut m, entry, Op::Return { value: None });
        m
    };
    for rung in [0u8, 1] {
        let report = run_taint(
            &build(),
            &TaintConfig {
                alias_rung: rung,
                ..std_config()
            },
        );
        assert_eq!(report.alias_rung_used, rung);
        assert_eq!(
            report.hits.len(),
            1,
            "rung {rung}: the legacy (level, slot) channel reads back"
        );
    }
}

/// The rung-2 environment-identity channel, precise side: `PutLexVar`
/// keys by the `NewLexEnv` site (`Heap(env).[AnyIndex ++ chain]`) and a
/// same-function `GetLexVar` intersects it exactly.
#[test]
fn lexvar_precise_env_channel_rung2() {
    let mut m = mk_module();
    // w(t) { NewLexEnv; a1 = t.f1; E[0] = a1; x = E[0]; y = x.f1;
    // print(y) }.
    let w = add_func_named(&mut m, "w");
    m.func_mut(w).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    let y;
    {
        let b = entry_of(&m, w);
        add_param(&mut m, w, 0);
        add_param(&mut m, w, 1);
        add_param(&mut m, w, 2);
        let t = add_param(&mut m, w, 3);
        emit(&mut m, b, Op::NewLexEnv { num_vars: 1 });
        let f1 = intern(&mut m, "f1");
        let a1 = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: t,
                name: f1,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: a1,
            },
        );
        let x = emit(&mut m, b, Op::GetLexVar { level: 0, slot: 0 });
        y = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: x,
                name: f1,
            },
        );
        print_call(&mut m, b, vec![y]);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let wv = load_method_ref(&mut m, entry, w);
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: wv,
            this: None,
            args: vec![p],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = run_taint(&m, &std_config());
    assert_eq!(report.alias_rung_used, 2);
    // The precise channel's read-back: the [AnyIndex, f1] heap fact cut
    // to [] through the GetLexVar + LoadProp pair. (A second, may-hit
    // rides the unknown-base wildcard: the env-keyed heap fact also
    // matches the `x.f1` load directly — sound over-approximation.)
    assert!(
        report
            .hits
            .iter()
            .any(|h| h.fact.local_base() == Some(y) && h.fact.fields.is_empty()),
        "the precise env channel read the slot back: {:?}",
        report.hits
    );
}

/// The rung-2 environment channel, imprecise-reader fallback: the
/// reader has NO environment (its captured chain is empty), so a
/// `GetLexVar` matches ANY env-keyed fact (the may-direction rule).
#[test]
fn lexvar_imprecise_reader_fallback_rung2() {
    let mut m = mk_module();
    // w(t) { NewLexEnv; E[0] = t; } — the precise writer.
    let w = add_func_named(&mut m, "w");
    m.func_mut(w).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    {
        let b = entry_of(&m, w);
        add_param(&mut m, w, 0);
        add_param(&mut m, w, 1);
        add_param(&mut m, w, 2);
        let t = add_param(&mut m, w, 3);
        emit(&mut m, b, Op::NewLexEnv { num_vars: 1 });
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: t,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }
    // r() { x = GetLexVar(0,0); print(x) } — no env anywhere in r's
    // captured chain (defined before any NewLexEnv).
    let r = add_func_named(&mut m, "r");
    m.func_mut(r).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    {
        let b = entry_of(&m, r);
        let x = emit(&mut m, b, Op::GetLexVar { level: 0, slot: 0 });
        print_call(&mut m, b, vec![x]);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let wv = load_method_ref(&mut m, entry, w);
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: wv,
            this: None,
            args: vec![p],
            kind: CallKind::Direct,
        },
    );
    let rv = load_method_ref(&mut m, entry, r);
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: rv,
            this: None,
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = run_taint(&m, &std_config());
    assert_eq!(report.alias_rung_used, 2);
    assert_eq!(
        report.hits.len(),
        1,
        "the imprecise reader matched the env-keyed fact: {:?}",
        report.hits
    );
}

/// The module-variable channel plus the global-record/try-store arms:
/// `StoreModuleVar`/`LoadModuleVar` round-trip, and
/// `StoreGlobalRecord`/`TryStoreGlobal` feeding `TryGetGlobal`.
#[test]
fn module_var_and_global_store_channels() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    emit_void(&mut m, entry, Op::StoreModuleVar { index: 3, value: p });
    let x = emit(&mut m, entry, Op::LoadModuleVar { index: 3 });
    print_call(&mut m, entry, vec![x]);
    let gr = intern(&mut m, "GR");
    emit_void(
        &mut m,
        entry,
        Op::StoreGlobalRecord {
            name: gr,
            value: p,
            is_const: false,
        },
    );
    let ts = intern(&mut m, "TS");
    emit_void(&mut m, entry, Op::TryStoreGlobal { name: ts, value: p });
    let g1 = try_get_global(&mut m, entry, "GR");
    print_call(&mut m, entry, vec![g1]);
    let g2 = try_get_global(&mut m, entry, "TS");
    print_call(&mut m, entry, vec![g2]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = run_taint(&m, &std_config());
    assert_eq!(
        report.hits.len(),
        3,
        "module-var + both global-store flavors read back: {:?}",
        report.hits
    );
}

/// The sink-position arms: taint riding `this`, the `base` (the
/// receiver of the callee's defining LoadProp), and the `callee` value
/// itself all report their exact positions.
#[test]
fn sink_positions_this_base_callee() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // this-position: a bare-global callee called with a tainted this.
    let c1 = try_get_global(&mut m, entry, "sinkThis");
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: c1,
            this: Some(p),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    // base-position: `o.run()` — `o` is a global-load source; the call
    // carries no explicit this, so the base is the LoadProp's object.
    let g = try_get_global(&mut m, entry, "o");
    let run = intern(&mut m, "run");
    let callee2 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: g,
            name: run,
        },
    );
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: callee2,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    // callee-position: the callee VALUE is the tainted global.
    let c3 = try_get_global(&mut m, entry, "sinkCallee");
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: c3,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let config = TaintConfig {
        sources: vec![
            SourceSpec::FunctionParams {
                name: "func_main_0".to_owned(),
                params: None,
            },
            SourceSpec::GlobalLoad {
                name: "o".to_owned(),
            },
            SourceSpec::GlobalLoad {
                name: "sinkCallee".to_owned(),
            },
        ],
        sinks: vec![
            SinkSpec::Call {
                name: "sinkThis".to_owned(),
            },
            SinkSpec::Call {
                name: "o.run".to_owned(),
            },
            SinkSpec::Call {
                name: "sinkCallee".to_owned(),
            },
        ],
        ..std_config()
    };
    let report = run_taint(&m, &config);
    let pairs: Vec<(&str, &str)> = report
        .hits
        .iter()
        .map(|h| (h.sink.as_str(), h.position.as_str()))
        .collect();
    // `o.run` reports TWICE: the tainted receiver (`base`) and the
    // tainted load result that became the callee (`callee` — the load
    // rule extends the receiver's chain by the method key).
    assert!(
        pairs.contains(&("sinkThis", "this")),
        "the this position: {pairs:?}"
    );
    assert!(
        pairs.contains(&("o.run", "base")),
        "the base position: {pairs:?}"
    );
    assert!(
        pairs.contains(&("o.run", "callee")) && pairs.contains(&("sinkCallee", "callee")),
        "the callee positions: {pairs:?}"
    );
    assert_eq!(report.hits.len(), 4, "{pairs:?}");
}

/// A block-TERMINAL call (no in-block continuation): the return-site
/// computation takes the successor-block path. (v0.2 models control
/// flow via explicit edges, so the IR can carry the shape.)
#[test]
fn block_terminal_call_hit_reports() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let b2 = add_block(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // The call is the LAST instruction of the entry block.
    print_call(&mut m, entry, vec![p]);
    link(&mut m, entry, b2);
    let s = load_string(&mut m, b2, "clean");
    print_call(&mut m, b2, vec![s]);
    emit_void(&mut m, b2, Op::Return { value: None });

    let report = run_taint(&m, &std_config());
    assert_eq!(report.hits.len(), 1, "the terminal call is the sink");
    assert_eq!(report.hits[0].position, "arg 0");
}

/// The path-reconstruction detour through a callee's exits: the return
/// channel AND the throw channel both reach sinks; the return value
/// aimed at a HANDLER entry is dropped (only thrown values land there).
#[test]
fn return_and_throw_exit_channels() {
    let mut m = mk_module();
    // boom(x) { if (…) { throw x } else { return x } } — both exits
    // carry the tainted formal.
    let boom = add_func_named(&mut m, "boom");
    m.func_mut(boom).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    let boom_blocks;
    {
        let b = entry_of(&m, boom);
        add_param(&mut m, boom, 0);
        add_param(&mut m, boom, 1);
        add_param(&mut m, boom, 2);
        let x = add_param(&mut m, boom, 3);
        let th = add_block(&mut m, boom);
        let re = add_block(&mut m, boom);
        let c = load_number(&mut m, b, 1.0);
        emit_void(
            &mut m,
            b,
            Op::CondBranch {
                cond: c,
                true_dest: th,
                false_dest: re,
            },
        );
        emit_void(&mut m, th, Op::Throw { value: x });
        emit_void(&mut m, re, Op::Return { value: Some(x) });
        link(&mut m, b, th);
        link(&mut m, b, re);
        boom_blocks = vec![b, th, re];
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let handler = add_block(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let bv = load_method_ref(&mut m, entry, boom);
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: bv,
            this: None,
            args: vec![p],
            kind: CallKind::Direct,
        },
    );
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });
    let exc = add_exception_param(&mut m, handler);
    print_call(&mut m, handler, vec![exc]);
    emit_void(&mut m, handler, Op::Return { value: None });
    add_try(&mut m, f, vec![entry], handler, exc);
    // A second region that does NOT protect the call block (the
    // region-loop's skip arm in return_sites_of).
    let other = add_block(&mut m, f);
    let h2 = add_block(&mut m, f);
    emit_void(&mut m, other, Op::Return { value: None });
    let exc2 = add_exception_param(&mut m, h2);
    emit_void(&mut m, h2, Op::Return { value: None });
    add_try(&mut m, f, vec![other], h2, exc2);

    let report = run_taint(&m, &std_config());
    assert_eq!(
        report.hits.len(),
        2,
        "both the return and the thrown channel hit: {:?}",
        report.hits
    );
    assert!(report.hits.iter().any(|h| h.fact.local_base() == Some(r)));
    assert!(report.hits.iter().any(|h| h.fact.local_base() == Some(exc)));
    // The return-channel hit's path detours through the callee's exit.
    let ret_hit = report
        .hits
        .iter()
        .find(|h| h.fact.local_base() == Some(r))
        .unwrap();
    assert!(
        ret_hit.path.iter().any(|step| {
            let inst = m.inst(step.inst).expect("step inst");
            boom_blocks.contains(&inst.block)
        }),
        "the path detours through the callee: {:?}",
        ret_hit.path
    );
}

/// The unbalanced-return arm: a caller-less function whose RETURN value
/// is tainted (via a global source) invokes `return_flow` with no call
/// site and no return site — the flow dies there (nothing to rebase
/// onto).
#[test]
fn unbalanced_return_without_result_dies() {
    let mut m = mk_module();
    // orphan() { return TryGetGlobal("T") } — never called.
    let orphan = add_func_named(&mut m, "orphan");
    {
        let b = entry_of(&m, orphan);
        let g = try_get_global(&mut m, b, "T");
        emit_void(&mut m, b, Op::Return { value: Some(g) });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let g = try_get_global(&mut m, entry, "T");
    print_call(&mut m, entry, vec![g]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let config = TaintConfig {
        sources: vec![SourceSpec::GlobalLoad {
            name: "T".to_owned(),
        }],
        ..std_config()
    };
    let report = run_taint(&m, &config);
    assert_eq!(
        report.hits.len(),
        1,
        "only the caller-side read reports (the orphan's return dies): {:?}",
        report.hits
    );
}

/// `SourceSpec::FunctionParams` with explicit indices seeds exactly
/// those params; an out-of-range index and an unknown function name
/// seed nothing.
#[test]
fn function_params_explicit_indices() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let p0 = add_param(&mut m, f, 0);
    let p1 = add_param(&mut m, f, 1);
    print_call(&mut m, entry, vec![p0]);
    print_call(&mut m, entry, vec![p1]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let config = TaintConfig {
        sources: vec![
            SourceSpec::FunctionParams {
                name: "func_main_0".to_owned(),
                params: Some(vec![1]),
            },
            // Out-of-range and unknown-name specs seed nothing.
            SourceSpec::FunctionParams {
                name: "func_main_0".to_owned(),
                params: Some(vec![9]),
            },
            SourceSpec::FunctionParams {
                name: "no_such_function".to_owned(),
                params: None,
            },
        ],
        ..std_config()
    };
    let report = run_taint(&m, &config);
    assert_eq!(report.hits.len(), 1, "only params[1] was seeded");
    assert_eq!(report.hits[0].fact.local_base(), Some(p1));
}
