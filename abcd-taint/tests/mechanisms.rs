//! Mechanism unit tests (task §6): one test per taint mechanism, each
//! over a hand-built module (the builders in `tests/common` keep the IR
//! invariants the verifier checks).

mod common;

use abcd_ir::{CallKind, Loc, Op};
use abcd_taint::driver::run_taint_full;
use abcd_taint::fact::{Fact, TaintBase, TaintFact};
use abcd_taint::summary::{Endpoint, Summary};
use abcd_taint::{SinkSpec, SourceSpec, TaintConfig};
use common::*;

/// The standard config: all `func_main_0` params are sources, `print`
/// is the sink, no builtin summaries (tests register exactly what they
/// exercise).
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

/// `print(...)` call in block `b` over `args`; returns the call inst.
fn print_call(
    m: &mut abcd_ir::Module,
    b: abcd_ir::BlockId,
    args: Vec<abcd_ir::ValueId>,
) -> abcd_ir::InstId {
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
    )
}

/// Access-path cutoff: chains never exceed the configured k, and
/// extensions beyond k collapse onto the prefix (heap.rs `pushed`).
#[test]
fn access_path_cutoff() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let this = add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);

    // Build a chain-grower: base-taint p itself is the source; loads
    // extend the chain and stores re-key it into the heap.
    //   a1 = p.f1          → Local(a1, [f1])
    //   o1.f2 = a1         → Heap(s1, [f2, f1])
    //   a2 = o1.f2         → Local(a2, [f1])
    //   ... alternating grows the chain until the cap merges it.
    let f1 = intern(&mut m, "f1");
    let f2 = intern(&mut m, "f2");
    let mut cur = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: p,
            name: f1,
        },
    );
    let mut last_store = None;
    for _ in 0..6 {
        let obj = alloc_object(&mut m, entry);
        emit_void(
            &mut m,
            entry,
            Op::StoreProp {
                object: obj,
                name: f2,
                value: cur,
            },
        );
        cur = emit(
            &mut m,
            entry,
            Op::LoadProp {
                object: obj,
                name: f2,
            },
        );
        last_store = Some(obj);
    }
    let _ = last_store;
    print_call(&mut m, entry, vec![cur]);
    emit_void(&mut m, entry, Op::Return { value: None });
    let _ = this;

    let config = TaintConfig {
        max_field_chain: 2,
        ..std_config()
    };
    let (report, result) = run_taint_full(&m, &config);
    assert_eq!(report.hits.len(), 1, "the flow exists (capped, not lost)");
    // No fact anywhere exceeds the cap.
    for edge in result.path_edges() {
        if let Fact::Taint(t) = &edge.target_fact {
            assert!(
                t.fields.len() <= 2,
                "chain {:?} exceeds the k-cap",
                t.fields
            );
        }
    }
    // And the cap actually engaged: some fact reached length exactly 2.
    let max_len = result
        .path_edges()
        .iter()
        .filter_map(|e| e.target_fact.taint().map(|t| t.fields.len()))
        .max()
        .unwrap_or(0);
    assert_eq!(max_len, 2, "the cutoff was exercised");
}

/// Exclusive semantics: a summary kills the call edge into the callee —
/// never merged (summaries.md §2.1). A sanitizer summary (exclusive, no
/// flows) over a RESOLVED callee must suppress the body's flow.
#[test]
fn exclusive_summary_kills_call_edge() {
    let build = || {
        let mut m = mk_module();
        // sanitize(x) { return x; } — a real body that WOULD propagate.
        let san = add_func_named(&mut m, "sanitize");
        let sb = entry_of(&m, san);
        add_param(&mut m, san, 0); // this
        let x = add_param(&mut m, san, 1);
        emit_void(&mut m, sb, Op::Return { value: Some(x) });

        let f = add_func_named(&mut m, "func_main_0");
        let entry = entry_of(&m, f);
        add_param(&mut m, f, 0);
        let p = add_param(&mut m, f, 1);
        let san_val = {
            let c = m.consts.push(abcd_ir::Const::MethodRef(san));
            emit(&mut m, entry, Op::LoadConst(c))
        };
        let r = emit(
            &mut m,
            entry,
            Op::Call {
                callee: san_val,
                this: None,
                args: vec![p],
                kind: CallKind::Direct,
            },
        );
        print_call(&mut m, entry, vec![r]);
        emit_void(&mut m, entry, Op::Return { value: None });
        m
    };

    // Control: no summary → the body carries the flow.
    let hits = abcd_taint::run_taint(&build(), &std_config()).hits.len();
    assert_eq!(hits, 1, "control: stepping into the body finds the flow");

    // Exclusive sanitizer: the call edge is killed, the body never runs.
    let mut config = std_config();
    config.extra_summaries.push((
        "sanitize".to_owned(),
        Some(1),
        Summary::new("sanitizer: kills all taint").exclusive(),
    ));
    let report = abcd_taint::run_taint(&build(), &config);
    assert_eq!(
        report.hits.len(),
        0,
        "exclusive summary suppresses the callee body entirely"
    );
    assert_eq!(report.stats.sites_body_step, 0, "no body step happened");
}

/// Fallback ladder rung 1→2: no summary but the callee has a body →
/// normal IFDS steps into it (the control arm of the exclusive test),
/// counted as a body step.
#[test]
fn fallback_steps_into_body() {
    let mut m = mk_module();
    let id_fn = add_func_named(&mut m, "identity");
    let ib = entry_of(&m, id_fn);
    add_param(&mut m, id_fn, 0);
    let x = add_param(&mut m, id_fn, 1);
    emit_void(&mut m, ib, Op::Return { value: Some(x) });

    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let id_val = {
        let c = m.consts.push(abcd_ir::Const::MethodRef(id_fn));
        emit(&mut m, entry, Op::LoadConst(c))
    };
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: id_val,
            this: None,
            args: vec![p],
            kind: CallKind::Direct,
        },
    );
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &std_config());
    assert_eq!(report.hits.len(), 1);
    assert_eq!(report.stats.sites_body_step, 1, "the ladder stepped in");
    assert_eq!(
        report.stats.sites_native_keep, 1,
        "print itself was a named miss"
    );
}

/// Fallback ladder rung 3: native/unknown no-summary callee →
/// conservative keep + identity heuristic (tainted operand ⇒ tainted
/// return); the miss is counted by name (the backlog log).
#[test]
fn fallback_native_keep_and_miss_counters() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let mystery = try_get_global(&mut m, entry, "mysteryBuiltin");
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: mystery,
            this: None,
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &std_config());
    assert_eq!(report.hits.len(), 1, "identity heuristic keeps the flow");
    let registry = abcd_taint::SummaryRegistry::new();
    let _ = registry;
    // The named miss is logged (mysteryBuiltin); print is a named miss too.
    let misses: Vec<String> = report
        .stats
        .misses_named
        .keys()
        .map(|s| format!("{s:?}"))
        .collect();
    assert_eq!(
        misses.len(),
        2,
        "print and mysteryBuiltin missed: {misses:?}"
    );
    assert!(report.stats.sites_native_keep >= 1);

    // With the identity heuristic off, the operand taint still passes
    // through untouched (never sanitizes) but the return is clean.
    let config = TaintConfig {
        native_identity: false,
        ..std_config()
    };
    let report = abcd_taint::run_taint(&m, &config);
    assert_eq!(report.hits.len(), 0, "no identity ⇒ no return taint");
}

/// Negative control: source and sink disconnected → zero hits.
#[test]
fn negative_control_disconnected() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let _p = add_param(&mut m, f, 1);
    let c = load_string(&mut m, entry, "clean");
    print_call(&mut m, entry, vec![c]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &std_config());
    assert_eq!(report.hits.len(), 0, "no flow where none exists");
}

/// ExceptionParam taints the catch binding: `throw p` inside a try
/// region maps the thrown value's taint onto the handler's
/// ExceptionParam (T5/T10).
#[test]
fn exception_param_taints_catch_binding() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let handler = add_block(&mut m, f);
    let exc = add_exception_param(&mut m, handler);

    emit_void_loc(
        &mut m,
        entry,
        Op::Throw { value: p },
        Some(Loc {
            line: 3,
            column: Some(9),
        }),
    );
    let print_inst = {
        let print = try_get_global(&mut m, handler, "print");
        push_inst_loc(
            &mut m,
            handler,
            Op::Call {
                callee: print,
                this: None,
                args: vec![exc],
                kind: CallKind::Dynamic,
            },
            Some(Loc {
                line: 7,
                column: Some(5),
            }),
        )
    };
    emit_void(&mut m, handler, Op::Return { value: None });
    add_try(&mut m, f, vec![entry], handler, exc);

    let report = abcd_taint::run_taint(&m, &std_config());
    assert_eq!(report.hits.len(), 1, "the catch binding is tainted");
    let hit = &report.hits[0];
    assert_eq!(hit.call, print_inst);
    assert_eq!(hit.position, "arg 0");
    assert_eq!(
        hit.loc,
        Some(Loc {
            line: 7,
            column: Some(5)
        }),
        "T8: the report carries line/column"
    );
    assert!(!hit.path.is_empty(), "a path was reconstructed");
}

/// Heap weak update: a store through a phi-merged base keeps the old
/// heap taint (union), while a store through a provably-single-site base
/// kills the matching heap fact (strong update).
#[test]
fn heap_weak_vs_strong_update() {
    use abcd_ir::{Edge, EdgeKind};

    // ── Strong arm: straight-line alloc; obj.f = tainted; obj.f =
    // clean; x = obj.f → x clean.
    let strong_clean = {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "func_main_0");
        let entry = entry_of(&m, f);
        add_param(&mut m, f, 0);
        let p = add_param(&mut m, f, 1);
        let obj = alloc_object(&mut m, entry);
        let fld = intern(&mut m, "f");
        emit_void(
            &mut m,
            entry,
            Op::StoreProp {
                object: obj,
                name: fld,
                value: p,
            },
        );
        let clean = load_string(&mut m, entry, "clean");
        emit_void(
            &mut m,
            entry,
            Op::StoreProp {
                object: obj,
                name: fld,
                value: clean,
            },
        );
        let x = emit(
            &mut m,
            entry,
            Op::LoadProp {
                object: obj,
                name: fld,
            },
        );
        print_call(&mut m, entry, vec![x]);
        emit_void(&mut m, entry, Op::Return { value: None });
        abcd_taint::run_taint(&m, &std_config()).hits.len()
    };
    assert_eq!(strong_clean, 0, "strong update killed the heap taint");

    // ── Weak arm: the store base is a phi of two allocs; the kill must
    // NOT fire, so the load stays tainted.
    let weak_tainted = {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "func_main_0");
        let entry = entry_of(&m, f);
        add_param(&mut m, f, 0);
        let p = add_param(&mut m, f, 1);
        let t = add_block(&mut m, f);
        let e = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond: p,
                true_dest: t,
                false_dest: e,
            },
        );
        let a = alloc_object(&mut m, t);
        emit_void(&mut m, t, Op::Branch { dest: join });
        let b = alloc_object(&mut m, e);
        emit_void(&mut m, e, Op::Branch { dest: join });
        link(&mut m, entry, t);
        link(&mut m, entry, e);
        link(&mut m, t, join);
        link(&mut m, e, join);
        let phi = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: t,
                            kind: EdgeKind::Normal,
                        },
                        a,
                    ),
                    (
                        Edge {
                            from: e,
                            kind: EdgeKind::Normal,
                        },
                        b,
                    ),
                ],
            },
        );
        let fld = intern(&mut m, "f");
        emit_void(
            &mut m,
            join,
            Op::StoreProp {
                object: phi,
                name: fld,
                value: p,
            },
        );
        let clean = load_string(&mut m, join, "clean");
        emit_void(
            &mut m,
            join,
            Op::StoreProp {
                object: phi,
                name: fld,
                value: clean,
            },
        );
        let x = emit(
            &mut m,
            join,
            Op::LoadProp {
                object: phi,
                name: fld,
            },
        );
        print_call(&mut m, join, vec![x]);
        emit_void(&mut m, join, Op::Return { value: None });
        abcd_taint::run_taint(&m, &std_config()).hits.len()
    };
    assert_eq!(weak_tainted, 1, "weak update keeps the heap taint");
}

/// Global store/load round-trip: `StoreGlobal("g", p)` taints the
/// global binding; a later `TryGetGlobal("g")` picks it up — the
/// cross-script-mutation discipline (globals are never strong-updated).
#[test]
fn global_store_load_roundtrip() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let g = intern(&mut m, "g");
    emit_void(&mut m, entry, Op::StoreGlobal { name: g, value: p });
    // An intervening "clean" store does NOT kill the global taint
    // (globals are mutable across scripts: always weak).
    let clean = load_string(&mut m, entry, "clean");
    emit_void(
        &mut m,
        entry,
        Op::StoreGlobal {
            name: g,
            value: clean,
        },
    );
    let loaded = try_get_global(&mut m, entry, "g");
    print_call(&mut m, entry, vec![loaded]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &std_config());
    assert_eq!(report.hits.len(), 1, "the global binding stayed tainted");
}

/// A GlobalLoad source spec: `TryGetGlobal("hostInput")` is a source
/// without any param seeding.
#[test]
fn global_load_source() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let tainted = try_get_global(&mut m, entry, "hostInput");
    print_call(&mut m, entry, vec![tainted]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let config = TaintConfig {
        sources: vec![SourceSpec::GlobalLoad {
            name: "hostInput".to_owned(),
        }],
        ..std_config()
    };
    let report = abcd_taint::run_taint(&m, &config);
    assert_eq!(report.hits.len(), 1);
}

/// Summary flows over a qualified name (`console.log`-style resolution
/// through the global-load chain): `String` as a transformer via
/// `String(x)` — the registry hit applies param(0)→return.
#[test]
fn summary_hit_applies_flows() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let string_fn = try_get_global(&mut m, entry, "String");
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: string_fn,
            this: None,
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let mut config = std_config();
    config.extra_summaries.push((
        "String".to_owned(),
        None,
        Summary::new("coercion").flow(Endpoint::Param(0), Endpoint::Return),
    ));
    let report = abcd_taint::run_taint(&m, &config);
    assert_eq!(report.hits.len(), 1, "param(0)→return flow applied");
    assert_eq!(
        report.summaries_applied.len(),
        1,
        "the application was logged"
    );
}

/// Clear semantics: a clear kills the incoming taint even though a flow
/// would otherwise re-add it.
#[test]
fn summary_clear_kills_taint() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let sanitize = try_get_global(&mut m, entry, "bleach");
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: sanitize,
            this: None,
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let mut config = std_config();
    config.extra_summaries.push((
        "bleach".to_owned(),
        Some(1),
        Summary::new("sanitizer")
            .flow(Endpoint::Param(0), Endpoint::Return)
            .clear(Endpoint::Param(0)),
    ));
    let report = abcd_taint::run_taint(&m, &config);
    assert_eq!(report.hits.len(), 0, "the clear beat the flow");
}

/// The `base` endpoint: `obj.m(tainted)` where the summary flows
/// param(0)→base — the object of the LoadProp that produced the callee
/// is the base for `Dynamic` calls (no explicit `this`).
#[test]
fn summary_base_endpoint_via_loadprop() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let coll = try_get_global(&mut m, entry, "coll");
    let push_name = intern(&mut m, "push");
    let push_fn = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: coll,
            name: push_name,
        },
    );
    emit(
        &mut m,
        entry,
        Op::Call {
            callee: push_fn,
            this: None,
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    // The tainted base read back out: print(coll).
    print_call(&mut m, entry, vec![coll]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let mut config = std_config();
    config.extra_summaries.push((
        "coll.push".to_owned(),
        Some(1),
        Summary::new("mutator: element taint → base").flow(Endpoint::Param(0), Endpoint::Base),
    ));
    let report = abcd_taint::run_taint(&m, &config);
    assert_eq!(
        report.hits.len(),
        1,
        "param(0)→base flow tainted the receiver"
    );
}

/// Two runs over the same module are identical (determinism).
#[test]
fn determinism_two_runs_identical() {
    let build = || {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "func_main_0");
        let entry = entry_of(&m, f);
        add_param(&mut m, f, 0);
        let p = add_param(&mut m, f, 1);
        let q = emit(&mut m, entry, Op::Mov { src: p });
        let obj = alloc_object(&mut m, entry);
        let fld = intern(&mut m, "f");
        emit_void(
            &mut m,
            entry,
            Op::StoreProp {
                object: obj,
                name: fld,
                value: q,
            },
        );
        let x = emit(
            &mut m,
            entry,
            Op::LoadProp {
                object: obj,
                name: fld,
            },
        );
        print_call(&mut m, entry, vec![x]);
        emit_void(&mut m, entry, Op::Return { value: None });
        m
    };
    let m = build();
    let a = abcd_taint::run_taint(&m, &std_config());
    let b = abcd_taint::run_taint(&m, &std_config());
    assert_eq!(a.hits, b.hits);
    assert_eq!(a.path_edges, b.path_edges);
    assert_eq!(format!("{:?}", a.stats), format!("{:?}", b.stats));
}

/// The fact type's zero is distinct from every real fact (heros §2.4).
#[test]
fn zero_fact_is_distinct() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let p = add_param(&mut m, f, 0);
    assert_ne!(Fact::Zero, Fact::of(TaintFact::local(p)));
    let heap = TaintFact {
        base: TaintBase::Heap(Default::default()),
        fields: Default::default(),
    };
    assert_ne!(Fact::Zero, Fact::of(heap));
}

// ── N66: the vendored frame-slot param binding (call_flow) ──────────
//
// A callee's `params` are the code-header arg slots: leading implicit
// slots `[func][newTarget][this]` per the `L_ESCallTypeAnnotation;`
// callType bits, annotation absent on a STATIC callee ⇒ the vendored
// 0xF default (all three), source formals following left-aligned.
// These tests pin the binding map.

/// A `print(x)`-shaped module: `callee` is called with the tainted
/// param and its return is printed. Returns the report.
fn call_and_print(callee: abcd_ir::FuncId, m: &mut abcd_ir::Module) -> abcd_taint::TaintReport {
    let f = add_func_named(m, "func_main_0");
    let entry = entry_of(m, f);
    add_param(m, f, 0);
    let p = add_param(m, f, 1);
    let callee_val = {
        let c = m.consts.push(abcd_ir::Const::MethodRef(callee));
        emit(m, entry, Op::LoadConst(c))
    };
    let r = emit(
        m,
        entry,
        Op::Call {
            callee: callee_val,
            this: None,
            args: vec![p],
            kind: CallKind::Direct,
        },
    );
    print_call(m, entry, vec![r]);
    emit_void(m, entry, Op::Return { value: None });
    abcd_taint::run_taint(m, &std_config())
}

/// 0xF-shaped STATIC callee (annotation absent ⇒ [func][newTarget]
/// [this][formals…]): the tainted argument binds to params[3], NOT
/// params[1] (the pre-N66 off-by-two). A callee returning its first
/// formal flows; one returning a hidden slot does not.
#[test]
fn call_binding_frame_slot_default() {
    // Callee returning its first formal (params[3]): TP.
    let mut m = mk_module();
    let id_fn = add_func_named(&mut m, "identity0xF");
    m.functions[id_fn.index()].modifiers = abcd_ir::Modifiers::STATIC;
    let ib = entry_of(&m, id_fn);
    for i in 0..4 {
        add_param(&mut m, id_fn, i);
    }
    let formal = m.functions[id_fn.index()].params[3];
    emit_void(
        &mut m,
        ib,
        Op::Return {
            value: Some(formal),
        },
    );
    let report = call_and_print(id_fn, &mut m);
    assert_eq!(
        report.hits.len(),
        1,
        "0xF binding: args[0] -> params[3] (the first formal)"
    );

    // Callee returning a HIDDEN slot (params[1] = newTarget): no flow.
    let mut m = mk_module();
    let nt_fn = add_func_named(&mut m, "hidden_slot");
    m.functions[nt_fn.index()].modifiers = abcd_ir::Modifiers::STATIC;
    let nb = entry_of(&m, nt_fn);
    for i in 0..4 {
        add_param(&mut m, nt_fn, i);
    }
    let hidden = m.functions[nt_fn.index()].params[1];
    emit_void(
        &mut m,
        nb,
        Op::Return {
            value: Some(hidden),
        },
    );
    let report = call_and_print(nt_fn, &mut m);
    assert_eq!(
        report.hits.len(),
        0,
        "0xF binding: the argument must NOT land on hidden slot params[1]"
    );
}

/// Annotated callee (callType = 0 — NO implicit slots): formals start
/// at params[0], so the tainted argument binds to params[0].
#[test]
fn call_binding_annotated_calltype_zero() {
    let mut m = mk_module();
    // The annotation class record.
    let ann_name = m.sym.intern("L_ESCallTypeAnnotation;");
    let ann_class = abcd_ir::ClassId::new(m.classes.len() as u32);
    m.classes.push(abcd_ir::ClassData {
        descriptor: ann_name,
        name: ann_name,
        modifiers: abcd_ir::Modifiers::NONE,
        source_lang: abcd_ir::module::SourceLang::EcmaScript,
        super_class: None,
        interfaces: Vec::new(),
        fields: Vec::new(),
        methods: Vec::new(),
        annotations: Vec::new(),
        source_file: None,
    });
    let f = add_func_named(&mut m, "annotated");
    let fb = entry_of(&m, f);
    let formal = add_param(&mut m, f, 0);
    emit_void(
        &mut m,
        fb,
        Op::Return {
            value: Some(formal),
        },
    );
    let call_type = m.sym.intern("callType");
    let zero = m.consts.push(abcd_ir::Const::number(0.0));
    m.functions[f.index()]
        .annotations
        .push(abcd_ir::Annotation {
            class: ann_class,
            elements: vec![(call_type, abcd_ir::AnnValue::Const(zero))],
        });

    let report = call_and_print(f, &mut m);
    assert_eq!(
        report.hits.len(),
        1,
        "callType=0: no implicit slots, args[0] -> params[0]"
    );
}

/// NON-STATIC callee without a callType annotation: no reliable slot
/// model — taint must over-approximate (a tainted arg taints EVERY
/// param), never silently drop the flow.
#[test]
fn call_binding_nonstatic_unannotated_overapprox() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "opaque");
    // Modifiers::NONE (non-static), no annotation.
    let fb = entry_of(&m, f);
    let slot0 = add_param(&mut m, f, 0);
    add_param(&mut m, f, 1);
    emit_void(&mut m, fb, Op::Return { value: Some(slot0) });

    let report = call_and_print(f, &mut m);
    assert_eq!(
        report.hits.len(),
        1,
        "no slot model: conservative over-approximation taints every param"
    );
}

// ── Rung 1 (t-P2): the on-demand alias engine behind the AliasOracle
// seam (analysis-strategy §4.4 rung 1). Each test pins the rung-0
// behavior (the A/B control, `alias_rung: 0`) AND the rung-1 behavior —
// the delta IS the mechanism.

/// a4 shape: a store through a call-result base keyed the fact with an
/// EMPTY site set at rung 0 (may-aliasing every load of the field — the
/// recorded FP); rung 1's memoized backward query hops the call into the
/// callee and keys the store with the callee's alloc site, disjoint
/// from the loaded object's.
#[test]
fn rung1_store_through_call_result_keys_precisely() {
    let build = || {
        let mut m = mk_module();
        let mkobj = add_func_named(&mut m, "mkobj");
        m.functions[mkobj.index()].modifiers = abcd_ir::Modifiers::STATIC;
        {
            let b = entry_of(&m, mkobj);
            add_param(&mut m, mkobj, 0);
            add_param(&mut m, mkobj, 1);
            add_param(&mut m, mkobj, 2);
            let obj = alloc_object(&mut m, b);
            emit_void(&mut m, b, Op::Return { value: Some(obj) });
        }
        let f = add_func_named(&mut m, "func_main_0");
        let entry = entry_of(&m, f);
        add_param(&mut m, f, 0);
        let t = add_param(&mut m, f, 1);
        let def = emit(
            &mut m,
            entry,
            Op::DefineFunc {
                body: mkobj,
                captures: vec![],
                length: 0,
            },
        );
        let clo = emit(&mut m, entry, Op::AllocClosure { func: def });
        let p = emit(
            &mut m,
            entry,
            Op::Call {
                callee: clo,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let secret = intern(&mut m, "secret");
        emit_void(
            &mut m,
            entry,
            Op::StoreProp {
                object: p,
                name: secret,
                value: t,
            },
        );
        // A DISTINCT local object, same field name, never stored into.
        let o = alloc_object(&mut m, entry);
        let x = emit(
            &mut m,
            entry,
            Op::LoadProp {
                object: o,
                name: secret,
            },
        );
        print_call(&mut m, entry, vec![x]);
        emit_void(&mut m, entry, Op::Return { value: None });
        m
    };
    let rung0 = abcd_taint::run_taint(
        &build(),
        &TaintConfig {
            alias_rung: 0,
            ..std_config()
        },
    );
    assert_eq!(
        rung0.hits.len(),
        1,
        "rung 0: unknown-base wildcard fires (the recorded FP)"
    );
    let rung1 = abcd_taint::run_taint(&build(), &std_config());
    assert_eq!(
        rung1.hits.len(),
        0,
        "rung 1: the store keys to mkobj's site, disjoint from o's"
    );
}

/// a5 shape: a sanitizing store through an unproven alias (call result)
/// is a WEAK update at rung 0; rung 1's balanced call/return hop proves
/// the alias (id returns its formal, bound to THIS call's argument) and
/// the strong update kills the taint.
#[test]
fn rung1_strong_update_through_call_result_alias() {
    let build = || {
        let mut m = mk_module();
        let id = add_func_named(&mut m, "id");
        m.functions[id.index()].modifiers = abcd_ir::Modifiers::STATIC;
        {
            let b = entry_of(&m, id);
            add_param(&mut m, id, 0);
            add_param(&mut m, id, 1);
            add_param(&mut m, id, 2);
            let x = add_param(&mut m, id, 3); // first formal (0xF default)
            emit_void(&mut m, b, Op::Return { value: Some(x) });
        }
        let f = add_func_named(&mut m, "func_main_0");
        let entry = entry_of(&m, f);
        add_param(&mut m, f, 0);
        let t = add_param(&mut m, f, 1);
        let def = emit(
            &mut m,
            entry,
            Op::DefineFunc {
                body: id,
                captures: vec![],
                length: 1,
            },
        );
        let clo = emit(&mut m, entry, Op::AllocClosure { func: def });
        let o = alloc_object(&mut m, entry);
        let p = emit(
            &mut m,
            entry,
            Op::Call {
                callee: clo,
                this: None,
                args: vec![o],
                kind: CallKind::Dynamic,
            },
        );
        let secret = intern(&mut m, "secret");
        emit_void(
            &mut m,
            entry,
            Op::StoreProp {
                object: o,
                name: secret,
                value: t,
            },
        );
        let clean = load_string(&mut m, entry, "clean");
        emit_void(
            &mut m,
            entry,
            Op::StoreProp {
                object: p,
                name: secret,
                value: clean,
            },
        );
        let x = emit(
            &mut m,
            entry,
            Op::LoadProp {
                object: o,
                name: secret,
            },
        );
        print_call(&mut m, entry, vec![x]);
        emit_void(&mut m, entry, Op::Return { value: None });
        m
    };
    let rung0 = abcd_taint::run_taint(
        &build(),
        &TaintConfig {
            alias_rung: 0,
            ..std_config()
        },
    );
    assert_eq!(
        rung0.hits.len(),
        1,
        "rung 0: weak update — the taint survives (the recorded FP)"
    );
    let rung1 = abcd_taint::run_taint(&build(), &std_config());
    assert_eq!(
        rung1.hits.len(),
        0,
        "rung 1: must-alias proof makes the update strong"
    );
}

/// b3 shape: a callback invoked through a PARAMETER callee — the site is
/// unknown at rung 0 (no call edge, the body never sees the taint);
/// rung 1's points_to refinement bridges the edge and the body-step
/// carries the arg taint into the callback.
#[test]
fn rung1_param_callee_bridge_enters_callback() {
    let build = || {
        let mut m = mk_module();
        let cb = add_func_named(&mut m, "cb");
        m.functions[cb.index()].modifiers = abcd_ir::Modifiers::STATIC;
        {
            let b = entry_of(&m, cb);
            add_param(&mut m, cb, 0);
            add_param(&mut m, cb, 1);
            add_param(&mut m, cb, 2);
            let x = add_param(&mut m, cb, 3);
            print_call(&mut m, b, vec![x]);
            emit_void(&mut m, b, Op::Return { value: None });
        }
        let register = add_func_named(&mut m, "register");
        m.functions[register.index()].modifiers = abcd_ir::Modifiers::STATIC;
        {
            let b = entry_of(&m, register);
            add_param(&mut m, register, 0);
            add_param(&mut m, register, 1);
            add_param(&mut m, register, 2);
            let cb_param = add_param(&mut m, register, 3);
            let x_param = add_param(&mut m, register, 4);
            push_inst(
                &mut m,
                b,
                Op::Call {
                    callee: cb_param,
                    this: None,
                    args: vec![x_param],
                    kind: CallKind::Dynamic,
                },
            );
            emit_void(&mut m, b, Op::Return { value: None });
        }
        let f = add_func_named(&mut m, "func_main_0");
        let entry = entry_of(&m, f);
        add_param(&mut m, f, 0);
        let t = add_param(&mut m, f, 1);
        let def_reg = emit(
            &mut m,
            entry,
            Op::DefineFunc {
                body: register,
                captures: vec![],
                length: 2,
            },
        );
        let clo_reg = emit(&mut m, entry, Op::AllocClosure { func: def_reg });
        let def_cb = emit(
            &mut m,
            entry,
            Op::DefineFunc {
                body: cb,
                captures: vec![],
                length: 1,
            },
        );
        let clo_cb = emit(&mut m, entry, Op::AllocClosure { func: def_cb });
        push_inst(
            &mut m,
            entry,
            Op::Call {
                callee: clo_reg,
                this: None,
                args: vec![clo_cb, t],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, entry, Op::Return { value: None });
        m
    };
    let rung0 = abcd_taint::run_taint(
        &build(),
        &TaintConfig {
            alias_rung: 0,
            ..std_config()
        },
    );
    assert_eq!(
        rung0.hits.len(),
        0,
        "rung 0: param callee unresolved — the callback is never entered"
    );
    let rung1 = abcd_taint::run_taint(&build(), &std_config());
    assert_eq!(
        rung1.hits.len(),
        1,
        "rung 1: the bridged edge carries the taint into cb"
    );
    assert!(
        rung1.stats.sites_body_step >= 1,
        "the inner site stepped into a body (not the identity heuristic)"
    );
}

/// e5 shape: a summary's alias flow (Object.assign) matches a HEAP-keyed
/// field taint on the source argument via positive points-to
/// intersection and re-keys it onto the destination's sites.
#[test]
fn rung1_summary_endpoint_matches_heap_field_taint() {
    let build = || {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "func_main_0");
        let entry = entry_of(&m, f);
        add_param(&mut m, f, 0);
        let t = add_param(&mut m, f, 1);
        let o = alloc_object(&mut m, entry);
        let lit = alloc_object(&mut m, entry);
        let secret = intern(&mut m, "secret");
        emit_void(
            &mut m,
            entry,
            Op::StoreProp {
                object: lit,
                name: secret,
                value: t,
            },
        );
        let obj_global = try_get_global(&mut m, entry, "Object");
        let assign_name = intern(&mut m, "assign");
        let assign = emit(
            &mut m,
            entry,
            Op::LoadProp {
                object: obj_global,
                name: assign_name,
            },
        );
        push_inst(
            &mut m,
            entry,
            Op::Call {
                callee: assign,
                this: None,
                args: vec![o, lit],
                kind: CallKind::Dynamic,
            },
        );
        let x = emit(
            &mut m,
            entry,
            Op::LoadProp {
                object: o,
                name: secret,
            },
        );
        print_call(&mut m, entry, vec![x]);
        emit_void(&mut m, entry, Op::Return { value: None });
        m
    };
    let config = |rung: u8| TaintConfig {
        extra_summaries: vec![(
            "Object.assign".to_owned(),
            None,
            Summary::new("test; srcs → dst").alias_flow(Endpoint::Param(1), Endpoint::Param(0)),
        )],
        alias_rung: rung,
        ..std_config()
    };
    // The endpoint match is NOT oracle-gated: it fires whenever
    // `site_info_at` resolves the argument's sites — the rung-0 local
    // walk suffices for a locally allocated argument like this one (the
    // rung-1 engine matters when the endpoint value needs the
    // interprocedural query; the compiled-probe A/B — e5 flips at both
    // rungs, a4/a5/b3 only at rung 1 — is in the t-P2 report). What this
    // test pins is that the match EXISTS at all: the pre-t-P2
    // `match_endpoint` returned None for heap facts (the e5 FN).
    let rung0 = abcd_taint::run_taint(&build(), &config(0));
    assert_eq!(
        rung0.hits.len(),
        1,
        "local allocs: the rung-0 local walk already resolves the sites"
    );
    let rung1 = abcd_taint::run_taint(&build(), &config(1));
    assert_eq!(
        rung1.hits.len(),
        1,
        "rung 1: the heap fact matches param(1) and lands on param(0)'s sites"
    );
}

/// Rung 1 is deterministic: two runs over the same module are identical
/// (the engine's memoization is lookup-only; iteration is B-tree/
/// insertion-ordered — N20).
#[test]
fn rung1_determinism_two_runs_identical() {
    let mut m = mk_module();
    let mkobj = add_func_named(&mut m, "mkobj");
    m.functions[mkobj.index()].modifiers = abcd_ir::Modifiers::STATIC;
    {
        let b = entry_of(&m, mkobj);
        add_param(&mut m, mkobj, 0);
        add_param(&mut m, mkobj, 1);
        add_param(&mut m, mkobj, 2);
        let obj = alloc_object(&mut m, b);
        emit_void(&mut m, b, Op::Return { value: Some(obj) });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let t = add_param(&mut m, f, 1);
    let def = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: mkobj,
            captures: vec![],
            length: 0,
        },
    );
    let clo = emit(&mut m, entry, Op::AllocClosure { func: def });
    let p = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clo,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let secret = intern(&mut m, "secret");
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: p,
            name: secret,
            value: t,
        },
    );
    let x = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: p,
            name: secret,
        },
    );
    print_call(&mut m, entry, vec![x]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let a = abcd_taint::run_taint(&m, &std_config());
    let b = abcd_taint::run_taint(&m, &std_config());
    assert_eq!(a.hits, b.hits);
    assert_eq!(a.path_edges, b.path_edges);
    assert_eq!(format!("{:?}", a.stats), format!("{:?}", b.stats));
    assert_eq!(a.hits.len(), 1, "the refined flow itself is found");
}

// ────────────────────────────────────────────────────────────────────
// t-P3: the prototype-resolution path (prototype.rs) — receiver-typed
// builtin summary lookup. One test per mechanism: alloc-kind→family,
// constant/global-provenance family, multi-site merge, negative
// control, precedence (direct name beats prototype; user object beats
// builtin), negative caching, unknown-receiver fall-through, the
// GetIterator family, and the push alias flow.
// ────────────────────────────────────────────────────────────────────

/// The std config plus the full builtin registry (top-20 + the t-P3
/// prototype-family entries).
fn builtin_config() -> TaintConfig {
    TaintConfig {
        builtin_summaries: true,
        ..std_config()
    }
}

/// `recv.leaf(args...)` with an explicit `this` receiver; returns the
/// call's result value.
fn method_call(
    m: &mut abcd_ir::Module,
    b: abcd_ir::BlockId,
    recv: abcd_ir::ValueId,
    leaf: &str,
    args: Vec<abcd_ir::ValueId>,
) -> abcd_ir::ValueId {
    let name = intern(m, leaf);
    let f = emit(m, b, Op::LoadProp { object: recv, name });
    emit(
        m,
        b,
        Op::Call {
            callee: f,
            this: Some(recv),
            args,
            kind: CallKind::Dynamic,
        },
    )
}

/// kind→family (AllocArray ⇒ `Array.prototype`): `a[i] = tainted` then
/// `a.pop()` — the element taint flows to the popped value through the
/// heap-fact Field([AnyIndex]) endpoint match.
#[test]
fn prototype_family_alloc_array_pop() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
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
    let r = method_call(&mut m, entry, a, "pop", vec![]);
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    // TWO sink hits on the one print: the element fact fires BOTH of
    // pop's flows — Field([AnyIndex])→Return (leftover [], the precise
    // carrier) and Base→Return (leftover [AnyIndex] appended — the
    // registered leftover-append over-approximation, FlowDroid's
    // cutSubFields=false default; harmless: the probe runner dedups
    // sink hits by source line).
    assert_eq!(report.hits.len(), 2, "the popped element is tainted");
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Array.prototype.pop"),
        "the prototype summary applied: {:?}",
        report.summaries_applied
    );
    // The direct name candidate set is empty (a local receiver has no
    // global name) — nothing was logged as a named miss for this site.
    assert!(
        !report.summary_misses.contains_key("Array.prototype.pop"),
        "a rescued site is not backlog"
    );
}

/// Constant family through global-store provenance: two stores into
/// `sg` (a string constant + the tainted param) — the family union is
/// {String}, the taint rides the param store, and
/// `String.prototype.charCodeAt`'s Base→Return flow carries it.
#[test]
fn prototype_family_const_string_via_global_provenance() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let sg = intern(&mut m, "sg");
    let s = load_string(&mut m, entry, "abc");
    emit_void(&mut m, entry, Op::StoreGlobal { name: sg, value: s });
    emit_void(&mut m, entry, Op::StoreGlobal { name: sg, value: p });
    let g = try_get_global(&mut m, entry, "sg");
    let zero = load_number(&mut m, entry, 0.0);
    let r = method_call(&mut m, entry, g, "charCodeAt", vec![zero]);
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert_eq!(report.hits.len(), 1, "the code unit derives from taint");
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "String.prototype.charCodeAt"),
        "the const-family summary applied: {:?}",
        report.summaries_applied
    );
}

/// Multi-site merge: a phi of an AllocArray and an AllocObject types
/// the receiver {Array, Object} — the Array family's summary fires
/// and the heap fact on the array's site still matches through the
/// phi-merged points-to set.
#[test]
fn prototype_multi_site_phi_merge() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let left = add_block(&mut m, f);
    let right = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p,
            true_dest: left,
            false_dest: right,
        },
    );
    let a = alloc_array(&mut m, left);
    let idx = load_number(&mut m, left, 0.0);
    emit_void(
        &mut m,
        left,
        Op::StorePropIdx {
            object: a,
            index: idx,
            value: p,
        },
    );
    emit_void(&mut m, left, Op::Branch { dest: join });
    let o = alloc_object(&mut m, right);
    emit_void(&mut m, right, Op::Branch { dest: join });
    link(&mut m, entry, left);
    link(&mut m, entry, right);
    link(&mut m, left, join);
    link(&mut m, right, join);
    let recv = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    abcd_ir::Edge {
                        from: left,
                        kind: abcd_ir::EdgeKind::Normal,
                    },
                    a,
                ),
                (
                    abcd_ir::Edge {
                        from: right,
                        kind: abcd_ir::EdgeKind::Normal,
                    },
                    o,
                ),
            ],
        },
    );
    let r = method_call(&mut m, join, recv, "pop", vec![]);
    print_call(&mut m, join, vec![r]);
    emit_void(&mut m, join, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    // Two hits: the double-fire documented in
    // `prototype_family_alloc_array_pop` (Base→Return's leftover plus
    // the precise Field flow).
    assert_eq!(
        report.hits.len(),
        2,
        "the array arm's element taint survives the merge"
    );
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Array.prototype.pop"),
        "the Array family's summary applied to the merged receiver"
    );
}

/// Negative control: a user OBJECT with a `pop` property read must NOT
/// get `Array.prototype.pop`'s summary (family Object has no pop
/// registered — the builtin stays out). The synthesized
/// `Object.prototype.pop` candidate is logged as a miss (the backlog
/// signal) and the site falls through to the unknown-keep ladder rung.
#[test]
fn prototype_negative_control_user_object_pop() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let _p = add_param(&mut m, f, 1);
    let o = alloc_object(&mut m, entry);
    let r = method_call(&mut m, entry, o, "pop", vec![]);
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert_eq!(report.hits.len(), 0, "no builtin flow on a user object");
    assert!(
        !report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Array.prototype.pop"),
        "the array builtin stayed out"
    );
    assert!(
        report.summary_misses.contains_key("Object.prototype.pop"),
        "the prototype miss is the backlog signal: {:?}",
        report.summary_misses
    );
    assert_eq!(
        report.stats.sites_unknown, 1,
        "fell through to the unknown-keep rung"
    );
}

/// Precedence: a summary registered under the DIRECT qualified name
/// (`a.pop`) beats the prototype path (`Array.prototype.pop`) — the
/// direct name match is rung 1 of the lookup ladder.
#[test]
fn prototype_precedence_direct_name_wins() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // The receiver is a global whose store is an array (family Array)
    // — both the direct candidate `a.pop` AND the prototype candidate
    // `Array.prototype.pop` are applicable.
    let a_name = intern(&mut m, "a");
    let arr = alloc_array(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::StoreGlobal {
            name: a_name,
            value: arr,
        },
    );
    let g = try_get_global(&mut m, entry, "a");
    let r = method_call(&mut m, entry, g, "pop", vec![p]);
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let mut config = builtin_config();
    config.extra_summaries.push((
        "a.pop".to_owned(),
        Some(1),
        Summary::new("user override: param → return").flow(Endpoint::Param(0), Endpoint::Return),
    ));
    let report = abcd_taint::run_taint(&m, &config);
    assert!(
        report.summaries_applied.iter().any(|(_, n)| n == "a.pop"),
        "the direct name won: {:?}",
        report.summaries_applied
    );
    assert!(
        !report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Array.prototype.pop"),
        "the prototype path was not consulted"
    );
}

/// Negative caching: two `Object.prototype.pop` misses — the second
/// lookup is served by the registry's negative cache.
#[test]
fn prototype_negative_caching() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let _p = add_param(&mut m, f, 1);
    let o1 = alloc_object(&mut m, entry);
    let o2 = alloc_object(&mut m, entry);
    let r1 = method_call(&mut m, entry, o1, "pop", vec![]);
    let r2 = method_call(&mut m, entry, o2, "pop", vec![]);
    let s = add(&mut m, entry, r1, r2);
    print_call(&mut m, entry, vec![s]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report.stats.negative_cache_hits >= 1,
        "the second Object.prototype.pop lookup hit the negative cache: {:?}",
        report.stats
    );
    assert_eq!(
        report.summary_misses.get("Object.prototype.pop"),
        Some(&2),
        "both sites logged the miss: {:?}",
        report.summary_misses
    );
}

/// Unknown receiver (a parameter): NO family is invented — the
/// prototype path produces no candidate at all and the site falls
/// through untouched.
#[test]
fn prototype_unknown_receiver_no_lookup() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let r = method_call(&mut m, entry, p, "pop", vec![]);
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report
            .summary_misses
            .keys()
            .all(|n| !n.contains(".prototype.")),
        "no prototype candidate was synthesized: {:?}",
        report.summary_misses
    );
    assert!(
        report
            .summaries_applied
            .iter()
            .all(|(_, n)| !n.contains(".prototype.")),
        "no prototype summary applied: {:?}",
        report.summaries_applied
    );
}

/// The GetIterator family: for-of's protocol object over an AllocArray
/// types `Iterator.prototype`; the source's `[AnyIndex]` element taint
/// re-keys onto the iterator (the GetIterator flow rule), rides
/// `Iterator.prototype.next`'s Field([AnyIndex])→Return flow, and a
/// `.value` read picks it up.
#[test]
fn prototype_iterator_next_family() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
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
    let it = emit(&mut m, entry, Op::GetIterator { obj: a });
    let r = method_call(&mut m, entry, it, "next", vec![]);
    let value_name = intern(&mut m, "value");
    let v = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: r,
            name: value_name,
        },
    );
    print_call(&mut m, entry, vec![v]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    // Two hits — the same double-fire as pop (the Base→Return leftover
    // rides alongside the precise Field([AnyIndex]) carrier).
    assert_eq!(
        report.hits.len(),
        2,
        "the element taint rode next().value out of the loop protocol"
    );
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Iterator.prototype.next"),
        "the iterator summary applied: {:?}",
        report.summaries_applied
    );
}

/// The push alias flow: `a.push(tainted)` re-keys the argument onto
/// the array's `[AnyIndex]` element channel; a later indexed load
/// reads it back.
#[test]
fn prototype_array_push_alias_flow() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let a = alloc_array(&mut m, entry);
    let _ = method_call(&mut m, entry, a, "push", vec![p]);
    let idx = load_number(&mut m, entry, 0.0);
    let x = emit(
        &mut m,
        entry,
        Op::LoadPropIdx {
            object: a,
            index: idx,
        },
    );
    print_call(&mut m, entry, vec![x]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert_eq!(report.hits.len(), 1, "the pushed element reads back");
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Array.prototype.push"),
        "the push summary applied: {:?}",
        report.summaries_applied
    );
}

/// Nested-hop family resolution: an AllocArray reached through a
/// GLOBAL STORE (the corpus' `let a = […]; sttoglobalrecord "a"` —
/// `a.pop()` shape) — the stored value never passes the top-level site
/// walk, so the def-chain walk must carry the alloc kind itself
/// (pinned against the smoke-caught regression where `a.pop` stayed a
/// miss). A second store (the tainted param) exercises the provenance
/// UNION: families merge to {Array}, the taint rides the global
/// binding, and pop's Base→Return flow carries it. (Element-precise
/// matching through a global alias stays out of scope: the unknown-
/// base heap key and the endpoint's positive-intersection discipline
/// deliberately do not meet — see local_alias_evidence.)
#[test]
fn prototype_family_alloc_via_global_provenance() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let a_name = intern(&mut m, "a");
    let arr = alloc_array(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::StoreGlobal {
            name: a_name,
            value: arr,
        },
    );
    // A second store of the same global (may-redefinition): the
    // family union stays {Array} and the global binding is tainted.
    emit_void(
        &mut m,
        entry,
        Op::StoreGlobal {
            name: a_name,
            value: p,
        },
    );
    let g = try_get_global(&mut m, entry, "a");
    let r = method_call(&mut m, entry, g, "pop", vec![]);
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Array.prototype.pop"),
        "the global-provenance family applied: {:?}",
        report.summaries_applied
    );
    assert!(
        !report.summary_misses.contains_key("a.pop"),
        "the rescued direct name left the backlog log"
    );
    assert!(
        report.hits.len() >= 1,
        "the may-array receiver's taint rode pop's Base→Return flow"
    );
}

// ────────────────────────────────────────────────────────────────────
// t-P4: the full gap propagator (gap.rs) — a summary's callback
// carries taint INTO the user callback's formals (gap enter) and the
// callback's RESULT back onto the summary call's result (gap return),
// through synthetic call edges layered onto the solver's call graph
// (GapCallGraph). Registered drivers: Array.prototype.forEach/map/
// filter (the canonical gap trio).
// ────────────────────────────────────────────────────────────────────

/// A STATIC callback `cb(e) { <body over e> }` skeleton: the es2abc
/// 0xF frame default ([func][newTarget][this][formals…]) so the gap
/// enter binds formal 0 = params[3]. Returns (FuncId, formal ValueId,
/// entry block) for the test to fill in.
fn gap_cb_skeleton(
    m: &mut abcd_ir::Module,
    name: &str,
) -> (abcd_ir::FuncId, abcd_ir::ValueId, abcd_ir::BlockId) {
    let cb = add_func_named(m, name);
    m.functions[cb.index()].modifiers = abcd_ir::Modifiers::STATIC;
    let b = entry_of(m, cb);
    add_param(m, cb, 0);
    add_param(m, cb, 1);
    add_param(m, cb, 2);
    let e = add_param(m, cb, 3);
    (cb, e, b)
}

/// Gap ENTER wiring: `a[i] = tainted; a.forEach(cb)` — the array's
/// `[AnyIndex]` heap taint matches forEach's Field([AnyIndex]) enter
/// rule (positive site intersection) and seeds the callback's formal;
/// the print inside the callback body fires. This is the FlowDroid
/// "spawn the normal analysis into user code" step: the callback body
/// is entered through an ordinary IFDS call edge (GapCallGraph), not a
/// side-channel.
#[test]
fn gap_for_each_enters_callback() {
    let mut m = mk_module();
    let (cb, e, cb_entry) = gap_cb_skeleton(&mut m, "cb");
    {
        print_call(&mut m, cb_entry, vec![e]);
        emit_void(&mut m, cb_entry, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
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
    let def_cb = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: cb,
            captures: vec![],
            length: 1,
        },
    );
    let clo_cb = emit(&mut m, entry, Op::AllocClosure { func: def_cb });
    method_call(&mut m, entry, a, "forEach", vec![clo_cb]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        !report.hits.is_empty(),
        "the element taint entered the callback: {:?}",
        report.hits
    );
    assert!(
        report.hits.iter().all(|h| h.fact.local_base() == Some(e)),
        "every hit is on the callback formal: {:?}",
        report.hits
    );
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Array.prototype.forEach"),
        "the forEach summary applied: {:?}",
        report.summaries_applied
    );
    assert_eq!(report.gap_sites_resolved, 1, "the callback resolved");
    assert_eq!(report.gap_sites_unresolved, 0);
}

/// Gap RETURN wiring: `let b = a.map(e => e); print(b[0])` — the
/// callback's returned taint flows back onto the map result's
/// `[AnyIndex]` chain (map's `return_to_result`), and the indexed load
/// cuts it.
#[test]
fn gap_map_return_wires_result_elements() {
    let mut m = mk_module();
    let (cb, e, cb_entry) = gap_cb_skeleton(&mut m, "cb");
    {
        emit_void(&mut m, cb_entry, Op::Return { value: Some(e) });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
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
    let def_cb = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: cb,
            captures: vec![],
            length: 1,
        },
    );
    let clo_cb = emit(&mut m, entry, Op::AllocClosure { func: def_cb });
    let r = method_call(&mut m, entry, a, "map", vec![clo_cb]);
    let x = emit(
        &mut m,
        entry,
        Op::LoadPropIdx {
            object: r,
            index: idx,
        },
    );
    print_call(&mut m, entry, vec![x]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(x)),
        "the callback return wired onto the result's elements: {:?}",
        report.hits
    );
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Array.prototype.map"),
        "the map summary applied: {:?}",
        report.summaries_applied
    );
    assert_eq!(report.gap_sites_resolved, 1);
}

/// The negative control for the gap RETURN channel (probe e13's
/// mechanism-level twin, isolated from the load rule's unknown-base
/// wildcard): map's callback IGNORES its parameter and returns a
/// constant — the result value must carry NO `[AnyIndex]` taint (the
/// result's element taint comes from the callback's return, not from
/// the base array directly). Prints the result itself (no indexed
/// load), so the heap fact on the SOURCE array cannot meet the sink
/// through an unknown-base load.
#[test]
fn gap_map_callback_ignoring_param_no_return_flow() {
    let mut m = mk_module();
    let (cb, _e, cb_entry) = gap_cb_skeleton(&mut m, "cb");
    {
        let zero = load_number(&mut m, cb_entry, 0.0);
        emit_void(&mut m, cb_entry, Op::Return { value: Some(zero) });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
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
    let def_cb = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: cb,
            captures: vec![],
            length: 1,
        },
    );
    let clo_cb = emit(&mut m, entry, Op::AllocClosure { func: def_cb });
    let r = method_call(&mut m, entry, a, "map", vec![clo_cb]);
    print_call(&mut m, entry, vec![r]); // the result array itself — clean
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report.hits.is_empty(),
        "a param-ignoring callback taints nothing: {:?}",
        report.hits
    );
    assert_eq!(report.gap_sites_resolved, 1, "the gap still resolved");
}

/// forEach's return channel is `None` (the result is undefined): the
/// callback's RETURN taint dies at the gap return, but the callback
/// body still RAN — pinned by its side effect (a tainted global store)
/// reaching the later read. Two assertions: `print(foreach_result)` is
/// clean, `print(leaked_global)` hits.
#[test]
fn gap_for_each_discards_callback_return_but_runs_body() {
    let mut m = mk_module();
    let leak = intern(&mut m, "LEAK");
    let (cb, e, cb_entry) = gap_cb_skeleton(&mut m, "cb");
    {
        emit_void(
            &mut m,
            cb_entry,
            Op::StoreGlobal {
                name: leak,
                value: e,
            },
        );
        // The callback RETURNS its tainted formal — forEach must drop it.
        emit_void(&mut m, cb_entry, Op::Return { value: Some(e) });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
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
    let def_cb = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: cb,
            captures: vec![],
            length: 1,
        },
    );
    let clo_cb = emit(&mut m, entry, Op::AllocClosure { func: def_cb });
    let r = method_call(&mut m, entry, a, "forEach", vec![clo_cb]);
    print_call(&mut m, entry, vec![r]); // forEach result: undefined — clean
    let g = try_get_global(&mut m, entry, "LEAK");
    print_call(&mut m, entry, vec![g]); // the body's side effect — tainted
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        !report.hits.iter().any(|h| h.fact.local_base() == Some(r)),
        "the callback return must NOT reach the forEach result: {:?}",
        report.hits
    );
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(g)),
        "the callback body's global side effect proves the body ran: {:?}",
        report.hits
    );
}

/// Exclusive × gap: an EXCLUSIVE summary with a callback must still run
/// the user callback (the gap edge is not the callee-body edge —
/// FlowDroid's spawnAnalysisIntoClientCode discipline), while the
/// exclusive bypass kill still applies to the summary call's operands
/// (the tainted argument does not survive the call-to-return edge).
#[test]
fn gap_exclusive_callback_summary_still_enters() {
    let mut m = mk_module();
    let (cb, e, cb_entry) = gap_cb_skeleton(&mut m, "cb");
    {
        print_call(&mut m, cb_entry, vec![e]);
        emit_void(&mut m, cb_entry, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let def_cb = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: cb,
            captures: vec![],
            length: 1,
        },
    );
    let clo_cb = emit(&mut m, entry, Op::AllocClosure { func: def_cb });
    let collect = try_get_global(&mut m, entry, "collect");
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: collect,
            this: None,
            args: vec![p, clo_cb],
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![p]); // killed by the exclusive bypass
    emit_void(&mut m, entry, Op::Return { value: None });

    let config = abcd_taint::TaintConfig {
        extra_summaries: vec![(
            "collect".to_owned(),
            Some(2),
            abcd_taint::Summary::new("exclusive gap test: arg0 → cb formal 0")
                .exclusive()
                .callback(1)
                .gap_enter(Endpoint::Param(0), 0),
        )],
        ..builtin_config()
    };
    let report = abcd_taint::run_taint(&m, &config);
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(e)),
        "the exclusive summary's gap edge still entered the callback: {:?}",
        report.hits
    );
    assert!(
        !report.hits.iter().any(|h| h.fact.local_base() == Some(p)),
        "the exclusive bypass kill still applies to the operands: {:?}",
        report.hits
    );
    assert!(
        report.summaries_applied.iter().any(|(_, n)| n == "collect"),
        "the custom summary applied: {:?}",
        report.summaries_applied
    );
    assert_eq!(report.gap_sites_resolved, 1);
}

/// The honest fallback: the callback value is an opaque global load —
/// no gap edge, the summary still applies, the element taint never
/// enters user code (the mini-gap tag alone remains). The wrapper
/// counter records the unresolved site.
#[test]
fn gap_unresolved_callback_falls_back() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
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
    let opaque_cb = try_get_global(&mut m, entry, "CB");
    let r = method_call(&mut m, entry, a, "forEach", vec![opaque_cb]);
    print_call(&mut m, entry, vec![r]); // forEach result: undefined — clean
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report.hits.is_empty(),
        "no flow without a resolved callback: {:?}",
        report.hits
    );
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Array.prototype.forEach"),
        "the summary still applied: {:?}",
        report.summaries_applied
    );
    assert_eq!(report.gap_sites_resolved, 0);
    assert_eq!(
        report.gap_sites_unresolved, 1,
        "the unresolved callback is counted (the honest fallback)"
    );
}

/// Depth/termination: a gap-entered callback body contributes its OWN
/// gap edge (cb1's body allocates an array, stores the tainted element,
/// and forEach's it with cb2). Gap edges are static — the solver's
/// monotone dedup is the whole termination argument; this test pins
/// that nested gaps converge and carry taint across BOTH hops.
#[test]
fn gap_nested_callbacks_terminate() {
    let mut m = mk_module();
    let (cb2, f2, cb2_entry) = gap_cb_skeleton(&mut m, "cb2");
    {
        print_call(&mut m, cb2_entry, vec![f2]);
        emit_void(&mut m, cb2_entry, Op::Return { value: None });
    }
    let (cb1, e1, cb1_entry) = gap_cb_skeleton(&mut m, "cb1");
    {
        // let c = [e]; c.forEach(cb2) — the nested gap, its receiver a
        // LOCAL alloc (element taint re-keys onto c's site). The store
        // must come BEFORE the print: print's exclusive summary kills
        // the operand taint on its own call-to-return edge
        // (WrapperPropagationRule's killSource — the pinned
        // exclusive-summary semantics), so a print first would sever
        // the flow into the store.
        let c = alloc_array(&mut m, cb1_entry);
        let idx = load_number(&mut m, cb1_entry, 0.0);
        emit_void(
            &mut m,
            cb1_entry,
            Op::StorePropIdx {
                object: c,
                index: idx,
                value: e1,
            },
        );
        let def_cb2 = emit(
            &mut m,
            cb1_entry,
            Op::DefineFunc {
                body: cb2,
                captures: vec![],
                length: 1,
            },
        );
        let clo_cb2 = emit(&mut m, cb1_entry, Op::AllocClosure { func: def_cb2 });
        method_call(&mut m, cb1_entry, c, "forEach", vec![clo_cb2]);
        print_call(&mut m, cb1_entry, vec![e1]);
        emit_void(&mut m, cb1_entry, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
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
    let def_cb1 = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: cb1,
            captures: vec![],
            length: 1,
        },
    );
    let clo_cb1 = emit(&mut m, entry, Op::AllocClosure { func: def_cb1 });
    method_call(&mut m, entry, a, "forEach", vec![clo_cb1]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(e1)),
        "the outer gap entered cb1: {:?}",
        report.hits
    );
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(f2)),
        "the nested gap entered cb2 (and the solver terminated): {:?}",
        report.hits
    );
    assert_eq!(
        report.gap_sites_resolved, 2,
        "both the outer and the nested gap edge resolved"
    );
}

/// The mini-gap channel (the callback VALUE's `[AnyIndex]` tag) still
/// covers DIRECT user calls of the tagged value, and binds the first
/// FORMAL (params[formal_base], the N66 fix — not params[1]). The
/// summary here is mini-gap only (`callback` without enter rules), so
/// no full gap edge exists: `gap_counts == (0, 0)` pins that the hit
/// arrives through the tag + direct call. The receiver is a phi of an
/// AllocArray and the tainted param — the phi types Array (the summary
/// applies) AND carries the whole-array local taint (the tag fires on
/// the Base match).
#[test]
fn gap_mini_gap_tag_binds_first_formal_on_direct_call() {
    use abcd_ir::{Edge, EdgeKind};
    let mut m = mk_module();
    let (cb, e, cb_entry) = gap_cb_skeleton(&mut m, "cb");
    {
        print_call(&mut m, cb_entry, vec![e]);
        emit_void(&mut m, cb_entry, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let t = add_block(&mut m, f);
    let els = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p,
            true_dest: t,
            false_dest: els,
        },
    );
    let arr = alloc_array(&mut m, t);
    emit_void(&mut m, t, Op::Branch { dest: join });
    emit_void(&mut m, els, Op::Branch { dest: join });
    link(&mut m, entry, t);
    link(&mut m, entry, els);
    link(&mut m, t, join);
    link(&mut m, els, join);
    let recv = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    arr,
                ),
                (
                    Edge {
                        from: els,
                        kind: EdgeKind::Normal,
                    },
                    p,
                ),
            ],
        },
    );
    let def_cb = emit(
        &mut m,
        join,
        Op::DefineFunc {
            body: cb,
            captures: vec![],
            length: 1,
        },
    );
    let clo_cb = emit(&mut m, join, Op::AllocClosure { func: def_cb });
    // tagit: mini-gap only (no enter rules) — tags the callback value.
    method_call(&mut m, join, recv, "tagit", vec![clo_cb]);
    // The DIRECT call of the tagged value: the mini-gap channel seeds
    // the callback's first formal.
    let zero = load_number(&mut m, join, 0.0);
    push_inst(
        &mut m,
        join,
        Op::Call {
            callee: clo_cb,
            this: None,
            args: vec![zero],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, join, Op::Return { value: None });

    let config = abcd_taint::TaintConfig {
        extra_summaries: vec![(
            "Array.prototype.tagit".to_owned(),
            None,
            abcd_taint::Summary::new("mini-gap only: tags the callback value").callback(0),
        )],
        ..builtin_config()
    };
    let report = abcd_taint::run_taint(&m, &config);
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(e)),
        "the tagged callback value seeded the first formal at the direct call: {:?}",
        report.hits
    );
    assert_eq!(
        (report.gap_sites_resolved, report.gap_sites_unresolved),
        (0, 0),
        "no full gap edge — the mini-gap channel carried the flow"
    );
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Array.prototype.tagit"),
        "the mini-gap summary applied: {:?}",
        report.summaries_applied
    );
}

// ────────────────────────────────────────────────────────────────────
// t-P5: the miss-log-driven second tier — String.prototype.replace's
// dual form (string replacement + the callback gap), the
// constructor-result family arm (RegExp.prototype.test), split/join,
// parseInt, and Object.assign's result identity.
// ────────────────────────────────────────────────────────────────────

/// A string receiver typed through global-store provenance (the
/// `prototype_family_const_string_via_global_provenance` pattern): a
/// string constant store types the family, a tainted-param store
/// carries the taint. Returns the receiver value (`TryGetGlobal("s")`).
fn tainted_string_global(
    m: &mut abcd_ir::Module,
    entry: abcd_ir::BlockId,
    p: abcd_ir::ValueId,
) -> abcd_ir::ValueId {
    let s_name = intern(m, "s");
    let clean = load_string(m, entry, "clean");
    emit_void(
        m,
        entry,
        Op::StoreGlobal {
            name: s_name,
            value: clean,
        },
    );
    emit_void(
        m,
        entry,
        Op::StoreGlobal {
            name: s_name,
            value: p,
        },
    );
    try_get_global(m, entry, "s")
}

/// replace's STRING form: Base→Return carries the receiver's content
/// taint; Param(1)→Return carries the replacement's; the PATTERN
/// (param 0) selects — control, not content, so a tainted pattern over
/// a clean base taints nothing (the identity heuristic would — the
/// clean assertion pins the summary's win). The string replacement is
/// a provably non-callable constant: the gap scan must NOT count the
/// site as an unresolved callback (the t-P5 refinement).
#[test]
fn replace_string_form_flows() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // s.replace("a", "!") — Base→Return.
    let s = tainted_string_global(&mut m, entry, p);
    let pat1 = load_string(&mut m, entry, "a");
    let bang = load_string(&mut m, entry, "!");
    let r1 = method_call(&mut m, entry, s, "replace", vec![pat1, bang]);
    print_call(&mut m, entry, vec![r1]);
    // clean.replace("a", p) — Param(1)→Return (replacement verbatim).
    let c_name = intern(&mut m, "c");
    let clean2 = load_string(&mut m, entry, "clean");
    emit_void(
        &mut m,
        entry,
        Op::StoreGlobal {
            name: c_name,
            value: clean2,
        },
    );
    let c = try_get_global(&mut m, entry, "c");
    let pat2 = load_string(&mut m, entry, "a");
    let r2 = method_call(&mut m, entry, c, "replace", vec![pat2, p]);
    print_call(&mut m, entry, vec![r2]);
    // c.replace(p, "!") — the pattern is control: CLEAN.
    let c2 = try_get_global(&mut m, entry, "c");
    let bang2 = load_string(&mut m, entry, "!");
    let r3 = method_call(&mut m, entry, c2, "replace", vec![p, bang2]);
    print_call(&mut m, entry, vec![r3]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(r1)),
        "Base→Return: the receiver's content taints the result: {:?}",
        report.hits
    );
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(r2)),
        "Param(1)→Return: the replacement is inserted verbatim: {:?}",
        report.hits
    );
    assert!(
        !report.hits.iter().any(|h| h.fact.local_base() == Some(r3)),
        "the pattern selects (control, not content) — no flow: {:?}",
        report.hits
    );
    assert_eq!(
        report
            .summaries_applied
            .iter()
            .filter(|(_, n)| n == "String.prototype.replace")
            .count(),
        3,
        "all three replace sites applied the summary: {:?}",
        report.summaries_applied
    );
    // The two CONSTANT-replacement sites contribute nothing to the gap
    // counters (the t-P5 not-a-callback refinement); the
    // `c.replace("a", p)` site's replacement is a PARAM — possibly a
    // function — and honestly counts as unresolved.
    assert_eq!(report.gap_sites_resolved, 0);
    assert_eq!(
        report.gap_sites_unresolved, 1,
        "only the param-replacement site is an honest unresolved callback"
    );
}

/// replace's FUNCTION form: the callback receives the base-derived
/// match (gap enter on formal 0) and its RETURN is inserted into the
/// result string (the EMPTY-chain return channel — the result is a
/// string, not map's array). To pin the return channel against the
/// static Base→Return flow, the receiver is CLEAN and the callback
/// returns a global it loads (the state base crosses the gap edge; the
/// return channel is the ONLY route to the result).
#[test]
fn replace_function_form_gap_return() {
    let mut m = mk_module();
    let leak = intern(&mut m, "LEAK");
    let (cb, _e, cb_entry) = gap_cb_skeleton(&mut m, "cb");
    {
        // cb(m) { return LEAK; } — the returned taint is NOT
        // base-derived, so only the gap return channel can carry it.
        let g = try_get_global(&mut m, cb_entry, "LEAK");
        emit_void(&mut m, cb_entry, Op::Return { value: Some(g) });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // A CLEAN string receiver (one store — the family types String,
    // the taint never touches it).
    let s_name = intern(&mut m, "s");
    let clean = load_string(&mut m, entry, "clean");
    emit_void(
        &mut m,
        entry,
        Op::StoreGlobal {
            name: s_name,
            value: clean,
        },
    );
    // The taint lives on the LEAK global the callback loads.
    emit_void(
        &mut m,
        entry,
        Op::StoreGlobal {
            name: leak,
            value: p,
        },
    );
    let s = try_get_global(&mut m, entry, "s");
    let pat = load_string(&mut m, entry, "a");
    let def_cb = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: cb,
            captures: vec![],
            length: 1,
        },
    );
    let clo_cb = emit(&mut m, entry, Op::AllocClosure { func: def_cb });
    let r = method_call(&mut m, entry, s, "replace", vec![pat, clo_cb]);
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(r)),
        "the callback return rode the empty-chain gap return onto the result: {:?}",
        report.hits
    );
    assert_eq!(report.gap_sites_resolved, 1, "the callback resolved");
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "String.prototype.replace"),
        "the replace summary applied"
    );
}

/// replace's function form, gap ENTER: a tainted receiver's content
/// enters the callback on formal 0 (the match) — the print inside the
/// callback body fires.
#[test]
fn replace_function_form_gap_enter() {
    let mut m = mk_module();
    let (cb, e, cb_entry) = gap_cb_skeleton(&mut m, "cb");
    {
        print_call(&mut m, cb_entry, vec![e]);
        emit_void(&mut m, cb_entry, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let s = tainted_string_global(&mut m, entry, p);
    let pat = load_string(&mut m, entry, "a");
    let def_cb = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: cb,
            captures: vec![],
            length: 1,
        },
    );
    let clo_cb = emit(&mut m, entry, Op::AllocClosure { func: def_cb });
    method_call(&mut m, entry, s, "replace", vec![pat, clo_cb]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(e)),
        "the base content entered the callback's match formal: {:?}",
        report.hits
    );
    assert_eq!(report.gap_sites_resolved, 1);
}

/// The constructor-result family arm (t-P5, prototype.rs §5): the
/// receiver of `r.test(...)` is the result of `new RegExp(...)` — the
/// shape es2abc lowers regexp literals to. RegExp.prototype.test
/// applies, and its NO-FLOW model (a pure verdict) beats the identity
/// heuristic: the tainted haystack does NOT taint the boolean result.
#[test]
fn regexp_test_constructor_result_family() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // r = new RegExp("a+") — the callee is a bare global load.
    let ctor = try_get_global(&mut m, entry, "RegExp");
    let pat = load_string(&mut m, entry, "a+");
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: ctor,
            this: None,
            args: vec![pat],
            kind: CallKind::New,
        },
    );
    let verdict = method_call(&mut m, entry, r, "test", vec![p]);
    print_call(&mut m, entry, vec![verdict]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "RegExp.prototype.test"),
        "the constructor-result arm typed the receiver RegExp: {:?}",
        report.summaries_applied
    );
    assert!(
        !report
            .hits
            .iter()
            .any(|h| h.fact.local_base() == Some(verdict)),
        "the verdict is a fresh boolean — the tainted haystack carries nothing: {:?}",
        report.hits
    );
}

/// The corpus shape (regexp.js): the `new RegExp(...)` result reaches
/// the receiver through a GLOBAL STORE (flow-insensitive provenance
/// union), not a direct def chain. Same summary, same verdict purity.
#[test]
fn regexp_test_via_global_provenance_constructor_arm() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let r_name = intern(&mut m, "r");
    let ctor = try_get_global(&mut m, entry, "RegExp");
    let pat = load_string(&mut m, entry, "a+");
    let newed = emit(
        &mut m,
        entry,
        Op::Call {
            callee: ctor,
            this: None,
            args: vec![pat],
            kind: CallKind::New,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::StoreGlobal {
            name: r_name,
            value: newed,
        },
    );
    let r = try_get_global(&mut m, entry, "r");
    let verdict = method_call(&mut m, entry, r, "test", vec![p]);
    print_call(&mut m, entry, vec![verdict]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "RegExp.prototype.test"),
        "the provenance hop reached the constructor arm: {:?}",
        report.summaries_applied
    );
    assert!(
        report.hits.is_empty(),
        "a pure verdict over a tainted haystack: no flow: {:?}",
        report.hits
    );
}

/// Constructor-arm negative control: `new Foo()` (a user/global
/// constructor NOT in the builtin table) types NOTHING — no prototype
/// candidate is synthesized, no summary applies.
#[test]
fn constructor_arm_never_invents_user_families() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let ctor = try_get_global(&mut m, entry, "Foo");
    let newed = emit(
        &mut m,
        entry,
        Op::Call {
            callee: ctor,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    let r = method_call(&mut m, entry, newed, "test", vec![p]);
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report
            .summaries_applied
            .iter()
            .all(|(_, n)| !n.contains(".prototype.")),
        "no prototype summary fired for a user constructor: {:?}",
        report.summaries_applied
    );
    assert!(
        report
            .summary_misses
            .keys()
            .all(|n| !n.contains(".prototype.")),
        "no prototype candidate was synthesized: {:?}",
        report.summary_misses
    );
}

/// split: the pieces derive from the base's content (Base→Return; an
/// element read cuts one step). The SEPARATOR is removed — control,
/// not content: a tainted separator over a clean base taints nothing
/// (the identity heuristic would; the clean assertion pins the win).
#[test]
fn split_base_flow_separator_is_control() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // s.split(",") — tainted base.
    let s = tainted_string_global(&mut m, entry, p);
    let comma = load_string(&mut m, entry, ",");
    let parts = method_call(&mut m, entry, s, "split", vec![comma]);
    let zero = load_number(&mut m, entry, 0.0);
    let first = emit(
        &mut m,
        entry,
        Op::LoadPropIdx {
            object: parts,
            index: zero,
        },
    );
    print_call(&mut m, entry, vec![first]);
    // clean.split(p) — tainted separator: CLEAN result.
    let c_name = intern(&mut m, "c");
    let clean = load_string(&mut m, entry, "x,y");
    emit_void(
        &mut m,
        entry,
        Op::StoreGlobal {
            name: c_name,
            value: clean,
        },
    );
    let c = try_get_global(&mut m, entry, "c");
    let parts2 = method_call(&mut m, entry, c, "split", vec![p]);
    print_call(&mut m, entry, vec![parts2]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report
            .hits
            .iter()
            .any(|h| h.fact.local_base() == Some(first)),
        "the piece derives from the base: {:?}",
        report.hits
    );
    assert!(
        !report
            .hits
            .iter()
            .any(|h| h.fact.local_base() == Some(parts2)),
        "the separator is control, not content: {:?}",
        report.hits
    );
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "String.prototype.split"),
        "the split summary applied"
    );
}

/// join: element taint rides Field([AnyIndex])→Return (the push-tagged
/// element channel), and the SEPARATOR is inserted verbatim
/// (Param(0)→Return) — the asymmetry with split is the semantics.
#[test]
fn join_element_and_separator_flows() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // a.push(p); a.join("-") — the element channel.
    let a = alloc_array(&mut m, entry);
    method_call(&mut m, entry, a, "push", vec![p]);
    let dash = load_string(&mut m, entry, "-");
    let joined = method_call(&mut m, entry, a, "join", vec![dash]);
    print_call(&mut m, entry, vec![joined]);
    // clean.join(p) — the separator is inserted verbatim.
    let b = alloc_array(&mut m, entry);
    let joined2 = method_call(&mut m, entry, b, "join", vec![p]);
    print_call(&mut m, entry, vec![joined2]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report
            .hits
            .iter()
            .any(|h| h.fact.local_base() == Some(joined)),
        "the element taint joined into the string: {:?}",
        report.hits
    );
    assert!(
        report
            .hits
            .iter()
            .any(|h| h.fact.local_base() == Some(joined2)),
        "the separator is inserted verbatim: {:?}",
        report.hits
    );
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Array.prototype.join"),
        "the join summary applied"
    );
}

/// parseInt (direct global name): Param(0)→Return — a content-derived
/// digit parse (the charCodeAt discipline); the radix is control. The
/// t-P5 exclusive-policy review registers parseInt NON-exclusive (a
/// pure READ of its operand: killSource would be a real FN for SSA
/// re-use, and the callee-body kill is vacuous for a native), so the
/// one tainted param threads all three call sites.
#[test]
fn parseint_content_derived_radix_is_control() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let pi = try_get_global(&mut m, entry, "parseInt");
    let r1 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: pi,
            this: None,
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![r1]);
    // parseInt("42", p) — the radix is control: CLEAN.
    let pi2 = try_get_global(&mut m, entry, "parseInt");
    let fortytwo = load_string(&mut m, entry, "42");
    let r2 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: pi2,
            this: None,
            args: vec![fortytwo, p],
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![r2]);
    // Number.parseInt(p) — the qualified name resolves the same model.
    let number = try_get_global(&mut m, entry, "Number");
    let parseint_leaf = intern(&mut m, "parseInt");
    let pi3 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: number,
            name: parseint_leaf,
        },
    );
    let r3 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: pi3,
            this: None,
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![r3]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(r1)),
        "parseInt(tainted) derives from the string content: {:?}",
        report.hits
    );
    assert!(
        !report.hits.iter().any(|h| h.fact.local_base() == Some(r2)),
        "the radix is control, not content: {:?}",
        report.hits
    );
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(r3)),
        "Number.parseInt resolves the same model: {:?}",
        report.hits
    );
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "parseInt")
            && report
                .summaries_applied
                .iter()
                .any(|(_, n)| n == "Number.parseInt"),
        "both keys applied: {:?}",
        report.summaries_applied
    );
}

/// Object.assign's result identity (t-P5 deepening): the call RESULT
/// is param 0, so a tainted SOURCE argument flows to the result
/// directly (Param(1)→Return) — the `let o = Object.assign({}, src)`
/// shape needs no load through the mutated target.
#[test]
fn assign_result_carries_source_taint() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let o = alloc_object(&mut m, entry);
    let assign = try_get_global(&mut m, entry, "Object");
    let assign_leaf = intern(&mut m, "assign");
    let assign_fn = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: assign,
            name: assign_leaf,
        },
    );
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: assign_fn,
            this: None,
            args: vec![o, p],
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &builtin_config());
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(r)),
        "the result IS the mutated target — the source taint reaches it: {:?}",
        report.hits
    );
    assert!(
        report
            .summaries_applied
            .iter()
            .any(|(_, n)| n == "Object.assign"),
        "the assign summary applied"
    );
}
