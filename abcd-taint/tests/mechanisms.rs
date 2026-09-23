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
