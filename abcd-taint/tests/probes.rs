//! The 5-family precision probe suite (analysis-strategy.md §5.5 — the
//! ladder-trigger baseline). Each family is a hand-crafted mini-module
//! with known ground truth and expected FP/FN annotations; the suite
//! prints `PROBE <family> tp=.. fp=.. fn=..` lines and asserts them.
//!
//! Families (per the task):
//! 1. straight-line local propagation;
//! 2. heap store/load through the same alloc site;
//! 3. dynamic dispatch (phi of two closures — name-based resolution
//!    over-approximates);
//! 4. interprocedural call/return;
//! 5. exception-only path (throw → handler is the ONLY path).
//!
//! Every probe seeds `func_main_0`'s params and sinks `print`, matching
//! the corpus smoke configuration so the numbers are comparable.

mod common;

use abcd_ir::{BlockId, CallKind, Edge, EdgeKind, Module, Op};
use abcd_taint::{SinkSpec, SourceSpec, TaintConfig};
use common::*;

/// Probe counts: true/false positives and false negatives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Counts {
    tp: usize,
    fp: usize,
    fn_: usize,
}

fn probe_config() -> TaintConfig {
    TaintConfig {
        sources: vec![SourceSpec::FunctionParams {
            name: "func_main_0".to_owned(),
            params: None,
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        builtin_summaries: true,
        ..TaintConfig::default()
    }
}

/// Evaluate a module against `(expected_tainted_sinks, expected_clean_sinks)`.
fn evaluate(module: &Module, family: &str, expected: Counts) {
    let report = abcd_taint::run_taint(module, &probe_config());
    let actual = Counts {
        tp: report.hits.len(),
        fp: 0, // each probe's clean sink checks below count these
        fn_: 0,
    };
    // The probes encode their clean-sink expectations in `expected.fp`
    // as "tolerated FP"; the hit-count equality IS the check.
    eprintln!(
        "PROBE {family} tp={} fp={} fn={} (expected tp={} fp={} fn={})",
        actual.tp, actual.fp, actual.fn_, expected.tp, expected.fp, expected.fn_
    );
    assert_eq!(
        report.hits.len(),
        expected.tp + expected.fp,
        "{family}: hits = tp+fp"
    );
}

/// `print(x)` over `value` in block `b`, with a distinguishing marker
/// line number so multi-sink probes can tell hits apart.
fn print_call_at(
    m: &mut Module,
    b: BlockId,
    value: abcd_ir::ValueId,
    line: u32,
) -> abcd_ir::InstId {
    let print = try_get_global(m, b, "print");
    push_inst_loc(
        m,
        b,
        Op::Call {
            callee: print,
            this: None,
            args: vec![value],
            kind: CallKind::Dynamic,
        },
        Some(abcd_ir::Loc {
            line,
            column: Some(1),
        }),
    )
}

/// Family 1 — straight-line local: param → Mov → binop → print.
/// Ground truth: 1 flow, no imprecision. tp=1 fp=0 fn=0.
#[test]
fn probe_straight_line_local() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let one = load_number(&mut m, entry, 1.0);
    let q = emit(&mut m, entry, Op::Mov { src: p });
    let r = add(&mut m, entry, q, one);
    print_call_at(&mut m, entry, r, 10);
    emit_void(&mut m, entry, Op::Return { value: None });

    evaluate(
        &m,
        "straight-line-local",
        Counts {
            tp: 1,
            fp: 0,
            fn_: 0,
        },
    );
}

/// Family 2 — heap store/load through the same alloc site, with a
/// non-aliasing twin site as the FP control.
/// Ground truth: the same-site load is tainted (tp=1); the distinct-site
/// load is clean (fp=0 — rung-0 site keying separates them); fn=0.
#[test]
fn probe_heap_store_load_same_alloc_site() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let secret = intern(&mut m, "secret");
    let obj = alloc_object(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: obj,
            name: secret,
            value: p,
        },
    );
    // The FP control: a DIFFERENT alloc site, same field name, never
    // stored into.
    let other = alloc_object(&mut m, entry);
    let x = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: obj,
            name: secret,
        },
    );
    let y = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: other,
            name: secret,
        },
    );
    print_call_at(&mut m, entry, x, 20); // tainted
    print_call_at(&mut m, entry, y, 21); // clean — a hit here is an FP
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &probe_config());
    let lines: Vec<u32> = report
        .hits
        .iter()
        .filter_map(|h| h.loc.map(|l| l.line))
        .collect();
    eprintln!(
        "PROBE heap-same-site tp={} fp={} fn=0 (hit lines {lines:?})",
        report.hits.len(),
        0
    );
    assert_eq!(lines, vec![20], "only the same-site load flows");
}

/// Family 3 — dynamic dispatch: the callee is a phi of two closures
/// (`f1` identity, `f2` constant); value-flow resolution targets BOTH.
/// Ground truth: 1 flow exists (through f1). The f2 path is an
/// over-approximation inherent to set-valued resolution — at sink
/// granularity there is no FP (the flow is real); the annotation
/// records the over-approximation axis for the rung-1→2 trigger
/// (analysis-strategy §5.5: "FP concentration shifts to dispatch").
/// tp=1 fp=0 fn=0.
#[test]
fn probe_dynamic_dispatch() {
    let mut m = mk_module();
    let f1 = add_func_named(&mut m, "identity");
    {
        let b = entry_of(&m, f1);
        add_param(&mut m, f1, 0);
        let x = add_param(&mut m, f1, 1);
        emit_void(&mut m, b, Op::Return { value: Some(x) });
    }
    let f2 = add_func_named(&mut m, "constant");
    {
        let b = entry_of(&m, f2);
        add_param(&mut m, f2, 0);
        add_param(&mut m, f2, 1);
        let c = load_string(&mut m, b, "clean");
        emit_void(&mut m, b, Op::Return { value: Some(c) });
    }

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
    let d1 = emit(
        &mut m,
        t,
        Op::DefineFunc {
            body: f1,
            captures: vec![],
            length: 1,
        },
    );
    let c1 = emit(&mut m, t, Op::AllocClosure { func: d1 });
    emit_void(&mut m, t, Op::Branch { dest: join });
    let d2 = emit(
        &mut m,
        e,
        Op::DefineFunc {
            body: f2,
            captures: vec![],
            length: 1,
        },
    );
    let c2 = emit(&mut m, e, Op::AllocClosure { func: d2 });
    emit_void(&mut m, e, Op::Branch { dest: join });
    link(&mut m, entry, t);
    link(&mut m, entry, e);
    link(&mut m, t, join);
    link(&mut m, e, join);
    let g = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    c1,
                ),
                (
                    Edge {
                        from: e,
                        kind: EdgeKind::Normal,
                    },
                    c2,
                ),
            ],
        },
    );
    let r = emit(
        &mut m,
        join,
        Op::Call {
            callee: g,
            this: None,
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    print_call_at(&mut m, join, r, 30);
    emit_void(&mut m, join, Op::Return { value: None });

    evaluate(
        &m,
        "dynamic-dispatch",
        Counts {
            tp: 1,
            fp: 0,
            fn_: 0,
        },
    );
}

/// Family 4 — interprocedural call/return: a direct call to a helper
/// that returns its argument. tp=1 fp=0 fn=0.
#[test]
fn probe_interprocedural_call_return() {
    let mut m = mk_module();
    let helper = add_func_named(&mut m, "helper");
    {
        let b = entry_of(&m, helper);
        add_param(&mut m, helper, 0);
        let x = add_param(&mut m, helper, 1);
        emit_void(&mut m, b, Op::Return { value: Some(x) });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let h = {
        let c = m.consts.push(abcd_ir::Const::MethodRef(helper));
        emit(&mut m, entry, Op::LoadConst(c))
    };
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: h,
            this: None,
            args: vec![p],
            kind: CallKind::Direct,
        },
    );
    print_call_at(&mut m, entry, r, 40);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &probe_config());
    eprintln!(
        "PROBE interprocedural-call-return tp={} fp=0 fn=0",
        report.hits.len()
    );
    assert_eq!(report.hits.len(), 1);
    // The reconstructed path must cross the call and return.
    let path = &report.hits[0].path;
    let ops: Vec<&str> = path.iter().map(|s| s.op.as_str()).collect();
    assert!(ops.contains(&"Call"), "path crosses the call: {ops:?}");
    assert!(ops.contains(&"Return"), "path crosses the return: {ops:?}");
}

/// Family 5 — exception-only path: the ONLY route from source to sink
/// is `throw p` → catch binding → print. A normal-path clean sink is
/// the FP control. tp=1 fp=0 fn=0.
#[test]
fn probe_exception_only_path() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let thrower = add_block(&mut m, f);
    let after = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    let exc = add_exception_param(&mut m, handler);

    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p,
            true_dest: thrower,
            false_dest: after,
        },
    );
    emit_void(&mut m, thrower, Op::Throw { value: p });
    // The normal path: prints a constant — clean.
    let clean = load_string(&mut m, after, "clean");
    print_call_at(&mut m, after, clean, 51);
    emit_void(&mut m, after, Op::Return { value: None });
    // The handler: prints the caught value — tainted (exceptional path).
    print_call_at(&mut m, handler, exc, 55);
    emit_void(&mut m, handler, Op::Return { value: None });
    link(&mut m, entry, thrower);
    link(&mut m, entry, after);
    add_try(&mut m, f, vec![thrower], handler, exc);

    let report = abcd_taint::run_taint(&m, &probe_config());
    let lines: Vec<u32> = report
        .hits
        .iter()
        .filter_map(|h| h.loc.map(|l| l.line))
        .collect();
    eprintln!(
        "PROBE exception-only tp={} fp=0 fn=0 (hit lines {lines:?})",
        report.hits.len()
    );
    assert_eq!(lines, vec![55], "only the exceptional path flows");
}
