//! ECMAScript builtin library summaries, backward liveness pruning, 256 KiB stack safety,
//! and demand-driven PTA scaling tests.

use crate::common::*;
use abcd_ir::{CallKind, Op};
use abcd_taint::driver::run_taint_full;
use abcd_taint::fact::{Fact, TaintFact};
use abcd_taint::summary::{Endpoint, Summary};
use abcd_taint::{SinkSpec, SourceSpec, TaintConfig};

use super::prototype_and_gap::gap_cb_skeleton;
use super::{builtin_config, method_call, print_call, std_config};

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
/// site as an unresolved callback (`definitely_not_callable`).
#[test]
fn replace_string_form_flows() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
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
    // counters (`definitely_not_callable` refinement); the
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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

/// Constructor-result family arm (prototype.rs §5): the
/// receiver of `r.test(...)` is the result of `new RegExp(...)` — the
/// shape es2abc lowers regexp literals to. RegExp.prototype.test
/// applies, and its NO-FLOW model (a pure verdict) beats the identity
/// heuristic: the tainted haystack does NOT taint the boolean result.
#[test]
fn regexp_test_constructor_result_family() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
/// digit parse (the charCodeAt discipline); the radix is control.
/// `parseInt` is registered NON-exclusive (a pure READ of its operand:
/// killing operand taint on the bypass edge would cause a false negative
/// for SSA re-use, and the callee-body kill is vacuous for a native), so
/// the one tainted param threads all three call sites.
#[test]
fn parseint_content_derived_radix_is_control() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
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

/// Object.assign's result identity: the call RESULT
/// is param 0, so a tainted SOURCE argument flows to the result
/// directly (Param(1)→Return) — the `let o = Object.assign({}, src)`
/// shape needs no load through the mutated target.
#[test]
fn assign_result_carries_source_taint() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
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

// ────────────────────────────────────────────────────────────────────
// Algorithmic scaling & IFDS explosion regressions (Issue #33)
// ────────────────────────────────────────────────────────────────────

/// Multi-hundred-instruction chain regression: dead intermediate SSA
/// temporaries (`v_i` defined at instruction `i` and consumed only at
/// `i + 1`) must be pruned by backward SSA local liveness so `path_edges`
/// scales linearly `O(L)` rather than quadratically `O(L^2)`, including
/// across `native_identity = true` unknown calls and wildcard `Heap(empty)`
/// property-load amplification.
#[test]
fn liveness_pruning_scales_linearly_on_long_chains() {
    let build_chain = |steps: usize| {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "func_main_0");
        let entry = entry_of(&m, f);
        add_param(&mut m, f, 0);
        let p = add_param(&mut m, f, 1);

        // Also seed a wildcard `Heap(empty).[item]` fact (unknown base store)
        // so every property load in the chain generates a fresh tainted local.
        let unk = try_get_global(&mut m, entry, "unknownContainer");
        let item_sym = intern(&mut m, "item");
        emit_void(
            &mut m,
            entry,
            Op::StoreProp {
                object: unk,
                name: item_sym,
                value: p,
            },
        );

        let one = load_number(&mut m, entry, 1.0);
        let helper_fn = try_get_global(&mut m, entry, "nativeTransform");
        let mut cur = try_get_global(&mut m, entry, "SEED");
        for i in 0..steps {
            cur = if i % 3 == 0 {
                add(&mut m, entry, cur, one)
            } else if i % 3 == 1 {
                emit(
                    &mut m,
                    entry,
                    Op::Call {
                        callee: helper_fn,
                        this: None,
                        args: vec![cur],
                        kind: CallKind::Dynamic,
                    },
                )
            } else {
                emit(
                    &mut m,
                    entry,
                    Op::LoadProp {
                        object: cur,
                        name: item_sym,
                    },
                )
            };
        }
        print_call(&mut m, entry, vec![cur]);
        emit_void(&mut m, entry, Op::Return { value: None });
        m
    };

    let cfg = TaintConfig {
        sources: vec![
            SourceSpec::FunctionParams {
                name: "func_main_0".to_owned(),
                params: None,
            },
            SourceSpec::GlobalLoad {
                name: "SEED".to_owned(),
            },
        ],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        alias_rung: 0,
        ..TaintConfig::default()
    };

    let rep_250 = abcd_taint::run_taint(&build_chain(250), &cfg);
    let rep_500 = abcd_taint::run_taint(&build_chain(500), &cfg);

    assert!(
        !rep_250.hits.is_empty() && !rep_500.hits.is_empty(),
        "taint reaches the final sink across all 500 steps"
    );
    assert!(
        !rep_500.hits[0].path.is_empty(),
        "witness path reconstruction remains intact"
    );
    // Without liveness pruning, 500 chained temporaries generate >125,000
    // path edges and quadruple (~4.0x) when doubling from 250 to 500.
    // With liveness pruning, total edges stay O(L) (< 6,000 at L=500) and
    // doubling L scales by ~2.0x.
    assert!(
        rep_500.path_edges < 6_000,
        "expected O(L) path_edges (< 6,000), got {} (250-step had {})",
        rep_500.path_edges,
        rep_250.path_edges
    );
    assert!(
        rep_500.path_edges * 10 <= rep_250.path_edges * 22,
        "expected near-2x linear scaling from L=250 ({}) to L=500 ({})",
        rep_250.path_edges,
        rep_500.path_edges
    );
}

/// IFDS `0 -> d` unconditional source generators (`GlobalLoad`,
/// `ModuleImport`, `CallReturn`) must fire ONLY on `Fact::Zero`, never
/// cross-multiplying unrelated incoming procedure-entry taint facts.
#[test]
fn ifds_zero_sources_do_not_cross_multiply_incoming_facts() {
    use abcd_ir::module::{EsModule, ImportDecl, Modifiers, ModuleRequest};
    use abcd_ir::op::ModuleVarKind;

    let mut m = mk_module();
    let s_dev = m.sym.intern("@ohos.deviceInfo");
    let s_odid = m.sym.intern("ODID");
    m.classes[0].es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: s_odid,
            import_name: s_odid,
            module_request: s_dev,
        }],
        exports: Vec::new(),
        module_requests: vec![ModuleRequest {
            specifier: s_dev,
            lazy: false,
        }],
    });

    // Callee entered with 6 distinct tainted parameters from `func_main_0`,
    // while also containing GlobalLoad, ModuleImport, and CallReturn sources.
    let worker = add_func_named(&mut m, "worker");
    m.func_mut(worker).unwrap().modifiers = Modifiers::STATIC;
    let (g_src, m_src, c_src);
    {
        let wb = entry_of(&m, worker);
        for i in 0..9 {
            add_param(&mut m, worker, i);
        }
        g_src = try_get_global(&mut m, wb, "HOST_SECRET");
        m_src = emit(
            &mut m,
            wb,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let api = try_get_global(&mut m, wb, "readClipboard");
        c_src = emit(
            &mut m,
            wb,
            Op::Call {
                callee: api,
                this: None,
                args: Vec::new(),
                kind: CallKind::Dynamic,
            },
        );
        print_call(&mut m, wb, vec![g_src]);
        print_call(&mut m, wb, vec![m_src]);
        print_call(&mut m, wb, vec![c_src]);
        emit_void(&mut m, wb, Op::Return { value: None });
    }

    let main_fn = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, main_fn);
    add_param(&mut m, main_fn, 0);
    let mut call_args = Vec::new();
    for i in 1..=6 {
        call_args.push(add_param(&mut m, main_fn, i));
    }
    let wref = load_method_ref(&mut m, entry, worker);
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: wref,
            this: None,
            args: call_args,
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let cfg = TaintConfig {
        sources: vec![
            SourceSpec::FunctionParams {
                name: "func_main_0".to_owned(),
                params: None,
            },
            SourceSpec::GlobalLoad {
                name: "HOST_SECRET".to_owned(),
            },
            SourceSpec::ModuleImport {
                specifier: "@ohos.deviceInfo".to_owned(),
                import_name: None,
            },
            SourceSpec::CallReturn {
                name: "readClipboard".to_owned(),
            },
        ],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        ..TaintConfig::default()
    };

    let (report, result) = run_taint_full(&m, &cfg);
    assert_eq!(report.hits.len(), 3, "all three 0->d sources reach print");
    for src_val in [g_src, m_src, c_src] {
        let anchors: Vec<&Fact> = result
            .path_edges()
            .iter()
            .filter(|e| e.target_fact == Fact::of(TaintFact::local(src_val)))
            .map(|e| &e.source_fact)
            .collect();
        assert!(
            !anchors.is_empty(),
            "expected path edges for generated source {src_val:?}"
        );
        assert!(
            anchors.iter().all(|a| matches!(a, Fact::Zero)),
            "0->d source {src_val:?} must only anchor to Fact::Zero, got {anchors:?}"
        );
    }
}

/// Soundness guard for all four implicit SSA local-use channels during
/// liveness pruning:
/// 1. `call_base_value` at `Op::Call` (`this: None`, receiver only on earlier `LoadProp`),
/// 2. `await_resume` (`AwaitUncaught` -> dead gap -> `ResumeGenerator`),
/// 3. `ctor_this` at `Op::Return { value: None }` inside `FunctionKind::Constructor`,
/// 4. Rung-2 interprocedural alias evidence (`site_info_at(v)` non-empty when Rung-0 sites empty).
#[test]
fn liveness_preserves_implicit_uses_and_interprocedural_aliases() {
    use abcd_ir::module::{FunctionKind, Modifiers};

    let mut m = mk_module();

    // (3) Constructor storing `this.secret = arg` then running dead instructions before `return;`.
    let ctor = add_func_named(&mut m, "BoxCtor");
    {
        let fd = m.func_mut(ctor).unwrap();
        fd.kind = FunctionKind::Constructor;
        fd.modifiers = Modifiers::STATIC;
        let cb = entry_of(&m, ctor);
        add_param(&mut m, ctor, 0);
        add_param(&mut m, ctor, 1);
        let this_v = add_param(&mut m, ctor, 2);
        let arg_v = add_param(&mut m, ctor, 3);
        let sec = intern(&mut m, "secret");
        emit_void(
            &mut m,
            cb,
            Op::StoreProp {
                object: this_v,
                name: sec,
                value: arg_v,
            },
        );
        let _dead1 = load_number(&mut m, cb, 1.0);
        let _dead2 = load_number(&mut m, cb, 2.0);
        emit_void(&mut m, cb, Op::Return { value: None });
    }

    // (4) Factory + identity helper for Rung-2 interprocedural local alias evidence.
    let mk_obj = add_func_named(&mut m, "mkObj");
    m.func_mut(mk_obj).unwrap().modifiers = Modifiers::STATIC;
    {
        let mb = entry_of(&m, mk_obj);
        for i in 0..3 {
            add_param(&mut m, mk_obj, i);
        }
        let o = alloc_object(&mut m, mb);
        emit_void(&mut m, mb, Op::Return { value: Some(o) });
    }
    let id_fn = add_func_named(&mut m, "idObj");
    m.func_mut(id_fn).unwrap().modifiers = Modifiers::STATIC;
    {
        let ib = entry_of(&m, id_fn);
        for i in 0..3 {
            add_param(&mut m, id_fn, i);
        }
        let x = add_param(&mut m, id_fn, 3);
        emit_void(&mut m, ib, Op::Return { value: Some(x) });
    }

    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let p_assign = add_param(&mut m, f, 2);

    // (1) `call_base_value`: `recv` is a `Call` result (`site_info_at` empty),
    // `callee = recv.send`, followed by dead ops where `recv` is never mentioned
    // again, then `callee()` (`this: None`) whose summary reads `Endpoint::Base`.
    let get_recv = try_get_global(&mut m, entry, "makeTaintedRecv");
    let recv = emit(
        &mut m,
        entry,
        Op::Call {
            callee: get_recv,
            this: None,
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    let send_sym = intern(&mut m, "send");
    let send_callee = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: recv,
            name: send_sym,
        },
    );
    let _pad_a = load_number(&mut m, entry, 10.0);
    let _pad_b = load_number(&mut m, entry, 20.0);
    let base_res = emit(
        &mut m,
        entry,
        Op::Call {
            callee: send_callee,
            this: None,
            args: Vec::new(),
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![base_res]);

    // (2) `await_resume`: `awaited` is an instruction temporary, unused across
    // intervening ops until `ResumeGenerator(gen_obj)`.
    let gen_obj = emit(&mut m, entry, Op::AsyncFunctionEnter);
    let awaited = add(&mut m, entry, p, _pad_a);
    let _ = emit(
        &mut m,
        entry,
        Op::AwaitUncaught {
            funcobj: gen_obj,
            value: awaited,
        },
    );
    let _pad_c = load_number(&mut m, entry, 30.0);
    let _pad_d = load_number(&mut m, entry, 40.0);
    let resumed = emit(&mut m, entry, Op::ResumeGenerator { genobj: gen_obj });
    print_call(&mut m, entry, vec![resumed]);

    // (3) Invoke `new BoxCtor(p)` and read `.secret`.
    let ctor_ref = load_method_ref(&mut m, entry, ctor);
    let inst = emit(
        &mut m,
        entry,
        Op::Call {
            callee: ctor_ref,
            this: None,
            args: vec![p],
            kind: CallKind::New,
        },
    );
    let sec = intern(&mut m, "secret");
    let ctor_read = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: inst,
            name: sec,
        },
    );
    print_call(&mut m, entry, vec![ctor_read]);

    // (4) Rung-2 interprocedural alias: `box1 = mkObj(); box2 = idObj(box1);`
    // `Object.assign(box1, p)` taints `Local(box1)` (empty fields); `box1` has NO
    // further uses, while `box2.secret` reads through `local_alias_evidence`.
    let mk_ref = load_method_ref(&mut m, entry, mk_obj);
    let box1 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: mk_ref,
            this: None,
            args: Vec::new(),
            kind: CallKind::Direct,
        },
    );
    let id_ref = load_method_ref(&mut m, entry, id_fn);
    let box2 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: id_ref,
            this: None,
            args: vec![box1],
            kind: CallKind::Direct,
        },
    );
    let obj_glob = try_get_global(&mut m, entry, "Object");
    let assign_sym = intern(&mut m, "assign");
    let assign_fn = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: obj_glob,
            name: assign_sym,
        },
    );
    let _ = emit(
        &mut m,
        entry,
        Op::Call {
            callee: assign_fn,
            this: None,
            args: vec![box1, p_assign],
            kind: CallKind::Dynamic,
        },
    );
    let _pad_e = load_number(&mut m, entry, 50.0);
    let _pad_f = load_number(&mut m, entry, 60.0);
    let alias_read = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: box2,
            name: sec,
        },
    );
    print_call(&mut m, entry, vec![alias_read]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let mut cfg = builtin_config();
    cfg.extra_summaries.push((
        "makeTaintedRecv.send".to_owned(),
        Some(0),
        Summary::new("base -> return").flow(Endpoint::Base, Endpoint::Return),
    ));
    let report = abcd_taint::run_taint(&m, &cfg);
    for expected in [base_res, resumed, ctor_read, alias_read] {
        assert!(
            report
                .hits
                .iter()
                .any(|h| h.fact.local_base() == Some(expected)),
            "missing expected hit for {expected:?}: {:?}",
            report.hits
        );
    }
}

/// 256 KiB small-stack regression (`AGENTS.md` §3.1): deep `Mov` / `LoadProp`
/// chains must complete without call-stack overflow across name resolution,
/// prototype resolution, liveness analysis, and IFDS taint solving.
#[test]
fn small_stack_256k_deep_def_chains_no_overflow() {
    let handle = std::thread::Builder::new()
        .name("taint-256k".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut m = mk_module();
            let f = add_func_named(&mut m, "func_main_0");
            let entry = entry_of(&m, f);
            add_param(&mut m, f, 0);
            let p = add_param(&mut m, f, 1);

            let arr = alloc_array(&mut m, entry);
            let mut recv = arr;
            for _ in 0..2_500 {
                recv = emit(&mut m, entry, Op::Mov { src: recv });
            }
            let push_sym = intern(&mut m, "push");
            let mut callee = emit(
                &mut m,
                entry,
                Op::LoadProp {
                    object: recv,
                    name: push_sym,
                },
            );
            for _ in 0..2_500 {
                callee = emit(&mut m, entry, Op::Mov { src: callee });
            }
            let _ = emit(
                &mut m,
                entry,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![p],
                    kind: CallKind::Dynamic,
                },
            );
            let pop_val = method_call(&mut m, entry, arr, "pop", Vec::new());
            print_call(&mut m, entry, vec![pop_val]);
            emit_void(&mut m, entry, Op::Return { value: None });

            let cands = abcd_taint::names::callee_name_candidates(&m, callee);
            assert!(cands.is_empty());

            let cfg = TaintConfig {
                alias_rung: 0,
                ..builtin_config()
            };
            let report = abcd_taint::run_taint(&m, &cfg);
            assert!(
                report
                    .hits
                    .iter()
                    .any(|h| h.fact.local_base() == Some(pop_val)),
                "deep mov/loadprop chain preserved array push->pop taint: {:?}",
                report.hits
            );
        })
        .expect("spawn 256k thread");
    handle.join().expect("256k thread must not overflow stack");
}

/// Caller non-field `TaintBase::Local(x)` survives across `SiteClass::BodyStep`
/// helper calls (`helper(x); print(x)`), while non-empty `Local(o).secret`
/// field chains still defer to the callee body so field strong-kills fire.
#[test]
fn bodystep_preserves_caller_scalar_local_and_keeps_field_strong_kill() {
    use abcd_analysis::dataflow::heap::{FieldChain, FieldKey};
    use abcd_ir::Modifiers;

    // (A) Scalar caller local passed to a body-resolved helper still reaches a
    // subsequent caller sink across all alias rungs.
    {
        let mut m = mk_module();
        let helper = add_func_named(&mut m, "noopHelper");
        m.func_mut(helper).unwrap().modifiers = Modifiers::STATIC;
        {
            let hb = entry_of(&m, helper);
            for i in 0..4 {
                add_param(&mut m, helper, i);
            }
            let _ = load_number(&mut m, hb, 42.0);
            emit_void(&mut m, hb, Op::Return { value: None });
        }

        let main_fn = add_func_named(&mut m, "func_main_0");
        let entry = entry_of(&m, main_fn);
        add_param(&mut m, main_fn, 0);
        let tainted = add_param(&mut m, main_fn, 1);

        let href = load_method_ref(&mut m, entry, helper);
        let _ = emit(
            &mut m,
            entry,
            Op::Call {
                callee: href,
                this: None,
                args: vec![tainted],
                kind: CallKind::Direct,
            },
        );
        print_call(&mut m, entry, vec![tainted]);
        emit_void(&mut m, entry, Op::Return { value: None });

        for rung in [0u8, 1, 2] {
            let cfg = TaintConfig {
                alias_rung: rung,
                ..std_config()
            };
            let report = abcd_taint::run_taint(&m, &cfg);
            assert!(
                report.stats.sites_body_step >= 1,
                "rung {rung}: expected BodyStep classification"
            );
            assert_eq!(
                report.hits.len(),
                1,
                "rung {rung}: scalar caller local must survive BodyStep: {:?}",
                report.hits
            );
            assert_eq!(report.hits[0].fact.local_base(), Some(tainted));
        }
    }

    // (B) Field-bearing `Local(o).[secret]` does NOT bypass `BodyStep`, so a
    // callee strong-killing `formal_o.secret = clean` sanitizes `o.secret`.
    let run_field_case = |call_sanitizer: bool, rung: u8| -> usize {
        let mut m = mk_module();
        let sec = intern(&mut m, "secret");

        let sanitize = add_func_named(&mut m, "sanitizeSecret");
        m.func_mut(sanitize).unwrap().modifiers = Modifiers::STATIC;
        {
            let sb = entry_of(&m, sanitize);
            add_param(&mut m, sanitize, 0);
            add_param(&mut m, sanitize, 1);
            add_param(&mut m, sanitize, 2);
            let formal_o = add_param(&mut m, sanitize, 3);
            let clean = load_string(&mut m, sb, "clean");
            emit_void(
                &mut m,
                sb,
                Op::StoreProp {
                    object: formal_o,
                    name: sec,
                    value: clean,
                },
            );
            emit_void(
                &mut m,
                sb,
                Op::Return {
                    value: Some(formal_o),
                },
            );
        }

        let main_fn = add_func_named(&mut m, "func_main_0");
        let entry = entry_of(&m, main_fn);
        add_param(&mut m, main_fn, 0);
        let tainted = add_param(&mut m, main_fn, 1);

        let o = alloc_object(&mut m, entry);
        let mk_wrap = try_get_global(&mut m, entry, "mkFieldWrap");
        let wrap = emit(
            &mut m,
            entry,
            Op::Call {
                callee: mk_wrap,
                this: None,
                args: vec![tainted],
                kind: CallKind::Dynamic,
            },
        );
        let cp = try_get_global(&mut m, entry, "copyField");
        let _ = emit(
            &mut m,
            entry,
            Op::Call {
                callee: cp,
                this: None,
                args: vec![o, wrap],
                kind: CallKind::Dynamic,
            },
        );
        if call_sanitizer {
            let sref = load_method_ref(&mut m, entry, sanitize);
            let _ = emit(
                &mut m,
                entry,
                Op::Call {
                    callee: sref,
                    this: None,
                    args: vec![o],
                    kind: CallKind::Direct,
                },
            );
        }
        let read_sec = emit(
            &mut m,
            entry,
            Op::LoadProp {
                object: o,
                name: sec,
            },
        );
        print_call(&mut m, entry, vec![read_sec]);
        emit_void(&mut m, entry, Op::Return { value: None });

        let sec_chain = FieldChain::new().pushed(FieldKey::Named(sec), 5);
        let mut cfg = TaintConfig {
            alias_rung: rung,
            ..std_config()
        };
        cfg.extra_summaries.push((
            "mkFieldWrap".to_owned(),
            Some(1),
            Summary::new("param0 -> return.secret")
                .flow(Endpoint::Param(0), Endpoint::ReturnField(sec_chain)),
        ));
        cfg.extra_summaries.push((
            "copyField".to_owned(),
            Some(2),
            Summary::new("param1 -> param0").flow(Endpoint::Param(1), Endpoint::Param(0)),
        ));
        abcd_taint::run_taint(&m, &cfg).hits.len()
    };

    assert_eq!(
        run_field_case(false, 2),
        1,
        "rung 2: positive control without sanitizer must hit"
    );
    assert_eq!(
        run_field_case(true, 2),
        0,
        "rung 2: callee strong-kill on Local(o).secret must not be bypassed on call_to_return_flow"
    );
}

/// Demand-driven PTA root slicing (`> 512` functions) + `zero_needed` IFDS
/// `Λ`-seeding: in a 600+-function multi-record bundle with 595+ unrelated
/// object/method noise functions, a `GlobalLoad` -> OOP class method ->
/// cross-module ES `StoreModuleVar` / `LoadModuleVar` -> `print` sink flow
/// still resolves at Rung 2 with tiny `path_edges`.
#[test]
fn large_bundle_demand_pta_roots_and_zero_needed_slice_unrelated_subgraphs() {
    use abcd_ir::consts::Const;
    use abcd_ir::function::FunctionData;
    use abcd_ir::module::{
        ClassData, EsModule, ExportDecl, FunctionKind, ImportDecl, ModuleRequest,
    };
    use abcd_ir::op::ModuleVarKind;
    use abcd_ir::{ClassId, FuncId, Modifiers, Module};

    let mut m = Module::new();

    let add_record = |m: &mut Module, desc: &str, esm: EsModule| -> ClassId {
        let cid = ClassId::new(m.classes.len() as u32);
        let dsym = m.sym.intern(desc);
        let mut cls = ClassData::new(dsym, dsym);
        cls.es_module = Some(esm);
        m.classes.push(cls);
        cid
    };

    let add_fn_in = |m: &mut Module, cid: ClassId, name: &str, kind: FunctionKind| -> FuncId {
        let nsym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(cid, nsym, kind);
        fd.modifiers = Modifiers::STATIC;
        m.functions.push(fd);
        m.classes[cid.index()].methods.push(fid);
        add_block(m, fid);
        fid
    };

    let leaked_sym = m.sym.intern("leakedToken");
    let exp_spec_sym = m.sym.intern("exporter/service");

    let exp_cid = add_record(
        &mut m,
        "Lexporter/service;",
        EsModule {
            imports: Vec::new(),
            exports: vec![ExportDecl::Local {
                local_name: leaked_sym,
                export_name: leaked_sym,
            }],
            module_requests: Vec::new(),
        },
    );
    let imp_cid = add_record(
        &mut m,
        "Limporter/consumer;",
        EsModule {
            imports: vec![ImportDecl::Regular {
                local_name: leaked_sym,
                import_name: leaked_sym,
                module_request: exp_spec_sym,
            }],
            exports: Vec::new(),
            module_requests: vec![ModuleRequest {
                specifier: exp_spec_sym,
                lazy: false,
            }],
        },
    );
    let noise_cid = add_record(&mut m, "Lnoise/unrelated;", EsModule::default());

    // Record 0: OOP `Boxer` class (`ctor` + `wrap`) + `func_main_0` exporting wrapped secret.
    let ctor_fn = add_fn_in(&mut m, exp_cid, "Boxer", FunctionKind::Constructor);
    {
        let b = entry_of(&m, ctor_fn);
        for i in 0..3 {
            add_param(&mut m, ctor_fn, i);
        }
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let wrap_fn = add_fn_in(&mut m, exp_cid, "wrap", FunctionKind::Function);
    let payload_sym = intern(&mut m, "payload");
    {
        let b = entry_of(&m, wrap_fn);
        add_param(&mut m, wrap_fn, 0);
        add_param(&mut m, wrap_fn, 1);
        add_param(&mut m, wrap_fn, 2);
        let val = add_param(&mut m, wrap_fn, 3);
        let obj = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: obj,
                name: payload_sym,
                value: val,
            },
        );
        let loaded = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: obj,
                name: payload_sym,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(loaded),
            },
        );
    }

    let exp_main = add_fn_in(&mut m, exp_cid, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, exp_main);
        for i in 0..3 {
            add_param(&mut m, exp_main, i);
        }
        let wrap_sym = intern(&mut m, "wrap");
        let wrap_name_cid = m.consts.intern(Const::String(wrap_sym));
        let wrap_fn_cid = m.consts.intern(Const::MethodRef {
            func: wrap_fn,
            kind: abcd_ir::LitMethodKind::Method,
        });
        let members = m.consts.push_array(vec![wrap_name_cid, wrap_fn_cid]);
        let cls_val = emit(
            &mut m,
            b,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: ctor_fn,
                heritage: None,
                members,
                member_attrs: Vec::new(),
                count: 1,
            })),
        );
        let inst = emit(
            &mut m,
            b,
            Op::Call {
                callee: cls_val,
                this: None,
                args: Vec::new(),
                kind: CallKind::New,
            },
        );
        let src_val = try_get_global(&mut m, b, "SECRET_ENV");
        let wrap_callee = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: inst,
                name: wrap_sym,
            },
        );
        let wrapped = emit(
            &mut m,
            b,
            Op::Call {
                callee: wrap_callee,
                this: Some(inst),
                args: vec![src_val],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: wrapped,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Record 1: `func_main_0` importing `leakedToken` and passing it to `print`.
    let imp_main = add_fn_in(&mut m, imp_cid, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, imp_main);
        for i in 0..3 {
            add_param(&mut m, imp_main, i);
        }
        let imported = emit(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        print_call(&mut m, b, vec![imported]);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Record 2: `func_main_0` + 596 unrelated functions allocating objects and calling helpers.
    let tmp_sym = intern(&mut m, "tmp");
    let mut noise_fns = Vec::with_capacity(596);
    for idx in 0..596usize {
        let nf = add_fn_in(
            &mut m,
            noise_cid,
            &format!("noise_{idx}"),
            FunctionKind::Function,
        );
        noise_fns.push(nf);
    }
    for (idx, &nf) in noise_fns.iter().enumerate() {
        let b = entry_of(&m, nf);
        for i in 0..3 {
            add_param(&mut m, nf, i);
        }
        let obj = alloc_object(&mut m, b);
        let nval = load_number(&mut m, b, idx as f64);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: obj,
                name: tmp_sym,
                value: nval,
            },
        );
        let read_back = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: obj,
                name: tmp_sym,
            },
        );
        if idx % 4 != 3 && idx + 1 < noise_fns.len() {
            let next_ref = load_method_ref(&mut m, b, noise_fns[idx + 1]);
            let _ = emit(
                &mut m,
                b,
                Op::Call {
                    callee: next_ref,
                    this: None,
                    args: Vec::new(),
                    kind: CallKind::Direct,
                },
            );
        }
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(read_back),
            },
        );
    }
    let noise_main = add_fn_in(&mut m, noise_cid, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, noise_main);
        for i in 0..3 {
            add_param(&mut m, noise_main, i);
        }
        let first_ref = load_method_ref(&mut m, b, noise_fns[0]);
        let _ = emit(
            &mut m,
            b,
            Op::Call {
                callee: first_ref,
                this: None,
                args: Vec::new(),
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    assert!(
        m.functions.len() > 512,
        "expected > 512 functions to engage PTA root slicing, got {}",
        m.functions.len()
    );

    let cfg = TaintConfig {
        sources: vec![SourceSpec::GlobalLoad {
            name: "SECRET_ENV".to_owned(),
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        alias_rung: 2,
        ohos_lifecycle: true,
        ..TaintConfig::default()
    };
    let report = abcd_taint::run_taint(&m, &cfg);
    assert_eq!(report.alias_rung_used, 2);
    assert_eq!(
        report.hits.len(),
        1,
        "expected cross-module OOP export sink hit under sliced PTA + zero_needed: {:?}",
        report.hits
    );
    assert_eq!(report.hits[0].sink, "print");
    assert_eq!(report.hits[0].position, "arg 0");
    assert!(
        report.path_edges < 200,
        "expected zero_needed + root-sliced PTA to skip 596 noise functions, got path_edges = {}",
        report.path_edges
    );
}
