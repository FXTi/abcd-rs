//! Receiver prototype-family dispatch and callback-gap (`GapCallGraph`) mechanism tests.

use crate::common::*;
use abcd_ir::{CallKind, Op};
use abcd_taint::summary::{Endpoint, Summary};

use super::{builtin_config, method_call, print_call};

/// kind→family (AllocArray ⇒ `Array.prototype`): `a[i] = tainted` then
/// `a.pop()` — the element taint flows to the popped value through the
/// heap-fact Field([AnyIndex]) endpoint match.
#[test]
fn prototype_family_alloc_array_pop() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
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
    // carrier) and Base→Return (leftover [AnyIndex] appended; harmless:
    // the probe runner dedups sink hits by source line).
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
    // Both `Base -> Return` (`Local(r, [AnyIndex])`) and `Field([AnyIndex]) -> Return`
    // (`Local(r, [])`) converge onto whole-value `Local(v, [])` after reading `.value`.
    assert_eq!(
        report.hits.len(),
        1,
        "the element taint rode next().value out of the loop protocol: {:?}",
        report.hits
    );
    assert_eq!(report.hits[0].fact.local_base(), Some(v));
    assert!(report.hits[0].fact.fields.is_empty());
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
        !report.hits.is_empty(),
        "the may-array receiver's taint rode pop's Base→Return flow"
    );
}

// ────────────────────────────────────────────────────────────────────
// Full callback-gap propagator (gap.rs) — a summary's callback
// carries taint INTO the user callback's formals (gap enter) and the
// callback's RESULT back onto the summary call's result (gap return),
// through synthetic call edges layered onto the solver's call graph
// (GapCallGraph). Registered drivers: Array.prototype.forEach/map/
// filter.
// ────────────────────────────────────────────────────────────────────

/// A STATIC callback `cb(e) { <body over e> }` skeleton: the es2abc
/// 0xF frame default ([func][newTarget][this][formals…]) so the gap
/// enter binds formal 0 = params[3]. Returns (FuncId, formal ValueId,
/// entry block) for the test to fill in.
pub(super) fn gap_cb_skeleton(
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
/// the print inside the callback body fires because the callback body
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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

/// Exclusive × gap: an EXCLUSIVE summary kills only the call edge into the
/// callee body (never the callback gap edge and never unmodeled caller
/// operands unless listed in `Summary::clears`).
#[test]
fn gap_exclusive_callback_summary_still_enters() {
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
    let ext = try_get_global(&mut m, entry, "ext");
    let k = intern(&mut m, "k");
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: ext,
            name: k,
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
    let collect = try_get_global(&mut m, entry, "collect");
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: collect,
            this: None,
            args: vec![p, clo_cb, ext],
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![p]);
    let print_ext = print_call(&mut m, entry, vec![ext]);
    emit_void(&mut m, entry, Op::Return { value: None });

    // (1) Without `clears`: `exclusive` enters the callback and preserves both `p` and `ext`.
    let config = abcd_taint::TaintConfig {
        extra_summaries: vec![(
            "collect".to_owned(),
            Some(3),
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
        report.hits.iter().any(|h| h.fact.local_base() == Some(p)),
        "scalar pass-by-value Local(p) survives exclusive bypass: {:?}",
        report.hits
    );
    assert!(
        report.hits.iter().any(|h| h.call == print_ext),
        "unmodeled field-bearing Local(ext).[k] survives exclusive bypass unless cleared: {:?}",
        report.hits
    );
    assert!(
        report.summaries_applied.iter().any(|(_, n)| n == "collect"),
        "the custom summary applied: {:?}",
        report.summaries_applied
    );
    assert_eq!(report.gap_sites_resolved, 1);

    // (2) With explicit `.clear(Endpoint::Param(2))`: `Local(ext).[k]` is cleared.
    let cleared_config = abcd_taint::TaintConfig {
        extra_summaries: vec![(
            "collect".to_owned(),
            Some(3),
            abcd_taint::Summary::new("exclusive gap test with explicit clear")
                .exclusive()
                .clear(Endpoint::Param(2))
                .callback(1)
                .gap_enter(Endpoint::Param(0), 0),
        )],
        ..builtin_config()
    };
    let cleared_report = abcd_taint::run_taint(&m, &cleared_config);
    assert!(
        cleared_report
            .hits
            .iter()
            .any(|h| h.fact.local_base() == Some(e))
    );
    assert!(
        !cleared_report
            .hits
            .iter()
            .any(|h| h.call == print_ext || h.fact.local_base() == Some(ext)),
        "explicit `clear(Param(2))` kills Local(ext).[k]: {:?}",
        cleared_report.hits
    );
}

/// The honest fallback: the callback value is an opaque global load —
/// no gap edge, the summary still applies, the element taint never
/// enters user code (the mini-gap tag alone remains). The wrapper
/// counter records the unresolved site.
#[test]
fn gap_unresolved_callback_falls_back() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
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
        // the operand taint on its own call-to-return edge, so a print
        // first would sever the flow into the store.
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
    let entry = entry_of(&m, f);
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
    let entry = entry_of(&m, f);
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
// String / RegExp / parseInt / Object.assign builtins —
// String.prototype.replace's dual form (string replacement + the
// callback gap), the constructor-result family arm
// (RegExp.prototype.test), split/join, parseInt, and Object.assign's
// result identity.
// ────────────────────────────────────────────────────────────────────
