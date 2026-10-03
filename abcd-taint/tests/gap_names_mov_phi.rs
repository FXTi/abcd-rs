//! Gap-propagator and callee-name def-chain arm coverage (c-COV W10,
//! the longtail batch): callback values through `Mov`/`Phi` chains and
//! pooled `MethodRef` constants, the non-closure-site and cycle/dangling
//! guards, the not-a-callback refinement (const leaves), the
//! GapCallGraph merge dedup, and the name-resolution Mov/Phi arms
//! (including the loop-rotated callee phi). Exact hit/counter asserts.

mod common;

use abcd_ir::{CallKind, Const, Edge, EdgeKind, Op, ValueDef, ValueId};
use abcd_taint::driver::run_taint;
use abcd_taint::{SinkSpec, SourceSpec, TaintConfig};
use common::*;

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

/// A STATIC callback `cb(e) { print(e); return; }`; returns
/// (FuncId, formal value).
fn cb_print(m: &mut abcd_ir::Module, name: &str) -> (abcd_ir::FuncId, abcd_ir::ValueId) {
    let cb = add_func_named(m, name);
    m.func_mut(cb).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    let b = entry_of(m, cb);
    add_param(m, cb, 0);
    add_param(m, cb, 1);
    add_param(m, cb, 2);
    let e = add_param(m, cb, 3);
    print_call(m, b, vec![e]);
    emit_void(m, b, Op::Return { value: None });
    (cb, e)
}

/// `a[i] = p; a.forEach(cb_value)` — the canonical full-gap site.
fn foreach_site(
    m: &mut abcd_ir::Module,
    entry: abcd_ir::BlockId,
    p: abcd_ir::ValueId,
    cbv: abcd_ir::ValueId,
) {
    let a = alloc_array(m, entry);
    let idx = load_number(m, entry, 0.0);
    emit_void(
        m,
        entry,
        Op::StorePropIdx {
            object: a,
            index: idx,
            value: p,
        },
    );
    let leaf = intern(m, "forEach");
    let callee = emit(
        m,
        entry,
        Op::LoadProp {
            object: a,
            name: leaf,
        },
    );
    push_inst(
        m,
        entry,
        Op::Call {
            callee,
            this: Some(a),
            args: vec![cbv],
            kind: CallKind::Dynamic,
        },
    );
}

fn builtin_config() -> TaintConfig {
    TaintConfig {
        builtin_summaries: true,
        ..std_config()
    }
}

/// Callback values through a `Mov` and through a two-closure `Phi`:
/// the trace's Mov/Phi arms resolve them to bodies.
#[test]
fn gap_callback_through_mov_and_phi() {
    let mut m = mk_module();
    let (cb1, e1) = cb_print(&mut m, "cb1");
    let (cb2, e2) = cb_print(&mut m, "cb2");
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // (a) mov-chained callback.
    let clo1 = closure_of(&mut m, entry, cb1);
    let moved = emit(&mut m, entry, Op::Mov { src: clo1 });
    foreach_site(&mut m, entry, p, moved);
    // (b) a phi of two closures (in a diamond).
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
    let clo_t = closure_of(&mut m, t, cb1);
    emit_void(&mut m, t, Op::Branch { dest: join });
    let clo_e = closure_of(&mut m, els, cb2);
    emit_void(&mut m, els, Op::Branch { dest: join });
    link(&mut m, entry, t);
    link(&mut m, entry, els);
    link(&mut m, t, join);
    link(&mut m, els, join);
    let phiced = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    clo_t,
                ),
                (
                    Edge {
                        from: els,
                        kind: EdgeKind::Normal,
                    },
                    clo_e,
                ),
            ],
        },
    );
    foreach_site(&mut m, join, p, phiced);
    emit_void(&mut m, join, Op::Return { value: None });

    let report = run_taint(&m, &builtin_config());
    assert_eq!(
        report.gap_sites_resolved, 2,
        "both callback values resolved"
    );
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(e1)),
        "the mov-chained callback body ran: {:?}",
        report.hits
    );
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(e2)),
        "the phi's second closure body ran: {:?}",
        report.hits
    );
}

/// The callback as a pooled `Const::MethodRef`: the trace's LoadConst
/// arm resolves it statically.
#[test]
fn gap_callback_through_methodref_const() {
    let mut m = mk_module();
    let (cb, e) = cb_print(&mut m, "cb");
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let mr = load_method_ref(&mut m, entry, cb);
    foreach_site(&mut m, entry, p, mr);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = run_taint(&m, &builtin_config());
    assert_eq!(report.gap_sites_resolved, 1);
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(e)),
        "the MethodRef callback body ran: {:?}",
        report.hits
    );
}

/// A callback value whose points-to set is a NON-closure site (a plain
/// object alloc through a Mov): the site mapping yields nothing and the
// site counts as an unresolved callback (not a non-callback — the
/// object may carry a `call` method, unproven).
#[test]
fn gap_callback_nonclosure_site_is_unresolved() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let o = alloc_object(&mut m, entry);
    let moved = emit(&mut m, entry, Op::Mov { src: o });
    foreach_site(&mut m, entry, p, moved);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = run_taint(&m, &builtin_config());
    assert_eq!(report.gap_sites_resolved, 0);
    assert_eq!(
        report.gap_sites_unresolved, 1,
        "the object-typed callback value is the honest fallback"
    );
}

/// A mov-CYCLE callback value: the trace's cycle guard cuts (no funcs),
/// and the not-a-callback walk's cycle arm answers true (a cycle has no
/// callable leaf) — the site is NEITHER resolved NOR unresolved.
#[test]
fn gap_callback_mov_cycle_is_neither() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // v1 = mov v2; v2 = mov v1 (the cycle).
    let v1 = ValueId::new(m.values.len() as u32);
    let v2 = ValueId::new(m.values.len() as u32 + 1);
    let m1 = push_inst(&mut m, entry, Op::Mov { src: v2 });
    m.values.push(abcd_ir::Value {
        def: ValueDef::Inst(m1),
        ty: abcd_ir::Ty::Any,
    });
    m.inst_mut(m1).unwrap().result = Some(v1);
    let m2 = push_inst(&mut m, entry, Op::Mov { src: v1 });
    m.values.push(abcd_ir::Value {
        def: ValueDef::Inst(m2),
        ty: abcd_ir::Ty::Any,
    });
    m.inst_mut(m2).unwrap().result = Some(v2);
    foreach_site(&mut m, entry, p, v1);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = run_taint(&m, &builtin_config());
    assert_eq!(
        (report.gap_sites_resolved, report.gap_sites_unresolved),
        (0, 0),
        "a cycle is not a callback site at all"
    );
}

/// A dangling callback value id: the trace skips it (no funcs) and the
/// not-a-callback walk answers false (unknown) — the honest fallback.
#[test]
fn gap_callback_dangling_value_is_unresolved() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    foreach_site(&mut m, entry, p, ValueId::new(9999));
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = run_taint(&m, &builtin_config());
    assert_eq!(
        (report.gap_sites_resolved, report.gap_sites_unresolved),
        (0, 1),
        "a dangling callback value is the honest fallback"
    );
}

/// The not-a-callback refinement: const-defined leaves (a direct
/// `ValueDef::Const`, a phi of two, a mov of a LoadConst) are NOT
/// callback sites — never counted unresolved.
#[test]
fn gap_const_callback_slots_are_not_sites() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // (a) a const-defined string (no instruction).
    let xs = intern(&mut m, "x");
    let cv = const_value(&mut m, Const::String(xs));
    foreach_site(&mut m, entry, p, cv);
    // (b) a phi of two const-defined values.
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
    let c1 = const_value(&mut m, Const::Bool(true));
    let c2 = const_value(&mut m, Const::Bool(false));
    emit_void(&mut m, t, Op::Branch { dest: join });
    emit_void(&mut m, els, Op::Branch { dest: join });
    link(&mut m, entry, t);
    link(&mut m, entry, els);
    link(&mut m, t, join);
    link(&mut m, els, join);
    let phiced = emit(
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
                        from: els,
                        kind: EdgeKind::Normal,
                    },
                    c2,
                ),
            ],
        },
    );
    foreach_site(&mut m, join, p, phiced);
    // (c) a mov of a LoadConst.
    let s = load_string(&mut m, join, "x");
    let moved = emit(&mut m, join, Op::Mov { src: s });
    foreach_site(&mut m, join, p, moved);
    emit_void(&mut m, join, Op::Return { value: None });

    let report = run_taint(&m, &builtin_config());
    assert_eq!(
        (report.gap_sites_resolved, report.gap_sites_unresolved),
        (0, 0),
        "constant callback slots are not callback sites"
    );
}

/// The GapCallGraph merge dedup: the callback body is ALSO a
/// base-graph callee of the same call site (a phi callee mixing the
/// summary-named function and the callback) — the merge skips the
/// duplicate on both the callees and callers sides.
#[test]
fn gap_edges_dedup_against_base_graph() {
    let mut m = mk_module();
    let (cb, e) = cb_print(&mut m, "cb");
    // each(x, cb) { print(x); } — a real body named like the summary.
    let each = add_func_named(&mut m, "each");
    m.func_mut(each).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    let xp;
    {
        let b = entry_of(&m, each);
        add_param(&mut m, each, 0);
        add_param(&mut m, each, 1);
        add_param(&mut m, each, 2);
        xp = add_param(&mut m, each, 3);
        add_param(&mut m, each, 4);
        print_call(&mut m, b, vec![xp]);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let els = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p,
            true_dest: t,
            false_dest: els,
        },
    );
    let mr_each = load_method_ref(&mut m, t, each);
    emit_void(&mut m, t, Op::Branch { dest: join });
    let mr_cb = load_method_ref(&mut m, els, cb);
    emit_void(&mut m, els, Op::Branch { dest: join });
    link(&mut m, entry, t);
    link(&mut m, entry, els);
    link(&mut m, t, join);
    link(&mut m, els, join);
    // The callee phi resolves to BOTH bodies; the summary's callback is
    // also cb — the gap edge duplicates a base edge.
    let callee = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    mr_each,
                ),
                (
                    Edge {
                        from: els,
                        kind: EdgeKind::Normal,
                    },
                    mr_cb,
                ),
            ],
        },
    );
    let clo_cb = closure_of(&mut m, join, cb);
    push_inst(
        &mut m,
        join,
        Op::Call {
            callee,
            this: None,
            args: vec![p, clo_cb],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, join, Op::Return { value: None });

    let mut config = std_config();
    config.extra_summaries.push((
        "each".to_owned(),
        None,
        abcd_taint::Summary::new("gap at param 1")
            .callback(1)
            .gap_enter(abcd_taint::Endpoint::Param(0), 0),
    ));
    let report = run_taint(&m, &config);
    assert_eq!(report.gap_sites_resolved, 1);
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(e)),
        "the (deduplicated) gap edge still entered the callback: {:?}",
        report.hits
    );
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(xp)),
        "the base callee edge ran the body: {:?}",
        report.hits
    );
}

/// Name resolution through a Mov chain: `console.log` where the callee
/// is `mov(loadprop(console, log))` — the Mov arm of both the candidate
// walk and the base walk.
#[test]
fn names_mov_chained_callee() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let g = try_get_global(&mut m, entry, "console");
    let log = intern(&mut m, "log");
    let lp = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: g,
            name: log,
        },
    );
    let moved = emit(&mut m, entry, Op::Mov { src: lp });
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: moved,
            this: None,
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let config = TaintConfig {
        sinks: vec![SinkSpec::Call {
            name: "console.log".to_owned(),
        }],
        ..std_config()
    };
    let report = run_taint(&m, &config);
    assert_eq!(
        report.hits.len(),
        1,
        "the mov-chained qualified name matched: {:?}",
        report.hits
    );
    assert_eq!(report.hits[0].position, "arg 0");
}

/// Name/base/leaf resolution through a phi of two property loads and
// the loop-rotated callee phi (the for-of `next` shape: the phi merges
// the pre-loop load with itself — the find_map skips the cycle entry).
#[test]
fn names_phi_and_loop_rotated_callees() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // (a) A phi of `ga.f` and `gb.f`.
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
    let ga = try_get_global(&mut m, t, "ga");
    let leaf = intern(&mut m, "f");
    let la = emit(
        &mut m,
        t,
        Op::LoadProp {
            object: ga,
            name: leaf,
        },
    );
    emit_void(&mut m, t, Op::Branch { dest: join });
    let gb = try_get_global(&mut m, els, "gb");
    let lb = emit(
        &mut m,
        els,
        Op::LoadProp {
            object: gb,
            name: leaf,
        },
    );
    emit_void(&mut m, els, Op::Branch { dest: join });
    link(&mut m, entry, t);
    link(&mut m, entry, els);
    link(&mut m, t, join);
    link(&mut m, els, join);
    let phiced = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    la,
                ),
                (
                    Edge {
                        from: els,
                        kind: EdgeKind::Normal,
                    },
                    lb,
                ),
            ],
        },
    );
    push_inst(
        &mut m,
        join,
        Op::Call {
            callee: phiced,
            this: None,
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    // (b) The loop-rotated callee: head's phi merges the pre-header
    // `it.next` load with the phi itself (self entry first).
    let it = try_get_global(&mut m, join, "it");
    let next = intern(&mut m, "next");
    let lp = emit(
        &mut m,
        join,
        Op::LoadProp {
            object: it,
            name: next,
        },
    );
    let head = add_block(&mut m, f);
    let latch = add_block(&mut m, f);
    emit_void(&mut m, join, Op::Branch { dest: head });
    link(&mut m, join, head);
    let phi_val = ValueId::new(m.values.len() as u32);
    let rot = emit(
        &mut m,
        head,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: latch,
                        kind: EdgeKind::Normal,
                    },
                    phi_val,
                ),
                (
                    Edge {
                        from: join,
                        kind: EdgeKind::Normal,
                    },
                    lp,
                ),
            ],
        },
    );
    assert_eq!(rot, phi_val);
    push_inst(
        &mut m,
        head,
        Op::Call {
            callee: rot,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, head, Op::Branch { dest: latch });
    link(&mut m, head, latch);
    emit_void(&mut m, latch, Op::Return { value: None });

    let config = TaintConfig {
        sources: vec![
            SourceSpec::GlobalLoad {
                name: "it".to_owned(),
            },
            SourceSpec::FunctionParams {
                name: "func_main_0".to_owned(),
                params: None,
            },
        ],
        sinks: vec![
            SinkSpec::Call {
                name: "gb.f".to_owned(),
            },
            SinkSpec::Call {
                name: "it.next".to_owned(),
            },
        ],
        ..std_config()
    };
    let report = run_taint(&m, &config);
    assert!(
        report
            .hits
            .iter()
            .any(|h| h.sink == "gb.f" && h.position == "arg 0"),
        "the phi-callee's qualified name matched: {:?}",
        report.hits
    );
    assert!(
        report
            .hits
            .iter()
            .any(|h| h.sink == "it.next" && h.position == "base"),
        "the loop-rotated callee found its base through the cycle: {:?}",
        report.hits
    );
}

/// The name-walk guards: a dangling callee value (all three walks
// answer None/empty), a `LoadConst(MethodRef)` callee's name, a bare
// `DefineFunc` callee's name, and the push_unique dedup/empty guards.
#[test]
fn names_guards_and_const_callee_names() {
    let mut m = mk_module();
    // The two named callee bodies (empty — the hits land on the calls).
    let mut named = Vec::new();
    for name in ["via_ref", "via_def"] {
        let g = add_func_named(&mut m, name);
        named.push(g);
        let b = entry_of(&m, g);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    // Each call gets its OWN tainted param: a resolved body-step call
    // kills its operand's fact downstream (killIncomingTaint).
    let p_a = add_param(&mut m, f, 1);
    let p_b = add_param(&mut m, f, 2);
    let p_c = add_param(&mut m, f, 3);
    let p_d = add_param(&mut m, f, 4);
    // (a) A dangling callee value.
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: ValueId::new(9999),
            this: None,
            args: vec![p_a],
            kind: CallKind::Dynamic,
        },
    );
    // (b) A MethodRef-const callee.
    let mr = load_method_ref(&mut m, entry, named[0]);
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: mr,
            this: None,
            args: vec![p_b],
            kind: CallKind::Dynamic,
        },
    );
    // (c) A bare DefineFunc callee (no AllocClosure wrapper).
    let def = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: named[1],
            captures: vec![],
            length: 1,
        },
    );
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: def,
            this: None,
            args: vec![p_c],
            kind: CallKind::Dynamic,
        },
    );
    // (d) The push_unique guards: a phi of two loads of the SAME name,
    // plus an empty-named global.
    let g1 = try_get_global(&mut m, entry, "dd");
    let g2 = try_get_global(&mut m, entry, "dd");
    let t = add_block(&mut m, f);
    let els = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p_d,
            true_dest: t,
            false_dest: els,
        },
    );
    emit_void(&mut m, t, Op::Branch { dest: join });
    emit_void(&mut m, els, Op::Branch { dest: join });
    link(&mut m, entry, t);
    link(&mut m, entry, els);
    link(&mut m, t, join);
    link(&mut m, els, join);
    let phiced = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    g1,
                ),
                (
                    Edge {
                        from: els,
                        kind: EdgeKind::Normal,
                    },
                    g2,
                ),
            ],
        },
    );
    push_inst(
        &mut m,
        join,
        Op::Call {
            callee: phiced,
            this: None,
            args: vec![p_d],
            kind: CallKind::Dynamic,
        },
    );
    let empty_named = try_get_global(&mut m, join, "");
    push_inst(
        &mut m,
        join,
        Op::Call {
            callee: empty_named,
            this: None,
            args: vec![p_d],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, join, Op::Return { value: None });

    let config = TaintConfig {
        sinks: vec![
            SinkSpec::Call {
                name: "via_ref".to_owned(),
            },
            SinkSpec::Call {
                name: "via_def".to_owned(),
            },
            SinkSpec::Call {
                name: "dd".to_owned(),
            },
        ],
        ..std_config()
    };
    let report = run_taint(&m, &config);
    let sinks: Vec<&str> = report.hits.iter().map(|h| h.sink.as_str()).collect();
    assert!(sinks.contains(&"via_ref"), "the MethodRef name: {sinks:?}");
    assert!(sinks.contains(&"via_def"), "the DefineFunc name: {sinks:?}");
    assert!(
        sinks.iter().filter(|s| **s == "dd").count() == 1,
        "the duplicate name deduped: {sinks:?}"
    );
    assert!(
        !sinks.contains(&""),
        "the empty name never registers: {sinks:?}"
    );
}
