//! Flow-rule arm coverage (c-COV W10): the `problem.rs` arms no corpus
//! fixture exercises — the store-rule kill/wildcard/re-key arms, the
//! summary endpoint match/substitute arms (all mismatch families), the
//! object-family ops (CopyDataProps/SetObjectWithProto/StorePrivate/
//! DefinePrivate/DefineMethod), the DefineFunc capture channel, the
//! call-binding arms (params < implicit slots, the precise this-slot,
//! Apply spreading, SuperForwardAllArgs), the fresh-result-site arms,
//! and the gap-propagator arms driven directly (absent callback arg,
//! non-gap callee at a gap site, OverApproxAll gap enter, OverApproxAll
//! mini-gap). Exact hit/fact asserts throughout.

mod common;

use abcd_ir::{CallKind, Op};
use abcd_taint::driver::{run_taint, run_taint_full};
use abcd_taint::fact::{Fact, TaintBase};
use abcd_taint::summary::{Endpoint, Summary};
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

/// The store rule's kill arms: a state-base fact at a strong store is
/// never killed (`_ => false`); a strong store through a wildcard key
/// kills the matching field fact.
#[test]
fn store_rule_state_base_survives_and_wildcard_kills() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // A state-base fact (Global) live at a strong store.
    let g = intern(&mut m, "G");
    emit_void(&mut m, entry, Op::StoreGlobal { name: g, value: p });
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
    // Read the field back BEFORE the kill (the hit witnesses the flow).
    let early = emit(&mut m, entry, Op::LoadProp { object: o, name: k });
    print_call(&mut m, entry, vec![early]);
    // The strong store through a wildcard key kills `Heap(o).[k]`.
    let i = load_number(&mut m, entry, 0.0);
    let clean = load_string(&mut m, entry, "clean");
    emit_void(
        &mut m,
        entry,
        Op::StorePropIdx {
            object: o,
            index: i,
            value: clean,
        },
    );
    let late = emit(&mut m, entry, Op::LoadProp { object: o, name: k });
    print_call(&mut m, entry, vec![late]);
    // A result-less load of a tainted base (the no-result guard).
    push_inst(&mut m, entry, Op::LoadProp { object: p, name: k });
    // The Global fact survived the strong stores: read it back.
    let g2 = try_get_global(&mut m, entry, "G");
    print_call(&mut m, entry, vec![g2]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = run_taint(&m, &std_config());
    assert!(
        report
            .hits
            .iter()
            .any(|h| h.fact.local_base() == Some(early)),
        "the pre-kill read hits: {:?}",
        report.hits
    );
    assert!(
        !report
            .hits
            .iter()
            .any(|h| h.fact.local_base() == Some(late)),
        "the wildcard strong kill eliminated the field fact: {:?}",
        report.hits
    );
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(g2)),
        "the state-base fact survived the strong store: {:?}",
        report.hits
    );
}

/// The store rule's rung-0/imprecise re-key with a NON-EMPTY field
/// chain: `o.f2 = a1` where `a1 = p.f1` keys `Heap(sites(o)).[f2, f1]`
/// and reads back through both cuts.
#[test]
fn store_rekey_appends_the_value_chain() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let f1 = intern(&mut m, "f1");
    let f2 = intern(&mut m, "f2");
    let a1 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: p,
            name: f1,
        },
    );
    // The store base is a global load — imprecise at every rung, so the
    // baseline (rung-0) re-key runs even at rung 2.
    let o = try_get_global(&mut m, entry, "o");
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: o,
            name: f2,
            value: a1,
        },
    );
    let t = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: o,
            name: f2,
        },
    );
    let u = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: t,
            name: f1,
        },
    );
    print_call(&mut m, entry, vec![u]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let (report, result) = run_taint_full(&m, &std_config());
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(u)),
        "the two-key chain reads back: {:?}",
        report.hits
    );
    // The re-keyed heap fact carried both keys.
    assert!(
        result.path_edges().iter().any(|e| {
            matches!(&e.target_fact, Fact::Taint(t)
                if matches!(t.base, TaintBase::Heap(_)) && t.fields.len() == 2)
        }),
        "a two-element heap chain existed"
    );
}

/// The summary ENDPOINT match arms: `Base` at a base-less call, the
/// chain-too-short and named-mismatch guards, and the leftover loop
/// (an empty `Field([])` path passes the whole chain through).
#[test]
fn summary_endpoint_match_arms() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // (a) A bare-global call (no base): the Base flow never matches.
    let clean = try_get_global(&mut m, entry, "clean");
    let r1 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: clean,
            this: None,
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![r1]);
    // A receiver carrying a one-element chain: w2.y = (p.z); recv = w2.y
    // gives Local(recv, [z]).
    let z = intern(&mut m, "z");
    let y = intern(&mut m, "y");
    let a1 = emit(&mut m, entry, Op::LoadProp { object: p, name: z });
    let w2 = try_get_global(&mut m, entry, "w2");
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: w2,
            name: y,
            value: a1,
        },
    );
    let recv = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: w2,
            name: y,
        },
    );
    // (b) `m()` with `this = recv`: Field([x]) mismatches the [z] chain,
    // Field([x, y]) is longer than the chain, Field([z]) matches.
    let mv = try_get_global(&mut m, entry, "m");
    let r2 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: mv,
            this: Some(recv),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![r2]);
    // (c) `m2()` with `this = recv2` (same chain): the empty Field([])
    // path passes [z] through as the leftover.
    let recv2 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: w2,
            name: y,
        },
    );
    let m2v = try_get_global(&mut m, entry, "m2");
    let r3 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: m2v,
            this: Some(recv2),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![r3]);
    emit_void(&mut m, entry, Op::Return { value: None });

    // Build the field chains against the MODULE's symbol table.
    let fx = m.sym.intern("x");
    let fy = m.sym.intern("y");
    let fz = m.sym.intern("z");
    let fc = |keys: &[abcd_ir::Sym]| {
        let mut c = abcd_analysis::dataflow::heap::FieldChain::new();
        for &k in keys {
            c = c.pushed(
                abcd_analysis::dataflow::heap::FieldKey::Named(k),
                abcd_analysis::dataflow::heap::DEFAULT_MAX_FIELD_CHAIN,
            );
        }
        c
    };
    let mut config = std_config();
    config.extra_summaries = vec![
        (
            "clean".to_owned(),
            None,
            Summary::new("base never matches at a bare call")
                .flow(Endpoint::Base, Endpoint::Return)
                .flow(Endpoint::Param(0), Endpoint::Return),
        ),
        (
            "m".to_owned(),
            None,
            Summary::new("mismatch + too-long guards, then the match")
                .flow(Endpoint::Field(fc(&[fx])), Endpoint::Return)
                .flow(Endpoint::Field(fc(&[fx, fy])), Endpoint::Param(0))
                .flow(Endpoint::Field(fc(&[fz])), Endpoint::Return),
        ),
        (
            "m2".to_owned(),
            None,
            Summary::new("empty path passes the chain through")
                .flow(Endpoint::Field(fc(&[])), Endpoint::Return),
        ),
    ];
    let report = run_taint(&m, &config);
    // (a): the Param flow fired, the Base flow could not (no base).
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(r1)),
        "the param flow fired: {:?}",
        report.hits
    );
    // (b): exactly one fact reaches r2 — the [z] match with empty
    // leftover.
    let r2_hits: Vec<_> = report
        .hits
        .iter()
        .filter(|h| h.fact.local_base() == Some(r2))
        .collect();
    assert_eq!(r2_hits.len(), 1, "only the [z] flow fired: {:?}", r2_hits);
    assert!(r2_hits[0].fact.fields.is_empty());
    // (c): the empty path appended the whole [z] chain.
    let r3_hits: Vec<_> = report
        .hits
        .iter()
        .filter(|h| h.fact.local_base() == Some(r3))
        .collect();
    assert_eq!(r3_hits.len(), 1, "{:?}", report.hits);
    assert_eq!(r3_hits[0].fact.fields.len(), 1, "the leftover chain");
}

/// The heap-sourced endpoint match arms: a `Heap(sites).[z, w]` fact
/// against `Field` endpoints — the named mismatch, the too-short chain,
/// and the match whose leftover re-keys onto the target's precise sites
/// (the `value_key` heap arm). Plus the empty-site heap fact's early
// bail and the Base target.
#[test]
fn summary_heap_endpoint_and_substitute_arms() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let zz = intern(&mut m, "z");
    let ww = intern(&mut m, "w");
    // Heap(site_o).[z, w]: store o.z = a1 where a1 = p.w.
    let a1 = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: p,
            name: ww,
        },
    );
    let o = alloc_object(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: o,
            name: zz,
            value: a1,
        },
    );
    // An empty-site heap fact (a store through a global base).
    let u = try_get_global(&mut m, entry, "u");
    let kk = intern(&mut m, "k");
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: u,
            name: kk,
            value: p,
        },
    );
    // The call: `set(v)` with `this = o`, v a precise alloc.
    let v = alloc_object(&mut m, entry);
    let sv = try_get_global(&mut m, entry, "set");
    let r_set = emit(
        &mut m,
        entry,
        Op::Call {
            callee: sv,
            this: Some(o),
            args: vec![v],
            kind: CallKind::Dynamic,
        },
    );
    print_call(&mut m, entry, vec![r_set]);
    // Read back: v.w must be tainted (the leftover re-keyed onto v's
    // site); v.x must not.
    let vw = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: v,
            name: ww,
        },
    );
    print_call(&mut m, entry, vec![vw]);
    let xname = intern(&mut m, "x");
    let vx = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: v,
            name: xname,
        },
    );
    print_call(&mut m, entry, vec![vx]);
    // The Base target: `touch()` with this = p (the tainted param).
    let tv = try_get_global(&mut m, entry, "touch");
    emit(
        &mut m,
        entry,
        Op::Call {
            callee: tv,
            this: Some(p),
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let fx = m.sym.intern("x");
    let fz = m.sym.intern("z");
    let fw = m.sym.intern("w");
    let fq = m.sym.intern("q");
    let fc = |keys: &[abcd_ir::Sym]| {
        let mut c = abcd_analysis::dataflow::heap::FieldChain::new();
        for &k in keys {
            c = c.pushed(
                abcd_analysis::dataflow::heap::FieldKey::Named(k),
                abcd_analysis::dataflow::heap::DEFAULT_MAX_FIELD_CHAIN,
            );
        }
        c
    };
    let mut config = std_config();
    config.extra_summaries = vec![
        (
            "set".to_owned(),
            None,
            Summary::new("heap endpoint arms")
                .flow(Endpoint::Field(fc(&[fx])), Endpoint::Param(0))
                .flow(Endpoint::Field(fc(&[fz])), Endpoint::Param(0))
                .flow(Endpoint::Field(fc(&[fz])), Endpoint::ReturnField(fc(&[fq])))
                .flow(Endpoint::Field(fc(&[fz, fw, fq])), Endpoint::Param(0)),
        ),
        (
            "touch".to_owned(),
            None,
            Summary::new("base target").flow(Endpoint::Base, Endpoint::Base),
        ),
    ];
    let report = run_taint(&m, &config);
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(vw)),
        "the [z] match re-keyed the [w] leftover onto v's site: {:?}",
        report.hits
    );
    assert!(
        !report.hits.iter().any(|h| h.fact.local_base() == Some(vx)),
        "the named mismatch never fired: {:?}",
        report.hits
    );
    // The ReturnField flow appended the [w] leftover below its [q] path.
    let r_hits: Vec<_> = report
        .hits
        .iter()
        .filter(|h| h.fact.local_base() == Some(r_set))
        .collect();
    assert_eq!(
        r_hits.len(),
        1,
        "the ReturnField flow fired once: {:?}",
        r_hits
    );
    assert_eq!(r_hits[0].fact.fields.len(), 2, "path ++ leftover");
    assert!(
        report.summaries_applied.iter().any(|(_, n)| n == "touch"),
        "the Base→Base flow applied"
    );
}

/// The object-family ops: CopyDataProps (src taint copies to dst),
/// SetObjectWithProto (proto taint tags obj's dynamic channel),
/// StorePrivate/DefinePrivate (unknown vs precise obj sites), and
/// DefineMethod fed by a capture-tainted closure (the DefineFunc
/// capture arm).
#[test]
fn object_family_ops() {
    let mut m = mk_module();
    // The method body for the DefineFunc capture.
    let meth = add_func_named(&mut m, "meth");
    {
        let b = entry_of(&m, meth);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // CopyDataProps.
    let dst = alloc_object(&mut m, entry);
    emit_void(&mut m, entry, Op::CopyDataProps { dst, src: p });
    print_call(&mut m, entry, vec![dst]);
    // SetObjectWithProto: proto taint tags obj.[AnyDynamic].
    let obj = alloc_object(&mut m, entry);
    emit_void(&mut m, entry, Op::SetObjectWithProto { proto: p, obj });
    let kk = intern(&mut m, "k");
    let x = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: obj,
            name: kk,
        },
    );
    print_call(&mut m, entry, vec![x]);
    // StorePrivate into an unknown-site obj, StorePrivate + DefinePrivate
    // into precise ones.
    let uo = try_get_global(&mut m, entry, "uo");
    emit_void(
        &mut m,
        entry,
        Op::StorePrivate {
            level: 0,
            slot: 1,
            obj: uo,
            value: p,
        },
    );
    let o2 = alloc_object(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::StorePrivate {
            level: 0,
            slot: 2,
            obj: o2,
            value: p,
        },
    );
    let o3 = alloc_object(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::DefinePrivate {
            level: 0,
            slot: 3,
            obj: o3,
            value: p,
        },
    );
    // DefineMethod over a capture-tainted closure value.
    let cap = intern(&mut m, "c");
    let def = emit(
        &mut m,
        entry,
        Op::DefineFunc {
            body: meth,
            captures: vec![(cap, p)],
            length: 0,
        },
    );
    let o4 = alloc_object(&mut m, entry);
    let mname = intern(&mut m, "m");
    emit(
        &mut m,
        entry,
        Op::DefineMethod {
            object: o4,
            name: mname,
            func: def,
            length: 0,
        },
    );
    let r = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: o4,
            name: mname,
        },
    );
    print_call(&mut m, entry, vec![r]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let (report, result) = run_taint_full(&m, &std_config());
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(dst)),
        "CopyDataProps copied the taint: {:?}",
        report.hits
    );
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(x)),
        "the proto-linked object reads tainted: {:?}",
        report.hits
    );
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(r)),
        "the method table entry reads tainted (capture → method): {:?}",
        report.hits
    );
    // The private-channel facts, exactly.
    let has_fact = |pred: &dyn Fn(&TaintBase, usize) -> bool| {
        result
            .path_edges()
            .iter()
            .any(|e| matches!(&e.target_fact, Fact::Taint(t) if pred(&t.base, t.fields.len())))
    };
    assert!(
        has_fact(&|b, n| *b == TaintBase::Local(uo) && n == 1),
        "the unknown-site private store tagged the local"
    );
    let site_of = |v: abcd_ir::ValueId| match m.value(v).unwrap().def {
        abcd_ir::ValueDef::Inst(i) => i,
        _ => panic!("inst-defined"),
    };
    assert!(
        has_fact(&|b, n| matches!(b, TaintBase::Heap(s) if s.iter().eq([site_of(o2)]) && n == 1)),
        "the precise private store keyed the site"
    );
    assert!(
        has_fact(&|b, n| matches!(b, TaintBase::Heap(s) if s.iter().eq([site_of(o3)]) && n == 1)),
        "the precise private define keyed the site"
    );
}

/// Call binding arms: a callee with fewer params than its implicit
/// slots over-approximates; the precise this-slot binds; Apply spreads
/// the tainted argument array over every formal; SuperForwardAllArgs
/// binds nothing (the documented rung-0 gap).
#[test]
fn call_binding_arms() {
    // (a) params < implicit slots → OverApproxAll (every param tainted).
    let mut m = mk_module();
    let wee = add_func_named(&mut m, "wee");
    m.func_mut(wee).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    {
        let b = entry_of(&m, wee);
        let only = add_param(&mut m, wee, 0); // 1 param < 3 implicit
        print_call(&mut m, b, vec![only]);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let wv = load_method_ref(&mut m, entry, wee);
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
    assert_eq!(
        report.hits.len(),
        1,
        "the over-approx bound the tainted arg to the only param: {:?}",
        report.hits
    );

    // (b) The precise this-slot: `this` → params[2] under the 0xF
    // default; the formal stays clean.
    let mut m = mk_module();
    let g = add_func_named(&mut m, "g");
    m.func_mut(g).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    {
        let b = entry_of(&m, g);
        add_param(&mut m, g, 0);
        add_param(&mut m, g, 1);
        let this_slot = add_param(&mut m, g, 2);
        let formal = add_param(&mut m, g, 3);
        print_call(&mut m, b, vec![this_slot]);
        print_call(&mut m, b, vec![formal]);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let clean = load_string(&mut m, entry, "clean");
    let gv = load_method_ref(&mut m, entry, g);
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: gv,
            this: Some(p),
            args: vec![clean],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });
    let report = run_taint(&m, &std_config());
    assert_eq!(
        report.hits.len(),
        1,
        "only the this slot is tainted: {:?}",
        report.hits
    );

    // (c) Apply: the tainted argument array taints every formal.
    let mut m = mk_module();
    let g = add_func_named(&mut m, "g");
    m.func_mut(g).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    let (f0, f1);
    {
        let b = entry_of(&m, g);
        add_param(&mut m, g, 0);
        add_param(&mut m, g, 1);
        add_param(&mut m, g, 2);
        f0 = add_param(&mut m, g, 3);
        f1 = add_param(&mut m, g, 4);
        print_call(&mut m, b, vec![f0]);
        print_call(&mut m, b, vec![f1]);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let gv = load_method_ref(&mut m, entry, g);
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: gv,
            this: None,
            args: vec![p],
            kind: CallKind::Apply,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });
    let report = run_taint(&m, &std_config());
    let bases: Vec<_> = report
        .hits
        .iter()
        .filter_map(|h| h.fact.local_base())
        .collect();
    assert!(
        bases.contains(&f0) && bases.contains(&f1),
        "the tainted array spread over both formals: {:?}",
        report.hits
    );

    // (d) SuperForwardAllArgs: the caller's own formals are forwarded —
    // the call's operands bind NOTHING (the documented gap).
    let mut m = mk_module();
    let g = add_func_named(&mut m, "g");
    m.func_mut(g).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    {
        let b = entry_of(&m, g);
        add_param(&mut m, g, 0);
        add_param(&mut m, g, 1);
        add_param(&mut m, g, 2);
        let f0 = add_param(&mut m, g, 3);
        print_call(&mut m, b, vec![f0]);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let gv = load_method_ref(&mut m, entry, g);
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: gv,
            this: None,
            args: vec![p],
            kind: CallKind::SuperForwardAllArgs,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });
    let report = run_taint(&m, &std_config());
    assert!(
        report.hits.is_empty(),
        "nothing binds across SuperForwardAllArgs (documented gap): {:?}",
        report.hits
    );
}

/// The `fresh_result_site` arms: a param (non-Inst def) and a
// body-step call result (non-summary site) fall back to the
// unknown-base wildcard; a summary call result with no Return inflow
// keys by its call site (the e13 mechanism) and does NOT may-alias
// the source array's heap fact.
#[test]
fn fresh_result_site_arms() {
    let mut m = mk_module();
    // identity(v) { return v; } — a body-step call.
    let id = add_func_named(&mut m, "identity");
    m.func_mut(id).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    {
        let b = entry_of(&m, id);
        add_param(&mut m, id, 0);
        add_param(&mut m, id, 1);
        add_param(&mut m, id, 2);
        let v = add_param(&mut m, id, 3);
        emit_void(&mut m, b, Op::Return { value: Some(v) });
    }
    // helper(o) { x = o.k; print(x); r = identity(o); y = r.k;
    // print(y); } — a param receiver (non-Inst) and a body-step call
    // result both wildcard-match the live heap fact.
    let helper = add_func_named(&mut m, "helper");
    m.func_mut(helper).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    {
        let b = entry_of(&m, helper);
        add_param(&mut m, helper, 0);
        add_param(&mut m, helper, 1);
        add_param(&mut m, helper, 2);
        let o = add_param(&mut m, helper, 3);
        let k = intern(&mut m, "k");
        let x = emit(&mut m, b, Op::LoadProp { object: o, name: k });
        print_call(&mut m, b, vec![x]);
        let idv = load_method_ref(&mut m, b, id);
        let r = emit(
            &mut m,
            b,
            Op::Call {
                callee: idv,
                this: None,
                args: vec![o],
                kind: CallKind::Direct,
            },
        );
        let y = emit(&mut m, b, Op::LoadProp { object: r, name: k });
        print_call(&mut m, b, vec![y]);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let a = alloc_object(&mut m, entry);
    let k = intern(&mut m, "k");
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: a,
            name: k,
            value: p,
        },
    );
    // The fresh container: `mk()` (a summary with NO flows) then
    // `mk().k` — the call-site key does NOT may-alias the array's fact.
    let mkv = try_get_global(&mut m, entry, "mk");
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: mkv,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let z = emit(&mut m, entry, Op::LoadProp { object: r, name: k });
    print_call(&mut m, entry, vec![z]);
    // A second load through the same fresh value (the memo hit).
    let z2 = emit(&mut m, entry, Op::LoadProp { object: r, name: k });
    print_call(&mut m, entry, vec![z2]);
    // Drive the helper with an UNKNOWN-base argument (a global load):
    // its param's sites stay empty, so both loads wildcard-match.
    let hv = load_method_ref(&mut m, entry, helper);
    let uo = try_get_global(&mut m, entry, "uo");
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: hv,
            this: None,
            args: vec![uo],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let mut config = std_config();
    config
        .extra_summaries
        .push(("mk".to_owned(), Some(0), Summary::new("fresh container")));
    let report = run_taint(&m, &config);
    // helper's two loads both wildcard-matched the array's heap fact.
    let helper_hits = report.hits.iter().filter(|h| h.sink == "print").count();
    assert!(
        helper_hits >= 2,
        "the param and the body-step result both wildcard-match: {:?}",
        report.hits
    );
    // The fresh result does NOT may-alias the array's heap fact.
    assert!(
        !report.hits.iter().any(|h| h.fact.local_base() == Some(z)),
        "the fresh container stays clean (e13): {:?}",
        report.hits
    );
    assert!(
        !report.hits.iter().any(|h| h.fact.local_base() == Some(z2)),
        "the memoized fresh answer stays clean: {:?}",
        report.hits
    );
}

/// The gap-propagator arms: a callback argument absent entirely (the
// unresolved counter), a resolved non-gap callee at a gap site (the
// `gap_at` miss), an OverApproxAll gap enter, and an OverApproxAll
// mini-gap direct call.
#[test]
fn gap_absent_callback_arg_is_unresolved() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // each(p) — the summary declares a callback gap at param 1, but the
    // call passes only one argument.
    let ev = try_get_global(&mut m, entry, "each");
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: ev,
            this: None,
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let mut config = std_config();
    config.extra_summaries.push((
        "each".to_owned(),
        None,
        Summary::new("gap at param 1")
            .callback(1)
            .gap_enter(Endpoint::Param(0), 0),
    ));
    let report = run_taint(&m, &config);
    assert_eq!(report.gap_sites_resolved, 0);
    assert_eq!(
        report.gap_sites_unresolved, 1,
        "the absent callback argument is the honest fallback"
    );
}

/// A gap site whose base-resolved callee is NOT the callback body:
/// `gap_at` returns None for it (the call edge into the summary-named
/// user function survives as a normal body step).
#[test]
fn gap_site_with_real_callee_runs_both_edges() {
    let mut m = mk_module();
    // cb(e) { print(e); } — the user callback.
    let cb = add_func_named(&mut m, "cb");
    m.func_mut(cb).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    let e;
    {
        let b = entry_of(&m, cb);
        add_param(&mut m, cb, 0);
        add_param(&mut m, cb, 1);
        add_param(&mut m, cb, 2);
        e = add_param(&mut m, cb, 3);
        print_call(&mut m, b, vec![e]);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    // each(x, cb) { print(x); } — a REAL body named like the summary.
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
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let ev = load_method_ref(&mut m, entry, each);
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
            callee: ev,
            this: None,
            args: vec![p, clo_cb],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let mut config = std_config();
    config.extra_summaries.push((
        "each".to_owned(),
        None,
        Summary::new("gap at param 1")
            .callback(1)
            .gap_enter(Endpoint::Param(0), 0),
    ));
    let report = run_taint(&m, &config);
    assert_eq!(report.gap_sites_resolved, 1, "the callback resolved");
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(e)),
        "the gap edge seeded the callback's formal: {:?}",
        report.hits
    );
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(xp)),
        "the base callee edge ran the real body too (gap_at miss): {:?}",
        report.hits
    );
}

/// The gap enter's OverApproxAll arm: the callback has no reliable
/// frame-slot model (non-static, unannotated), so a matching enter rule
/// taints EVERY formal.
#[test]
fn gap_enter_overapprox_binds_all_formals() {
    let mut m = mk_module();
    // The callback is deliberately NON-static with no annotation.
    let cb = add_func_named(&mut m, "cb");
    let (p0, p1);
    {
        let b = entry_of(&m, cb);
        p0 = add_param(&mut m, cb, 0);
        p1 = add_param(&mut m, cb, 1);
        print_call(&mut m, b, vec![p0]);
        print_call(&mut m, b, vec![p1]);
        emit_void(&mut m, b, Op::Return { value: None });
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
    // a.forEach(cb) — the builtin's full gap (enter Field([AnyIndex])).
    let pop_name = intern(&mut m, "forEach");
    let callee = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: a,
            name: pop_name,
        },
    );
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee,
            this: Some(a),
            args: vec![clo_cb],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let config = TaintConfig {
        builtin_summaries: true,
        ..std_config()
    };
    let report = run_taint(&m, &config);
    assert_eq!(report.gap_sites_resolved, 1);
    let bases: Vec<_> = report
        .hits
        .iter()
        .filter_map(|h| h.fact.local_base())
        .collect();
    assert!(
        bases.contains(&p0) && bases.contains(&p1),
        "OverApproxAll seeded every formal: {:?}",
        report.hits
    );
}

/// The mini-gap tag over an OverApproxAll direct call: the tagged
/// callback value seeds every formal.
#[test]
fn mini_gap_tag_overapprox_direct_call() {
    let mut m = mk_module();
    // The callback is non-static (no slot model).
    let cb = add_func_named(&mut m, "cb");
    let cbp;
    {
        let b = entry_of(&m, cb);
        cbp = add_param(&mut m, cb, 0);
        print_call(&mut m, b, vec![cbp]);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // The receiver is a phi of an AllocArray and the tainted param (the
    // existing mini-gap test's shape): typed Array AND base-tainted.
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
                    abcd_ir::Edge {
                        from: t,
                        kind: abcd_ir::EdgeKind::Normal,
                    },
                    arr,
                ),
                (
                    abcd_ir::Edge {
                        from: els,
                        kind: abcd_ir::EdgeKind::Normal,
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
    // recv.tagit(cb) — the mini-gap summary tags the callback value.
    let tag = intern(&mut m, "tagit");
    let callee = emit(
        &mut m,
        join,
        Op::LoadProp {
            object: recv,
            name: tag,
        },
    );
    push_inst(
        &mut m,
        join,
        Op::Call {
            callee,
            this: Some(recv),
            args: vec![clo_cb],
            kind: CallKind::Dynamic,
        },
    );
    // The direct call of the tagged value.
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

    let mut config = TaintConfig {
        builtin_summaries: true,
        ..std_config()
    };
    config.extra_summaries.push((
        "Array.prototype.tagit".to_owned(),
        None,
        Summary::new("mini-gap only").callback(0),
    ));
    let report = run_taint(&m, &config);
    assert!(
        report.hits.iter().any(|h| h.fact.local_base() == Some(cbp)),
        "the tagged callback value seeded the formal at the direct call: {:?}",
        report.hits
    );
}

/// The miss-log hygiene arm: candidate names starting with `#` (es2abc
/// internal mangling) never enter the backlog log.
#[test]
fn hash_mangled_miss_names_are_not_logged() {
    let mut m = mk_module();
    // A directly-resolved function with an es2abc-mangled name.
    let weird = add_func_named(&mut m, "#*#internal");
    m.func_mut(weird).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    {
        let b = entry_of(&m, weird);
        add_param(&mut m, weird, 0);
        add_param(&mut m, weird, 1);
        add_param(&mut m, weird, 2);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let wv = load_method_ref(&mut m, entry, weird);
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
    assert!(
        !report.summary_misses.contains_key("#*#internal"),
        "the mangled name stayed out of the backlog: {:?}",
        report.summary_misses
    );
    assert_eq!(
        report.stats.sites_body_step, 1,
        "the site stepped into the body (the miss was NOT logged)"
    );
}

/// The remaining load/store arms: `LoadPropDyn` (computed-key read),
/// `StoreOwnPropName`, and `StoreOwnPropDyn` (the own-store family).
#[test]
fn dyn_load_and_own_store_arms() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let k = load_string(&mut m, entry, "k");
    // LoadPropDyn of a base-tainted param: the wildcard cut.
    let x = emit(&mut m, entry, Op::LoadPropDyn { object: p, key: k });
    print_call(&mut m, entry, vec![x]);
    // StoreOwnPropName: own-store re-keys into the heap and reads back.
    let o = alloc_object(&mut m, entry);
    let kk = intern(&mut m, "kk");
    emit_void(
        &mut m,
        entry,
        Op::StoreOwnPropName {
            object: o,
            name: kk,
            value: p,
        },
    );
    let y = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: o,
            name: kk,
        },
    );
    print_call(&mut m, entry, vec![y]);
    // StoreOwnPropDyn: the dynamic own-store.
    let o2 = alloc_object(&mut m, entry);
    let idx = load_number(&mut m, entry, 0.0);
    emit_void(
        &mut m,
        entry,
        Op::StoreOwnPropDyn {
            object: o2,
            key: idx,
            value: p,
        },
    );
    let z = emit(
        &mut m,
        entry,
        Op::LoadPropDyn {
            object: o2,
            key: idx,
        },
    );
    print_call(&mut m, entry, vec![z]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = run_taint(&m, &std_config());
    let bases: Vec<_> = report
        .hits
        .iter()
        .filter_map(|h| h.fact.local_base())
        .collect();
    assert!(bases.contains(&x), "the dyn load cut: {:?}", report.hits);
    assert!(
        bases.contains(&y),
        "the own-store name readback: {:?}",
        report.hits
    );
    assert!(
        bases.contains(&z),
        "the own-store dyn readback: {:?}",
        report.hits
    );
}

/// `seed_all_functions` skips bodyless (external) function records.
#[test]
fn seed_all_functions_skips_bodyless_records() {
    let mut m = mk_module();
    let _ext = add_external_func(&mut m, "native_ext");
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    print_call(&mut m, entry, vec![p]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = run_taint(&m, &std_config());
    assert_eq!(report.hits.len(), 1);
}
