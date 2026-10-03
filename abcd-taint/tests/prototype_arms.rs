//! Prototype-resolver arm coverage (c-COV W10): the receiver-family
//! arms the corpus never typed — Function/RegExp alloc kinds, the
//! Number/Bool const wrappers, the direct `PrototypeResolver` walks
//! (Mov/Phi/Const/cycle/dangling), the GetIterator non-builtin arm, the
//! constructor-result arm's Mov/Phi recursion and non-global bottoms,
//! the TryStoreGlobal provenance alternative, and the family key
//! labels. Exact `FamilyAnswer` asserts.

mod common;

use std::cell::RefCell;
use std::collections::HashMap;

use abcd_analysis::dataflow::heap::Rung0AliasOracle;
use abcd_ir::{CallKind, Const, Edge, EdgeKind, Op, ValueDef, ValueId};
use abcd_taint::oracle::Oracle;
use abcd_taint::prototype::{FamilyAnswer, ProtoFamily, PrototypeResolver};
use abcd_taint::{SinkSpec, SourceSpec, TaintConfig};
use common::*;

/// Resolve `value`'s families through a rung-0 oracle.
fn families(m: &abcd_ir::Module, value: ValueId) -> FamilyAnswer {
    let oracle = Oracle::Rung0(Rung0AliasOracle::new(m));
    let memo = RefCell::new(HashMap::new());
    PrototypeResolver::new(m, &oracle, &memo).families_of(value, abcd_ir::InstId::new(0))
}

/// The family-key vocabulary is stable (the registry key prefixes).
#[test]
fn proto_family_keys_are_stable() {
    let want = [
        (ProtoFamily::Array, "Array.prototype"),
        (ProtoFamily::Object, "Object.prototype"),
        (ProtoFamily::RegExp, "RegExp.prototype"),
        (ProtoFamily::Function, "Function.prototype"),
        (ProtoFamily::Str, "String.prototype"),
        (ProtoFamily::Num, "Number.prototype"),
        (ProtoFamily::Bool, "Boolean.prototype"),
        (ProtoFamily::Iterator, "Iterator.prototype"),
    ];
    for (family, key) in want {
        assert_eq!(family.key(), key, "{family:?}");
    }
}

/// Alloc-kind arms the corpus never typed: an AllocClosure receiver is
/// `Function.prototype`, an AllocRegExp receiver is `RegExp.prototype`.
#[test]
fn alloc_kind_closure_and_regexp_families() {
    let mut m = mk_module();
    let body = add_func_named(&mut m, "body");
    {
        let b = entry_of(&m, body);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let clo = closure_of(&mut m, entry, body);
    let re_pat = intern(&mut m, "a+");
    let re = emit(
        &mut m,
        entry,
        Op::AllocRegExp {
            pattern: re_pat,
            flags: 0,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let fc = families(&m, clo);
    assert!(
        fc.families.contains(&ProtoFamily::Function),
        "the closure receiver: {fc:?}"
    );
    let fr = families(&m, re);
    assert!(
        fr.families.contains(&ProtoFamily::RegExp),
        "the regexp receiver: {fr:?}"
    );
    assert!(fr.precise);
}

/// Const-wrapper families: `LoadConst(Number)`/`LoadConst(Bool)`
/// receivers type `Number.prototype`/`Boolean.prototype`; a
/// const-DEFINED number (no instruction) types through the walk's
// `ValueDef::Const` arm.
#[test]
fn const_wrapper_families() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let n = load_number(&mut m, entry, 1.0);
    let b_c = push_const(&mut m, Const::Bool(true));
    let b = emit(&mut m, entry, Op::LoadConst(b_c));
    let cd = const_value(&mut m, Const::number(2.0));
    let ssym = intern(&mut m, "s");
    let cs = const_value(&mut m, Const::String(ssym));
    emit_void(&mut m, entry, Op::Return { value: None });

    let fn_ = families(&m, n);
    assert!(
        fn_.families.contains(&ProtoFamily::Num),
        "the number load: {fn_:?}"
    );
    let fb = families(&m, b);
    assert!(
        fb.families.contains(&ProtoFamily::Bool),
        "the bool load: {fb:?}"
    );
    let fd = families(&m, cd);
    assert!(
        fd.families.contains(&ProtoFamily::Num),
        "the const-DEFINED number (the walk arm): {fd:?}"
    );
    let fs = families(&m, cs);
    assert!(
        fs.families.contains(&ProtoFamily::Str),
        "the const-DEFINED string: {fs:?}"
    );
}

/// The walk's def-chain arms: a `Mov` passes through; a receiver whose
/// value id dangles and whose def-inst dangles marks imprecise (never
/// panics).
#[test]
fn walk_mov_and_dangling_arms() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let a = alloc_array(&mut m, entry);
    let moved = emit(&mut m, entry, Op::Mov { src: a });
    emit_void(&mut m, entry, Op::Return { value: None });

    let fm = families(&m, moved);
    assert!(
        fm.families.contains(&ProtoFamily::Array),
        "the mov passes through: {fm:?}"
    );
    // A dangling value id: imprecise, no families, no panic.
    let fd = families(&m, ValueId::new(9999));
    assert!(fd.families.is_empty() && !fd.precise, "{fd:?}");
    // A dangling def-inst: same.
    let bogus = ValueId::new(m.values.len() as u32);
    m.values.push(abcd_ir::Value {
        def: ValueDef::Inst(abcd_ir::InstId::new(9999)),
        ty: abcd_ir::Ty::Any,
    });
    let fb = families(&m, bogus);
    assert!(fb.families.is_empty() && !fb.precise, "{fb:?}");
}

/// A phi back-edge cycle: the shared visiting set terminates the walk,
/// marked imprecise (the cycle's own incoming value is not re-walked).
#[test]
fn walk_phi_cycle_terminates() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let latch = add_block(&mut m, f);
    let a = alloc_array(&mut m, entry);
    // A phi whose latch incoming is the phi itself.
    let phi_val = ValueId::new(m.values.len() as u32);
    let phi = emit(
        &mut m,
        entry,
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
                        from: entry,
                        kind: EdgeKind::Normal,
                    },
                    a,
                ),
            ],
        },
    );
    assert_eq!(phi, phi_val);
    emit_void(&mut m, entry, Op::Branch { dest: latch });
    emit_void(&mut m, latch, Op::Branch { dest: entry });
    link(&mut m, entry, latch);
    link(&mut m, latch, entry);

    let fp = families(&m, phi);
    assert!(
        fp.families.contains(&ProtoFamily::Array),
        "the acyclic incoming typed the phi: {fp:?}"
    );
    assert!(!fp.precise, "the cycle is imprecise");
}

/// A `GetIterator` over a non-builtin iterable (a plain object) types
/// NOTHING — the family is never invented.
#[test]
fn getiterator_non_builtin_iterable_types_nothing() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let o = alloc_object(&mut m, entry);
    let it = emit(&mut m, entry, Op::GetIterator { obj: o });
    emit_void(&mut m, entry, Op::Return { value: None });

    let fi = families(&m, it);
    assert!(
        !fi.families.contains(&ProtoFamily::Iterator),
        "a user object's iterator is not the builtin: {fi:?}"
    );
    assert!(!fi.precise);
}

/// The constructor-result arm: `new (mov Array)()` and
/// `new (phi(Array, Object))()` recurse to the global constructors; a
/// parameter constructor and a non-global op bottom out (no invented
/// family).
#[test]
fn constructor_family_recursion_arms() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let els = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    // (a) new (mov Array)()
    let arr_g = try_get_global(&mut m, entry, "Array");
    let moved = emit(&mut m, entry, Op::Mov { src: arr_g });
    let new_a = emit(
        &mut m,
        entry,
        Op::Call {
            callee: moved,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    // (b) new (phi(Array, Object))()
    let p = add_param(&mut m, f, 0);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p,
            true_dest: t,
            false_dest: els,
        },
    );
    let ga = try_get_global(&mut m, t, "Array");
    emit_void(&mut m, t, Op::Branch { dest: join });
    let go = try_get_global(&mut m, els, "Object");
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
                    ga,
                ),
                (
                    Edge {
                        from: els,
                        kind: EdgeKind::Normal,
                    },
                    go,
                ),
            ],
        },
    );
    let new_phi = emit(
        &mut m,
        join,
        Op::Call {
            callee: phiced,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    // (c) new (param)() — the callee's def is not an instruction.
    let new_param = emit(
        &mut m,
        join,
        Op::Call {
            callee: p,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    // (d) new (load_number())() — the def chain bottoms at a non-global
    // op. And (e): a dangling constructor value, plus a phi with the
    // SAME incoming twice (the visiting-set skip).
    let new_dangling = emit(
        &mut m,
        join,
        Op::Call {
            callee: ValueId::new(9999),
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    let gdup = try_get_global(&mut m, join, "Array");
    let phi_dup = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    gdup,
                ),
                (
                    Edge {
                        from: els,
                        kind: EdgeKind::Normal,
                    },
                    gdup,
                ),
            ],
        },
    );
    let new_dup = emit(
        &mut m,
        join,
        Op::Call {
            callee: phi_dup,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    let num = load_number(&mut m, join, 1.0);
    let new_num = emit(
        &mut m,
        join,
        Op::Call {
            callee: num,
            this: None,
            args: vec![],
            kind: CallKind::New,
        },
    );
    emit_void(&mut m, join, Op::Return { value: None });

    let fa = families(&m, new_a);
    assert!(
        fa.families.contains(&ProtoFamily::Array),
        "the mov recursion found Array: {fa:?}"
    );
    let fp = families(&m, new_phi);
    assert!(
        fp.families.contains(&ProtoFamily::Array) && fp.families.contains(&ProtoFamily::Object),
        "the phi recursion found both constructors: {fp:?}"
    );
    let fc = families(&m, new_param);
    assert!(
        fc.families.is_empty(),
        "a param constructor invents nothing: {fc:?}"
    );
    let fd = families(&m, new_num);
    assert!(
        fd.families.is_empty(),
        "a non-global bottom invents nothing: {fd:?}"
    );
    let fdang = families(&m, new_dangling);
    assert!(
        fdang.families.is_empty(),
        "a dangling constructor invents nothing: {fdang:?}"
    );
    let fdup = families(&m, new_dup);
    assert!(
        fdup.families.contains(&ProtoFamily::Array),
        "the duplicate phi entries resolve once: {fdup:?}"
    );
}

/// Global-store provenance through a `TryStoreGlobal` (the third store
// arm): the stored string constant types the global's family.
#[test]
fn global_provenance_try_store_global() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let s = load_string(&mut m, entry, "abc");
    let g = intern(&mut m, "g");
    emit_void(&mut m, entry, Op::TryStoreGlobal { name: g, value: s });
    emit_void(&mut m, entry, Op::Return { value: None });

    let recv = try_get_global(&mut m, entry, "g");
    let fr = families(&m, recv);
    assert!(
        fr.families.contains(&ProtoFamily::Str),
        "the TryStoreGlobal store typed the global: {fr:?}"
    );
    assert!(!fr.precise, "a global hop is never precise");
}

/// The end-to-end hooks: a direct `LoadConst(String)` receiver's method
/// call classifies through `String.prototype.*` (the walk's LoadConst
/// arm), and an `AllocRegExp` receiver's through `RegExp.prototype.*`
/// (the alloc-kind arm) — the summaries apply.
#[test]
fn const_and_regexp_families_drive_summary_lookup() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    // "abc".slice(p) — the string-const receiver.
    let s = load_string(&mut m, entry, "abc");
    let leaf = intern(&mut m, "slice");
    let callee = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: s,
            name: leaf,
        },
    );
    emit(
        &mut m,
        entry,
        Op::Call {
            callee,
            this: Some(s),
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    // r.test(p) — the regexp-alloc receiver.
    let r_pat = intern(&mut m, "a+");
    let r = emit(
        &mut m,
        entry,
        Op::AllocRegExp {
            pattern: r_pat,
            flags: 0,
        },
    );
    let tleaf = intern(&mut m, "test");
    let tcallee = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: r,
            name: tleaf,
        },
    );
    emit(
        &mut m,
        entry,
        Op::Call {
            callee: tcallee,
            this: Some(r),
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, entry, Op::Return { value: None });

    let config = TaintConfig {
        sources: vec![SourceSpec::FunctionParams {
            name: "func_main_0".to_owned(),
            params: None,
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        ..TaintConfig::default()
    };
    let report = abcd_taint::run_taint(&m, &config);
    let applied: Vec<&str> = report
        .summaries_applied
        .iter()
        .map(|(_, n)| n.as_str())
        .collect();
    assert!(
        applied.contains(&"String.prototype.slice"),
        "the const family qualified the lookup: {applied:?}"
    );
    assert!(
        applied.contains(&"RegExp.prototype.test"),
        "the regexp alloc family qualified the lookup: {applied:?}"
    );
}

/// The `_ => None` arms: a receiver that is a property-LOAD result
/// (family_of_alloc does not know it; the walk marks imprecise, no
/// family invented) and a const-DEFINED `null` (family_of_const has no
/// null wrapper).
#[test]
fn non_alloc_and_null_receivers_invent_nothing() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    let g = try_get_global(&mut m, entry, "g");
    let k = intern(&mut m, "k");
    let loaded = emit(&mut m, entry, Op::LoadProp { object: g, name: k });
    emit_void(&mut m, entry, Op::Return { value: None });
    let null_cv = const_value(&mut m, Const::Null);

    let fl = families(&m, loaded);
    assert!(
        fl.families.is_empty() && !fl.precise,
        "a load result invents nothing: {fl:?}"
    );
    let fn_ = families(&m, null_cv);
    // No family, and the empty answer is marked imprecise (the
    // compute() tail: empty means "no receiver type recoverable").
    assert!(
        fn_.families.is_empty() && !fn_.precise,
        "const null: no family: {fn_:?}"
    );
}
