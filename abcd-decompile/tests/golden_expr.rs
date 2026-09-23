//! Golden expression-tree dumps (design/decompile.md §7 d-P2 gate): one
//! crafted case per §5 taxonomy family — the trivial + needs-work
//! families, the guard-elision family, phi/handler-phi, lexenv naming,
//! the legalizer, and the documented hard-7 fallbacks.
//!
//! The expected strings are the STABLE dump form ([`abcd_decompile::dump`]);
//! they are reviewed, hand-written expectations — not snapshots.

mod common;

use abcd_analysis::dataflow::UseDefChains;
use abcd_decompile::dump::{dump_func, dump_module};
use abcd_decompile::recover::{builder_hook, recover_func};
use abcd_ir::module::FunctionKind;
use abcd_ir::op::{BinOp, CallKind, CmpOp, PropKey, SuperCheck, SuperKey, UnOp};
use abcd_ir::{Const, DebugData, Edge, EdgeKind, LocalName, LocalScope, Op};

use common::*;

/// t01 — compute family (BinaryOp/UnaryOp/Mov/Compare): pure chains
/// inline; a multi-use value becomes a `const` temp (SSA
/// single-assignment proof).
#[test]
fn t01_compute_chain() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "calc");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let a = add_param(&mut m, f);
    let bb = add_param(&mut m, f);
    let s = add(&mut m, b, a, bb);
    let pr = emit(
        &mut m,
        b,
        Op::BinaryOp {
            op: BinOp::Mul,
            left: s,
            right: s,
        },
    );
    let neg = emit(
        &mut m,
        b,
        Op::UnaryOp {
            op: UnOp::Minus,
            operand: pr,
        },
    );
    let mv = emit(&mut m, b, Op::Mov { src: neg });
    let sum = add(&mut m, b, mv, mv);
    emit_void(&mut m, b, Op::Return { value: Some(sum) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "calc" kind=function params=(this, p1, p2)
  bb B0 preds=[]:
    const v3 = (p1 + p2) ; v3
    const v6 = (-(v3 * v3)) ; v6
    return (v6 + v6)
"#;
    assert_eq!(got, want);
}

/// t02 — the inline rule's three boundaries: multi-use → temp, an
/// observable instruction between def and use → temp, cross-block use →
/// temp; single-use same-block barrier-free → inline.
#[test]
fn t02_inline_barriers() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let one = load_number(&mut m, b0, 1.0);
    let two = load_number(&mut m, b0, 2.0);
    let s = add(&mut m, b0, one, two);
    let call = emit(
        &mut m,
        b0,
        Op::Call {
            callee: p1,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let after = add(&mut m, b0, call, s);
    let b1 = add_block(&mut m, f);
    emit_void(&mut m, b0, Op::Branch { dest: b1 });
    link(&mut m, b0, b1);
    let late = add(&mut m, b1, after, one);
    emit_void(&mut m, b1, Op::Return { value: Some(late) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "f" kind=function params=(this, p1)
  bb B0 preds=[]:
    const v2 = 1.0 ; v2
    const v4 = (v2 + 2.0) ; v4
    const v5 = (p1()) ; v5
    const v6 = (v5 + v4) ; v6
    branch B1
  bb B1 preds=[B0:N]:
    return (v6 + v2)
"#;
    assert_eq!(got, want);
}

/// t03 — literal emission from `Const`: f64 bit-exact shortest
/// round-trip (`-0.0`, `NaN`, `1e300`), string escaping, BigInt,
/// null/undefined/bool, RegExp flags.
#[test]
fn t03_literals() {
    let mut m = mk_module();
    let cases: Vec<(&str, Const)> = vec![
        ("negzero", Const::number(-0.0)),
        ("nan", Const::number(f64::NAN)),
        ("big", Const::number(1e300)),
        ("str", Const::String(sym_placeholder())),
        ("bigint", Const::BigInt(sym_placeholder())),
        ("null_lit", Const::Null),
        ("undef", Const::Undefined),
        ("bool_lit", Const::Bool(true)),
    ];
    let mut funcs = Vec::new();
    for (name, c) in cases {
        let f = add_func_named(&mut m, name);
        let b = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        funcs.push((f, b, c));
    }
    // Intern the string payloads after the funcs (Sym creation order is
    // irrelevant to the dump, but keep the construction explicit).
    let str_sym = intern(&mut m, "a\"b\\c\n");
    let bigint_sym = intern(&mut m, "123");
    for (_f, b, c) in funcs {
        let c = match c {
            Const::String(_) => Const::String(str_sym),
            Const::BigInt(_) => Const::BigInt(bigint_sym),
            other => other,
        };
        let v = load_const(&mut m, b, c);
        emit_void(&mut m, b, Op::Return { value: Some(v) });
    }
    // The RegExp case needs its own op.
    let f = add_func_named(&mut m, "regexp");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let pattern = intern(&mut m, "a+b/x");
    let v = emit(
        &mut m,
        b,
        Op::AllocRegExp {
            pattern,
            flags: 1 | 2,
        },
    );
    emit_void(&mut m, b, Op::Return { value: Some(v) });

    let got = dump_module(&m);
    let want = r#"fn #0 "negzero" kind=function params=(this)
  bb B0 preds=[]:
    return -0.0
fn #1 "nan" kind=function params=(this)
  bb B1 preds=[]:
    return NaN
fn #2 "big" kind=function params=(this)
  bb B2 preds=[]:
    return 1e300
fn #3 "str" kind=function params=(this)
  bb B3 preds=[]:
    return "a\"b\\c\n"
fn #4 "bigint" kind=function params=(this)
  bb B4 preds=[]:
    return 123n
fn #5 "null_lit" kind=function params=(this)
  bb B5 preds=[]:
    return null
fn #6 "undef" kind=function params=(this)
  bb B6 preds=[]:
    return undefined
fn #7 "bool_lit" kind=function params=(this)
  bb B7 preds=[]:
    return true
fn #8 "regexp" kind=function params=(this)
  bb B8 preds=[]:
    const v17 = /a+b\/x/gi ; v17
    return v17
"#;
    assert_eq!(got, want);
}

/// A marker `Sym` replaced after interning (construction convenience for
/// the cases table above — never reaches the dump).
fn sym_placeholder() -> abcd_ir::Sym {
    abcd_ir::Sym::new(u32::MAX)
}

/// t04 — property access: named/index/dynamic loads and stores,
/// `delete`, `in` — observable loads always become temps.
#[test]
fn t04_property_access() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "props");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let obj = add_param(&mut m, f);
    let x = intern(&mut m, "x");
    let vx = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: obj,
            name: x,
        },
    );
    let c0 = load_number(&mut m, b, 0.0);
    let vidx = emit(
        &mut m,
        b,
        Op::LoadPropIdx {
            object: obj,
            index: c0,
        },
    );
    let vdyn = emit(
        &mut m,
        b,
        Op::LoadPropDyn {
            object: obj,
            key: vx,
        },
    );
    let y = intern(&mut m, "y");
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: obj,
            name: y,
            value: vidx,
        },
    );
    let c1 = load_number(&mut m, b, 1.0);
    emit_void(
        &mut m,
        b,
        Op::StorePropIdx {
            object: obj,
            index: c1,
            value: vdyn,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::StorePropDyn {
            object: obj,
            key: vx,
            value: vidx,
        },
    );
    let _vdel = emit(
        &mut m,
        b,
        Op::DeleteProp {
            object: obj,
            key: vx,
        },
    );
    let z = intern(&mut m, "z");
    let vtest = emit(
        &mut m,
        b,
        Op::TestProp {
            object: obj,
            key: PropKey::Name(z),
        },
    );
    emit_void(&mut m, b, Op::Return { value: Some(vtest) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "props" kind=function params=(this, p1)
  bb B0 preds=[]:
    const x = (p1.x) ; v2
    const v4 = (p1[0.0]) ; v4
    const v5 = (p1[x]) ; v5
    p1.y = v4
    p1[1.0] = v5
    p1[x] = v4
    (delete (p1[x]))
    const v8 = ("z" in p1) ; v8
    return v8
"#;
    assert_eq!(got, want);
}

/// t05 — the whole `CallKind` family: Direct (`this` explicit), Dynamic,
/// Apply (`.apply(this, arr)` shape), New, and the three Super forms.
#[test]
fn t05_call_kinds() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "calls");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let one = load_number(&mut m, b, 1.0);
    let _direct = emit(
        &mut m,
        b,
        Op::Call {
            callee: p1,
            this: Some(p2),
            args: vec![one],
            kind: CallKind::Direct,
        },
    );
    let _dyn = emit(
        &mut m,
        b,
        Op::Call {
            callee: p1,
            this: None,
            args: vec![p2],
            kind: CallKind::Dynamic,
        },
    );
    let arr = emit(&mut m, b, Op::AllocArray { shape: None });
    let _apply = emit(
        &mut m,
        b,
        Op::Call {
            callee: p1,
            this: Some(p2),
            args: vec![arr],
            kind: CallKind::Apply,
        },
    );
    let _new = emit(
        &mut m,
        b,
        Op::Call {
            callee: p1,
            this: None,
            args: vec![p2],
            kind: CallKind::New,
        },
    );
    let _sup = emit(
        &mut m,
        b,
        Op::Call {
            callee: p1,
            this: None,
            args: vec![p2],
            kind: CallKind::Super,
        },
    );
    let arr2 = emit(&mut m, b, Op::AllocArray { shape: None });
    let _sspread = emit(
        &mut m,
        b,
        Op::Call {
            callee: p1,
            this: None,
            args: vec![arr2],
            kind: CallKind::SuperSpread,
        },
    );
    let _sfwd = emit(
        &mut m,
        b,
        Op::Call {
            callee: p1,
            this: Some(_this),
            args: vec![_this],
            kind: CallKind::SuperForwardAllArgs,
        },
    );

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "calls" kind=function params=(this, p1, p2)
  bb B0 preds=[]:
    call(p1, this=p2, 1.0)
    (p1(p2))
    (p1.apply(p2, []))
    (new p1(p2))
    super(p2)
    super(...[])
    super(...args) /*forward-all*/
"#;
    assert_eq!(got, want);
}

/// t06 — object/array literal builders from shape consts; the own-store
/// sequence stays as statements with the d-P3 fold hook exposed.
#[test]
fn t06_literal_builders() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "builders");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let ka = intern(&mut m, "a");
    let kbc = intern(&mut m, "b c");
    let vx = intern(&mut m, "x");
    let shape = const_id(
        &mut m,
        Const::ObjectLiteral {
            keys: vec![Const::String(ka), Const::String(kbc)],
            values: vec![Const::number(1.0), Const::String(vx)],
        },
    );
    let obj = emit(&mut m, b, Op::AllocObject { shape });
    let ko = intern(&mut m, "o");
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: p1,
            name: ko,
            value: obj,
        },
    );
    let arr_shape = const_id(
        &mut m,
        Const::ArrayLiteral(vec![Const::number(1.0), Const::number(2.0)]),
    );
    let arr = emit(
        &mut m,
        b,
        Op::AllocArray {
            shape: Some(arr_shape),
        },
    );
    let c5 = load_number(&mut m, b, 5.0);
    let c6 = load_number(&mut m, b, 6.0);
    let own_store = emit_void(
        &mut m,
        b,
        Op::StoreOwnPropIdx {
            object: arr,
            index: c5,
            value: c6,
        },
    );
    let spread = emit_void(&mut m, b, Op::CopyDataProps { dst: arr, src: p1 });
    emit_void(&mut m, b, Op::Return { value: Some(arr) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "builders" kind=function params=(this, p1)
  bb B0 preds=[]:
    p1.o = {a: 1.0, "b c": "x"}
    const v3 = [1.0, 2.0] ; v3
    v3[5.0] = 6.0 /*own*/
    copy-data-props(v3, p1) /*plumbing*/
    return v3
"#;
    assert_eq!(got, want);

    // The d-P3 fold hook: the own-store + spread sequence, in order.
    let chains = UseDefChains::build(&m, f);
    let hook = builder_hook(&m, &chains, arr);
    assert_eq!(hook, vec![own_store, spread]);
}

/// t07 — closures (DefineFunc + AllocClosure pair) and classes
/// (DefineClass deferred node; DefineSendableClass as the documented
/// hard-7 fallback node).
#[test]
fn t07_closures_and_classes() {
    let mut m = mk_module();
    let inner = add_func_named(&mut m, "inner");
    {
        let b = entry_of(&m, inner);
        let _this = add_param(&mut m, inner);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let f = add_func_named(&mut m, "outer");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let cap = intern(&mut m, "cap");
    let df = emit(
        &mut m,
        b,
        Op::DefineFunc {
            body: inner,
            captures: vec![(cap, p1)],
            length: 0,
        },
    );
    let cl = emit(&mut m, b, Op::AllocClosure { func: df });
    let km = intern(&mut m, "m");
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: p2,
            name: km,
            value: cl,
        },
    );
    let members = const_id(
        &mut m,
        Const::ObjectLiteral {
            keys: vec![],
            values: vec![],
        },
    );
    let cls = emit(
        &mut m,
        b,
        Op::DefineClass {
            ctor: inner,
            heritage: Some(p1),
            members,
            member_attrs: Vec::new(),
            count: 0,
        },
    );
    let members2 = const_id(
        &mut m,
        Const::ObjectLiteral {
            keys: vec![],
            values: vec![],
        },
    );
    let _send = emit(
        &mut m,
        b,
        Op::DefineSendableClass {
            ctor: inner,
            heritage: None,
            members: members2,
            member_attrs: Vec::new(),
            count: 0,
        },
    );
    emit_void(&mut m, b, Op::Return { value: Some(cls) });

    let got = dump_module(&m);
    let want = r#"fn #0 "inner" kind=function params=(this)
  bb B0 preds=[]:
    return
fn #1 "outer" kind=function params=(this, p1, p2)
  bb B1 preds=[]:
    p2.m = closure(fn#0 "inner" function captures=[cap=p1])
    const inner = class(fn#0 "inner" extends p1 members=c#0) ; v6
    class(fn#0 "inner" members=c#1) /*sendable*/
    return inner
"#;
    assert_eq!(got, want);
}

/// t08 — the `Throw*` guard family is elided ON PURPOSE (each with its
/// documented §5 reason); `ThrowDeleteSuperProperty` is a loud fallback
/// (its member expression is not recoverable from the op); `Throw` is a
/// real statement.
#[test]
fn t08_guard_elision() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "guards");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    emit_void(
        &mut m,
        b,
        Op::ThrowIfSuperNotCalled {
            value: p1,
            kind: SuperCheck::NotCalled,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::ThrowUndefinedIfHole {
            name: p1,
            value: p1,
        },
    );
    let x = intern(&mut m, "x");
    emit_void(
        &mut m,
        b,
        Op::ThrowUndefinedIfHoleWithName { name: x, value: p1 },
    );
    emit_void(&mut m, b, Op::ThrowNotExists);
    emit_void(&mut m, b, Op::ThrowPatternNonCoercible);
    emit_void(&mut m, b, Op::ThrowDeleteSuperProperty);
    emit_void(&mut m, b, Op::ThrowConstAssignment { name: p1 });
    emit_void(&mut m, b, Op::ThrowIfNotObject { value: p1 });
    let _enter = emit(&mut m, b, Op::AsyncFunctionEnter);
    emit_void(&mut m, b, Op::Throw { value: p1 });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "guards" kind=function params=(this, p1)
  bb B0 preds=[]:
    ; elided ThrowIfSuperNotCalled: derived-ctor `this` guard; emitted source proves the condition can't fire (§5 row 58)
    ; elided ThrowUndefinedIfHole: TDZ guard; emitted source has no TDZ-hole reads (§5 row 59)
    ; elided ThrowUndefinedIfHoleWithName: TDZ guard (compile-time name); emitted source has no TDZ-hole reads (§5 row 60)
    ; elided ThrowNotExists: ReferenceError guard; elided in normal-flow reconstruction (§5 row 61)
    ; elided ThrowPatternNonCoercible: destructuring coercion guard; elided in destructuring reconstruction (§5 row 62)
    ; fallback ThrowDeleteSuperProperty: `delete super.x` reconstruction (N); the throw IS the delete's semantics, but the op carries no object operand — the member expression is unrecoverable at Stage A (§5 row 63)
    ; elided ThrowConstAssignment: const-violation guard; elided — the const binding is reconstructed (§5 row 64)
    ; elided ThrowIfNotObject: for-in/for-of coercion guard; elided in loop reconstruction (§5 row 65)
    ; elided AsyncFunctionEnter: async-machinery entry; recognized and elided inside `async function` emission (§5 row 72)
    throw p1
"#;
    assert_eq!(got, want);
}

/// t09 — phi → `let` temporary + per-predecessor assignment records
/// (out-of-SSA at AST level); the `IsTrue` condition folds into the
/// branch head.
#[test]
fn t09_phi_diamond() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let cond = emit(
        &mut m,
        b0,
        Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: p1,
        },
    );
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let b3 = add_block(&mut m, f);
    emit_void(
        &mut m,
        b0,
        Op::CondBranch {
            cond,
            true_dest: b1,
            false_dest: b2,
        },
    );
    let x = load_number(&mut m, b1, 2.0);
    emit_void(&mut m, b1, Op::Branch { dest: b3 });
    let y = load_number(&mut m, b2, 3.0);
    emit_void(&mut m, b2, Op::Branch { dest: b3 });
    link(&mut m, b0, b1);
    link(&mut m, b0, b2);
    link(&mut m, b1, b3);
    link(&mut m, b2, b3);
    let phi = emit(
        &mut m,
        b3,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b1,
                        kind: EdgeKind::Normal,
                    },
                    x,
                ),
                (
                    Edge {
                        from: b2,
                        kind: EdgeKind::Normal,
                    },
                    y,
                ),
            ],
        },
    );
    emit_void(&mut m, b3, Op::Return { value: Some(phi) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "f" kind=function params=(this, p1)
  bb B0 preds=[]:
    if (istrue p1) then B1 else B2
  bb B1 preds=[B0:N]:
    branch B3
    phi-assign v5 = 2.0 ; edge -> B3 (normal)
  bb B2 preds=[B0:N]:
    branch B3
    phi-assign v5 = 3.0 ; edge -> B3 (normal)
  bb B3 preds=[B1:N,B2:N]:
    let v5 ; phi v5
    return v5
"#;
    assert_eq!(got, want);
}

/// t10 — `ExceptionParam` becomes the `catch (e)` binding directly;
/// handler phis stay temporaries with EXCEPTIONAL-edge assignments
/// (N38 conservatism).
#[test]
fn t10_catch_binding_and_handler_phi() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let call = emit(
        &mut m,
        b0,
        Op::Call {
            callee: p1,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    let one = load_number(&mut m, b0, 1.0);
    let vdef = add(&mut m, b0, call, one);
    let b1 = add_block(&mut m, f); // handler
    let b2 = add_block(&mut m, f); // normal exit
    emit_void(&mut m, b0, Op::Branch { dest: b2 });
    link(&mut m, b0, b2);
    let exc = add_exception_param(&mut m, b1);
    add_try(&mut m, f, vec![b0], b1, exc);
    let phi = emit(
        &mut m,
        b1,
        Op::Phi {
            entries: vec![(
                Edge {
                    from: b0,
                    kind: EdgeKind::Exceptional,
                },
                vdef,
            )],
        },
    );
    let sum = add(&mut m, b1, phi, exc);
    emit_void(&mut m, b1, Op::Return { value: Some(sum) });
    let zero = load_number(&mut m, b2, 0.0);
    emit_void(&mut m, b2, Op::Return { value: Some(zero) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "f" kind=function params=(this, p1)
  bb B0 preds=[]:
    const v2 = (p1()) ; v2
    branch B2
    phi-assign v6 = (v2 + 1.0) ; edge -> B1 (exceptional)
  bb B1 preds=[B0:X]:
    catch e
    let v6 ; phi v6
    return (v6 + e)
  bb B2 preds=[B0:N]:
    return 0.0
"#;
    assert_eq!(got, want);
}

/// t11 — iteration-protocol plumbing nodes (for-of/for-in
/// reconstruction is d-P3); `IteratorReturn`/`IteratorThrow` are the
/// documented hard-7 fallbacks.
#[test]
fn t11_iteration_plumbing() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "iter");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let it = emit(&mut m, b, Op::GetIterator { obj: p1 });
    let nxt = emit(&mut m, b, Op::IteratorNext { iterator: it });
    let _ret = emit(&mut m, b, Op::IteratorReturn { iterator: it });
    let _thr = emit(&mut m, b, Op::IteratorThrow { iterator: it });
    let pi = emit(&mut m, b, Op::GetPropIterator { obj: p1 });
    let _npn = emit(&mut m, b, Op::NextPropName { iterator: pi });
    let cfalse = load_const(&mut m, b, Const::Bool(false));
    let res = emit(
        &mut m,
        b,
        Op::CreateIterResultObj {
            value: nxt,
            done: cfalse,
        },
    );
    emit_void(&mut m, b, Op::Return { value: Some(res) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "iter" kind=function params=(this, p1)
  bb B0 preds=[]:
    const v2 = get-iterator(p1) /*plumbing*/ ; v2
    const v3 = iter-next(v2) /*plumbing*/ ; v3
    iter-return(v2) /*hard-fallback*/
    iter-throw(v2) /*hard-fallback*/
    next-prop-name(get-prop-iterator(p1) /*plumbing*/) /*plumbing*/
    return {value: v3, done: false} /*iter-result*/
"#;
    assert_eq!(got, want);
}

/// t12 — generator/async: `SuspendGenerator` → `yield`,
/// `Await`/`AwaitUncaught` → `await`; the driver plumbing
/// (`ResumeGenerator`, `GetResumeMode`, `AsyncResolve`, `AsyncReject`)
/// lands as the documented hard-7 fallback nodes.
#[test]
fn t12_generator_async() {
    let mut m = mk_module();
    let g = add_func_kind(&mut m, "gen", FunctionKind::Generator);
    {
        let b = entry_of(&m, g);
        let _this = add_param(&mut m, g);
        let p1 = add_param(&mut m, g);
        let cg = emit(&mut m, b, Op::CreateGenerator { func: p1 });
        let s = emit(
            &mut m,
            b,
            Op::SuspendGenerator {
                genobj: cg,
                value: p1,
            },
        );
        let _rg = emit(&mut m, b, Op::ResumeGenerator { genobj: cg });
        let grm = emit(&mut m, b, Op::GetResumeMode { genobj: cg });
        let ret = add(&mut m, b, s, grm);
        emit_void(&mut m, b, Op::Return { value: Some(ret) });
    }
    let a = add_func_kind(&mut m, "af", FunctionKind::Async);
    {
        let b = entry_of(&m, a);
        let _this = add_param(&mut m, a);
        let p1 = add_param(&mut m, a);
        let ae = emit(&mut m, b, Op::Await { value: p1 });
        let au = emit(&mut m, b, Op::AwaitUncaught { value: p1 });
        let _ar = emit(&mut m, b, Op::AsyncResolve { value: ae });
        let _aj = emit(&mut m, b, Op::AsyncReject { value: au });
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let got = dump_module(&m);
    let want = r#"fn #0 "gen" kind=generator params=(this, p1)
  bb B0 preds=[]:
    const v2 = create-generator(p1) /*plumbing*/ ; v2
    const v3 = (yield p1) ; v3
    resume-generator(v2) /*hard-fallback*/
    return (v3 + get-resume-mode(v2) /*hard-fallback*/)
fn #1 "af" kind=async params=(this, p1)
  bb B1 preds=[]:
    const v9 = (await p1) ; v9
    const v10 = (await p1 /*uncaught*/) ; v10
    async-resolve(v9) /*hard-fallback*/
    async-reject(v10) /*hard-fallback*/
    return
"#;
    assert_eq!(got, want);
}

/// t13 — lexenv: `NewLexEnvWithName` scope names resolve `{level, slot}`
/// through the env chain; the UNNAMED `NewLexEnv` (gap G1) gets the
/// cosmetic `v{abs}_{slot}` fallback keyed by the frame's ABSOLUTE chain
/// index (capture-consistent across functions — d-P7); an intervening
/// `PopLexEnv` is an inline barrier (it writes LEX_ENV).
#[test]
fn t13_lexenv() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "lex");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let x = intern(&mut m, "x");
    let y = intern(&mut m, "y");
    let names = const_id(
        &mut m,
        Const::ArrayLiteral(vec![Const::String(x), Const::String(y)]),
    );
    let _ne = emit(
        &mut m,
        b,
        Op::NewLexEnvWithName {
            num_vars: 2,
            scope_names: names,
        },
    );
    let c1 = load_number(&mut m, b, 1.0);
    emit_void(
        &mut m,
        b,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: c1,
        },
    );
    let _nu = emit(&mut m, b, Op::NewLexEnv { num_vars: 1 });
    let c2 = load_number(&mut m, b, 2.0);
    emit_void(
        &mut m,
        b,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: c2,
        },
    );
    let g1 = emit(&mut m, b, Op::GetLexVar { level: 1, slot: 1 });
    let g2 = emit(&mut m, b, Op::GetLexVar { level: 0, slot: 0 });
    let s = add(&mut m, b, g1, g2);
    emit_void(&mut m, b, Op::PopLexEnv);
    emit_void(&mut m, b, Op::PopLexEnv);
    emit_void(&mut m, b, Op::Return { value: Some(s) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "lex" kind=function params=(this)
  bb B0 preds=[]:
    scope-push [x, y]
    lex x = 1.0 /*L0#0*/
    scope-push [<unnamed>]
    lex v1_0 = 2.0 /*L0#0*/
    const v7 = (y + v1_0) ; v7
    scope-pop
    scope-pop
    return v7
"#;
    assert_eq!(got, want);
}

/// t14 — globals (incl. the not-a-legal-identifier global reachable only
/// through `globalThis[...]`, and the temp/global name-shadowing guard),
/// module-local slots (gap G2 synthetic names), namespace, dynamic import.
#[test]
fn t14_globals_and_module() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let console = intern(&mut m, "console");
    let _tg1 = emit(
        &mut m,
        b,
        Op::TryGetGlobal {
            name: console,
            default: None,
        },
    );
    let weird = intern(&mut m, "not a legal ident");
    let _tg2 = emit(
        &mut m,
        b,
        Op::TryGetGlobal {
            name: weird,
            default: None,
        },
    );
    let g = intern(&mut m, "g");
    emit_void(
        &mut m,
        b,
        Op::StoreGlobal {
            name: g,
            value: _tg1,
        },
    );
    let h = intern(&mut m, "h");
    emit_void(
        &mut m,
        b,
        Op::TryStoreGlobal {
            name: h,
            value: _tg2,
        },
    );
    let lmv = emit(&mut m, b, Op::LoadModuleVar { index: 3 });
    emit_void(
        &mut m,
        b,
        Op::StoreModuleVar {
            index: 3,
            value: lmv,
        },
    );
    let ns = emit(&mut m, b, Op::GetModuleNamespace { index: 0 });
    let spec = load_string(&mut m, b, "./x.js");
    let _di = emit(&mut m, b, Op::DynamicImport { specifier: spec });
    emit_void(&mut m, b, Op::Return { value: Some(ns) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "f" kind=function params=(this)
  bb B0 preds=[]:
    const console$1 = console ; v1
    const not_a_legal_ident$1 = (globalThis["not a legal ident"]) ; v2
    g = console$1
    h = not_a_legal_ident$1 /*try*/
    m3 = m3 /*module slot 3*/
    const ns0$1 = ns0 ; v4
    import("./x.js")
    return ns0$1
"#;
    assert_eq!(got, want);
}

/// t15 — private names: `CreatePrivateNames` registers; the
/// `{level, slot}` private ops resolve through the registration.
#[test]
fn t15_private_names() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "priv");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let _ne = emit(&mut m, b, Op::NewLexEnv { num_vars: 1 });
    let a = intern(&mut m, "a");
    let bb = intern(&mut m, "b");
    let names = const_id(
        &mut m,
        Const::ArrayLiteral(vec![Const::String(a), Const::String(bb)]),
    );
    emit_void(&mut m, b, Op::CreatePrivateNames { count: 2, names });
    let lp = emit(
        &mut m,
        b,
        Op::LoadPrivate {
            level: 0,
            slot: 0,
            obj: p1,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::StorePrivate {
            level: 0,
            slot: 1,
            obj: p1,
            value: lp,
        },
    );
    let nine = load_number(&mut m, b, 9.0);
    emit_void(
        &mut m,
        b,
        Op::DefinePrivate {
            level: 0,
            slot: 1,
            obj: p1,
            value: nine,
        },
    );
    let tp = emit(
        &mut m,
        b,
        Op::TestPrivate {
            level: 0,
            slot: 0,
            obj: p1,
        },
    );
    emit_void(&mut m, b, Op::Return { value: Some(tp) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "priv" kind=function params=(this, p1)
  bb B0 preds=[]:
    scope-push [<unnamed>]
    private-names [#a, #b]
    const v3 = (p1.#a) ; v3
    store p1.#b = v3
    define p1.#b = 9.0
    const v5 = (#a in p1) ; v5
    return v5
"#;
    assert_eq!(got, want);
}

/// t16 — template objects: cooked-string resolution from the const pool
/// (gap G4: cooked-only fallback, documented); unresolved literal
/// operand → the loud `<unresolved>` form.
#[test]
fn t16_template_objects() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "tmpl");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let s1 = intern(&mut m, "hello ");
    let s2 = intern(&mut m, " world");
    let arr = const_id(
        &mut m,
        Const::ArrayLiteral(vec![Const::String(s1), Const::String(s2)]),
    );
    let lit = emit(&mut m, b, Op::LoadConst(arr));
    let t1 = emit(&mut m, b, Op::GetTemplateObject { literal: lit });
    let t2 = emit(&mut m, b, Op::GetTemplateObject { literal: p1 });
    let sum = add(&mut m, b, t1, t2);
    emit_void(&mut m, b, Op::Return { value: Some(sum) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "tmpl" kind=function params=(this, p1)
  bb B0 preds=[]:
    const v3 = template(["hello ", " world"]) /*cooked-only (G4)*/ ; v3
    const v4 = template(<unresolved>) /*cooked-only (G4)*/ ; v4
    return (v3 + v4)
"#;
    assert_eq!(got, want);
}

/// t17 — frame/special value loaders and super-property access.
#[test]
fn t17_frame_specials() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "frame");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let store = |m: &mut abcd_ir::Module, name: &str, v: abcd_ir::ValueId| {
        let name = intern(m, name);
        emit_void(
            m,
            b,
            Op::StoreProp {
                object: p1,
                name,
                value: v,
            },
        );
    };
    let nt = emit(&mut m, b, Op::LoadNewTarget);
    store(&mut m, "nt", nt);
    let go = emit(&mut m, b, Op::LoadGlobalObject);
    store(&mut m, "go", go);
    let lf = emit(&mut m, b, Op::LoadFunction);
    store(&mut m, "self", lf);
    let ua = emit(&mut m, b, Op::GetUnmappedArgs);
    store(&mut m, "args", ua);
    let cra = emit(&mut m, b, Op::CopyRestArgs { start_index: 1 });
    store(&mut m, "rest", cra);
    let foo = intern(&mut m, "foo");
    let ls = emit(
        &mut m,
        b,
        Op::LoadSuper {
            key: SuperKey::Name(foo),
        },
    );
    let bar = intern(&mut m, "bar");
    emit_void(
        &mut m,
        b,
        Op::StoreSuper {
            key: SuperKey::Name(bar),
            value: ls,
        },
    );
    let k = load_string(&mut m, b, "k");
    emit_void(
        &mut m,
        b,
        Op::StoreSuper {
            key: SuperKey::Dynamic(k),
            value: ls,
        },
    );
    emit_void(&mut m, b, Op::Return { value: None });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "frame" kind=function params=(this, p1)
  bb B0 preds=[]:
    p1.nt = new.target
    p1.go = globalThis
    p1.self = frame
    p1.args = arguments
    p1.rest = ...rest[from 1]
    const v7 = super.foo ; v7
    super.bar = v7
    super["k"] = v7
    return
"#;
    assert_eq!(got, want);
}

/// t18 — naming: `DebugData.param_names` through the legalizer
/// (reserved-word `class` → `class_`), `local_names` scope extents →
/// temp names with collision disambiguation (`y`, `y$1`).
#[test]
fn t18_naming_and_legalizer() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let s1 = add(&mut m, b, p1, p2);
    let i1 = m.insts.len() - 1;
    let s2 = add(&mut m, b, s1, s1);
    let i2 = m.insts.len() - 1;
    let s3 = add(&mut m, b, s2, s2);
    emit_void(&mut m, b, Op::Return { value: Some(s3) });

    let class = intern(&mut m, "class");
    let x = intern(&mut m, "x");
    let y = intern(&mut m, "y");
    m.func_mut(f).unwrap().debug = Some(DebugData {
        param_names: vec![class, x],
        local_names: vec![LocalName {
            name: y,
            ty: None,
            scope: Some(LocalScope {
                start: abcd_ir::InstId::new(i1 as u32),
                end: abcd_ir::InstId::new(i2 as u32),
            }),
        }],
        ..Default::default()
    });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "f" kind=function params=(this, class_, x)
  bb B0 preds=[]:
    const y = (class_ + x) ; v3
    const y$1 = (y + y) ; v4
    return (y$1 + y$1)
"#;
    assert_eq!(got, want);
}

/// t19 — unary/compare forms (ToNumber renders as the `+x` coercion;
/// `typeof`; chained inlining through pure defs).
#[test]
fn t19_unary_forms() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "unary");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let t = emit(
        &mut m,
        b,
        Op::UnaryOp {
            op: UnOp::TypeOf,
            operand: p1,
        },
    );
    let n = emit(
        &mut m,
        b,
        Op::UnaryOp {
            op: UnOp::LogicalNot,
            operand: t,
        },
    );
    let null = load_const(&mut m, b, Const::Null);
    let eq = emit(
        &mut m,
        b,
        Op::Compare {
            op: CmpOp::StrictEq,
            // N36: semantic `n === null` is stored acc=null/vreg=n.
            left: null,
            right: n,
        },
    );
    let num = emit(
        &mut m,
        b,
        Op::UnaryOp {
            op: UnOp::ToNumber,
            operand: eq,
        },
    );
    let sum = add(&mut m, b, num, num);
    emit_void(&mut m, b, Op::Return { value: Some(sum) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "unary" kind=function params=(this, p1)
  bb B0 preds=[]:
    const v6 = (+((!(typeof p1)) === null)) ; v6
    return (v6 + v6)
"#;
    assert_eq!(got, want);
}

/// t20 — capture-consistent fallback naming (d-P7; dream-gate family
/// for-update-continue-1): unnamed lexenv slots get the cosmetic
/// `v{abs}_{slot}` fallback keyed by the frame's ABSOLUTE index in the
/// seeded chain, so a nested closure's `GetLexVar { level > 0 }` names
/// the SAME binding the owning ancestor's `PutLexVar` wrote. The legacy
/// relative `v{level}_{slot}` scheme only coincided when reader and
/// writer sat at the same depth — f19's `ldlexvar 2,1` (a `v0_1` write
/// in the ancestor) surfaced as an unassigned orphan ("v2_1 is not a
/// function").
#[test]
fn t20_capture_consistent_fallback() {
    let mut m = mk_module();
    // child (#0): own frame + reads of the grand/parent frames.
    let child = add_func_named(&mut m, "child");
    {
        let b = entry_of(&m, child);
        let _this = add_param(&mut m, child);
        let _ne = emit(&mut m, b, Op::NewLexEnv { num_vars: 1 });
        let c7 = load_number(&mut m, b, 7.0);
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: c7,
            },
        );
        let g1 = emit(&mut m, b, Op::GetLexVar { level: 2, slot: 1 });
        let g2 = emit(&mut m, b, Op::GetLexVar { level: 1, slot: 0 });
        let s = add(&mut m, b, g1, g2);
        emit_void(&mut m, b, Op::PopLexEnv);
        emit_void(&mut m, b, Op::Return { value: Some(s) });
    }
    // parent (#1): own frame, defines child.
    let parent = add_func_named(&mut m, "parent");
    {
        let b = entry_of(&m, parent);
        let _this = add_param(&mut m, parent);
        let _ne = emit(&mut m, b, Op::NewLexEnv { num_vars: 1 });
        let c20 = load_number(&mut m, b, 20.0);
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: c20,
            },
        );
        let df = emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: child,
                captures: vec![],
                length: 0,
            },
        );
        emit_void(&mut m, b, Op::PopLexEnv);
        emit_void(&mut m, b, Op::Return { value: Some(df) });
    }
    // grand (#2): two unnamed slots, defines parent.
    let grand = add_func_named(&mut m, "grand");
    {
        let b = entry_of(&m, grand);
        let _this = add_param(&mut m, grand);
        let _ne = emit(&mut m, b, Op::NewLexEnv { num_vars: 2 });
        let c10 = load_number(&mut m, b, 10.0);
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: c10,
            },
        );
        let c21 = load_number(&mut m, b, 21.0);
        emit_void(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 1,
                value: c21,
            },
        );
        let df = emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: parent,
                captures: vec![],
                length: 0,
            },
        );
        emit_void(&mut m, b, Op::PopLexEnv);
        emit_void(&mut m, b, Op::Return { value: Some(df) });
    }

    let got_grand = dump_func(&recover_func(&m, grand));
    let want_grand = r#"fn #2 "grand" kind=function params=(this)
  bb B2 preds=[]:
    scope-push [<unnamed>, <unnamed>]
    lex v0_0 = 10.0 /*L0#0*/
    lex v0_1 = 21.0 /*L0#1*/
    const parent = closure(fn#1 "parent" function captures=[]) ; v14
    scope-pop
    return parent
"#;
    assert_eq!(got_grand, want_grand);

    let got_parent = dump_func(&recover_func(&m, parent));
    let want_parent = r#"fn #1 "parent" kind=function params=(this)
  bb B1 preds=[]:
    scope-push [<unnamed>]
    lex v1_0 = 20.0 /*L0#0*/
    const child = closure(fn#0 "child" function captures=[]) ; v9
    scope-pop
    return child
"#;
    assert_eq!(got_parent, want_parent);

    // The fix's core: child's reads of the grand/parent frames name the
    // SAME bindings (`v0_1`, `v1_0`) the ancestors wrote — not the
    // legacy relative fallbacks (`v2_1`, `v1_0` at the wrong depth).
    let got_child = dump_func(&recover_func(&m, child));
    let want_child = r#"fn #0 "child" kind=function params=(this)
  bb B0 preds=[]:
    scope-push [<unnamed>]
    lex v2_0 = 7.0 /*L0#0*/
    const v5 = (v0_1 + v1_0) ; v5
    scope-pop
    return v5
"#;
    assert_eq!(got_child, want_child);
}
