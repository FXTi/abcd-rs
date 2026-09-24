//! Golden async-generator state-machine fold tests (d-P14 — the
//! AsyncGenerator counterpart of d-P11's generator fold and d-P13's
//! async fold, design/decompile.md §8 R4): the es2abc
//! `async function*` machinery (`CreateAsyncGeneratorObj` entry
//! protocol + per-yield pre-await + `AsyncGeneratorResolve` yield +
//! the three-way resume-mode dispatch + the
//! `AsyncGeneratorResolve(done=true)` completion + the catch-all
//! `AsyncGeneratorReject`) folds back into the source-level
//! `async function*` body.
//!
//! Vendor lowering model: es2panda
//! `compiler/function/asyncGeneratorFunctionBuilder.cpp`
//! (`Prepare`: `CreateAsyncGeneratorObj` + entry
//! `SuspendResumeExecution(undefined)`; `Yield`: `Await(value)` +
//! `AsyncYield` = `AsyncGeneratorResolve(gen, awaited, false)` +
//! resume pair, then the three-way dispatch — `RETURN(0)`: await the
//! resume value, `AsyncGeneratorResolve(gen, awaited, true)` + return;
//! `THROW(1)`: throw the resume value; `NEXT(2)`: the resumption value
//! is the yield's result; `DirectReturn`/`ImplicitReturn`/
//! `ExplicitReturn`; `CleanUp`: `AsyncGeneratorReject`) and
//! `compiler/function/functionBuilder.cpp` (`Await`,
//! `SuspendResumeExecution`, `resumeGenerator`, `HandleCompletion` —
//! the ASYNC_GENERATOR kind tests THROW only, no RETURN arm);
//! `enum class ResumeMode { RETURN=0, THROW=1, NEXT=2 }` in
//! `functionBuilder.h`; runtime
//! `ecmascript/interpreter/interpreter-inl.cpp`
//! `ASYNCGENERATORRESOLVE_V8_V8_V8` (v0 = generator, v1 = value,
//! v2 = done flag), `ecmascript/js_generator_object.h`
//! `GeneratorResumeMode`.
//!
//! IR note: the lift folds `asyncgeneratorresolve v0,v1,v2` to
//! `CreateIterResultObj { value: v0, done: v1 }` (v0.1 parity) — the
//! GENERATOR object lands in the iter-result's `value` slot and the
//! resolved value in the `done` slot; the actual done flag (v2) is not
//! modeled. The yield-point resolve's result is dead (the accumulator
//! is overwritten by the resumption pair) and drops at Stage A; the
//! completion resolves survive as `return { value: genobj, done: X }`
//! and fold to `return X` inside the gated machinery. These goldens
//! build the IR in exactly that lifted form.
//!
//! Shapes covered: the plain yield (the corpus `local/async-generator`
//! fixture shape), a source-level await inside the body plus a bound
//! yield result plus an explicit return, the per-site bail (a
//! sabotaged three-way dispatch keeps the whole site loud), and the
//! entry-gate bail (a genobj temp used outside the machinery keeps
//! EVERYTHING loud).
//!
//! The expected strings are STABLE emission forms — reviewed,
//! hand-written expectations, not snapshots.

mod common;

use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_ir::module::FunctionKind;
use abcd_ir::op::{CmpOp, UnOp};
use abcd_ir::{BlockId, Const, FuncId, Module, Op, ValueId};

use common::*;

/// Decompile and strip the two-line header comment.
fn decompiled(m: &Module) -> String {
    let d = decompile_module(m, &EmitOptions::default());
    let mut lines: Vec<&str> = d.text.lines().collect();
    assert!(lines.len() >= 2, "header missing:\n{}", d.text);
    let mut out = lines.split_off(2).join("\n");
    if !out.is_empty() {
        out.push('\n');
    }
    out
}

/// The pieces every es2abc async-generator function shares.
struct AGScaffold {
    genobj: ValueId,
    handler: BlockId,
    protected: Vec<BlockId>,
}

/// Begin an async-generator function: the hidden funcObj param, the
/// `CreateAsyncGeneratorObj` temp (lifted to `Op::CreateGenerator`),
/// and the entry protocol suspend (`Prepare`:
/// `SuspendGenerator(undefined)` + the dead resumption value — the
/// entry `GetResumeMode` result is dead and drops at Stage A). Call
/// [`finish_ag`] after the body blocks.
fn begin_ag(m: &mut Module, name: &str) -> (FuncId, BlockId, AGScaffold) {
    let f = add_func_kind(m, name, FunctionKind::AsyncGenerator);
    let entry = entry_of(m, f);
    let funcobj = add_param(m, f);
    let genobj = emit(m, entry, Op::CreateGenerator { func: funcobj });
    let undef = load_const(m, entry, Const::Undefined);
    emit(
        m,
        entry,
        Op::SuspendGenerator {
            genobj,
            value: undef,
        },
    );
    // The entry resumption value: dead (es2abc never reads it — the
    // first `next(v)` argument is dropped per spec); kept as a stmt.
    emit(m, entry, Op::ResumeGenerator { genobj });
    let handler = add_block(m, f);
    (
        f,
        entry,
        AGScaffold {
            genobj,
            handler,
            protected: vec![entry],
        },
    )
}

/// Wire the catch-all rejection try region (`CleanUp`:
/// `AsyncGeneratorReject` — lifted to `Op::AsyncReject` — + return)
/// over the body blocks.
fn finish_ag(m: &mut Module, f: FuncId, sc: &AGScaffold) {
    let exc = add_exception_param(m, sc.handler);
    let rej = emit(
        m,
        sc.handler,
        Op::AsyncReject {
            funcobj: sc.genobj,
            value: exc,
        },
    );
    emit_void(m, sc.handler, Op::Return { value: Some(rej) });
    let mut protected = sc.protected.clone();
    protected.retain(|b| *b != sc.handler);
    add_try(m, f, protected, sc.handler, exc);
}

/// An `Await` (`functionBuilder.cpp`): `AsyncFunctionAwaitUncaught` +
/// `SuspendGenerator` + the resumption pair; returns (resume, mode).
fn ag_await(m: &mut Module, b: BlockId, sc: &AGScaffold, v: ValueId) -> (ValueId, ValueId) {
    let aw = emit(
        m,
        b,
        Op::AwaitUncaught {
            funcobj: sc.genobj,
            value: v,
        },
    );
    emit(
        m,
        b,
        Op::SuspendGenerator {
            genobj: sc.genobj,
            value: aw,
        },
    );
    let resume = emit(m, b, Op::ResumeGenerator { genobj: sc.genobj });
    let mode = emit(m, b, Op::GetResumeMode { genobj: sc.genobj });
    (resume, mode)
}

/// The `HandleCompletion` THROW-only dispatch (the ASYNC_GENERATOR
/// kind emits no RETURN arm here): `if (!(mode == 1)) cont else throw
/// resume`. Returns the continuation block.
fn ag_throw_dispatch(
    m: &mut Module,
    f: FuncId,
    sc: &mut AGScaffold,
    b: BlockId,
    mode: ValueId,
    resume: ValueId,
) -> BlockId {
    ag_throw_dispatch_as(m, f, sc, b, mode, resume, resume)
}

/// [`ag_throw_dispatch`] with a chosen thrown value (the sabotage hook
/// for the per-site bail golden).
fn ag_throw_dispatch_as(
    m: &mut Module,
    f: FuncId,
    sc: &mut AGScaffold,
    b: BlockId,
    mode: ValueId,
    thrown: ValueId,
    _resume: ValueId,
) -> BlockId {
    let cont = add_block(m, f);
    let throw_b = add_block(m, f);
    let one = load_number(m, b, 1.0);
    let eq = emit(
        m,
        b,
        Op::Compare {
            op: CmpOp::Eq,
            left: mode,
            right: one,
        },
    );
    let t = emit(
        m,
        b,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq,
        },
    );
    emit_void(
        m,
        b,
        Op::CondBranch {
            cond: t,
            true_dest: cont,
            false_dest: throw_b,
        },
    );
    emit_void(m, throw_b, Op::Throw { value: thrown });
    emit_void(m, throw_b, Op::Unreachable);
    link(m, b, cont);
    link(m, b, throw_b);
    sc.protected.extend([throw_b]);
    cont
}

/// The completion (`DirectReturn`): `AsyncGeneratorResolve(gen, v,
/// true)` + return — in the lifted form `return { value: genobj,
/// done: v }` (see the module doc IR note).
fn ag_completion(m: &mut Module, b: BlockId, sc: &AGScaffold, v: ValueId) {
    let iro = emit(
        m,
        b,
        Op::CreateIterResultObj {
            value: sc.genobj,
            done: v,
        },
    );
    emit_void(m, b, Op::Return { value: Some(iro) });
}

/// A full source `yield v` (`AsyncGeneratorFunctionBuilder::Yield`):
/// the pre-yield `Await(v)` + THROW dispatch, then `AsyncYield` (the
/// dead yield-point resolve + the resumption pair) and the three-way
/// dispatch. Returns (the yield's resumption value, the NEXT
/// continuation block).
fn ag_yield(
    m: &mut Module,
    f: FuncId,
    sc: &mut AGScaffold,
    b: BlockId,
    v: ValueId,
) -> (ValueId, BlockId) {
    // 27.6.3.8.5 Set value to ? Await(value).
    let (r, mode) = ag_await(m, b, sc, v);
    let cont = ag_throw_dispatch(m, f, sc, b, mode, r);
    sc.protected.push(cont);

    // AsyncYield: the yield-point `AsyncGeneratorResolve(gen, awaited,
    // false)` — its result is dead and drops at Stage A (the corpus
    // fixtures' trees carry no trace of it; emitted here for parity).
    let _dead = emit(
        m,
        cont,
        Op::CreateIterResultObj {
            value: sc.genobj,
            done: r,
        },
    );
    let ry = emit(m, cont, Op::ResumeGenerator { genobj: sc.genobj });
    let my = emit(m, cont, Op::GetResumeMode { genobj: sc.genobj });

    // The three-way dispatch: `if (!(my == RETURN)) notReturn else
    // <return arm>`; notReturn: `if (!(my == THROW)) next else throw
    // ry`.
    let ret_arm = add_block(m, f);
    let not_ret = add_block(m, f);
    let zero = load_number(m, cont, 0.0);
    let eq0 = emit(
        m,
        cont,
        Op::Compare {
            op: CmpOp::Eq,
            left: my,
            right: zero,
        },
    );
    let t0 = emit(
        m,
        cont,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq0,
        },
    );
    emit_void(
        m,
        cont,
        Op::CondBranch {
            cond: t0,
            true_dest: not_ret,
            false_dest: ret_arm,
        },
    );
    link(m, cont, not_ret);
    link(m, cont, ret_arm);

    // RETURN arm: await the resumption value, then
    // `AsyncGeneratorResolve(gen, awaited, true)` + return.
    let (rr, rmode) = ag_await(m, ret_arm, sc, ry);
    let ret_done = ag_throw_dispatch(m, f, sc, ret_arm, rmode, rr);
    sc.protected.push(ret_done);
    ag_completion(m, ret_done, sc, rr);

    // THROW arm / NEXT fallthrough.
    let next = add_block(m, f);
    let throw_b = add_block(m, f);
    let one = load_number(m, not_ret, 1.0);
    let eq1 = emit(
        m,
        not_ret,
        Op::Compare {
            op: CmpOp::Eq,
            left: my,
            right: one,
        },
    );
    let t1 = emit(
        m,
        not_ret,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq1,
        },
    );
    emit_void(
        m,
        not_ret,
        Op::CondBranch {
            cond: t1,
            true_dest: next,
            false_dest: throw_b,
        },
    );
    emit_void(m, throw_b, Op::Throw { value: ry });
    emit_void(m, throw_b, Op::Unreachable);
    link(m, not_ret, next);
    link(m, not_ret, throw_b);
    sc.protected.extend([ret_arm, not_ret, throw_b]);
    (ry, next)
}

/// ag01 — the plain async generator yielding (the corpus
/// `local/async-generator` fixture shape): `async function* g() {
/// yield 1; }`. The entry protocol suspend is elided, the yield
/// machinery folds to a plain `yield`, the implicit completion folds
/// to `return undefined`, and the catch-all rejection wrapper
/// dissolves.
#[test]
fn ag01_plain_async_generator_yield() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_ag(&mut m, "g");

    let one = load_number(&mut m, entry, 1.0);
    let (_ry, next) = ag_yield(&mut m, f, &mut sc, entry, one);
    // The body falls off the end: the implicit completion
    // (`ImplicitReturn` → `DirectReturn` of undefined).
    let undef = load_const(&mut m, next, Const::Undefined);
    ag_completion(&mut m, next, &sc, undef);
    sc.protected.push(next);
    finish_ag(&mut m, f, &sc);

    let text = decompiled(&m);
    expect(
        &text,
        "async function* g() {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  yield 1.0;\n  return undefined;\n}\n",
    );
}

/// ag02 — a source-level `await` inside the body, a bound yield
/// result, and an explicit return: `async function* h(p1) {
/// const a = await p1; const x = yield a; return x; }` (modulo the
/// bound temps). The explicit return lowers to an await of the value
/// (`ExplicitReturn`: `AsyncFunctionAwait` + resumption pair — no
/// `HandleCompletion`) + the `done=true` resolve; the fold dissolves
/// both into `return x`.
#[test]
fn ag02_await_bound_yield_explicit_return() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_ag(&mut m, "h");
    let p1 = add_param(&mut m, f);

    // `const a = await p1;` — a source-level await (THROW-only
    // dispatch; the ASYNC_GENERATOR `HandleCompletion`).
    let (r1, mode1) = ag_await(&mut m, entry, &sc, p1);
    let c1 = ag_throw_dispatch(&mut m, f, &mut sc, entry, mode1, r1);
    sc.protected.push(c1);

    // `const x = yield a;` — the full yield machinery; the NEXT
    // continuation reads the resumption value.
    let (ry, next) = ag_yield(&mut m, f, &mut sc, c1, r1);
    sc.protected.push(next);

    // `return x;` — `ExplicitReturn`: await the value (no
    // `HandleCompletion`; the mode result is dead and drops) + the
    // `done=true` resolve + return.
    let rr = emit(
        &mut m,
        next,
        Op::AwaitUncaught {
            funcobj: sc.genobj,
            value: ry,
        },
    );
    emit(
        &mut m,
        next,
        Op::SuspendGenerator {
            genobj: sc.genobj,
            value: rr,
        },
    );
    let rv = emit(&mut m, next, Op::ResumeGenerator { genobj: sc.genobj });
    ag_completion(&mut m, next, &sc, rv);
    finish_ag(&mut m, f, &sc);

    let text = decompiled(&m);
    expect(
        &text,
        "async function* h(p1) {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  const v8 = await p1;\n  const v21 = yield v8;\n  return v21;\n}\n",
    );
}

/// ag03 — the per-site bail: the three-way dispatch's THROW arm throws
/// the MODE temp, not the resumption value — not the vendor
/// `HandleCompletion` shape. The entry protocol still elides (it is
/// independently sound), but the yield site — pre-yield await
/// included — keeps its loud fallbacks: the pre-yield await must NOT
/// fold to a bare `await` (that would drop the yield entirely).
#[test]
fn ag03_dispatch_mismatch_keeps_site_loud() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_ag(&mut m, "odd");

    let one = load_number(&mut m, entry, 1.0);
    // The pre-yield await.
    let (r, mode) = ag_await(&mut m, entry, &sc, one);
    let cont = ag_throw_dispatch(&mut m, f, &mut sc, entry, mode, r);
    sc.protected.push(cont);
    // The yield-point resumption pair.
    let _dead = emit(
        &mut m,
        cont,
        Op::CreateIterResultObj {
            value: sc.genobj,
            done: r,
        },
    );
    let ry = emit(&mut m, cont, Op::ResumeGenerator { genobj: sc.genobj });
    let my = emit(&mut m, cont, Op::GetResumeMode { genobj: sc.genobj });
    // The three-way dispatch — sabotaged: the THROW arm throws the
    // MODE temp.
    let ret_arm = add_block(&mut m, f);
    let not_ret = add_block(&mut m, f);
    let zero = load_number(&mut m, cont, 0.0);
    let eq0 = emit(
        &mut m,
        cont,
        Op::Compare {
            op: CmpOp::Eq,
            left: my,
            right: zero,
        },
    );
    let t0 = emit(
        &mut m,
        cont,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq0,
        },
    );
    emit_void(
        &mut m,
        cont,
        Op::CondBranch {
            cond: t0,
            true_dest: not_ret,
            false_dest: ret_arm,
        },
    );
    link(&mut m, cont, not_ret);
    link(&mut m, cont, ret_arm);
    let (rr, rmode) = ag_await(&mut m, ret_arm, &sc, ry);
    let ret_done = ag_throw_dispatch(&mut m, f, &mut sc, ret_arm, rmode, rr);
    sc.protected.push(ret_done);
    ag_completion(&mut m, ret_done, &sc, rr);
    let next = add_block(&mut m, f);
    let throw_b = add_block(&mut m, f);
    let one2 = load_number(&mut m, not_ret, 1.0);
    let eq1 = emit(
        &mut m,
        not_ret,
        Op::Compare {
            op: CmpOp::Eq,
            left: my,
            right: one2,
        },
    );
    let t1 = emit(
        &mut m,
        not_ret,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq1,
        },
    );
    emit_void(
        &mut m,
        not_ret,
        Op::CondBranch {
            cond: t1,
            true_dest: next,
            false_dest: throw_b,
        },
    );
    emit_void(&mut m, throw_b, Op::Throw { value: my }); // sabotage
    emit_void(&mut m, throw_b, Op::Unreachable);
    link(&mut m, not_ret, next);
    link(&mut m, not_ret, throw_b);
    sc.protected.extend([ret_arm, not_ret, throw_b]);
    let undef = load_const(&mut m, next, Const::Undefined);
    ag_completion(&mut m, next, &sc, undef);
    sc.protected.push(next);
    finish_ag(&mut m, f, &sc);

    let text = decompiled(&m);
    // The sabotaged three-way keeps the whole yield site loud: the
    // entry protocol still elides (independently sound) and the
    // completions still fold, but the pre-yield await is NOT folded
    // to a bare `await` (the yield-point guard — folding it would
    // silently drop the yield), and the resumption pair + dispatch
    // keep their hard fallbacks. The RETURN arm's inner await folds
    // independently (it is a valid d-P13 await site).
    expect(
        &text,
        "async function* odd() {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  const v1 = /*CreateGenerator plumbing*/ this;\n  const v6 = await 1.0;\n  yield v6;\n  const v8 = /*hard-fallback ResumeGenerator (generator driver, R4)*/ v1;\n  if (!(1.0 == /*hard-fallback GetResumeMode (generator driver, R4)*/ v1)) {\n    const v14 = /*hard-fallback ResumeGenerator (generator driver, R4)*/ v1;\n    const v15 = /*hard-fallback GetResumeMode (generator driver, R4)*/ v1;\n    switch (v15) {\n    case 0.0: {\n        const v21 = await v14;\n        return v21;\n      }\n    case 1.0: {\n        throw v15;\n        /* unreachable */\n      }\n    default: {\n        return undefined;\n      }\n    }\n  } else {\n    throw v8;\n    /* unreachable */\n  }\n}\n",
    );
}

/// ag04 — the entry gate: the genobj temp has a NON-machinery use
/// (here it is itself the awaited value). Not the vendor shape: the
/// WHOLE function keeps its documented fallbacks — all-or-nothing per
/// function, never a silent half-fold.
#[test]
fn ag04_entry_gate_bail_keeps_fallbacks() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_ag(&mut m, "weird");

    // Sabotage: yield the genobj itself — a use outside the
    // suspend/resume machinery.
    let (r, mode) = ag_await(&mut m, entry, &sc, sc.genobj);
    let cont = ag_throw_dispatch(&mut m, f, &mut sc, entry, mode, r);
    sc.protected.push(cont);
    let undef = load_const(&mut m, cont, Const::Undefined);
    ag_completion(&mut m, cont, &sc, undef);
    finish_ag(&mut m, f, &sc);

    let text = decompiled(&m);
    // The gate refuses the whole function: entry, await machinery,
    // dispatch, and completion all keep their documented fallbacks.
    expect(
        &text,
        "async function* weird() {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  const v1 = /*CreateGenerator plumbing*/ this;\n  yield undefined;\n  /*hard-fallback ResumeGenerator (generator driver, R4)*/ v1;\n  const v5 = await v1;\n  yield v5;\n  const v7 = /*hard-fallback ResumeGenerator (generator driver, R4)*/ v1;\n  if (!(1.0 == /*hard-fallback GetResumeMode (generator driver, R4)*/ v1)) {\n    return { value: v1, done: undefined } /*iter-result*/;\n  } else {\n    throw v7;\n    /* unreachable */\n  }\n}\n",
    );
}

/// Reviewed-expectation helper: on mismatch, print the actual text in
/// a paste-ready form.
fn expect(actual: &str, expected: &str) {
    if actual != expected {
        eprintln!("──── ACTUAL ────\n{actual}────");
        panic!("golden mismatch (see actual output above)");
    }
}
