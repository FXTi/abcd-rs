//! Golden async state-machine fold tests (N68 remainder — the async
//! counterpart of d-P11's generator fold, design/decompile.md §8 R4):
//! the es2abc async-body machinery (`AsyncFunctionEnter` entry protocol
//! + per-await `AsyncFunctionAwaitUncaught` + `SuspendGenerator` +
//! the `ResumeGenerator`/`GetResumeMode` completion pair + the
//! `mode == THROW → throw` dispatch) folds back into the source-level
//! `await` control flow of a plain `async function` body.
//!
//! Vendor lowering model: es2panda
//! `compiler/function/asyncFunctionBuilder.cpp` (`Prepare`:
//! `AsyncFunctionEnter` + catch-all `AsyncFunctionReject`;
//! `DirectReturn`: `AsyncFunctionResolve` + return) and
//! `compiler/function/functionBuilder.cpp` (`Await`:
//! `AsyncFunctionAwait` + `SuspendResumeExecution` + `HandleCompletion`
//! — the ASYNC kind emits ONLY the `ResumeMode::THROW` test, no RETURN
//! arm; `enum class ResumeMode { RETURN=0, THROW=1, NEXT=2 }` in
//! `functionBuilder.h`). Runtime: interpreter-inl.cpp
//! `ASYNCFUNCTIONAWAITUNCAUGHT_V8` :5357-5366 (awaits the acc value),
//! `SUSPENDGENERATOR_V8` :5279 (suspends with the acc value).
//!
//! Shapes covered: the plain await (`return await x`), the dead resume
//! value (`await x;` as a statement), an await inside a loop, chained
//! awaits (the resumption value feeds the next await), the entry-gate
//! bail (a funcobj temp used outside the machinery keeps EVERYTHING
//! loud), the per-site bail (a dispatch whose THROW arm throws the
//! wrong temp keeps that site loud), and the async-generator bail
//! (`AsyncGenerator` kind carries no `AsyncFunctionEnter` — its
//! yield machinery is d-P14's separate fold, so THIS fold is a no-op
//! for it).
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

/// The pieces every es2abc async function shares.
struct AsyncScaffold {
    funcobj: ValueId,
    handler: BlockId,
    protected: Vec<BlockId>,
}

/// Begin an async function: the `AsyncFunctionEnter` entry protocol
/// (`AsyncFunctionBuilder::Prepare`) and the catch-all rejection
/// handler (`CleanUp`). Call [`finish_async`] after the body blocks.
fn begin_async(m: &mut Module, name: &str) -> (FuncId, BlockId, AsyncScaffold) {
    let f = add_func_kind(m, name, FunctionKind::Async);
    let entry = entry_of(m, f);
    let funcobj = emit(m, entry, Op::AsyncFunctionEnter);
    let handler = add_block(m, f);
    (
        f,
        entry,
        AsyncScaffold {
            funcobj,
            handler,
            protected: vec![entry],
        },
    )
}

/// Wire the catch-all rejection try region (`AsyncFunctionReject` +
/// return) over the body blocks.
fn finish_async(m: &mut Module, f: FuncId, sc: &AsyncScaffold) {
    let exc = add_exception_param(m, sc.handler);
    let rej = emit(
        m,
        sc.handler,
        Op::AsyncReject {
            funcobj: sc.funcobj,
            value: exc,
        },
    );
    emit_void(m, sc.handler, Op::Return { value: Some(rej) });
    let mut protected = sc.protected.clone();
    protected.retain(|b| *b != sc.handler);
    add_try(m, f, protected, sc.handler, exc);
}

/// A real await point (`FunctionBuilder::Await`):
/// `AsyncFunctionAwaitUncaught(funcobj, acc=v)` + `SuspendGenerator`
/// + the completion pair; returns (resume, mode).
fn await_point(m: &mut Module, b: BlockId, sc: &AsyncScaffold, v: ValueId) -> (ValueId, ValueId) {
    let aw = emit(
        m,
        b,
        Op::AwaitUncaught {
            funcobj: sc.funcobj,
            value: v,
        },
    );
    emit(
        m,
        b,
        Op::SuspendGenerator {
            genobj: sc.funcobj,
            value: aw,
        },
    );
    let resume = emit(m, b, Op::ResumeGenerator { genobj: sc.funcobj });
    let mode = emit(m, b, Op::GetResumeMode { genobj: sc.funcobj });
    (resume, mode)
}

/// The async `HandleCompletion` dispatch on `mode` with an inline
/// immediate: THROW(1) check only (the ASYNC builder kind emits no
/// RETURN arm). Returns the continuation block.
fn async_dispatch(
    m: &mut Module,
    f: FuncId,
    sc: &mut AsyncScaffold,
    b: BlockId,
    mode: ValueId,
    resume: ValueId,
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
    emit_void(m, throw_b, Op::Throw { value: resume });
    emit_void(m, throw_b, Op::Unreachable);
    link(m, b, cont);
    link(m, b, throw_b);
    sc.protected.extend([b, throw_b]);
    cont
}

/// The async completion (`AsyncFunctionBuilder::DirectReturn`):
/// `AsyncFunctionResolve(funcobj, acc=v)` + return.
fn async_return(m: &mut Module, b: BlockId, sc: &AsyncScaffold, v: ValueId) {
    let res = emit(
        m,
        b,
        Op::AsyncResolve {
            funcobj: sc.funcobj,
            value: v,
        },
    );
    emit_void(m, b, Op::Return { value: Some(res) });
}

/// a01 — the plain async function: `async function value(p1) {
/// return await p1; }`. The suspend/resume/mode machinery dissolves;
/// the resumption value binds at the await site; the folded
/// `AsyncResolve` completion (d-P12) returns it; the catch-all
/// rejection wrapper dissolves.
#[test]
fn a01_plain_async_await_folds() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_async(&mut m, "value");
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);

    let (r, mode) = await_point(&mut m, entry, &sc, p1);
    let cont = async_dispatch(&mut m, f, &mut sc, entry, mode, r);
    async_return(&mut m, cont, &sc, r);
    sc.protected.push(cont);
    finish_async(&mut m, f, &sc);

    let text = decompiled(&m);
    expect(
        &text,
        "async function value(p1) {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  /* elided AsyncFunctionEnter: async-machinery entry; recognized and elided inside `async function` emission (§5 row 72) */\n  const v5 = await p1;\n  return v5;\n}\n",
    );
}

/// a02 — a dead resumption value: `async function drop(p1) { await p1;
/// }` — the await is a statement, the completion resolves `undefined`.
#[test]
fn a02_await_statement_dead_resume() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_async(&mut m, "drop");
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);

    let (r, mode) = await_point(&mut m, entry, &sc, p1);
    let cont = async_dispatch(&mut m, f, &mut sc, entry, mode, r);
    let undef = load_const(&mut m, cont, Const::Undefined);
    async_return(&mut m, cont, &sc, undef);
    sc.protected.push(cont);
    finish_async(&mut m, f, &sc);

    let text = decompiled(&m);
    expect(
        &text,
        "async function drop(p1) {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  /* elided AsyncFunctionEnter: async-machinery entry; recognized and elided inside `async function` emission (§5 row 72) */\n  await p1;\n  return undefined;\n}\n",
    );
}

/// a03 — an await inside a loop body folds the same way:
/// `async function f() { while (true) { await 2; } }`.
#[test]
fn a03_await_in_loop() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_async(&mut m, "f");
    let _this = add_param(&mut m, f);

    // `while (true)` header.
    let head = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    emit_void(&mut m, entry, Op::Branch { dest: head });
    link(&mut m, entry, head);
    let t = load_const(&mut m, head, Const::Bool(true));
    let cond = emit(
        &mut m,
        head,
        Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: t,
        },
    );
    emit_void(
        &mut m,
        head,
        Op::CondBranch {
            cond,
            true_dest: body,
            false_dest: exit,
        },
    );
    link(&mut m, head, body);
    link(&mut m, head, exit);

    let two = load_number(&mut m, body, 2.0);
    let (r, mode) = await_point(&mut m, body, &sc, two);
    let cont = async_dispatch(&mut m, f, &mut sc, body, mode, r);
    emit_void(&mut m, cont, Op::Branch { dest: head });
    link(&mut m, cont, head);

    let undef = load_const(&mut m, exit, Const::Undefined);
    async_return(&mut m, exit, &sc, undef);
    sc.protected.extend([head, body, cont, exit]);
    finish_async(&mut m, f, &sc);

    let text = decompiled(&m);
    expect(
        &text,
        "async function f() {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  /* elided AsyncFunctionEnter: async-machinery entry; recognized and elided inside `async function` emission (§5 row 72) */\n  while (true) {\n    await 2.0;\n    continue;\n  }\n  return undefined;\n}\n",
    );
}

/// a04 — chained awaits: the first resumption value feeds the second
/// await: `async function f(p1) { const a = await p1; return await a; }`
/// (modulo the bound temps).
#[test]
fn a04_chained_awaits() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_async(&mut m, "f");
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);

    let (r1, mode1) = await_point(&mut m, entry, &sc, p1);
    let cont1 = async_dispatch(&mut m, f, &mut sc, entry, mode1, r1);
    let (r2, mode2) = await_point(&mut m, cont1, &sc, r1);
    let cont2 = async_dispatch(&mut m, f, &mut sc, cont1, mode2, r2);
    async_return(&mut m, cont2, &sc, r2);
    sc.protected.extend([cont1, cont2]);
    finish_async(&mut m, f, &sc);

    let text = decompiled(&m);
    expect(
        &text,
        "async function f(p1) {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  /* elided AsyncFunctionEnter: async-machinery entry; recognized and elided inside `async function` emission (§5 row 72) */\n  const v5 = await p1;\n  const v12 = await v5;\n  return v12;\n}\n",
    );
}

/// a05 — the entry gate: the funcobj temp has a NON-machinery use
/// (here it is itself the awaited value). Not the vendor shape: the
/// WHOLE function keeps its documented fallbacks — all-or-nothing per
/// function, never a silent half-fold.
#[test]
fn a05_entry_gate_bail_keeps_fallbacks() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_async(&mut m, "weird");
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);

    // Sabotage: await the funcobj itself — a use outside the
    // suspend/resume machinery.
    let (r, mode) = await_point(&mut m, entry, &sc, sc.funcobj);
    let cont = async_dispatch(&mut m, f, &mut sc, entry, mode, r);
    async_return(&mut m, cont, &sc, p1);
    sc.protected.push(cont);
    finish_async(&mut m, f, &sc);

    let text = decompiled(&m);
    expect(
        &text,
        "async function weird(p1) {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  /* elided AsyncFunctionEnter: async-machinery entry; recognized and elided inside `async function` emission (§5 row 72) */\n  const v0 = undefined /*fallback AsyncFunctionEnter: async-context value used after elided AsyncFunctionEnter*/;\n  const v3 = await v0;\n  /*async-machinery suspend (R4; not a source yield)*/ v3;\n  const v5 = /*hard-fallback ResumeGenerator (generator driver, R4)*/ v0;\n  if (!(1.0 == /*hard-fallback GetResumeMode (generator driver, R4)*/ v0)) {\n    return p1;\n  } else {\n    throw v5;\n    /* unreachable */\n  }\n}\n",
    );
}

/// a06 — the per-site bail: the dispatch's THROW arm throws the MODE
/// temp, not the resumption value — not the vendor `HandleCompletion`
/// shape. The site keeps its loud fallbacks (the funcobj's uses are
/// still machinery-only, so the gate holds; the SITE refuses).
#[test]
fn a06_dispatch_mismatch_keeps_site_loud() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_async(&mut m, "odd");
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);

    let (r, mode) = await_point(&mut m, entry, &sc, p1);
    // Sabotage: throw the mode temp instead of the resume value.
    let cont = add_block(&mut m, f);
    let throw_b = add_block(&mut m, f);
    let one = load_number(&mut m, entry, 1.0);
    let eq = emit(
        &mut m,
        entry,
        Op::Compare {
            op: CmpOp::Eq,
            left: mode,
            right: one,
        },
    );
    let t = emit(
        &mut m,
        entry,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: t,
            true_dest: cont,
            false_dest: throw_b,
        },
    );
    emit_void(&mut m, throw_b, Op::Throw { value: mode });
    emit_void(&mut m, throw_b, Op::Unreachable);
    link(&mut m, entry, cont);
    link(&mut m, entry, throw_b);
    sc.protected.extend([throw_b]);
    async_return(&mut m, cont, &sc, r);
    sc.protected.push(cont);
    finish_async(&mut m, f, &sc);

    let text = decompiled(&m);
    expect(
        &text,
        "async function odd(p1) {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  /* elided AsyncFunctionEnter: async-machinery entry; recognized and elided inside `async function` emission (§5 row 72) */\n  const v0 = undefined /*fallback AsyncFunctionEnter: async-context value used after elided AsyncFunctionEnter*/;\n  const v3 = await p1;\n  /*async-machinery suspend (R4; not a source yield)*/ v3;\n  const v5 = /*hard-fallback ResumeGenerator (generator driver, R4)*/ v0;\n  const v6 = /*hard-fallback GetResumeMode (generator driver, R4)*/ v0;\n  switch (v6) {\n  case 1.0: {\n      throw v6;\n      /* unreachable */\n    }\n  default: {\n      return v5;\n    }\n  }\n}\n",
    );
}

/// a07 — the async-generator no-op: `FunctionKind::AsyncGenerator`
/// carries NO `AsyncFunctionEnter` (its entry protocol is the
/// generator `CreateGeneratorObj` + the AsyncGeneratorResolve/yield
/// machinery — d-P14's [`async_generator_machine_fold`] owns it; its
/// own entry gate also refuses this entry-suspend-less shape, so the
/// documented fallbacks stay). THIS fold's entry gate refuses the
/// whole function.
#[test]
fn a07_async_generator_kind_bails() {
    let mut m = mk_module();
    let f = add_func_kind(&mut m, "g", FunctionKind::AsyncGenerator);
    let entry = entry_of(&mut m, f);
    let funcobj = add_param(&mut m, f);
    let genobj = emit(&mut m, entry, Op::CreateGenerator { func: funcobj });

    // An await-shaped suspend/resume site on the CreateGenerator
    // funcobj — the async-generator lowering's per-yield await.
    let one = load_number(&mut m, entry, 1.0);
    let aw = emit(
        &mut m,
        entry,
        Op::AwaitUncaught {
            funcobj: genobj,
            value: one,
        },
    );
    emit(&mut m, entry, Op::SuspendGenerator { genobj, value: aw });
    let r = emit(&mut m, entry, Op::ResumeGenerator { genobj });
    let mode = emit(&mut m, entry, Op::GetResumeMode { genobj });
    let cont = add_block(&mut m, f);
    let throw_b = add_block(&mut m, f);
    let eq = emit(
        &mut m,
        entry,
        Op::Compare {
            op: CmpOp::Eq,
            left: mode,
            right: one,
        },
    );
    let t = emit(
        &mut m,
        entry,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: t,
            true_dest: cont,
            false_dest: throw_b,
        },
    );
    emit_void(&mut m, throw_b, Op::Throw { value: r });
    emit_void(&mut m, throw_b, Op::Unreachable);
    link(&mut m, entry, cont);
    link(&mut m, entry, throw_b);
    emit_void(&mut m, cont, Op::Return { value: Some(r) });

    let text = decompiled(&m);
    expect(
        &text,
        "async function* g() {\n  const v1 = /*CreateGenerator plumbing*/ this;\n  const v2 = 1.0;\n  const v3 = await v2;\n  yield v3;\n  const v5 = /*hard-fallback ResumeGenerator (generator driver, R4)*/ v1;\n  if (!(v2 == /*hard-fallback GetResumeMode (generator driver, R4)*/ v1)) {\n    return v5;\n  } else {\n    throw v5;\n    /* unreachable */\n  }\n}\n",
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
