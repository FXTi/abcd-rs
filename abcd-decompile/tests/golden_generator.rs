//! Golden generator/async driver-fold tests (d-P11, R4 —
//! design/decompile.md §8): the es2abc generator state machine
//! (`CreateGenerator` + entry `SuspendGenerator(undefined)` + per-yield
//! `CreateIterResultObj(v, false)` + the `ResumeGenerator`/
//! `GetResumeMode` completion pair + the `mode == RETURN → return` /
//! `mode == THROW → throw` dispatch) folds back into a plain
//! `function*` body.
//!
//! Vendor lowering model: es2panda
//! `compiler/function/generatorFunctionBuilder.cpp` (`Prepare`/`Yield`/
//! `CleanUp`) + `compiler/function/functionBuilder.cpp`
//! (`SuspendResumeExecution`, `resumeGenerator`, `HandleCompletion`);
//! runtime mode enum `ecmascript/js_generator_object.h`
//! `GeneratorResumeMode { RETURN=0, THROW=1, NEXT=2 }`.
//!
//! Shapes covered: the baseline/debug-info profile form (inline
//! immediates), the optimized profile form (mode immediates
//! materialized as shared const temps), a used resumption value
//! (`x = yield v`), a yield inside a loop, the entry-gate bail (a
//! malformed entry dispatch keeps ALL machinery as documented
//! fallbacks), and the async honesty floor (IR gap G6: the modern
//! `asyncfunction*` bytecodes carry the value in the accumulator,
//! which the lift does not model — the async machinery stays loud).
//!
//! The expected strings are STABLE emission forms — reviewed,
//! hand-written expectations, not snapshots.

mod common;

use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_ir::module::FunctionKind;
use abcd_ir::op::{BinOp, CmpOp, UnOp};
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

/// The pieces every es2abc generator function shares.
struct GenScaffold {
    genobj: ValueId,
    handler: BlockId,
    protected: Vec<BlockId>,
}

/// Begin a generator function: the funcobj hidden param, the
/// `CreateGenerator` temp, and the catch-all rethrow handler
/// (`GeneratorFunctionBuilder::CleanUp`). Call [`finish_gen`] after
/// building the body blocks.
fn begin_gen(m: &mut Module, name: &str) -> (FuncId, BlockId, GenScaffold) {
    let f = add_func_kind(m, name, FunctionKind::Generator);
    let entry = entry_of(m, f);
    let funcobj = add_param(m, f);
    let genobj = emit(m, entry, Op::CreateGenerator { func: funcobj });
    let handler = add_block(m, f);
    (
        f,
        entry,
        GenScaffold {
            genobj,
            handler,
            protected: Vec::new(),
        },
    )
}

/// Wire the catch-all rethrow try region over the body blocks.
fn finish_gen(m: &mut Module, f: FuncId, sc: &GenScaffold) {
    let exc = add_exception_param(m, sc.handler);
    emit_void(m, sc.handler, Op::Throw { value: exc });
    let mut protected = sc.protected.clone();
    // The handler itself is not protected.
    protected.retain(|b| *b != sc.handler);
    add_try(m, f, protected, sc.handler, exc);
}

/// The entry protocol suspend (`Prepare`): `SuspendGenerator(genobj,
/// undefined)` + the completion pair; returns (resume, mode).
fn entry_suspend(m: &mut Module, b: BlockId, sc: &GenScaffold) -> (ValueId, ValueId) {
    let undef = load_const(m, b, Const::Undefined);
    emit(
        m,
        b,
        Op::SuspendGenerator {
            genobj: sc.genobj,
            value: undef,
        },
    );
    let resume = emit(m, b, Op::ResumeGenerator { genobj: sc.genobj });
    let mode = emit(m, b, Op::GetResumeMode { genobj: sc.genobj });
    (resume, mode)
}

/// A real yield point (`Yield`): `CreateIterResultObject(v, false)` +
/// suspend + the completion pair; returns (resume, mode).
fn yield_point(m: &mut Module, b: BlockId, sc: &GenScaffold, v: ValueId) -> (ValueId, ValueId) {
    let f = load_const(m, b, Const::Bool(false));
    let iro = emit(m, b, Op::CreateIterResultObj { value: v, done: f });
    emit(
        m,
        b,
        Op::SuspendGenerator {
            genobj: sc.genobj,
            value: iro,
        },
    );
    let resume = emit(m, b, Op::ResumeGenerator { genobj: sc.genobj });
    let mode = emit(m, b, Op::GetResumeMode { genobj: sc.genobj });
    (resume, mode)
}

/// The `HandleCompletion` dispatch on `mode` with inline immediates
/// (the baseline/debug-info profile shape): allocates the two case-arm
/// blocks (return-resume / throw-resume) and returns the continuation
/// block. `zero`/`one` are loaded fresh in the test block.
fn dispatch_inline(
    m: &mut Module,
    f: FuncId,
    sc: &mut GenScaffold,
    b: BlockId,
    mode: ValueId,
    resume: ValueId,
) -> BlockId {
    let cont = add_block(m, f);
    let ret_b = add_block(m, f);
    let throw_b = add_block(m, f);
    let mid = add_block(m, f);

    let zero = load_number(m, b, 0.0);
    let eq0 = emit(
        m,
        b,
        Op::Compare {
            op: CmpOp::Eq,
            left: mode,
            right: zero,
        },
    );
    let t0 = emit(
        m,
        b,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq0,
        },
    );
    emit_void(
        m,
        b,
        Op::CondBranch {
            cond: t0,
            true_dest: mid,
            false_dest: ret_b,
        },
    );
    let one = load_number(m, mid, 1.0);
    let eq1 = emit(
        m,
        mid,
        Op::Compare {
            op: CmpOp::Eq,
            left: mode,
            right: one,
        },
    );
    let t1 = emit(
        m,
        mid,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq1,
        },
    );
    emit_void(
        m,
        mid,
        Op::CondBranch {
            cond: t1,
            true_dest: cont,
            false_dest: throw_b,
        },
    );
    emit_void(
        m,
        ret_b,
        Op::Return {
            value: Some(resume),
        },
    );
    emit_void(m, throw_b, Op::Throw { value: resume });
    emit_void(m, throw_b, Op::Unreachable);

    link(m, b, mid);
    link(m, b, ret_b);
    link(m, mid, cont);
    link(m, mid, throw_b);
    sc.protected.extend([b, mid, ret_b, throw_b]);
    cont
}

/// g01 — the plain generator, baseline shape (inline immediates):
/// `function* seq() { yield 2; yield 3; return 4; }`.
#[test]
fn g01_plain_generator_inline_immediates() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_gen(&mut m, "seq");
    sc.protected.push(entry);

    let (r0, m0) = entry_suspend(&mut m, entry, &sc);
    let b1 = dispatch_inline(&mut m, f, &mut sc, entry, m0, r0);

    let two = load_number(&mut m, b1, 2.0);
    let (r1, m1) = yield_point(&mut m, b1, &sc, two);
    let b2 = dispatch_inline(&mut m, f, &mut sc, b1, m1, r1);

    let three = load_number(&mut m, b2, 3.0);
    let (r2, m2) = yield_point(&mut m, b2, &sc, three);
    let b3 = dispatch_inline(&mut m, f, &mut sc, b2, m2, r2);

    let four = load_number(&mut m, b3, 4.0);
    emit_void(&mut m, b3, Op::Return { value: Some(four) });
    sc.protected.push(b3);
    finish_gen(&mut m, f, &sc);

    let text = decompiled(&m);
    expect(
        &text,
        "function* seq() {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  yield 2.0;\n  yield 3.0;\n  return 4.0;\n}\n",
    );
}

/// The `HandleCompletion` dispatch with shared immediate temps (the
/// optimized profile shape): `zero` (and optionally `one`) are loaded
/// once by the caller and reused across dispatches; returns the
/// continuation block and the `one` temp in use.
#[allow(clippy::too_many_arguments)]
fn dispatch_shared(
    m: &mut Module,
    f: FuncId,
    sc: &mut GenScaffold,
    b: BlockId,
    mode: ValueId,
    resume: ValueId,
    zero: ValueId,
    one: Option<ValueId>,
) -> (BlockId, ValueId) {
    let cont = add_block(m, f);
    let ret_b = add_block(m, f);
    let throw_b = add_block(m, f);
    let mid = add_block(m, f);
    let eq0 = emit(
        m,
        b,
        Op::Compare {
            op: CmpOp::Eq,
            left: mode,
            right: zero,
        },
    );
    let t0 = emit(
        m,
        b,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq0,
        },
    );
    emit_void(
        m,
        b,
        Op::CondBranch {
            cond: t0,
            true_dest: mid,
            false_dest: ret_b,
        },
    );
    let one = one.unwrap_or_else(|| load_number(m, mid, 1.0));
    let eq1 = emit(
        m,
        mid,
        Op::Compare {
            op: CmpOp::Eq,
            left: mode,
            right: one,
        },
    );
    let t1 = emit(
        m,
        mid,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq1,
        },
    );
    emit_void(
        m,
        mid,
        Op::CondBranch {
            cond: t1,
            true_dest: cont,
            false_dest: throw_b,
        },
    );
    emit_void(
        m,
        ret_b,
        Op::Return {
            value: Some(resume),
        },
    );
    emit_void(m, throw_b, Op::Throw { value: resume });
    emit_void(m, throw_b, Op::Unreachable);
    link(m, b, mid);
    link(m, b, ret_b);
    link(m, mid, cont);
    link(m, mid, throw_b);
    sc.protected.extend([b, mid, ret_b, throw_b]);
    (cont, one)
}

/// g02 — the optimized profile shape: the mode immediates are
/// materialized ONCE as shared const temps (a const-env + dead-sweep
/// exercise).
#[test]
fn g02_generator_shared_mode_consts() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_gen(&mut m, "seq");
    sc.protected.push(entry);

    // Shared immediates: zero in the entry block, one in the first
    // dispatch's mid block (the optimized profile's placement).
    let zero = load_number(&mut m, entry, 0.0);

    let (r0, m0) = entry_suspend(&mut m, entry, &sc);
    let (b1, one) = dispatch_shared(&mut m, f, &mut sc, entry, m0, r0, zero, None);

    let two = load_number(&mut m, b1, 2.0);
    let (r1, m1) = yield_point(&mut m, b1, &sc, two);
    let (b2, _) = dispatch_shared(&mut m, f, &mut sc, b1, m1, r1, zero, Some(one));

    let four = load_number(&mut m, b2, 4.0);
    emit_void(&mut m, b2, Op::Return { value: Some(four) });
    sc.protected.push(b2);
    finish_gen(&mut m, f, &sc);

    let text = decompiled(&m);
    expect(
        &text,
        "function* seq() {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  yield 2.0;\n  return 4.0;\n}\n",
    );
}

/// g03 — a USED resumption value binds at the yield site:
/// `function* echo() { const x = yield 1; return x + 1; }`.
#[test]
fn g03_yield_result_bound() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_gen(&mut m, "echo");
    sc.protected.push(entry);

    let (r0, m0) = entry_suspend(&mut m, entry, &sc);
    let b1 = dispatch_inline(&mut m, f, &mut sc, entry, m0, r0);

    let one = load_number(&mut m, b1, 1.0);
    let (r1, m1) = yield_point(&mut m, b1, &sc, one);
    let b2 = dispatch_inline(&mut m, f, &mut sc, b1, m1, r1);

    // The resumption value is genuinely used: `return x + 1`.
    let one2 = load_number(&mut m, b2, 1.0);
    let sum = emit(
        &mut m,
        b2,
        Op::BinaryOp {
            op: BinOp::Add,
            left: one2,
            right: r1,
        },
    );
    emit_void(&mut m, b2, Op::Return { value: Some(sum) });
    sc.protected.push(b2);
    finish_gen(&mut m, f, &sc);

    let text = decompiled(&m);
    expect(
        &text,
        "function* echo() {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  const v16 = yield 1.0;\n  return v16 + 1.0;\n}\n",
    );
}

/// g04 — a yield inside a loop body folds the same way:
/// `function* f() { while (true) { yield 2; } }`.
#[test]
fn g04_yield_in_loop() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_gen(&mut m, "f");
    sc.protected.push(entry);

    let (r0, m0) = entry_suspend(&mut m, entry, &sc);
    let head = dispatch_inline(&mut m, f, &mut sc, entry, m0, r0);

    // `while (true)` header: cond = istrue(true) → body / exit.
    let body = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
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
    let (r1, m1) = yield_point(&mut m, body, &sc, two);
    let cont = dispatch_inline(&mut m, f, &mut sc, body, m1, r1);
    emit_void(&mut m, cont, Op::Branch { dest: head });
    link(&mut m, cont, head);

    emit_void(&mut m, exit, Op::Return { value: None });
    sc.protected.extend([head, body, cont, exit]);
    finish_gen(&mut m, f, &sc);

    let text = decompiled(&m);
    expect(
        &text,
        "function* f() {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  while (true) {\n    yield 2.0;\n    continue;\n  }\n  return;\n}\n",
    );
}

/// g05 — the entry gate: a malformed ENTRY dispatch (the RETURN arm
/// returns the wrong temp) keeps ALL the machinery as documented
/// fallbacks — all-or-nothing per function, never a silent half-fold.
#[test]
fn g05_entry_gate_bail_keeps_fallbacks() {
    let mut m = mk_module();
    let (f, entry, mut sc) = begin_gen(&mut m, "seq");
    sc.protected.push(entry);

    let (r0, m0) = entry_suspend(&mut m, entry, &sc);
    // Sabotage: the RETURN arm returns the genobj, not the resume
    // value — not the vendor `HandleCompletion` shape.
    let cont = add_block(&mut m, f);
    let ret_b = add_block(&mut m, f);
    let throw_b = add_block(&mut m, f);
    let mid = add_block(&mut m, f);
    let zero = load_number(&mut m, entry, 0.0);
    let eq0 = emit(
        &mut m,
        entry,
        Op::Compare {
            op: CmpOp::Eq,
            left: m0,
            right: zero,
        },
    );
    let t0 = emit(
        &mut m,
        entry,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq0,
        },
    );
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: t0,
            true_dest: mid,
            false_dest: ret_b,
        },
    );
    let one = load_number(&mut m, mid, 1.0);
    let eq1 = emit(
        &mut m,
        mid,
        Op::Compare {
            op: CmpOp::Eq,
            left: m0,
            right: one,
        },
    );
    let t1 = emit(
        &mut m,
        mid,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq1,
        },
    );
    emit_void(
        &mut m,
        mid,
        Op::CondBranch {
            cond: t1,
            true_dest: cont,
            false_dest: throw_b,
        },
    );
    emit_void(
        &mut m,
        ret_b,
        Op::Return {
            value: Some(sc.genobj), // wrong temp — not the resume value
        },
    );
    emit_void(&mut m, throw_b, Op::Throw { value: r0 });
    emit_void(&mut m, throw_b, Op::Unreachable);
    link(&mut m, entry, mid);
    link(&mut m, entry, ret_b);
    link(&mut m, mid, cont);
    link(&mut m, mid, throw_b);

    let four = load_number(&mut m, cont, 4.0);
    emit_void(&mut m, cont, Op::Return { value: Some(four) });
    sc.protected.extend([mid, ret_b, throw_b, cont]);
    finish_gen(&mut m, f, &sc);

    let text = decompiled(&m);
    expect(
        &text,
        "function* seq() {\n  /* rethrow-only try/catch dissolved (semantic no-op) */\n  const v1 = /*CreateGenerator plumbing*/ this;\n  yield undefined;\n  const v4 = /*hard-fallback ResumeGenerator (generator driver, R4)*/ v1;\n  const v5 = /*hard-fallback GetResumeMode (generator driver, R4)*/ v1;\n  switch (v5) {\n  case 0.0: {\n      return v1;\n    }\n  case 1.0: {\n      throw v4;\n      /* unreachable */\n    }\n  default: {\n      return 4.0;\n    }\n  }\n}\n",
    );
}

/// g06 — the async honesty floor (IR gap G6): the modern
/// `asyncfunction*` bytecodes carry the awaited/resolved value in the
/// accumulator (isa.yaml `acc: inout:top`; runtime interpreter-inl.cpp
/// `ASYNCFUNCTIONAWAITUNCAUGHT_V8`), which the lift does not model —
/// the register operand it surfaces is the async func object. No
/// sound decompile-side fold exists; the machinery stays LOUD.
#[test]
fn g06_async_stays_documented_fallback() {
    let mut m = mk_module();
    let f = add_func_kind(&mut m, "value", FunctionKind::Async);
    let b0 = entry_of(&mut m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);

    // `Prepare`: AsyncFunctionEnter → funcobj.
    let funcobj = emit(&mut m, b0, Op::AsyncFunctionEnter);
    // `await p1`: AsyncFunctionAwaitUncaught + suspend + completion pair.
    let aw = emit(&mut m, b0, Op::AwaitUncaught { value: p1 });
    emit(
        &mut m,
        b0,
        Op::SuspendGenerator {
            genobj: funcobj,
            value: aw,
        },
    );
    let r = emit(&mut m, b0, Op::ResumeGenerator { genobj: funcobj });
    let mode = emit(&mut m, b0, Op::GetResumeMode { genobj: funcobj });
    // The async HandleCompletion: THROW check only.
    let cont = add_block(&mut m, f);
    let throw_b = add_block(&mut m, f);
    let one = load_number(&mut m, b0, 1.0);
    let eq = emit(
        &mut m,
        b0,
        Op::Compare {
            op: CmpOp::Eq,
            left: mode,
            right: one,
        },
    );
    let t = emit(
        &mut m,
        b0,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq,
        },
    );
    emit_void(
        &mut m,
        b0,
        Op::CondBranch {
            cond: t,
            true_dest: cont,
            false_dest: throw_b,
        },
    );
    emit_void(&mut m, throw_b, Op::Throw { value: r });
    emit_void(&mut m, throw_b, Op::Unreachable);
    link(&mut m, b0, cont);
    link(&mut m, b0, throw_b);
    // `DirectReturn`: AsyncFunctionResolve + return.
    let res = emit(&mut m, cont, Op::AsyncResolve { value: funcobj });
    emit_void(&mut m, cont, Op::Return { value: Some(res) });
    // `CleanUp`: catch-all → AsyncFunctionReject + return.
    let handler = add_block(&mut m, f);
    let exc = add_exception_param(&mut m, handler);
    let rej = emit(&mut m, handler, Op::AsyncReject { value: funcobj });
    emit_void(&mut m, handler, Op::Return { value: Some(rej) });
    add_try(&mut m, f, vec![b0, cont, throw_b], handler, exc);

    let text = decompiled(&m);
    expect(
        &text,
        "async function value(p1) {\n  var v2; /* hoisted temp: used outside its def's block */\n  try {\n    /* elided AsyncFunctionEnter: async-machinery entry; recognized and elided inside `async function` emission (§5 row 72) */\n    v2 = undefined /*fallback AsyncFunctionEnter: async-context value used after elided AsyncFunctionEnter*/;\n    const v3 = await p1;\n    /*async-machinery suspend (R4; not a source yield)*/ v3;\n    const v5 = /*hard-fallback ResumeGenerator (generator driver, R4)*/ v2;\n    if (!(1.0 == /*hard-fallback GetResumeMode (generator driver, R4)*/ v2)) {\n      const v10 = /*hard-fallback AsyncResolve (async driver, R4)*/ v2;\n      return v10;\n    } else {\n      throw v5;\n      /* unreachable */\n    }\n  } catch (e) {\n    const v12 = /*hard-fallback AsyncReject (async driver, R4)*/ v2;\n    return v12;\n  }\n}\n",
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
