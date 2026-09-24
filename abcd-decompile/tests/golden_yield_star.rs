//! Golden YieldStar (`yield*`) delegation fold tests (d-P15 — the
//! yield-delegation counterpart of d-P11's generator fold and d-P14's
//! async-generator fold, design/decompile.md §8 R4): the es2abc
//! YieldStar driver loop (`GetIterator`/`GetAsyncIterator` setup +
//! the resume-mode dispatch (`NEXT`/`THROW`/`RETURN`) + the
//! `method.call(iter, received)` + the pass-through suspend (the
//! delegate's result object yields AS-IS, no `CreateIterResultObj`
//! wrap) + the `inner.done` test + the completion dispatch with the
//! `.return()` propagation arm) folds back into `yield* <expr>` (or
//! `const ret = yield* <expr>` when the delegate's completion value
//! is used).
//!
//! Vendor lowering model: es2panda
//! `compiler/function/functionBuilder.cpp` `FunctionBuilder::YieldStar`
//! (:177-342, quoting ECMA-262 27.5.4.5/27.6.3.8 in its comments) and
//! the `Iterator` helper (`GetMethod`/`Close`/`CallMethodWithValue`/
//! `Complete`/`Value`); `enum class ResumeMode { RETURN=0, THROW=1,
//! NEXT=2 }` in `functionBuilder.h`.
//!
//! Unlike the other goldens these load the REAL fixtures
//! (`decompile-fixtures/yield-star/*.abc`, es2abc 24.0.0.0 baseline —
//! the corpus has zero `yield*` coverage, which is exactly why this
//! was a loud fallback): the pandasm dumps sit next to them
//! (`*.pa`). Shapes:
//!
//! - (a) `delegate-gen`: sync `function*` delegating to another
//!   generator; the delegate's RETURN value is used
//!   (`const ret = yield* inner(); yield ret;`).
//! - (b) `delegate-array`: sync `yield*` over a plain iterable; the
//!   delegation result is unused (bare `yield*` statement).
//! - (c) `delegate-async`: `async function*` with `yield*` (for-await
//!   consumption end); used completion value. The async YieldStar
//!   carries awaits around every protocol step and its completion
//!   dispatch sits INSIDE the loop's done arm.
//! - (d) `delegate-throw`: the delegate throws; the error propagates
//!   through the delegation to the consumer's try/catch.
//! - bail: `manual-iterator`: a hand-rolled iterator-protocol loop
//!   inside a generator — NOT `yield*`; the fold must leave it loud.
//!
//! The expected strings are STABLE emission forms — reviewed,
//! hand-written expectations, not snapshots.

use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_lift::lift_file;
use std::path::PathBuf;

/// The fixture root (standalone — deliberately outside exports/corpus;
/// the corpus gates hard-assert fixture counts).
fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("decompile-fixtures")
        .join("yield-star")
        .join(name)
}

/// Decompile one fixture and strip the two-line header comment.
fn decompiled(name: &str) -> String {
    let data = std::fs::read(fixture(name)).expect("read fixture");
    let file = abcd_file::decode(&data).expect("decode fixture");
    let module = lift_file(&file).expect("lift fixture");
    let d = decompile_module(&module, &EmitOptions::default());
    let mut lines: Vec<&str> = d.text.lines().collect();
    assert!(lines.len() >= 2, "header missing:\n{}", d.text);
    let mut out = lines.split_off(2).join("\n");
    if !out.is_empty() {
        out.push('\n');
    }
    out
}

/// (a) sync generator delegation; the delegate's return value is the
/// `yield*` expression's value and feeds the next `yield`.
#[test]
fn golden_yield_star_delegate_gen() {
    let text = decompiled("delegate-gen.abc");
    let expected = r#"var inner;
var log;
var outer;
function func_main_0() {
  /* rethrow-only try/catch dissolved (semantic no-op) */
  inner = function* ___inner() {
  /* rethrow-only try/catch dissolved (semantic no-op) */
  yield 1.0;
  yield 2.0;
  return "inner-done";
};
  outer = function* ___outer() {
  /* cross-arm edges unfolded (B30→B31, B24→B30, B29→B30); the tail-duplication fold bailed (budget/complexity) — the shared tail is NOT duplicated and the conditions are NOT merged; affected flow may read oddly */
  /* rethrow-only try/catch dissolved (semantic no-op) */
  const v45 = /*CreateGenerator plumbing*/ undefined /*fallback Param(funcobj): the hidden function-object slot has no JS surface form*/;
  const inner$1 = inner;
  const value$1 = yield* inner$1();
  yield value$1;
  return undefined;
};
  log = [];
  const outer$1 = outer;
  const v166 = outer$1();
  for (const value of v166) {
    /* iterator-cleanup try/catch folded into for-of's implicit cleanup (ECMA-262 §14.7.5) */
    /* try region 2: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary */
    const log$1 = log;
    const push = log$1.push;
    push.call(log$1, value);
    continue;
  }
  const print$1 = print;
  const log$2 = log;
  const join = log$2.join;
  const v202 = join.call(log$2, ",");
  print$1(v202);
  return;
}
"#;
    assert_eq!(text, expected);
}

/// (b) sync `yield*` over a plain iterable (array); unused result →
/// a bare `yield*` statement.
#[test]
fn golden_yield_star_delegate_array() {
    let text = decompiled("delegate-array.abc");
    let expected = r#"var log;
var outer;
function func_main_0() {
  /* rethrow-only try/catch dissolved (semantic no-op) */
  outer = function* ___outer() {
  /* cross-arm edges unfolded (B20→B21, B14→B20, B19→B20); the tail-duplication fold bailed (budget/complexity) — the shared tail is NOT duplicated and the conditions are NOT merged; affected flow may read oddly */
  /* rethrow-only try/catch dissolved (semantic no-op) */
  const v5 = /*CreateGenerator plumbing*/ undefined /*fallback Param(funcobj): the hidden function-object slot has no JS surface form*/;
  yield 0.0;
  yield* [10.0, 20.0, 30.0];
  yield 99.0;
  return undefined;
};
  log = [];
  const outer$1 = outer;
  const v136 = outer$1();
  for (const value of v136) {
    /* iterator-cleanup try/catch folded into for-of's implicit cleanup (ECMA-262 §14.7.5) */
    /* try region 2: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary */
    const log$1 = log;
    const push = log$1.push;
    push.call(log$1, value);
    continue;
  }
  const print$1 = print;
  const log$2 = log;
  const join = log$2.join;
  const v172 = join.call(log$2, ",");
  print$1(v172);
  return;
}
"#;
    assert_eq!(text, expected);
}

/// (d) the delegate throws: the error propagates through the
/// delegation to the consumer. The generator folds clean; the
/// consumer's own try-around-loop projects as ONE try/catch with the
/// post-try `print` emitted after it — the N69 fix (d-P16): the
/// region tree nests the unprotected join below the protected run,
/// and the join hoist wraps the whole protected span in a single
/// try (post-try statements no longer run on the catch path).
#[test]
fn golden_yield_star_delegate_throw() {
    let text = decompiled("delegate-throw.abc");
    let expected = r#"var boom;
var it;
var log;
var outer;
function func_main_0() {
  try {
    /* try region 0: the handler continuation (the try's join) is nested below the protected run in the region tree — the unprotected tail is hoisted out of the try body to after the try/catch (the VM's PC-range dispatch rejoins there) */
    boom = function* ___boom() {
  /* rethrow-only try/catch dissolved (semantic no-op) */
  yield "before";
  const Error$1 = Error;
  const v30 = new Error$1("delegated-boom");
  throw v30;
  /* unreachable */
};
    outer = function* ___outer() {
  /* cross-arm edges unfolded (B27→B28, B21→B27, B26→B27); the tail-duplication fold bailed (budget/complexity) — the shared tail is NOT duplicated and the conditions are NOT merged; affected flow may read oddly */
  /* rethrow-only try/catch dissolved (semantic no-op) */
  const v37 = /*CreateGenerator plumbing*/ undefined /*fallback Param(funcobj): the hidden function-object slot has no JS surface form*/;
  const boom$1 = boom;
  yield* boom$1();
  yield "after";
  return undefined;
};
    const outer$1 = outer;
    const v156 = outer$1();
    it = v156;
    log = [];
    const it$1 = it;
    const next = it$1.next;
    const v161 = next.call(it$1);
    v162 = v161;
    while (true) {
      var v162; /* phi */
      const done = v162.done;
      if (done) {
        v168 = false;
        v174 = v162;
      } else {
        v168 = true;
        v174 = v162;
      }
      var v168; /* phi */
      var v174; /* phi */
      if (!v168) {
        break;
      }
      const log$1 = log;
      const push = log$1.push;
      const value = v162.value;
      push.call(log$1, value);
      const it$2 = it;
      const next$1 = it$2.next;
      const v180 = next$1.call(it$2);
      v162 = v180;
      continue;
    }
    const log$2 = log;
    const push$1 = log$2.push;
    push$1.call(log$2, "completed");
  } catch (e) {
    const log$3 = log;
    const push$2 = log$3.push;
    const v189 = "caught:";
    const message = e.message;
    push$2.call(log$3, v189 + message);
  }
  const print$1 = print;
  const log$4 = log;
  const join = log$4.join;
  const v199 = join.call(log$4, ",");
  print$1(v199);
  return;
}
"#;
    assert_eq!(text, expected);
}

/// (c) the async YieldStar (`async function*`): awaits wrap every
/// protocol step and the completion dispatch sits inside the loop's
/// done arm. The folded body is `const value$2 = yield* inner$1()`.
/// The module's plain-async `main` (the `for await` driver) folds to
/// working await code since the N70 fix (d-P16) and to the literal
/// `for await (…)` source form since d-P17 — the golden above pins
/// the folded `outer` body only (main's text is long).
#[test]
fn golden_yield_star_delegate_async() {
    let text = decompiled("delegate-async.abc");
    // The folded async generator body (the fold's target) — the full
    // text is long (main's for-await driver); pin the outer body and
    // the absence of YieldStar machinery residues inside it.
    let outer = text
        .split("outer = async function* ___outer() {")
        .nth(1)
        .expect("outer present");
    let outer = outer.split("};").next().expect("outer body end");
    let expected = r#"
  var inner$1; /* hoisted temp: used outside its def's block */
  /* cross-arm edges unfolded (B51→B52, B43→B51, B50→B51); the tail-duplication fold bailed (budget/complexity) — the shared tail is NOT duplicated and the conditions are NOT merged; affected flow may read oddly */
  try {
    const v144 = /*CreateGenerator plumbing*/ undefined /*fallback Param(funcobj): the hidden function-object slot has no JS surface form*/;
    inner$1 = inner;
  } catch (e$1) {
    var v309; /* phi */
    throw e$1;
  }
  try {
    /* try region 1: protected statements are not contiguous in the structured output — this is wrapper #2 for the same region (catch body duplicated, finally-style) */
    const value$2 = yield* inner$1();
    yield value$2;
    return undefined;
  } catch (e$1) {
    var v309; /* phi */
    throw e$1;
  }
"#;
    assert_eq!(outer, expected);
}

/// (c)-main N70 shape pin: the plain-async `for await` driver folds
/// its suspend/resume machinery to plain awaits — NO
/// ResumeGenerator/GetResumeMode hard-fallbacks, NO AsyncFunctionEnter
/// fallback temp, NO AsyncReject/SuspendGenerator residues. Since
/// d-P17 the driver is the literal `for await (…)` form (the loop
/// await is the for-await's implicit await; the rejection path is the
/// implicit rejection of that await — behavior pinned by the node
/// rejection probe in `yield_star_node.rs`).
#[test]
fn golden_yield_star_delegate_async_main_folded() {
    let text = decompiled("delegate-async.abc");
    let main = text
        .split("main = async function ___main() {")
        .nth(1)
        .expect("main present");
    let main = main.split("\n};").next().expect("main body end");
    for gone in [
        "ResumeGenerator",
        "GetResumeMode",
        "fallback AsyncFunctionEnter",
        "AsyncReject",
        "SuspendGenerator",
    ] {
        assert!(
            !main.contains(gone),
            "folded main keeps {gone} machinery:\n{main}"
        );
    }
    // The d-P16 working-loop form is superseded by the literal
    // for-await form (d-P17): no header await temp, no cleanup await.
    assert!(
        !main.contains("= await v16;"),
        "the header await temp is absorbed into `for await`:\n{main}"
    );
    assert!(
        !main.contains("await v42;"),
        "the iterator-cleanup await folds into for-await's implicit cleanup:\n{main}"
    );
}

/// (c)-main d-P17 literal-form pin (N70 residual 1): the driver loop
/// prints as the LITERAL `for await (const value of v10) {…}` source
/// form — the header's extra await temp absorbed, the loop-carried
/// bookkeeping phis substituted back to their sources (`v29`→`v8`),
/// the iterator-cleanup try folded into the implicit protocol, and
/// the done-arm's absorbed post-loop tail (print + return) re-homed
/// AFTER the loop. Exact segment pin:
#[test]
fn golden_yield_star_delegate_async_main_for_await() {
    let text = decompiled("delegate-async.abc");
    let main = text
        .split("main = async function ___main() {")
        .nth(1)
        .expect("main present");
    let main = main.split("\n};").next().expect("main body end");
    let expected = r#"for await (const value of v10) {
    /* rethrow-only try/catch dissolved (semantic no-op) */
    /* iterator-cleanup try/catch folded into for-of's implicit cleanup (ECMA-262 §14.7.5) */
    /* try region 2: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary */
    const push = v8.push;
    push.call(v8, value);
  }
  const print$1 = print;
  const join = v8.join;
  const v58 = join.call(v8, ",");
  print$1(v58);
  return undefined;
"#;
    assert!(
        main.contains(expected),
        "the literal for-await driver form:\n{main}"
    );
    // N70 residual 2 (negative pin): the dead loop-exit dispatch
    // `throw <resume>` the conservative v1 kept is provably
    // unreachable post-fold and swept — no `throw` residue, and the
    // resume temp's hoist (it was hoisted ONLY because the dead throw
    // used it) is gone too.
    assert!(
        !main.contains("throw v20"),
        "dead loop-exit dispatch throw residue:\n{main}"
    );
    assert!(
        !main.contains("var v20"),
        "the resume temp's hoist is dead with the sweep:\n{main}"
    );
}

/// Bail: a hand-rolled iterator-protocol loop inside a generator is
/// NOT `yield*` — the fold must not fire; the machinery stays loud.
#[test]
fn golden_yield_star_bail_manual_iterator() {
    let text = decompiled("manual-iterator.abc");
    assert!(
        !text.contains("yield*"),
        "the bail shape must not produce yield*:\n{text}"
    );
    // The loud fallback markers of the unfolded machine stay.
    assert!(
        text.contains("hard-fallback ResumeGenerator"),
        "bail keeps the loud fallbacks:\n{text}"
    );
    assert!(
        text.contains("/*iter-result*/"),
        "bail keeps the iter-result wrap:\n{text}"
    );
}
