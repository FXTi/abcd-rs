//! N76: the five structurer deep-water rows of the test262 dream-gate
//! ledger (`scripts/test262-dream-divergences.json`,
//! `decompile-bug-misc-assertion-divergence`).
//!
//! Mechanisms pinned here (one test per row; each decompiles the
//! offending fixture and asserts the repaired surface):
//!
//! 1. `switch/S12.11_A1_T2` — multi-entry continuation sets whose
//!    per-entry slices overlap on a SHARED TAIL (the switch
//!    fall-through shape) used to escape to the state-variable hatch
//!    (design §4.2.4), which ran unconditionally inline and clobbered
//!    the result (`SwitchTest(1)` returned NaN). The analysis now
//!    decomposes them into a tail-arm-first `Alternates`
//!    (`abcd_analysis::control::regions::Builder::structure_shared_tail`),
//!    and the sequence-run fold accepts an arm that DIVERGES via a
//!    terminator action (the arm's `break L$…` into the tail label) —
//!    previously it bailed and the leaf emitter silently dropped the
//!    skip edge's jump.
//! 2. `try/S12.14_A7_T1` — the outer finally region (whose protected
//!    range covers inner-handler BODY blocks, not just the handler
//!    head) never rode along into the shim, so the outer try/catch —
//!    and with it the handler body holding `var v384` — was dropped
//!    (`ReferenceError: v384 is not defined`). The outer-finally walk
//!    (`outer_wrap_plan`) now falls back to the ROOT frame's full plan
//!    list when the shim's ride-along approximation lacks the plan.
//! 3. `try/S12.14_A7_T2` — same finally-idiom gap, observed as the
//!    replaced exception escaping (`ex3` reached the top level because
//!    the `#2.3` outer catch was never emitted). The walk fix is shared
//!    with row 2; `pending_wraps` suppresses redundant re-wrapping of
//!    the in-flight chain so the nested finally chain does not
//!    duplicate exponentially.
//! 4. `try/S12.14_A15` — handler-rejoin targets (blocks with
//!    handler-side Normal predecessors) were buried inside conditional
//!    arms: the finally-dispatch epilogue landed in a switch arm the
//!    sibling `break` skipped, and a handler's cut edge to the return
//!    tail fell out of the catch clause to nowhere. The analysis now
//!    demotes such blocks to the continuation
//!    (`structure_acyclic`'s external-pred demotion), and the emitter
//!    duplicates small terminal tails at handler cut edges when the
//!    fall-out is not verified to reach them.
//! 5. `try/S12.14_A9_T5` (N78) — a try range cuts a do-while: the
//!    protected region is the loop header + body prefix, and the
//!    catch's `continue` rejoins the IN-LOOP test. Whole-wrapping the
//!    loop (the legacy `emit_mixed` Loop rule) made the catch clause
//!    fall out PAST the loop — one caught iteration, then `#1.4`.
//!    `Ctx::try_loop_cut_do_while` emits the source shape: the
//!    try/catch (plus its finally chain) inside a `do {…} while (…)`
//!    body, the catch ending in `continue` (which targets the loop
//!    test), the normal-path-only prefix verified chain-protected or
//!    pure phi wiring.
//!
//! Corpus-fixture tests (`#[ignore]`d like `n74_w4.rs`); run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-decompile --release -- --ignored --nocapture n76_structurer
//! ```

use crate::common;

use abcd_decompile::emit::{decompile_module, EmitOptions};

/// Decompile one corpus fixture (twice — determinism is part of the
/// contract) and return the text.
fn decompile(abc: &str) -> String {
    let root = common::corpus_root();
    let data = std::fs::read(root.join(abc)).expect("read fixture");
    let file = abcd_file::decode(&data).expect("decode fixture");
    let module = abcd_lift::lift_file(&file).expect("lift fixture");
    let opts = EmitOptions {
        call_entry: true,
        ..EmitOptions::default()
    };
    let d1 = decompile_module(&module, &opts);
    let d2 = decompile_module(&module, &opts);
    assert_eq!(d1.text, d2.text, "non-deterministic output in {abc}");
    d1.text
}

/// 1. switch/S12.11_A1_T2: the fall-through switch with a duplicate
///    `case 0` no longer escapes to the state-machine hatch; the shared
///    tails structure as tail-arm alternates and every dispatch path
///    reaches `return v568` with the right accumulator value.
#[test]
#[ignore]
fn switch_fallthrough_shared_tail() {
    let text =
        decompile("24.0.0.0/test262/language/statements/switch/S12.11_A1_T2/baseline/input.abc");
    assert!(
        !text.contains("IRREDUCIBLE CFG escape hatch"),
        "the multi-entry fall-through tails must structure as alternates, not the hatch:\n{}",
        &text[..text.len().min(4000)]
    );
    // The `case '1'` tail (`result += 4`) breaks INTO the shared
    // return tail rather than re-running it unconditionally.
    assert!(
        text.contains("v568 = v548 + 4.0;\n      break L$140;"),
        "the case-'1' arm must jump into the shared return tail:\n{}",
        &text[..text.len().min(4000)]
    );
    // The return tail exists exactly once, after the dispatch.
    assert_eq!(
        text.matches("return v568;").count(),
        1,
        "exactly one return tail for SwitchTest"
    );
}

/// 2. try/S12.14_A7_T1: the outer finally region whose protected range
///    covers the inner catch BODY must wrap the inner try/catch even when
///    the shim ride-along approximation dropped it — the outer handler
///    holds the phi temporaries (`var v384`) the inner blocks flush to.
#[test]
#[ignore]
fn try_nested_finally_phi_temps_declared() {
    let text =
        decompile("24.0.0.0/test262/language/statements/try/S12.14_A7_T1/baseline/input.abc");
    assert!(
        text.contains("var v384; /* phi */"),
        "the outer handler's phi declaration must be emitted (its body must exist):\n{}",
        &text[text.len() / 3..2 * text.len() / 3]
    );
    assert!(
        text.contains("catch (e$16)"),
        "the outer finally dispatch handler must be emitted"
    );
}

/// 3. try/S12.14_A7_T2: nested-finally exception replacement — the
///    outer catches that receive the replaced exception (`#2.3`, `#3.2`,
///    `#4.2`, `#5.1` …) must all be emitted, so `throw "ex3"` from the
///    inner finally is dispatched instead of escaping.
#[test]
#[ignore]
fn try_nested_finally_exception_replacement() {
    let text =
        decompile("24.0.0.0/test262/language/statements/try/S12.14_A7_T2/baseline/input.abc");
    for check in ["#2.3", "#3.2", "#4.2", "#5.1", "#6.1", "#7.1"] {
        assert!(
            text.contains(check),
            "the outer-catch check {check} must survive structuring"
        );
    }
}

/// 4. try/S12.14_A15: switch-inside-try reconstruction — the
///    finally-dispatch epilogue must follow the dispatch (not hide in a
///    switch arm), and a handler's cut edge to the return tail must reach
///    it (tail duplication at the cut edge when fall-out is not verified).
#[test]
#[ignore]
fn try_switch_inside_finally_reconstruction() {
    let text = decompile("24.0.0.0/test262/language/statements/try/S12.14_A15/baseline/input.abc");
    // SwitchTest3's finally-`break` dispatch folds to a switch whose
    // `case undefined` (no-exception path) RETURNS the accumulated
    // result — at HEAD the dispatch was an if/else whose arms fell out
    // of the catch clause to nowhere (`return v529` survived only in
    // the never-taken outer `else` arm).
    let st3 = &text[text.find("___SwitchTest3").expect("SwitchTest3")..];
    assert!(
        st3.contains("switch (v514) {\n      case undefined: {\n"),
        "SwitchTest3's dispatch must fold to a switch over the completion marker:\n{}",
        &st3[..st3.len().min(2500)]
    );
    // SwitchTest1's inner dispatch switch must CLOSE before the
    // finally epilogue's phi declarations (at HEAD the epilogue was
    // buried inside the inner `default` arm, so the case-4 `break`
    // skipped it and SwitchTest1(4) returned `undefined`).
    let st1 = &text[text.find("___SwitchTest1").expect("SwitchTest1")..];
    assert!(
        st1.contains("            }\n            var v440; /* phi */\n            var v449; /* phi */\n            v439 = v440;"),
        "the epilogue must follow the inner dispatch switch, not hide in an arm:\n{}",
        &st1[..st1.len().min(3500)]
    );
}

/// 5. try/S12.14_A9_T5: the try range CUTS a do-while — the protected
///    region is the loop header + the body prefix, and the catch's
///    `continue` targets the IN-LOOP test (`i < 10`). Wrapping the whole
///    loop in the try (the legacy `emit_mixed` Loop rule) makes the catch
///    clause fall out PAST the loop: after one caught iteration the
///    `fin !== 10` check throws `#1.4`. The only sound projection is the
///    source shape: `do { try { … } catch (er1) { …; continue; } …
/// finally dispatch … } while (i < 10)` — a do-while continue targets
///    the loop test, which is exactly the handler's bytecode rejoin.
#[test]
#[ignore]
fn try_cuts_do_while_catch_continue() {
    let text =
        decompile("24.0.0.0/test262/language/statements/try/S12.14_A9_T5/baseline/input.abc");
    let main = &text[text.find("function func_main_0").expect("func_main_0")..];
    // The try/catch sits INSIDE a do-whose body, before the test.
    let do_at = main
        .find("do {")
        .expect("the cut loop must emit as a do-while with the try inside");
    let rest = &main[do_at..];
    let try_at = rest.find("try {").expect("try inside the loop body");
    let catch_at = rest.find("} catch (").expect("catch clause");
    let while_at = rest.find("} while (").expect("do-while test");
    assert!(
        try_at < catch_at && catch_at < while_at,
        "the try/catch must precede the loop test inside the do-while body:\n{rest}"
    );
    // The catch's continuation IS the loop test: the inlined finally
    // (`fin += 1`) is followed by `continue` — not by a fall-out past
    // the loop (the HEAD bug: one caught iteration, then #1.4).
    let catch_clause = &rest[catch_at..while_at];
    assert!(
        catch_clause.contains("continue;"),
        "the catch must `continue` to the in-loop test:\n{catch_clause}"
    );
    // Behavior pin (the ledger row's failure mode): the module runs
    // clean — 10 iterations, `fin === 10`, no `#1.4` throw.
    if std::process::Command::new("node")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
    {
        let dir = std::env::temp_dir().join("abcd-n76-a9t5");
        std::fs::create_dir_all(&dir).expect("tempdir");
        let file = dir.join("a9t5.js");
        std::fs::write(&file, &text).expect("write");
        let run = std::process::Command::new("node")
            .arg(&file)
            .output()
            .expect("run node");
        assert!(
            run.status.success(),
            "the decompiled module must run clean (HEAD throws #1.4):\n{}",
            String::from_utf8_lossy(&run.stderr)
        );
    } else {
        eprintln!("NODE-EVIDENCE node not found on this host — behavior run skipped");
    }
}
