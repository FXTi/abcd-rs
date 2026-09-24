//! d-P15 node evidence for the YieldStar (`yield*`) fold: the REAL
//! fixtures (`decompile-fixtures/yield-star/*.abc`, es2abc 24.0.0.0
//! baseline) are decompiled and executed under `node`, and the exact
//! stdout is compared against the source-level behavior (verified
//! identical on ark_js_vm at fixture-generation time).
//!
//! Evidence shape per fixture:
//!
//! - (a) `delegate-gen`: run the decompiled module entry
//!   (`func_main_0`) — the source prints `1,2,inner-done` (the
//!   delegated sequence PLUS the delegate's return value flowing
//!   through `const ret = yield* inner()` into the next yield).
//! - (b) `delegate-array`: module entry — `0,10,20,30,99`.
//! - (c) `delegate-async`: the module's own plain-async `main` (the
//!   `for await` driver) — pre-N70 it kept loud machinery and silently
//!   broke; fixed in d-P16 — PLUS a hand-written `for await` driver
//!   over the decompiled `outer` — `1,2,inner-done` twice.
//! - (d) `delegate-throw`: a hand-written consumer driver — the
//!   delegate's throw propagates through the delegation to the
//!   consumer's try/catch — `before,caught:delegated-boom`. The
//!   module's own entry is the N69 regression pin below (pre-fix the
//!   structurer fragmented the try-around-loop and ran the post-try
//!   statement on the catch path; fixed in d-P16).
//! - bail `manual-iterator`: node --check only; its stdout pins the
//!   loud-fallback form (unfolded iter-result objects), not source
//!   behavior.
//!
//! All five outputs are `node --check`-ed. When node is absent the
//! behavior assertions skip (reported); the checks always run.

use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_lift::lift_file;
use std::path::PathBuf;

/// The fixture root (standalone — deliberately outside exports/corpus).
fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("decompile-fixtures")
        .join("yield-star")
        .join(name)
}

/// Decompile one fixture to JS text (header comment kept — it is
/// syntactically inert under node).
fn decompiled(name: &str) -> String {
    let data = std::fs::read(fixture(name)).expect("read fixture");
    let file = abcd_file::decode(&data).expect("decode fixture");
    let module = lift_file(&file).expect("lift fixture");
    decompile_module(&module, &EmitOptions::default()).text
}

fn node_available() -> bool {
    std::process::Command::new("node")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Write `body` to a temp file and run it under node; return stdout.
fn run_node(dir: &std::path::Path, name: &str, body: &str) -> (bool, String, String) {
    let out = dir.join(name);
    std::fs::write(&out, body).expect("write sample");
    let run = std::process::Command::new("node")
        .arg(&out)
        .output()
        .expect("run node");
    (
        run.status.success(),
        String::from_utf8_lossy(&run.stdout).to_string(),
        String::from_utf8_lossy(&run.stderr).to_string(),
    )
}

/// (a)+(b): the module entry reproduces the source stdout exactly —
/// the delegated sequence and the delegation return value.
#[test]
fn yield_star_node_sync_entries() {
    if !node_available() {
        eprintln!("NODE-EVIDENCE node not found on this host — behavior run skipped");
        return;
    }
    let dir = std::env::temp_dir().join("abcd-dp15-node");
    std::fs::create_dir_all(&dir).expect("tempdir");
    for (fixture, want) in [
        ("delegate-gen.abc", "1,2,inner-done\n"),
        ("delegate-array.abc", "0,10,20,30,99\n"),
    ] {
        // `print` is an ark builtin; shim it for node. The decompiled
        // module defines `func_main_0` but does not call it (es2abc
        // treats it as the entry point).
        let body = format!(
            "const print = console.log;\n{}\nfunc_main_0();\n",
            decompiled(fixture)
        );
        let (ok, stdout, stderr) = run_node(&dir, &(fixture.replace('.', "_") + ".js"), &body);
        eprintln!("NODE-EVIDENCE {fixture} exit={ok} stdout={stdout:?} stderr={stderr:?}");
        assert!(ok, "node run {fixture} failed: {stderr}");
        assert_eq!(stdout, want, "{fixture}: behavior mismatch");
    }
}

/// (c): the async YieldStar — the module's OWN plain-async `main`
/// (the `for await` driver) decompiles to the LITERAL `for await
/// (const value of v10)` source form (d-P17; N70 fixed behavior in
/// d-P16: async_machine_fold covers the loop-driving shape), so the
/// entry prints the delegated sequence itself; the hand-written
/// `for await` driver over the decompiled `outer` repeats it.
#[test]
fn yield_star_node_async_driver() {
    let text = decompiled("delegate-async.abc");
    // The literal source form (the exact-segment golden pin lives in
    // `golden_yield_star.rs`); here the form gates the behavior run.
    assert!(
        text.contains("for await (const value of v10) {"),
        "the driver is the literal for-await form:\n{text}"
    );
    if !node_available() {
        eprintln!("NODE-EVIDENCE node not found on this host — behavior run skipped");
        return;
    }
    let dir = std::env::temp_dir().join("abcd-dp15-node");
    std::fs::create_dir_all(&dir).expect("tempdir");
    let body = format!(
        "const print = console.log;\n{}\nfunc_main_0();\n\
         (async () => {{ const log = []; for await (const v of outer()) {{ log.push(v); }} console.log(log.join(\",\")); }})();\n",
        decompiled("delegate-async.abc")
    );
    let (ok, stdout, stderr) = run_node(&dir, "delegate-async-driver.js", &body);
    eprintln!("NODE-EVIDENCE delegate-async exit={ok} stdout={stdout:?} stderr={stderr:?}");
    assert!(ok, "node run delegate-async failed: {stderr}");
    assert_eq!(
        stdout, "1,2,inner-done\n1,2,inner-done\n",
        "delegate-async: behavior mismatch (line 1 = the module's own for-await main, N70; line 2 = the hand-written driver)"
    );
}

/// (c) rejection probe (d-P17): with the driver in literal `for
/// await` form, a rejecting async iterator must reject `main()`'s
/// promise (the for-await's implicit await rethrows; the async
/// completion rejects) — the SAME behavior the d-P16 working-loop
/// form had. The probe lets the module entry's own `main()` finish
/// first (`1,2,inner-done`), rebinds the module-level `outer` to a
/// rejecting async iterable, and re-invokes `main`.
#[test]
fn yield_star_node_async_driver_rejection_probe() {
    if !node_available() {
        eprintln!("NODE-EVIDENCE node not found on this host — behavior run skipped");
        return;
    }
    let dir = std::env::temp_dir().join("abcd-dp15-node");
    std::fs::create_dir_all(&dir).expect("tempdir");
    let body = format!(
        "const print = console.log;\n{}\n\
         (async () => {{\n\
         \x20 func_main_0();\n\
         \x20 await new Promise(r => setTimeout(r, 10)); /* the entry's own main() finishes first */\n\
         \x20 outer = () => ({{ [Symbol.asyncIterator]() {{ return {{ next: () => Promise.reject(\"probe-reject\") }}; }} }});\n\
         \x20 await main().then(() => console.log(\"main resolved?!\"), e => console.log(\"main rejected: \" + e));\n\
         }})();\n",
        decompiled("delegate-async.abc")
    );
    let (ok, stdout, stderr) = run_node(&dir, "delegate-async-reject.js", &body);
    eprintln!(
        "NODE-EVIDENCE delegate-async rejection probe exit={ok} stdout={stdout:?} stderr={stderr:?}"
    );
    assert!(
        ok,
        "node run delegate-async rejection probe failed: {stderr}"
    );
    assert_eq!(
        stdout, "1,2,inner-done\nmain rejected: probe-reject\n",
        "delegate-async rejection probe: main's promise must reject with the iterator's rejection"
    );
}

/// (d): the delegate's throw propagates through the delegation to the
/// consumer's try/catch — a hand-written consumer driver (the
/// module's own entry is the pre-existing fragmentation case below).
#[test]
fn yield_star_node_throw_driver() {
    if !node_available() {
        eprintln!("NODE-EVIDENCE node not found on this host — behavior run skipped");
        return;
    }
    let dir = std::env::temp_dir().join("abcd-dp15-node");
    std::fs::create_dir_all(&dir).expect("tempdir");
    // The module entry must run (it defines `outer`) but its own
    // print goes to a no-op shim — the evidence is the hand-written
    // driver below (it isolates the fold's throw delegation from the
    // entry's own try-around-loop; the entry itself is the N69
    // regression pin in the next test).
    let body = format!(
        "const print = () => {{}};\n{}\nfunc_main_0();\n\
         const it2 = outer(); const log2 = [];\n\
         try {{ let r = it2.next(); while (!r.done) {{ log2.push(r.value); r = it2.next(); }} log2.push(\"completed\"); }}\n\
         catch (e) {{ log2.push(\"caught:\" + e.message); }}\n\
         console.log(log2.join(\",\"));\n",
        decompiled("delegate-throw.abc")
    );
    let (ok, stdout, stderr) = run_node(&dir, "delegate-throw-driver.js", &body);
    eprintln!("NODE-EVIDENCE delegate-throw exit={ok} stdout={stdout:?} stderr={stderr:?}");
    assert!(ok, "node run delegate-throw failed: {stderr}");
    assert_eq!(
        stdout, "before,caught:delegated-boom\n",
        "delegate-throw: behavior mismatch"
    );
}

/// N69 REGRESSION PIN (fixed in d-P16): the (d) module's own entry
/// wraps its consumer loop in `try { … } catch` spanning a `while`
/// loop. Pre-fix the structurer split the protected region into
/// sequential "finally-style" fragments (the region tree nests the
/// unprotected join below the protected run and the per-level
/// coalescing could not see across the nesting), so the post-try
/// statement (`log.push("completed")`) executed even on the catch
/// path (`before,caught:delegated-boom,completed`). The join hoist
/// now wraps the whole protected span in ONE try/catch and emits the
/// unprotected tail after it: the post-try statement is UNREACHABLE
/// from the catch path except through the structured join — the
/// source behavior `before,caught:delegated-boom`.
#[test]
fn yield_star_node_throw_main_correct() {
    if !node_available() {
        eprintln!("NODE-EVIDENCE node not found on this host — behavior run skipped");
        return;
    }
    let dir = std::env::temp_dir().join("abcd-dp15-node");
    std::fs::create_dir_all(&dir).expect("tempdir");
    let body = format!(
        "const print = console.log;\n{}\nfunc_main_0();\n",
        decompiled("delegate-throw.abc")
    );
    let (ok, stdout, stderr) = run_node(&dir, "delegate-throw-main.js", &body);
    eprintln!("NODE-EVIDENCE(N69-fixed) delegate-throw main exit={ok} stdout={stdout:?}");
    assert!(ok, "node run delegate-throw main failed: {stderr}");
    // Source behavior: the throw inside the loop routes to the catch;
    // `completed` (inside the protected span, after the loop) must
    // NOT run on the catch path.
    assert_eq!(
        stdout, "before,caught:delegated-boom\n",
        "delegate-throw main: N69 regression — post-try statement reachable from the catch path"
    );
}

/// The bail fixture: stdout pins the loud-fallback form (the
/// unfolded machine yields the raw iter-result objects — today's
/// honest fallback, not source behavior). This is the shape the fold
/// deliberately refuses to touch.
#[test]
fn yield_star_node_bail_loud_fallback() {
    if !node_available() {
        eprintln!("NODE-EVIDENCE node not found on this host — behavior run skipped");
        return;
    }
    let dir = std::env::temp_dir().join("abcd-dp15-node");
    std::fs::create_dir_all(&dir).expect("tempdir");
    let body = format!(
        "const print = console.log;\n{}\nfunc_main_0();\n",
        decompiled("manual-iterator.abc")
    );
    let (ok, stdout, stderr) = run_node(&dir, "manual-iterator.js", &body);
    eprintln!("NODE-EVIDENCE manual-iterator exit={ok} stdout={stdout:?}");
    assert!(ok, "node run manual-iterator failed: {stderr}");
    assert_eq!(
        stdout, "[object Object],[object Object],[object Object]\n",
        "manual-iterator: loud-fallback form changed (investigate!)"
    );
}

/// node --check on ALL five outputs: the fold (and the preserved
/// fallbacks) must leave syntactically valid JS.
#[test]
fn yield_star_node_check_all() {
    if !node_available() {
        eprintln!("NODE-CHECK node not found on this host — skipped");
        return;
    }
    let dir = std::env::temp_dir().join("abcd-dp15-node");
    std::fs::create_dir_all(&dir).expect("tempdir");
    for fixture in [
        "delegate-gen.abc",
        "delegate-array.abc",
        "delegate-async.abc",
        "delegate-throw.abc",
        "manual-iterator.abc",
    ] {
        let out = dir.join(fixture.replace('.', "_") + ".check.js");
        std::fs::write(&out, decompiled(fixture)).expect("write sample");
        let check = std::process::Command::new("node")
            .arg("--check")
            .arg(&out)
            .output()
            .expect("run node --check");
        assert!(
            check.status.success(),
            "node --check {fixture}: {}",
            String::from_utf8_lossy(&check.stderr)
        );
        eprintln!("NODE-CHECK ok {fixture}");
    }
}
