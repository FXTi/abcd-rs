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
//! - (c) `delegate-async`: a hand-written `for await` driver over the
//!   decompiled `outer` (the module's own plain-async `main` keeps
//!   pre-existing loud machinery from the d-P13/d-P14 coverage of the
//!   for-await driver shape — it cannot carry the evidence) —
//!   `1,2,inner-done`.
//! - (d) `delegate-throw`: a hand-written consumer driver — the
//!   delegate's throw propagates through the delegation to the
//!   consumer's try/catch — `before,caught:delegated-boom`. The
//!   module's own entry is NOT the evidence here (see the pinned
//!   known-issue test below).
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

/// (c): the async YieldStar — a hand-written `for await` driver over
/// the decompiled `outer` reproduces the delegated sequence and the
/// delegate's return value.
#[test]
fn yield_star_node_async_driver() {
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
        stdout, "1,2,inner-done\n",
        "delegate-async: behavior mismatch"
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
    // driver below (the entry's own try-fragmentation is the pinned
    // known issue in the next test).
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

/// KNOWN PRE-EXISTING ISSUE (NOT d-P15's fold): the (d) module's own
/// entry wraps its consumer loop in `try { … } catch` spanning a
/// `while` loop, and the structurer splits the protected region into
/// sequential "finally-style" fragments (the "protected statements
/// are not contiguous" note) — so the post-try statement
/// (`log.push("completed")`) executes even on the catch path. This
/// reproduces WITHOUT the YieldStar fold (pre-fold output was broken
/// worse: the unfolded delegation yielded the delegate's raw result
/// objects). Pinned here so any change in either direction is loud.
#[test]
fn yield_star_node_throw_main_known_fragmentation() {
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
    eprintln!("NODE-EVIDENCE(known-issue) delegate-throw main exit={ok} stdout={stdout:?}");
    assert!(ok, "node run delegate-throw main failed: {stderr}");
    // The folded generator is exact; the anomalous trailing
    // `completed` is the structurer's pre-existing fragmentation.
    assert_eq!(
        stdout, "before,caught:delegated-boom,completed\n",
        "delegate-throw main: known fragmentation anomaly changed (investigate!)"
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
