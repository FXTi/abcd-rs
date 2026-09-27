//! N72-C1 regression pins: the 16 test262 fixtures whose v2lift rewrite
//! dropped the LAST argument of every `callthisrange` /
//! `callthisrangewithname` (narrow and wide) call — behavior divergences
//! of the exit-code class (`Array/of` saw len 2 vs 3, `bind` saw
//! "ab[object Object]" vs "abc", `splice` mis-computed lengths, default
//! parameters referencing `arguments` saw `undefined`).
//!
//! Root cause (vendor-verified twice):
//!
//! - Runtime: `CALLTHISRANGE_IMM8_IMM8_V8` reads `actualNumArgs =
//!   READ_INST_8_1()` and pushes args via `CALL_PUSH_ARGS_THISRANGE`
//!   (`for (i = actualNumArgs; i > 0; i--) push sp[startReg + i]` — "1:
//!   skip this"), so the encoded argc counts the REAL arguments ONLY and
//!   the register window holds argc+1 slots `[this, args...]`
//!   (arkcompiler_ets_runtime-master/ecmascript/interpreter/
//!   interpreter-inl.cpp:1349-1356, :375-383).
//! - Compiler: es2panda `PandaGen::CallThis` emits
//!   `actualArgs = argCount - 1` for the range form where `argCount`
//!   counts this + args
//!   (arkcompiler_ets_frontend-master/es2panda/compiler/core/
//!   pandagen.cpp:1357-1366).
//!
//! The lift read only `argc` registers from the window (treating the
//! first as `this` and dropping the trailing argument), and the lower
//! symmetrically encoded `argc = window.len()` (including `this`). The
//! two off-by-one errors CANCEL on lift→lower round-trips, so the
//! project corpus stayed byte-identical while the runtime semantics
//! silently depended on the register one past the encoded window.
//!
//! The same vendor evidence fixes the (corpus-uncovered)
//! `deprecated.callthisrange` arm: `actualNumArgs = READ_INST_16_1() - 1`
//! with the window `[func, this, args...]` (func from the window, NOT
//! the acc — `acc: out:top` in isa.yaml:1145;
//! interpreter-inl.cpp:1365-1371 + DEPRECATED_CALL_INITIALIZE
//! `funcTagged = sp[startReg]`).
//!
//! Table-driven over the 16 ledger rows: each fixture is lifted +
//! lowered + encoded through the SAME `front_end` + `rewrite_fixture`
//! v2lift pipeline as `corpus_lower_oracle`/`test262_vm`, written under
//! `$ABCD_N72_DIR/v2lift/`, and then VM-compared against the baked
//! runtime record via `scripts/compare-rewritten-corpus.py --recorded
//! --recorded-stderr error-name` (the upstream test262 runner's stderr
//! rule — see test262_vm.rs). Red at HEAD (16 exit_code divergences),
//! green after the lift/lower fix.
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-lower --release -- --ignored --nocapture n72
//! ```

use std::path::PathBuf;
use std::process::Command;

use abcd_lower::LowerOptions;

use super::rewrite_pipeline::{front_end, guarded, rewrite_fixture};

/// The 16 behavior-exit-code ledger rows of the N72-C1 cluster
/// (corpus-relative abc paths), exactly as listed in
/// `scripts/test262-vm-divergences.json`.
const N72_FIXTURES: [&str; 16] = [
    "24.0.0.0/test262/built-ins/Array/of/construct-this-with-the-number-of-arguments/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Array/of/return-a-custom-instance/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Array/prototype/concat/S15.4.4.4_A1_T2/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Array/prototype/splice/S15.4.4.12_A1.2_T5/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Array/prototype/splice/S15.4.4.12_A1.3_T5/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Array/prototype/splice/S15.4.4.12_A1.4_T6/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Array/prototype/splice/S15.4.4.12_A2_T1/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Array/prototype/splice/S15.4.4.12_A2_T3/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Function/prototype/bind/15.3.4.5.1-4-1/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Function/prototype/bind/15.3.4.5.1-4-15/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Function/prototype/bind/15.3.4.5.1-4-3/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Function/prototype/bind/15.3.4.5.2-4-1/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Function/prototype/bind/15.3.4.5.2-4-14/baseline/input.abc",
    "24.0.0.0/test262/language/expressions/class/params-dflt-gen-meth-ref-arguments/baseline/input.abc",
    "24.0.0.0/test262/language/expressions/class/params-dflt-gen-meth-static-ref-arguments/baseline/input.abc",
    "24.0.0.0/test262/language/expressions/class/params-dflt-meth-static-ref-arguments/baseline/input.abc",
];

#[test]
#[ignore = "requires exported GHCR corpus, python3, and LOCAL docker"]
fn n72_callthisrange_argc_excludes_this() {
    let root = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus"));
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));

    // Output root: $ABCD_N72_DIR (absolute) or target/n72-vm. A fresh
    // tree per run: stale candidates must never mask a regression.
    let out_root = std::env::var_os("ABCD_N72_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| repo.join("target/n72-vm"));
    assert!(
        out_root.is_absolute(),
        "N72 output root must be absolute: {out_root:?}"
    );
    if out_root.exists() {
        std::fs::remove_dir_all(&out_root).expect("clear previous N72 output");
    }
    let out_candidates = out_root.join("v2lift");
    let out_index = out_root.join("index.jsonl");
    std::fs::create_dir_all(&out_candidates).expect("create N72 output root");

    // Filtered index: the raw manifest lines of the 16 rows, sorted by
    // abc path (same filtered-index pattern as test262_vm).
    let mut wanted: Vec<&str> = N72_FIXTURES.to_vec();
    wanted.sort_unstable();
    let python = r#"
import json, sys
wanted = set(sys.argv[3].split("\n"))
rows = []
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        if row["abc"] in wanted:
            rows.append((row["abc"], line))
rows.sort()
missing = wanted - {abc for abc, _ in rows}
assert not missing, f"manifest rows not found: {sorted(missing)}"
with open(sys.argv[2], "w", encoding="utf-8") as filtered:
    for _, line in rows:
        filtered.write(line)
"#;
    let output = Command::new("python3")
        .arg("-c")
        .arg(python)
        .arg(root.join("index.jsonl"))
        .arg(&out_index)
        .arg(wanted.join("\n"))
        .output()
        .expect("python3 is required by corpus tooling");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Stage 1: v2lift rewrite of every row (all-or-nothing per fixture;
    // a rewrite failure is a RED signal of its own).
    let mut rewrite_failures = Vec::new();
    for relative in N72_FIXTURES {
        let result = guarded(|| {
            let (file, module) = front_end(&root.join(relative))?;
            rewrite_fixture(&module, &file, LowerOptions::default())
        });
        match result {
            Ok((encoded, functions)) => {
                let target = out_candidates.join(relative);
                std::fs::create_dir_all(target.parent().expect("fixture parent"))
                    .expect("create fixture output dir");
                std::fs::write(&target, &encoded).expect("write candidate");
                eprintln!(
                    "WROTE {relative} ({functions} functions, {} bytes)",
                    encoded.len()
                );
            }
            Err((category, reason)) => {
                eprintln!("FAIL {relative} | {category} | {reason}");
                rewrite_failures.push(relative);
            }
        }
    }
    assert!(
        rewrite_failures.is_empty(),
        "N72: {} fixture(s) fail the v2lift rewrite itself: {rewrite_failures:?}",
        rewrite_failures.len()
    );

    // Stage 2: black-box VM compare against the baked runtime records.
    // exit_code/stdout/timeout EXACT, stderr by error-name (the upstream
    // test262 runner's rule). No --expect-divergences: this cluster must
    // pass CLEAN.
    let image = std::env::var("ARK_TEST_IMAGE").unwrap_or_else(|_| {
        "ghcr.io/fxti/arkcompiler-test@sha256:45f4daf6e422d67a26dd55a524c7c32246e8adf40145523a615e0ae344ae3ea3".to_string()
    });
    let status = Command::new("python3")
        .arg(repo.join("scripts/compare-rewritten-corpus.py"))
        .arg(&out_index)
        .arg(&out_candidates)
        .arg("--recorded")
        .arg("--recorded-stderr")
        .arg("error-name")
        .arg("--image")
        .arg(&image)
        .arg("--jobs")
        .arg("8")
        .status()
        .expect("run compare-rewritten-corpus.py (docker, local only)");
    assert!(
        status.success(),
        "N72: the callthisrange cluster still diverges from the baked runtime records"
    );
}
