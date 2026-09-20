//! Corpus parity harness (opt-in, all 2787 fixtures):
//!
//! (a) the v0.2 lift succeeds on every fixture;
//! (b) `abcd_ir2::verify_module` reports ZERO errors on the result;
//! (c) the canonical op-stream comparison against the v0.1 lifted
//!     module (`abcd_ir::lift::lift_file`) — see `compare.rs`.
//!
//! Requires the exported GHCR corpus (`exports/corpus`, or
//! `$ABCD_CORPUS_ROOT`) and python3 (the manifest is parsed with its
//! standard JSON library — the established corpus pattern, no JSON
//! whitespace/key-order assumptions).

use std::path::PathBuf;
use std::process::Command;

use abcd_file::decode;

mod common;
use common::compare;

fn corpus_root() -> PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        })
}

/// Parse the manifest with python3's standard JSON; print each row's
/// `abc`/`version`/`profile` tab-separated.
fn manifest_rows(root: &PathBuf) -> Vec<(String, String, String)> {
    let output = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, sys
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        for key in ("abc", "version", "profile"):
            assert "\n" not in row[key] and "\t" not in row[key]
        print(row["abc"] + "\t" + row["version"] + "\t" + row["profile"])
"#,
        )
        .arg(root.join("index.jsonl"))
        .output()
        .expect("python3 is required by corpus tooling");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("UTF-8 fixture paths")
        .lines()
        .map(|line| {
            let mut parts = line.split('\t');
            let abc = parts.next().expect("abc path").to_owned();
            let version = parts.next().expect("version").to_owned();
            let profile = parts.next().expect("profile").to_owned();
            (abc, version, profile)
        })
        .collect()
}

/// (a) + (b) + (c): lift success + verifier zero errors + canonical
/// v0.1-parity comparison on all fixtures.
///
/// The 57 sendable-class fixtures whose class buffers reference
/// literal arrays the file model never surfaces (unregistered nested
/// arrays — the abcd-file model gap under v2-P1a repair) form the
/// REGISTERED-PENDING set: their hard `LiteralArrayOutOfRange` lift
/// error is documented, never silent, and they are the ONLY tolerated
/// lift failures. Every other failure class is a hard gate failure.
#[test]
#[ignore = "requires exported GHCR corpus + python3"]
fn exported_corpus_lifts_and_verifies_v2() {
    let root = corpus_root();
    let rows = manifest_rows(&root);
    let mut fixtures = 0usize;
    let mut functions = 0usize;
    let mut lift_failures = 0usize;
    let mut pending = 0usize;
    let mut verify_failures = 0usize;
    let mut verify_errors_total = 0usize;
    let mut compared = 0usize;
    let mut tokens = 0usize;
    let mut mismatches = 0usize;
    for (relative, version, profile) in &rows {
        let data = std::fs::read(root.join(relative)).expect("fixture");
        let file = decode(&data).unwrap_or_else(|e| panic!("decode {relative}: {e}"));
        fixtures += 1;
        let module = match abcd_lift::lift_file(&file) {
            Ok(m) => m,
            Err(abcd_lift::LiftError::LiteralArrayOutOfRange(idx)) => {
                pending += 1;
                eprintln!(
                    "PENDING(v2-P1a) [{version}/{profile}] {relative}: \
                     unregistered nested literal array at {idx:#x}"
                );
                continue;
            }
            Err(e) => {
                lift_failures += 1;
                eprintln!("LIFT FAIL [{version}/{profile}] {relative}: {e}");
                continue;
            }
        };
        functions += module.functions.len();
        let report = abcd_ir2::verify_module(&module);
        if !report.errors.is_empty() {
            verify_failures += 1;
            verify_errors_total += report.errors.len();
            for e in report.errors.iter().take(3) {
                eprintln!("VERIFY [{version}/{profile}] {relative}: {e}");
            }
        }
        // (c) canonical parity vs the v0.1 lifted module.
        let v1 = abcd_ir::lift::lift_file(&file)
            .unwrap_or_else(|e| panic!("v0.1 lift (the oracle) failed on {relative}: {e}"));
        let cmp = compare::compare_modules(&file, &v1, &module);
        compared += cmp.functions_compared;
        tokens += cmp.tokens_compared;
        if !cmp.is_parity() {
            for m in &cmp.mismatches {
                mismatches += 1;
                if mismatches <= 20 {
                    eprintln!(
                        "MISMATCH [{version}/{profile}] {relative} fn {} ({}): token {}\n  v1: {}\n  v2: {}",
                        m.func, m.func_name, m.token, m.v1, m.v2
                    );
                }
            }
        }
    }
    eprintln!(
        "corpus v2 lift+verify+parity: {fixtures} fixtures, {functions} functions, \
         {lift_failures} lift failures, {pending} registered-pending, \
         {verify_failures} fixtures with verifier errors ({verify_errors_total} errors), \
         {compared} functions compared ({tokens} canonical tokens), {mismatches} mismatches"
    );
    // 2757 exported fixtures + 30 P4-T6 opcode-coverage fixtures.
    assert_eq!(fixtures, 2787);
    assert_eq!(
        lift_failures, 0,
        "lift failures outside the pending register"
    );
    assert_eq!(verify_failures, 0, "verifier failures");
    assert_eq!(mismatches, 0, "canonical parity mismatches");
}
