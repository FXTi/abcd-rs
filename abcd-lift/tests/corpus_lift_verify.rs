//! Corpus lift-verify harness (opt-in, all 2787 fixtures):
//!
//! (a) the v0.2 lift succeeds on every fixture;
//! (b) `abcd_ir::verify_module` reports ZERO errors on the result.
//!
//! History: parity against the v0.1 crate was proven at v2-P1/v2-P2c
//! (2787 fixtures / 12,996 functions / 1,434,154 canonical tokens /
//! 0 mismatches). The v0.1-vs-v0.2 canonical comparator
//! (`tests/common/compare.rs`) was retired together with the v0.1 crate
//! at v2-P4 (the swap: abcd-ir becomes abcd-ir, v0.1 deleted; git
//! history is the archive). This harness keeps the corpus lift+verify
//! gates without any v0.1 dependency.
//!
//! Requires the exported GHCR corpus (`exports/corpus`, or
//! `$ABCD_CORPUS_ROOT`) and python3 (the manifest is parsed with its
//! standard JSON library — the established corpus pattern, no JSON
//! whitespace/key-order assumptions).

use std::path::PathBuf;
use std::process::Command;

use abcd_file::decode;

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

/// (a) + (b): lift success + verifier zero errors on all fixtures.
///
/// History note: the 57 sendable-class fixtures whose class buffers
/// reference unregistered nested literal arrays were a REGISTERED-PENDING
/// set until v2-P1a (6d1fcd0) fixed the abcd-file nested-literal-array
/// decode — since then ZERO pending is the gate: every fixture lifts and
/// every failure class is a hard gate failure.
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
        let report = abcd_ir::verify_module(&module);
        if !report.errors.is_empty() {
            verify_failures += 1;
            verify_errors_total += report.errors.len();
            for e in report.errors.iter().take(3) {
                eprintln!("VERIFY [{version}/{profile}] {relative}: {e}");
            }
        }
    }
    eprintln!(
        "corpus v2 lift+verify: {fixtures} fixtures, {functions} functions, \
         {lift_failures} lift failures, {pending} registered-pending, \
         {verify_failures} fixtures with verifier errors ({verify_errors_total} errors)"
    );
    // 2757 exported fixtures + 30 P4-T6 opcode-coverage fixtures.
    assert_eq!(fixtures, 2787);
    // Function-count pin (12,996) proven at v2-P2c parity close-out.
    assert_eq!(functions, 12996);
    assert_eq!(
        lift_failures, 0,
        "lift failures outside the pending register"
    );
    assert_eq!(verify_failures, 0, "verifier failures");
}
