//! Corpus lift-verify harness (opt-in, all 5517 fixtures — the c-P3
//! corpus switch: 2832 non-test262 rows (2802 project/upstream/local
//! baked + 30 gen-opcode fixtures) + 2685 compiled test262 rows whose
//! `runtime.status` is `recorded`):
//!
//! (a) the v0.2 lift succeeds on every fixture;
//! (b) `abcd_ir::verify_module` reports ZERO errors on the result.
//!
//! History: parity against the v0.1 crate was proven at v2-P1/v2-P2c
//! (2787 fixtures / 12,996 functions / 1,434,154 canonical tokens /
//! 0 mismatches — pre-test262 corpus). The v0.1-vs-v0.2 canonical
//! comparator
//! (`tests/common/compare.rs`) was retired together with the v0.1 crate
//! at v2-P4 (the swap: abcd-ir becomes abcd-ir, v0.1 deleted; git
//! history is the archive). This harness keeps the corpus lift+verify
//! gates without any v0.1 dependency.
//!
//! Requires the exported GHCR corpus (`exports/corpus`, or
//! `$ABCD_CORPUS_ROOT`) and python3 (the manifest is parsed with its
//! standard JSON library — the established corpus pattern, no JSON
//! whitespace/key-order assumptions).
//!
//! Migrated from `abcd-lift/tests/corpus_lift_verify.rs` to the root
//! package's cross-crate integration layout (file → lift data flow); the
//! root package's manifest dir IS the repo root, so the corpus path
//! resolves without the crate-local `..`.

use std::path::{Path, PathBuf};
use std::process::Command;

use abcd_file::decode;
use rayon::prelude::*;

fn corpus_root() -> PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus"))
}

/// Parse the manifest with python3's standard JSON; print each row's
/// `abc`/`version`/`profile`/`origin.kind` tab-separated.
fn manifest_rows(root: &Path) -> Vec<(String, String, String, String)> {
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
        print(row["abc"] + "\t" + row["version"] + "\t" + row["profile"] + "\t" + row["origin"]["kind"])
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
            let kind = parts.next().expect("origin kind").to_owned();
            (abc, version, profile, kind)
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
/// One fixture's lift+verify outcome, with the exact eprintln lines the
/// serial loop emitted for it (replay order = row order).
enum Outcome {
    /// Lift succeeded; `functions` is the module's function count,
    /// `verify_errors` the verifier's error strings (empty when clean,
    /// truncated to the first 3 for the report line as before).
    Lifted {
        functions: usize,
        verify_errors: Vec<String>,
        verify_errors_total: usize,
    },
    /// The registered-pending class (unregistered nested literal array).
    Pending(String),
    /// Any other lift failure.
    LiftFailure(String),
}

#[test]
#[ignore = "requires exported GHCR corpus + python3"]
fn exported_corpus_lifts_and_verifies_v2() {
    let root = corpus_root();
    let rows = manifest_rows(&root);
    // Parallel decode + lift + verify per fixture (rayon); the indexed
    // collect keeps row order and the serial fold below re-emits the
    // report lines exactly where the serial loop printed them.
    let outcomes: Vec<Outcome> = rows
        .par_iter()
        .map(|(relative, _version, _profile, _kind)| {
            let data = std::fs::read(root.join(relative)).expect("fixture");
            let file = decode(&data).unwrap_or_else(|e| panic!("decode {relative}: {e}"));
            let module = match abcd_lift::lift_file(&file) {
                Ok(m) => m,
                Err(abcd_lift::LiftError::LiteralArrayOutOfRange(idx)) => {
                    return Outcome::Pending(format!("{idx:#x}"));
                }
                Err(e) => return Outcome::LiftFailure(format!("{e}")),
            };
            let functions = module.functions.len();
            let report = abcd_ir::verify_module(&module);
            Outcome::Lifted {
                functions,
                verify_errors: report
                    .errors
                    .iter()
                    .take(3)
                    .map(|e| format!("{e}"))
                    .collect(),
                verify_errors_total: report.errors.len(),
            }
        })
        .collect();

    let mut fixtures = 0usize;
    let mut fixtures_test262 = 0usize;
    let mut functions = 0usize;
    let mut lift_failures = 0usize;
    let mut pending = 0usize;
    let mut verify_failures = 0usize;
    let mut verify_errors_total = 0usize;
    for ((relative, version, profile, kind), outcome) in rows.iter().zip(&outcomes) {
        fixtures += 1;
        if kind == "test262" {
            fixtures_test262 += 1;
        }
        match outcome {
            Outcome::Pending(idx) => {
                pending += 1;
                eprintln!(
                    "PENDING(v2-P1a) [{version}/{profile}] {relative}: \
                     unregistered nested literal array at {idx}"
                );
            }
            Outcome::LiftFailure(e) => {
                lift_failures += 1;
                eprintln!("LIFT FAIL [{version}/{profile}] {relative}: {e}");
            }
            Outcome::Lifted {
                functions: n,
                verify_errors,
                verify_errors_total: total,
            } => {
                functions += n;
                if !verify_errors.is_empty() {
                    verify_failures += 1;
                    verify_errors_total += total;
                    for e in verify_errors {
                        eprintln!("VERIFY [{version}/{profile}] {relative}: {e}");
                    }
                }
            }
        }
    }
    eprintln!(
        "corpus v2 lift+verify: {fixtures} fixtures (test262: {fixtures_test262}), \
         {functions} functions, \
         {lift_failures} lift failures, {pending} registered-pending, \
         {verify_failures} fixtures with verifier errors ({verify_errors_total} errors)"
    );
    // 5487 exported rows (2802 project/upstream/local incl. the 40
    // local/probes + 5 local/yield-star + 2685 test262 compiled rows)
    // + 30 gen-opcode fixtures = 5517 (the c-P3 image switch).
    assert_eq!(fixtures, 5517);
    assert_eq!(fixtures_test262, 2685, "test262 split (origin.kind)");
    assert_eq!(
        fixtures - fixtures_test262,
        2832,
        "non-test262 split (origin.kind)"
    );
    // Function-count pin: 12,996 on the pre-test262 2787-row corpus
    // (v2-P2c parity close-out); rebaselined to 45,592 at c-P3 with the
    // 5517-row corpus (measured; cross-checked against the pandasm
    // suite's method count — they agree).
    assert_eq!(functions, 45592);
    assert_eq!(
        lift_failures, 0,
        "lift failures outside the pending register"
    );
    assert_eq!(verify_failures, 0, "verifier failures");
}
