//! The test262 dream gate (test262 P3): decompile → es2abc recompile →
//! ark_js_vm RECORDED-behavior comparison over the test262 corpus rows
//! (`origin.kind == "test262"`, `runtime.status == "recorded"` — raw
//! behavior records: exit_code/stdout/stderr/timeout, never pass/fail
//! judgments; all 24.0.0.0/baseline, script mode).
//!
//! This suite is the generator + determinism/panic assertion, mirroring
//! `dream_gate.rs` (the 1149-row project-corpus gate) with three
//! deliberate differences:
//!
//! - Row source: the 2685 test262 rows, NOT the runtime-passed project
//!   set. `corpus_decompile`/`corpus_stage_a` stay scoped to the 2832
//!   non-test262 rows — THIS module is the test262 first contact.
//! - Gate root: `target/dream-gate-t262/` (never committed), so the
//!   two gates never clobber each other's artifacts. A FILTERED index
//!   (test262 rows only) is written to
//!   `target/dream-gate-t262/index.jsonl` for
//!   `scripts/compare-rewritten-corpus.py --recorded` — comparing the
//!   full index would drag in the 1149 passed rows, whose candidates
//!   do not exist under this gate root.
//! - Oracle semantics: `compare-rewritten-corpus.py --recorded
//!   --recorded-stderr error-name` (the upstream test262 runner's
//!   stderr rule; see tests/lift-lower/test262_vm.rs for the empirical
//!   justification — 2659/2685 rows exit 0 with empty stderr, the 26
//!   throwing rows embed unreproducible baked paths in stderr).
//!
//! Panics: decode/lift/decompile run under `catch_unwind`; ANY panic is
//! a real decompiler bug (a corpus row must never crash the pipeline)
//! and fails the generate step with the offending rows listed.
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-decompile --release -- --ignored --nocapture dream_gate_t262
//! python3 scripts/dream-gate.py --gate-dir target/dream-gate-t262 \
//!   --index target/dream-gate-t262/index.jsonl \
//!   --recorded --recorded-stderr error-name \
//!   --expect-divergences scripts/test262-dream-divergences.json --jobs 8
//! ```

use crate::common;

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;

use abcd_decompile::emit::{decompile_module, EmitOptions};

/// The gate root inside `target/` (never committed).
fn gate_root() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("dream-gate-t262")
}

/// The test262 manifest rows as tab-separated records (python3 does the
/// JSON parsing, like [`common::manifest_paths`]):
/// `abc<TAB>case<TAB>version<TAB>profile`. As a side effect the helper
/// writes the FILTERED index (the verbatim test262 rows of the source
/// index) to `<gate>/index.jsonl` for the compare script.
fn t262_rows(root: &Path, gate: &Path) -> Vec<(String, String, String, String)> {
    std::fs::create_dir_all(gate).expect("create gate root");
    let output = std::process::Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, sys
rows = []
with open(sys.argv[1], encoding="utf-8") as manifest:
    selected = []
    for line in manifest:
        row = json.loads(line)
        if row.get("origin", {}).get("kind") == "test262" \
                and row["runtime"]["status"] == "recorded":
            selected.append(line if line.endswith("\n") else line + "\n")
            fields = [row["abc"], row["case"], row["version"], row["profile"]]
            assert not any("\t" in f or "\n" in f for f in fields)
            rows.append("\t".join(fields))
with open(sys.argv[2], "w", encoding="utf-8") as out:
    out.writelines(selected)
for row in rows:
    print(row)
"#,
        )
        .arg(root.join("index.jsonl"))
        .arg(gate.join("index.jsonl"))
        .output()
        .expect("python3 is required by corpus tooling");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("UTF-8 manifest")
        .lines()
        .map(|l| {
            let f: Vec<&str> = l.split('\t').collect();
            assert_eq!(f.len(), 4, "bad manifest row: {l}");
            (
                f[0].to_string(),
                f[1].to_string(),
                f[2].to_string(),
                f[3].to_string(),
            )
        })
        .collect()
}

/// The hard-fallback ops relevant to the EXPECTED-FALLBACK triage
/// bucket (same list as the project-corpus dream gate).
const HARD7: &[&str] = &[
    "IteratorReturn",
    "IteratorThrow",
    "DefineSendableClass",
    "ResumeGenerator",
    "GetResumeMode",
    "AsyncResolve",
    "AsyncReject",
    "SuspendGenerator(async-machinery)",
    "AsyncFunctionEnter",
    "GetTemplateObject",
];

fn json_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn dream_gate_t262_generate() {
    generate();
}

/// Generate the decompiled tree + manifest + filtered index; returns
/// the row count. Asserts the 2685-row shape and ZERO panics.
fn generate() -> usize {
    let root = common::corpus_root();
    let gate = gate_root();
    let rows = t262_rows(&root, &gate);
    assert_eq!(rows.len(), 2685, "the recorded test262 corpus");
    assert!(
        rows.iter()
            .all(|(_, _, v, p)| v == "24.0.0.0" && p == "baseline"),
        "test262 rows are all 24.0.0.0/baseline"
    );

    let src_root = gate.join("src");
    std::fs::create_dir_all(&src_root).expect("create gate src root");
    let mut manifest = String::new();

    let mut total_bytes = 0usize;
    let mut module_fixtures = 0usize;
    let mut panics: Vec<(String, String)> = Vec::new();
    let mut fallback_ops: BTreeMap<&'static str, usize> = BTreeMap::new();
    for (abc, case, version, profile) in &rows {
        let data = std::fs::read(root.join(abc)).expect("read fixture");
        let opts = EmitOptions {
            call_entry: true,
            ..EmitOptions::default()
        };
        // A panic ANYWHERE (decode/lift/decompile) is a real bug on a
        // corpus row: catch it, report it, keep going so ONE run lists
        // every offender.
        let attempt = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let file = abcd_file::decode(&data).expect("decode fixture");
            let module = abcd_lift::lift_file(&file).expect("lift fixture");
            let d1 = decompile_module(&module, &opts);
            let d2 = decompile_module(&module, &opts);
            assert_eq!(d1.text, d2.text, "non-deterministic output in {abc}");
            let is_module = !module.imports.is_empty()
                || !module.exports.is_empty()
                || !module.module_requests.is_empty();
            (module, d1, is_module)
        }));
        let (d1, is_module) = match attempt {
            Ok((_module, d1, is_module)) => (d1, is_module),
            Err(payload) => {
                let msg = payload
                    .downcast::<String>()
                    .map(|s| *s)
                    .or_else(|e| e.downcast::<&str>().map(|s| s.to_string()))
                    .unwrap_or_else(|_| "non-string panic".to_string());
                panics.push((abc.clone(), msg));
                continue;
            }
        };

        if is_module {
            module_fixtures += 1;
        }

        let js_path = src_root.join(format!("{abc}.js"));
        std::fs::create_dir_all(js_path.parent().expect("parent")).expect("mkdirs");
        std::fs::write(&js_path, &d1.text).expect("write js");
        total_bytes += d1.text.len();

        for (op, count) in &d1.stats.fallback_comments {
            *fallback_ops.entry(op).or_default() += count;
        }
        let hard: Vec<&str> = HARD7
            .iter()
            .copied()
            .filter(|op| d1.stats.fallback_comments.contains_key(op))
            .collect();
        let hard_json = hard
            .iter()
            .map(|op| format!("\"{}\"", json_escape(op)))
            .collect::<Vec<_>>()
            .join(", ");
        let mut row = String::new();
        write!(
            row,
            "{{\"abc\": \"{}\", \"case\": \"{}\", \"version\": \"{}\", \"profile\": \"{}\", \"module\": {}, \"hard_fallbacks\": [{}], \"cross_arm_residual\": {}, \"functions_with_fallbacks\": {}, \"js_bytes\": {}}}",
            json_escape(abc),
            json_escape(case),
            version,
            profile,
            is_module,
            hard_json,
            d1.stats.structure.cross_arm_notes,
            d1.stats.functions_with_fallbacks,
            d1.text.len(),
        )
        .expect("write row");
        manifest.push_str(&row);
        manifest.push('\n');
    }
    std::fs::write(gate.join("decompile-manifest.jsonl"), manifest).expect("write manifest");
    eprintln!(
        "DREAM-GATE-T262-GEN rows={} decompiled={} modules={} js_bytes={} -> {}",
        rows.len(),
        rows.len() - panics.len(),
        module_fixtures,
        total_bytes,
        gate.display()
    );
    eprintln!("DREAM-GATE-T262-FALLBACKS {fallback_ops:?}");
    if !panics.is_empty() {
        eprintln!("DREAM-GATE-T262-PANICS ({}):", panics.len());
        for (abc, msg) in &panics {
            eprintln!("  {abc}: {}", msg.lines().next().unwrap_or(""));
        }
    }
    assert!(
        panics.is_empty(),
        "decompile panicked on {} test262 rows (real bugs — see above)",
        panics.len()
    );
    rows.len()
}

/// The full test262 gate: generate, then run `scripts/dream-gate.py`
/// pointed at THIS gate root (es2abc recompile at 24.0.0.0/baseline,
/// script mode; ark_js_vm recorded-behavior compare; triage). Docker is
/// LOCAL-only (scripts/remote-test.sh).
///
/// GATE FORM (test262 P3, decided from the first-contact measurement
/// 2026-09-27, image sha256:45f4daf6): the compare gate is the B-plan
/// hard-error discipline (`--expect-divergences
/// scripts/test262-dream-divergences.json`): every missing/failing row
/// must be listed in the ledger and every listed row must still be
/// missing/failing, so the ledger self-cleans (a fixed row that was not
/// delisted fails the run). On top of that this test asserts the
/// first-contact pass floor below. Rationale: decompile-bug is NOT
/// zero (225 rows), so a hard zero-bucket gate is impossible — but the
/// bugs are REAL findings, registered per-row in the ledger under named
/// classes, never silently absorbed.
///
/// FIRST-CONTACT MEASUREMENT (full 2685 rows, local qemu/docker,
/// --jobs 8; image sha256:45f4daf6):
///
/// - decompile/generate: 6.1s (remote x86_64 release; 2685 decompiled,
///   ZERO panics, 0 modules, 39.8 MB JS; fallback ops: GetResumeMode
///   ×15, ResumeGenerator ×15, Param(funcobj) ×51).
/// - es2abc recompile: ~3m46s (2673/2685 recompiled; 12 SyntaxError
///   rejects — all ours: super/yield out of context, one invalid LHS).
/// - VM compare: ~8m6s (inflated by the 86 hang rows' VM timeouts).
///
/// Histogram: pass 2451 / decompile-bug 225 / es2abc-cant 0 /
/// expected-fallback 9 / fixture-unsupported 0. The 225 decompile-bug
/// rows cluster into 15 named classes (see the ledger's $comment); the
/// three largest with verified minimal repros:
///
/// - decompile-bug-for-in-iterator-stalls (85): the for-in loop
///   reconstruction emits a SELF-assigning back-edge (`v309 = v309`) —
///   the GetPropIterator/NextPropName plumbing never advances, the loop
///   hangs (VM timeout). SILENT bug: only "plumbing" comments, no
///   counted fallback.
/// - decompile-bug-readonly-global-name-collision (26): the emitter
///   names a local temp after the property it loads (`const NaN =
///   Number.NaN`); es2abc compiles a local named NaN/undefined as an
///   ASSIGNMENT TO THE READ-ONLY GLOBAL → TypeError. Minimal repro
///   verified against the image (`function f(){ const NaN = 5; ... }`).
/// - decompile-bug-top-level-this-undefined (9): FIXED (N74-W3,
///   delisted). The call_entry wrapper rebound script-level `this`
///   from globalThis to undefined under es2abc/ark_js_vm (a plain
///   function call has an undefined receiver under es2abc's strict
///   functions; Node's sloppy mode masked it). The entry call now
///   emits `func_main_0.call(this)` — the emitted file's own top-level
///   receiver is exactly what the VM bound for the original entry:
///   globalThis for a script main, undefined for a module.
///
/// The pass floor below guards regressions; raise it as ledger classes
/// are fixed and delisted.
#[test]
#[ignore = "requires exported GHCR corpus, python3, and LOCAL docker"]
fn dream_gate_t262_oracle() {
    generate();
    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let script = manifest_dir.join("scripts").join("dream-gate.py");
    let out = std::process::Command::new("python3")
        .arg(&script)
        .arg("--gate-dir")
        .arg(gate_root())
        .arg("--index")
        .arg(gate_root().join("index.jsonl"))
        .arg("--recorded")
        .arg("--recorded-stderr")
        .arg("error-name")
        .arg("--expect-divergences")
        .arg(manifest_dir.join("scripts/test262-dream-divergences.json"))
        .arg("--jobs")
        .arg("8")
        .output()
        .expect("run dream-gate.py (docker, local only)");
    let text =
        String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr);
    eprintln!("{text}");
    // The ledger gate: dream-gate.py propagates the compare script's
    // --expect-divergences failure (undocumented or stale divergence).
    assert!(
        out.status.success(),
        "dream-gate.py failed (ledger gate or script error) — see output above"
    );
    let report = gate_root().join("dream-gate-report.json");
    let report: crate::dream_gate::serde_jsonless::Report =
        crate::dream_gate::serde_jsonless::parse(
            &std::fs::read_to_string(&report).expect("report"),
        );
    eprintln!(
        "DREAM-GATE-T262-ASSERT pass={} decompile-bug={} es2abc-cant={} expected-fallback={} fixture-unsupported={}",
        report.pass,
        report.decompile_bug,
        report.es2abc_cant,
        report.expected_fallback,
        report.fixture_unsupported
    );
    // The first-contact acceptance floor (see the header comment). The
    // hard gate proper is the ledger inside the compare script; this
    // assert only guards regressions below the measured floor.
    assert!(
        report.pass >= T262_PASS_FLOOR,
        "test262 dream gate regression: pass {} < {}",
        report.pass,
        T262_PASS_FLOOR
    );
}

/// The measured first-contact pass floor (test262 P3, 2026-09-27):
/// N74 wave (2026-09-27): pass 2666 / decompile-bug 10 / expected-fallback 9
/// (the misc-assertion class holds the 10 documented residuals; the
/// expected-fallback class is the generator-machinery loud fallbacks).
/// N74 residual (2026-09-28): the labeled for-in row
/// (statements/labeled/S12.12_A1_T1) fixed + delisted — 2667.
/// The floor pins the post-wave state; the ledger gates the rest.
const T262_PASS_FLOOR: usize = 2675;
