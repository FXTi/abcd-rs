//! The dream gate (d-P4, design/decompile.md §7): decompile → es2abc
//! recompile → ark_js_vm behavior comparison.
//!
//! THIS test is the generator + determinism assertion: for every
//! runtime-passed corpus fixture (the 1149-row behavior oracle set) it
//! decompiles `input.abc` to JS text (twice — outputs must be
//! byte-identical) and writes:
//!
//! - `target/dream-gate/src/<abc-path>.js` — the decompiled source
//!   (path mirrors the corpus layout so `scripts/dream-gate.py` can
//!   recompile it into `target/dream-gate/abc/<abc-path>`, the tree
//!   `scripts/compare-rewritten-corpus.py` expects),
//! - `target/dream-gate/decompile-manifest.jsonl` — one row per
//!   fixture: abc path, case, version, profile, module-mode flag (IR:
//!   any imports/exports/module_requests), hard-7 fallback ops present,
//!   residual cross-arm notes, emitted byte count.
//!
//! The es2abc recompile + VM comparison + triage is driven by
//! `scripts/dream-gate.py` (docker is local-only; see
//! scripts/remote-test.sh).
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-decompile --test dream_gate --release -- --ignored --nocapture
//! python3 scripts/dream-gate.py --jobs 8
//! ```

mod common;

use std::fmt::Write as _;
use std::path::Path;

use abcd_decompile::emit::{EmitOptions, decompile_module};

/// The gate root inside `target/` (never committed).
fn gate_root() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("target")
        .join("dream-gate")
}

/// Manifest rows as tab-separated records (python3 does the JSON
/// parsing, like [`common::manifest_paths`]):
/// `abc<TAB>case<TAB>version<TAB>profile<TAB>runtime-status`.
fn manifest_rows(root: &Path) -> Vec<(String, String, String, String, String)> {
    let output = std::process::Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, sys
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        fields = [row["abc"], row["case"], row["version"], row["profile"],
                  row["runtime"]["status"]]
        assert not any("\t" in f or "\n" in f for f in fields)
        print("\t".join(fields))
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
        .expect("UTF-8 manifest")
        .lines()
        .map(|l| {
            let f: Vec<&str> = l.split('\t').collect();
            assert_eq!(f.len(), 5, "bad manifest row: {l}");
            (
                f[0].to_string(),
                f[1].to_string(),
                f[2].to_string(),
                f[3].to_string(),
                f[4].to_string(),
            )
        })
        .collect()
}

/// The fitness-class-H (hard-7) fallback ops relevant to the gate's
/// EXPECTED-FALLBACK triage bucket.
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
    // Documented fallback families beyond the hard 7: template literals
    // whose RAW strings are genuinely unrecoverable (G4 was resolved by
    // d-P10 — raw survives in the file and now emits as backtick text —
    // so this entry only buckets the honest cooked-only fallback) and
    // AllocObject shape buffers had a registered fallback path —
    // divergence is expected by construction.
    "GetTemplateObject",
];

fn json_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn dream_gate_generate() {
    generate();
}

/// Generate the decompiled tree + manifest; returns the fixture count.
fn generate() -> usize {
    let root = common::corpus_root();
    let rows = manifest_rows(&root);
    let passed: Vec<_> = rows.iter().filter(|r| r.4 == "passed").cloned().collect();
    assert_eq!(passed.len(), 1149, "the runtime-passed oracle set");

    let gate = gate_root();
    let src_root = gate.join("src");
    std::fs::create_dir_all(&src_root).expect("create gate src root");
    let mut manifest = String::new();

    let mut total_bytes = 0usize;
    let mut module_fixtures = 0usize;
    for (abc, case, version, profile, _status) in &passed {
        let data = std::fs::read(root.join(abc)).expect("read fixture");
        let file = abcd_file::decode(&data).expect("decode fixture");
        let module = abcd_lift::lift_file(&file).expect("lift fixture");

        // Determinism: two independent runs, byte-identical. The gate
        // emits the entry-point call so the recompiled program actually
        // runs (EmitOptions::call_entry).
        let opts = EmitOptions {
            call_entry: true,
            ..EmitOptions::default()
        };
        let d1 = decompile_module(&module, &opts);
        let d2 = decompile_module(&module, &opts);
        assert_eq!(d1.text, d2.text, "non-deterministic output in {abc}");

        let is_module = !module.imports.is_empty()
            || !module.exports.is_empty()
            || !module.module_requests.is_empty();
        if is_module {
            module_fixtures += 1;
        }

        let js_path = src_root.join(format!("{abc}.js"));
        std::fs::create_dir_all(js_path.parent().expect("parent")).expect("mkdirs");
        std::fs::write(&js_path, &d1.text).expect("write js");
        total_bytes += d1.text.len();

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
        "DREAM-GATE-GEN fixtures={} modules={} js_bytes={} -> {}",
        passed.len(),
        module_fixtures,
        total_bytes,
        gate.display()
    );
    passed.len()
}

/// The full gate: generate, then run `scripts/dream-gate.py`
/// (es2abc recompile + ark_js_vm behavior compare + triage) and assert
/// the recorded acceptance floor. Docker is LOCAL-only
/// (scripts/remote-test.sh).
///
/// The histogram at d-P10 (2026-09-25): pass 1131 / decompile-bug 0 /
/// es2abc-cant 0 / expected-fallback 18 / fixture-unsupported 0 (of
/// 1149). d-P10 closed IR gap G4 at the decompile side: the
/// `gettemplateobject` literal operand is the vendor pair
/// `[rawStrings, cookedStrings]` (es2panda `compiler/base/literals.cpp`;
/// runtime `ecmascript/template_string.cpp`), both lists resolve from
/// the const-pool pair or the imperative `createemptyarray` +
/// `definefieldbyvalue` build, and template nodes emit as backtick
/// literals carrying the raw text verbatim (identity tag reconstructs
/// the template object), so the 36 template/tagged-template fixtures
/// recompile and behave identically. The d-P9 histogram was
/// 1095/0/0/54/0. The floor guards regressions; raise it when the
/// buckets improve.
#[test]
#[ignore = "requires exported GHCR corpus, python3, and LOCAL docker"]
fn dream_gate_oracle() {
    generate();
    let script = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("scripts")
        .join("dream-gate.py");
    let out = std::process::Command::new("python3")
        .arg(&script)
        .arg("--jobs")
        .arg("8")
        .output()
        .expect("run dream-gate.py (docker, local only)");
    let text =
        String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr);
    eprintln!("{text}");
    let report = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("target")
        .join("dream-gate")
        .join("dream-gate-report.json");
    let report: serde_jsonless::Report =
        serde_jsonless::parse(&std::fs::read_to_string(&report).expect("report"));
    eprintln!(
        "DREAM-GATE-ASSERT pass={} decompile-bug={} es2abc-cant={} expected-fallback={} fixture-unsupported={}",
        report.pass,
        report.decompile_bug,
        report.es2abc_cant,
        report.expected_fallback,
        report.fixture_unsupported
    );
    assert!(
        report.pass >= 1131,
        "dream gate regression: pass {} < 1131 (the d-P10 acceptance floor)",
        report.pass
    );
}

/// Minimal JSON field extraction (no serde dependency in this crate's
/// tests — the corpus pattern is python3, but the report is small).
mod serde_jsonless {
    /// The triage histogram fields.
    pub struct Report {
        pub pass: usize,
        pub decompile_bug: usize,
        pub es2abc_cant: usize,
        pub expected_fallback: usize,
        pub fixture_unsupported: usize,
    }

    pub fn parse(text: &str) -> Report {
        let grab = |key: &str| -> usize {
            let marker = format!("\"{key}\": ");
            let start = text.find(&marker).expect(key) + marker.len();
            let end = text[start..]
                .find(|c: char| !c.is_ascii_digit())
                .expect("number end")
                + start;
            text[start..end].parse().expect("usize")
        };
        Report {
            pass: grab("pass"),
            decompile_bug: grab("decompile-bug"),
            es2abc_cant: grab("es2abc-cant"),
            expected_fallback: grab("expected-fallback"),
            fixture_unsupported: grab("fixture-unsupported"),
        }
    }
}
