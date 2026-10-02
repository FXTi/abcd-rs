//! Wild big-abc lift + decompile smoke sweep (q-P13 item 2 — first
//! contact of the "core-25 big-abc smoke" registration item).
//!
//! Scope: every module of every package in the exported 156-package
//! wild-OHOS corpus (`exports/corpus/wild/wild-haps/`, the same corpus
//! the hap-file gate consumes). Per module:
//!
//!   decode → lift → verify_module → decompile (timed, output bytes)
//!
//! plus an opt-in es2abc recompile sub-channel:
//!
//!   decompile (EmitOptions::call_entry) → write JS to
//!   `exports/wild-decompile/src/` + a dream-gate-format
//!   `decompile-manifest.jsonl` → `scripts/dream-gate.py --gate-dir
//!   exports/wild-decompile --skip-compare` recompiles each JS with the
//!   image's es2abc (24.0.0.0/baseline — the wild set has no producer
//!   version pin and no behavior oracle, so the newest es2abc is the
//!   reference) → `wild_smoke_recompile_check` decodes every recompiled
//!   artifact and compares function counts against the original module.
//!
//! There is NO semantic-equivalence assertion (wild packages call
//! system APIs; no VM oracle). The recompile channel exists because it
//! is the only way to discover "output does not compile" decompiler
//! bugs on the wild set.
//!
//! This is an INSTRUMENT, not a gate: it never fails on findings — it
//! records them (JSONL + summary under `exports/wild-decompile/`, all
//! gitignored) and prints a histogram. A decompiler PANIC is a P0-class
//! finding (the no-panic law) and is recorded with a captured
//! backtrace, per module, without aborting the sweep.
//!
//! Skip-by-absence: with no exported wild corpus the tests print a skip
//! line and return — they are `#[ignore]`d and never run in CI anyway.
//!
//! Run (on dabai via scripts/remote-test.sh, KEEP=1 so the artifacts
//! survive for the docker step):
//!
//! ```text
//! KEEP=1 scripts/remote-test.sh test -p abcd-rs --test lift-decompile --release -- --ignored --nocapture wild_smoke_sweep
//! ssh dabai 'cd <run-dir> && echo "{\"results\": [], \"passed\": 0, \"missing\": []}" > exports/wild-decompile/compare-stdout.json \
//!   && python3 scripts/dream-gate.py --gate-dir exports/wild-decompile --skip-compare --jobs 8'
//! KEEP=1 scripts/remote-test.sh test -p abcd-rs --test lift-decompile --release -- --ignored --nocapture wild_smoke_recompile_check
//! ```

use std::cell::RefCell;
use std::path::{Path, PathBuf};
use std::time::Instant;

use abcd_decompile::emit::{decompile_module, EmitOptions};

/// The exported wild corpus root; same override as the hap-file gate.
fn wild_corpus_root() -> PathBuf {
    std::env::var_os("ABCD_CORPUS_WILD_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus/wild/wild-haps")
        })
}

/// Smoke artifacts root (gitignored via `exports/`).
fn smoke_out_root() -> PathBuf {
    std::env::var_os("ABCD_WILD_SMOKE_OUT")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/wild-decompile"))
}

/// One wild-corpus manifest row (only the fields the smoke reads; the
/// rest is provenance owned by the hap-file gate).
#[derive(Debug, serde::Deserialize)]
struct WildPackage {
    path: String,
    size: u64,
    expectation: String,
}

#[derive(Debug, serde::Deserialize)]
struct WildManifest {
    packages: Vec<WildPackage>,
}

/// Per-module outcome, one JSON line in `smoke-modules.jsonl`.
#[derive(Debug, serde::Serialize)]
struct ModuleRow {
    pkg: String,
    entry: String,
    expectation: String,
    /// ok | expected-negative | decode-error | lift-error |
    /// decompile-error | panic
    status: String,
    /// Stage that produced a non-ok status (decode | lift | decompile).
    failed_stage: Option<String>,
    error: Option<String>,
    /// Captured backtrace for panics (P0 evidence).
    backtrace: Option<String>,
    pkg_bytes: u64,
    abc_bytes: usize,
    file_methods: Option<usize>,
    ir_functions: Option<usize>,
    verify_errors: Option<usize>,
    verify_first: Option<String>,
    decode_ms: Option<u64>,
    lift_ms: Option<u64>,
    decompile_ms: Option<u64>,
    js_bytes: Option<usize>,
    functions_with_fallbacks: Option<usize>,
    /// Top fallback-comment ops for this module (op=count, joined).
    fallbacks: Option<String>,
}

impl ModuleRow {
    fn new(pkg: &WildPackage, entry: &str, abc_bytes: usize) -> Self {
        ModuleRow {
            pkg: pkg.path.clone(),
            entry: entry.to_string(),
            expectation: pkg.expectation.clone(),
            status: "ok".to_string(),
            failed_stage: None,
            error: None,
            backtrace: None,
            pkg_bytes: pkg.size,
            abc_bytes,
            file_methods: None,
            ir_functions: None,
            verify_errors: None,
            verify_first: None,
            decode_ms: None,
            lift_ms: None,
            decompile_ms: None,
            js_bytes: None,
            functions_with_fallbacks: None,
            fallbacks: None,
        }
    }

    fn fail(&mut self, stage: &str, status: &str, error: String) {
        self.status = status.to_string();
        self.failed_stage = Some(stage.to_string());
        self.error = Some(error);
    }
}

/// One dream-gate-format manifest row (the recompile sub-channel).
/// `scripts/dream-gate.py` reads `abc`/`version`/`profile`/`module`/
/// `hard_fallbacks`; `functions`/`js_bytes` are ours (the recompile
/// check compares function counts; extra keys are ignored downstream).
#[derive(Debug, serde::Serialize, serde::Deserialize)]
struct RecompileRow {
    abc: String,
    case: String,
    version: String,
    profile: String,
    module: bool,
    hard_fallbacks: Vec<String>,
    functions: usize,
    js_bytes: usize,
}

thread_local! {
    /// Panic message + backtrace captured by the sweep's hook.
    static LAST_PANIC: RefCell<Option<(String, String)>> = const { RefCell::new(None) };
}

/// Install a hook that records panics (message + forced backtrace) so a
/// panicking stage becomes a REPORT ROW instead of an aborted sweep.
/// The default stderr printout is replaced to keep the log readable;
/// the message lands in the JSONL row verbatim.
fn install_panic_capture() {
    std::panic::set_hook(Box::new(|info| {
        let bt = std::backtrace::Backtrace::force_capture().to_string();
        LAST_PANIC.with(|p| *p.borrow_mut() = Some((info.to_string(), bt)));
    }));
}

fn take_panic() -> Option<(String, String)> {
    LAST_PANIC.with(|p| p.borrow_mut().take())
}

/// Total method count of a decoded file (the function-count metric the
/// recompile check applies to BOTH sides identically).
fn file_method_count(file: &abcd_file::File) -> usize {
    file.classes.values().map(|c| c.methods.len()).sum()
}

/// The hard-7 / documented fallback ops whose presence makes recompile
/// divergence expected by construction (same list as the dream gate).
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

#[test]
#[ignore = "requires the exported wild corpus; smoke instrument, not a gate"]
fn wild_smoke_sweep() {
    let root = wild_corpus_root();
    let manifest_path = root.join("manifest.json");
    if !manifest_path.exists() {
        eprintln!("wild-smoke: no wild corpus at {root:?}, skipping (corpus not exported)");
        return;
    }
    let manifest: WildManifest =
        serde_json::from_str(&std::fs::read_to_string(&manifest_path).expect("read wild manifest"))
            .expect("parse wild manifest");

    let out = smoke_out_root();
    let src_root = out.join("src");
    std::fs::create_dir_all(&src_root).expect("create smoke out dirs");

    install_panic_capture();

    let mut rows: Vec<ModuleRow> = Vec::new();
    let mut recompile: Vec<RecompileRow> = Vec::new();

    for pkg in &manifest.packages {
        let bytes = match std::fs::read(root.join(&pkg.path)) {
            Ok(b) => b,
            Err(e) => {
                let mut row = ModuleRow::new(pkg, "<package>", 0);
                row.fail("read", "decode-error", format!("package unreadable: {e}"));
                rows.push(row);
                continue;
            }
        };
        let modules = match abcd_hap::abc_modules(&bytes) {
            Ok(m) => m,
            Err(e) => {
                let mut row = ModuleRow::new(pkg, "<container>", 0);
                row.fail("decode", "decode-error", format!("container: {e}"));
                rows.push(row);
                continue;
            }
        };
        for m in &modules {
            let data = m.data.as_slice();
            let mut row = ModuleRow::new(pkg, &m.entry_name, data.len());

            // ── decode ──────────────────────────────────────────────
            let t = Instant::now();
            let decoded =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| abcd_file::decode(data)));
            row.decode_ms = Some(t.elapsed().as_millis() as u64);
            let file = match decoded {
                Ok(Ok(f)) => f,
                Ok(Err(e)) => {
                    let msg = e.to_string();
                    if pkg.expectation == "negative-invalid-opcode"
                        && msg.contains("invalid opcode")
                    {
                        row.status = "expected-negative".to_string();
                        row.error = Some(msg);
                    } else {
                        row.fail("decode", "decode-error", msg);
                    }
                    rows.push(row);
                    continue;
                }
                Err(_) => {
                    let (msg, bt) = take_panic()
                        .unwrap_or_else(|| ("unknown panic".to_string(), String::new()));
                    row.fail("decode", "panic", msg);
                    row.backtrace = Some(bt);
                    rows.push(row);
                    continue;
                }
            };
            // A negative-package module that DECODES is normal (the
            // expectation is only "≥1 module hits invalid opcode"; the
            // hap-file gate owns it) — keep smoking it like any other
            // module; the expectation field keeps it traceable.
            row.file_methods = Some(file_method_count(&file));

            // ── lift ────────────────────────────────────────────────
            let t = Instant::now();
            let lifted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                abcd_lift::lift_file(&file)
            }));
            row.lift_ms = Some(t.elapsed().as_millis() as u64);
            let module = match lifted {
                Ok(Ok(m)) => m,
                Ok(Err(e)) => {
                    row.fail("lift", "lift-error", format!("{e:?}"));
                    rows.push(row);
                    continue;
                }
                Err(_) => {
                    let (msg, bt) = take_panic()
                        .unwrap_or_else(|| ("unknown panic".to_string(), String::new()));
                    row.fail("lift", "panic", msg);
                    row.backtrace = Some(bt);
                    rows.push(row);
                    continue;
                }
            };
            row.ir_functions = Some(module.functions.len());

            // ── verify (report-only; decompile still attempted) ─────
            let report = abcd_ir::verify_module(&module);
            row.verify_errors = Some(report.errors.len());
            if let Some(first) = report.errors.first() {
                row.verify_first = Some(format!("{first:?}"));
            }

            // ── decompile (default options: the human-facing config,
            // as in tests/lift-decompile/corpus_decompile.rs) ───────
            let t = Instant::now();
            let emitted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                decompile_module(&module, &EmitOptions::default())
            }));
            row.decompile_ms = Some(t.elapsed().as_millis() as u64);
            let d1 = match emitted {
                Ok(d) => d,
                Err(_) => {
                    let (msg, bt) = take_panic()
                        .unwrap_or_else(|| ("unknown panic".to_string(), String::new()));
                    row.fail("decompile", "panic", msg);
                    row.backtrace = Some(bt);
                    rows.push(row);
                    continue;
                }
            };
            row.js_bytes = Some(d1.text.len());
            row.functions_with_fallbacks = Some(d1.stats.functions_with_fallbacks);
            if !d1.stats.fallback_comments.is_empty() {
                let mut pairs: Vec<_> = d1.stats.fallback_comments.iter().collect();
                pairs.sort_by(|a, b| b.1.cmp(a.1));
                row.fallbacks = Some(
                    pairs
                        .iter()
                        .take(8)
                        .map(|(op, n)| format!("{op}={n}"))
                        .collect::<Vec<_>>()
                        .join(","),
                );
            }

            // ── recompile artifact (call_entry variant — the recompile
            // channel's config, as in the dream gate) ────────────────
            let re = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                decompile_module(
                    &module,
                    &EmitOptions {
                        call_entry: true,
                        ..EmitOptions::default()
                    },
                )
            }));
            if let Ok(d2) = re {
                let rel = format!("{}#{}", pkg.path, m.entry_name);
                let js_path = src_root.join(format!("{rel}.js"));
                std::fs::create_dir_all(js_path.parent().expect("parent")).expect("mkdirs");
                std::fs::write(&js_path, &d2.text).expect("write js");
                let is_module = !module.imports.is_empty()
                    || !module.exports.is_empty()
                    || !module.module_requests.is_empty();
                let hard: Vec<String> = HARD7
                    .iter()
                    .filter(|op| d2.stats.fallback_comments.contains_key(*op))
                    .map(|op| op.to_string())
                    .collect();
                recompile.push(RecompileRow {
                    abc: rel,
                    case: pkg.path.clone(),
                    // No producer pin for the wild set: newest es2abc.
                    version: "24.0.0.0".to_string(),
                    profile: "baseline".to_string(),
                    module: is_module,
                    hard_fallbacks: hard,
                    functions: file_method_count(&file),
                    js_bytes: d2.text.len(),
                });
            } else {
                let (msg, bt) =
                    take_panic().unwrap_or_else(|| ("unknown panic".to_string(), String::new()));
                row.fail("decompile", "panic", format!("call_entry variant: {msg}"));
                row.backtrace = Some(bt);
            }

            rows.push(row);
        }
    }

    // ── artifacts ────────────────────────────────────────────────────
    let mut jsonl = String::new();
    for row in &rows {
        jsonl.push_str(&serde_json::to_string(row).expect("serialize row"));
        jsonl.push('\n');
    }
    std::fs::write(out.join("smoke-modules.jsonl"), &jsonl).expect("write module rows");

    let mut manifest_jsonl = String::new();
    for row in &recompile {
        manifest_jsonl.push_str(&serde_json::to_string(row).expect("serialize row"));
        manifest_jsonl.push('\n');
    }
    std::fs::write(out.join("decompile-manifest.jsonl"), &manifest_jsonl)
        .expect("write recompile manifest");

    // ── console histogram ────────────────────────────────────────────
    let mut by_status: std::collections::BTreeMap<&str, usize> = Default::default();
    for row in &rows {
        *by_status.entry(row.status.as_str()).or_insert(0) += 1;
    }
    let mut decompile_times: Vec<u64> = rows.iter().filter_map(|r| r.decompile_ms).collect();
    decompile_times.sort_unstable();
    let pct = |p: usize| -> u64 {
        if decompile_times.is_empty() {
            return 0;
        }
        decompile_times[(decompile_times.len() * p / 100).min(decompile_times.len() - 1)]
    };
    let total_js: usize = rows.iter().filter_map(|r| r.js_bytes).sum();
    eprintln!(
        "WILD-SMOKE packages={} modules={}",
        manifest.packages.len(),
        rows.len()
    );
    for (status, n) in &by_status {
        eprintln!("WILD-SMOKE status {status} = {n}");
    }
    eprintln!(
        "WILD-SMOKE decompile_ms p50={} p95={} max={} js_bytes_total={total_js}",
        pct(50),
        pct(95),
        decompile_times.last().copied().unwrap_or(0),
    );
    eprintln!(
        "WILD-SMOKE recompile rows={} -> {}",
        recompile.len(),
        out.join("decompile-manifest.jsonl").display()
    );
    let panics: Vec<_> = rows.iter().filter(|r| r.status == "panic").collect();
    if !panics.is_empty() {
        eprintln!("WILD-SMOKE P0 PANICS ({}):", panics.len());
        for p in &panics {
            eprintln!(
                "  PANIC {}#{} stage={:?}: {}",
                p.pkg,
                p.entry,
                p.failed_stage,
                p.error.as_deref().unwrap_or("?")
            );
        }
    }
}

/// Recompile-channel check: after `scripts/dream-gate.py --gate-dir
/// exports/wild-decompile --skip-compare` has run (docker, on dabai),
/// decode every recompiled artifact and compare its function count
/// against the original module's. Report-only.
#[test]
#[ignore = "requires the exported wild corpus + a completed docker recompile"]
fn wild_smoke_recompile_check() {
    let out = smoke_out_root();
    let manifest_path = out.join("decompile-manifest.jsonl");
    let results_path = out.join("compile-results.json");
    if !manifest_path.exists() || !results_path.exists() {
        eprintln!(
            "wild-smoke recompile: no artifacts at {out:?} (run wild_smoke_sweep + \
             scripts/dream-gate.py --gate-dir ... --skip-compare first), skipping"
        );
        return;
    }
    install_panic_capture();

    let rows: Vec<RecompileRow> = std::fs::read_to_string(&manifest_path)
        .expect("read recompile manifest")
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str(l).expect("parse recompile row"))
        .collect();
    let results: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&results_path).expect("read compile results"),
    )
    .expect("parse compile results");

    #[derive(serde::Serialize)]
    struct ReRow {
        abc: String,
        compiled: bool,
        compile_error: Option<String>,
        orig_functions: usize,
        recompiled_functions: Option<usize>,
        recompiled_decode_error: Option<String>,
        recompiled_panic: Option<String>,
    }

    let mut out_rows: Vec<ReRow> = Vec::new();
    for row in &rows {
        let res = results.get(row.abc.as_str()).cloned().unwrap_or_else(
            || serde_json::json!({"compiled": false, "error": "no compile record"}),
        );
        let compiled = res["compiled"].as_bool().unwrap_or(false);
        let mut re_row = ReRow {
            abc: row.abc.clone(),
            compiled,
            compile_error: res["error"].as_str().map(|s| s.to_string()),
            orig_functions: row.functions,
            recompiled_functions: None,
            recompiled_decode_error: None,
            recompiled_panic: None,
        };
        if compiled {
            let path = out.join("abc").join(&row.abc);
            match std::fs::read(&path) {
                Ok(bytes) => {
                    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        abcd_file::decode(&bytes)
                    })) {
                        Ok(Ok(f)) => re_row.recompiled_functions = Some(file_method_count(&f)),
                        Ok(Err(e)) => re_row.recompiled_decode_error = Some(e.to_string()),
                        Err(_) => {
                            let (msg, _bt) = take_panic()
                                .unwrap_or_else(|| ("unknown panic".to_string(), String::new()));
                            re_row.recompiled_panic = Some(msg);
                        }
                    }
                }
                Err(e) => {
                    re_row.recompiled_decode_error = Some(format!("artifact unreadable: {e}"))
                }
            }
        }
        out_rows.push(re_row);
    }

    let mut jsonl = String::new();
    for row in &out_rows {
        jsonl.push_str(&serde_json::to_string(row).expect("serialize row"));
        jsonl.push('\n');
    }
    std::fs::write(out.join("recompile-check.jsonl"), &jsonl).expect("write recompile rows");

    let compiled = out_rows.iter().filter(|r| r.compiled).count();
    let decode_ok = out_rows
        .iter()
        .filter(|r| r.recompiled_functions.is_some())
        .count();
    let decode_fail = out_rows
        .iter()
        .filter(|r| r.recompiled_decode_error.is_some())
        .count();
    let panics = out_rows
        .iter()
        .filter(|r| r.recompiled_panic.is_some())
        .count();
    eprintln!(
        "WILD-RECOMPILE rows={} compiled={compiled} recompiled-decode-ok={decode_ok} \
         recompiled-decode-fail={decode_fail} recompiled-decode-panic={panics}",
        out_rows.len()
    );
    // Function-count comparison (same metric both sides): report the
    // distribution, flag the worst drops as suspects.
    let mut deltas: Vec<(i64, &ReRow)> = out_rows
        .iter()
        .filter_map(|r| {
            r.recompiled_functions
                .map(|n| (n as i64 - r.orig_functions as i64, r))
        })
        .collect();
    deltas.sort_by_key(|(d, _)| *d);
    if !deltas.is_empty() {
        let zero = deltas.iter().filter(|(d, _)| *d == 0).count();
        eprintln!(
            "WILD-RECOMPILE function-count: exact-match={zero}/{} min-delta={} max-delta={}",
            deltas.len(),
            deltas.first().map(|(d, _)| *d).unwrap_or(0),
            deltas.last().map(|(d, _)| *d).unwrap_or(0),
        );
        eprintln!("WILD-RECOMPILE largest drops (suspects):");
        for (d, r) in deltas.iter().take(10) {
            eprintln!(
                "  DELTA {d:+} {} (orig={} recompiled={})",
                r.abc,
                r.orig_functions,
                r.recompiled_functions.unwrap_or(0)
            );
        }
    }
}
