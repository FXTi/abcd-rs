//! The wild gate: the core-25 wild-OHOS subset promoted from the
//! local-only smoke instrument (`wild_smoke.rs`) to a per-push CI gate.
//! Design: `design/wild-gate-evaluation.md` — the maintainer-approved
//! semantics are **A + B + the standing laws** (§6.E):
//!
//! - **A — recompile acceptance.** Per core-25 package: `abcd_hap`
//!   container extract → per module `abcd_file::decode` →
//!   `abcd_lift::lift_file` → `verify_module` (0 errors) → decompile
//!   with the dream gate's recompile config (`EmitOptions::call_entry`)
//!   → the GHCR image's es2abc (24.0.0.0/baseline, script mode — 0/64
//!   core-25 modules are ESM-flagged) **must accept** the emitted text
//!   (a `SyntaxError` is RED: that is the N79/N80 silent-emitter-bug
//!   capture surface) → the recompiled artifact must itself decode →
//!   function-count sanity: recompiled ≥ original (same
//!   `file.classes[*].methods.len()` metric on both sides).
//! - **B — fallback ledger + tripwire.** Per-package fallback-function
//!   accounting (`stats.functions_with_fallbacks`, summed over the
//!   package's modules) is gated against
//!   `scripts/wild-dream-divergences.json` (format copied from
//!   `scripts/test262-dream-divergences.json`): a package whose
//!   `[fallbacks, ir_functions]` pair drifted without a relist is RED
//!   (undocumented drift), and a listed row that no longer matches is
//!   RED too (stale — the ledger can never silently rot; fixing a
//!   fallback forces the delist, the self-cleaning property). On top,
//!   the coarse global tripwire: total fallback functions ≤ 1% of
//!   lifted functions (~10× the measured 0.116%).
//! - **Standing laws.** Any panic is red, lift errors = 0, verify
//!   errors = 0, and the selection totals are hard-asserted: exactly
//!   the 25 embedded packages, 64 modules, each `decode-ok` with the
//!   manifest's byte size — corpus-image drift goes red, no silent
//!   skips once the corpus is present.
//!
//! Skip-by-absence (the house rule for corpus suites): with no exported
//! wild corpus the gate prints a skip line and returns; it is
//! `#[ignore]`d and only runs where the corpus is exported (CI
//! `wild-gate` job, dabai).
//!
//! The core-25 list is EMBEDDED below (not read from the manifest):
//! a manifest change requires a corpus-image re-curation + digest bump
//! anyway, and the embedded list makes that drift a compile-time-visible
//! review act. Provenance: the q-P12 core-25 pick list, measured in
//! `design/wild-gate-evaluation.md` §3.2.
//!
//! Ledger regeneration: run the gate once; it writes the observed
//! per-package counts to `target/wild-gate/fallback-observed.json`
//! (also on failure — the failure message names the drifted rows).
//! Copy the map into `scripts/wild-dream-divergences.json` under
//! `fallback-counts` and re-run: green means the relist is exact.
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-decompile --release -- --ignored --nocapture wild_gate
//! ```

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use abcd_decompile::emit::{decompile_module, EmitOptions};
use rayon::prelude::*;

/// The core-25 selection (q-P12 pick list; evaluation §2/§3.2). Paths
/// are relative to `exports/corpus/wild/wild-haps/`. Grouped by OS
/// release, exactly as the pick list orders them; the trailing
/// 4.0-Beta2 Calc_Demo is the special FA-shape package.
const CORE25: &[&str] = &[
    // 3.2-Release
    "OpenHarmony-3.2-Release/Launcher.hap",
    "OpenHarmony-3.2-Release/CallUI.hap",
    "OpenHarmony-3.2-Release/adminprovisioning.hap",
    // 4.0-Release
    "OpenHarmony-4.0-Release/Settings.hap",
    "OpenHarmony-4.0-Release/dlp_manager.hap",
    "OpenHarmony-4.0-Release/SystemUI-SystemDialog.hap",
    // 4.1-Release
    "OpenHarmony-4.1-Release/Photos.hap",
    "OpenHarmony-4.1-Release/SystemUI.hap",
    "OpenHarmony-4.1-Release/Contacts_DataAbility.hap",
    // 5.0.3-Release
    "OpenHarmony-5.0.3-Release/Settings.hap",
    "OpenHarmony-5.0.3-Release/power_dialog.hap",
    "OpenHarmony-5.0.3-Release/SystemUI.hap",
    // 5.1.0-Release
    "OpenHarmony-5.1.0-Release/Photos.hap",
    "OpenHarmony-5.1.0-Release/AuthWidget.hap",
    "OpenHarmony-5.1.0-Release/Calc_Demo.hap",
    // 6.0-Release
    "OpenHarmony-6.0-Release/Contacts.hap",
    "OpenHarmony-6.0-Release/AuthWidget.hap",
    "OpenHarmony-6.0-Release/MobileDataSettings.hap",
    // 6.1-LTS
    "OpenHarmony-6.1-LTS/Photos.hap",
    "OpenHarmony-6.1-LTS/Contacts.hap",
    "OpenHarmony-6.1-LTS/SystemUI-NavigationBar.hap",
    // 7.0-Beta1
    "OpenHarmony-7.0-Beta1/Settings.hap",
    "OpenHarmony-7.0-Beta1/Launcher.hap",
    "OpenHarmony-7.0-Beta1/Music_Demo.hap",
    // The special FA-shape package (4.0-Beta2).
    "OpenHarmony-4.0-Beta2/Calc_Demo.hap",
];

/// Hard-asserted selection totals (evaluation §3: 25 packages / 64
/// modules). Corpus drift on the pinned image goes red here.
const EXPECTED_MODULES: usize = 64;

/// The global fallback tripwire (evaluation §6.B layer 2): total
/// fallback functions must stay ≤ 1% of lifted IR functions — ~10×
/// headroom over the measured 0.116%, the anti-rubber-stamp guard
/// against relisting a creeping degradation one row at a time.
const FALLBACK_TRIPWIRE_PERCENT: f64 = 1.0;

/// The exported wild corpus root; same override as the hap-file gate.
fn wild_corpus_root() -> PathBuf {
    std::env::var_os("ABCD_CORPUS_WILD_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus/wild/wild-haps")
        })
}

/// The gate root inside `target/` (never committed), mirroring the
/// dream gate's layout so `scripts/dream-gate.py` drives the es2abc
/// recompile with zero new machinery.
fn gate_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("wild-gate")
}

/// The fallback ledger (committed; format copied from
/// `scripts/test262-dream-divergences.json`).
fn ledger_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("scripts/wild-dream-divergences.json")
}

/// One wild-corpus manifest row (only the fields the gate reads; the
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

/// Per-package fallback accounting: `[functions_with_fallbacks,
/// ir_functions]`, summed over the package's modules. Packages with
/// zero fallbacks are absent from the map (same convention as the
/// empty buckets in the test262 ledger).
type FallbackCounts = BTreeMap<String, [usize; 2]>;

/// The ledger file shape: a `$comment` provenance header plus the
/// `fallback-counts` class key (the test262-dream-divergences format).
#[derive(Debug, serde::Deserialize)]
struct FallbackLedger {
    #[serde(rename = "fallback-counts")]
    fallback_counts: FallbackCounts,
}

/// One dream-gate-format manifest row for the recompile channel
/// (`scripts/dream-gate.py` reads `abc`/`version`/`profile`/`module`;
/// `case`/`hard_fallbacks` keep the row shape identical to the dream
/// gate's; `functions` is ours — the recheck's original-side count).
#[derive(Debug, serde::Serialize)]
struct RecompileRow {
    abc: String,
    case: String,
    version: String,
    profile: String,
    module: bool,
    hard_fallbacks: Vec<String>,
    functions: usize,
}

/// The hard-7 / documented fallback ops (same list as the dream gate;
/// informational on this gate — every core-25 fallback is in this
/// async/generator-machinery family, evaluation §3.2).
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

/// Total method count of a decoded file (the function-count metric the
/// recheck applies to BOTH sides identically).
fn file_method_count(file: &abcd_file::File) -> usize {
    file.classes.values().map(|c| c.methods.len()).sum()
}

/// The B-plan ledger gate (self-cleaning, hard-error BOTH directions):
///
/// - **undocumented drift = red**: an observed package with fallbacks
///   whose `[fallbacks, ir_functions]` pair is not listed verbatim;
/// - **stale = red**: a listed row that no longer matches the observed
///   pair (including a package that dropped to zero fallbacks — fixing
///   fallbacks forces the delist);
/// - **tripwire = red**: the global fallback rate over ALL selected
///   packages (zero-fallback ones included) exceeds 1%.
///
/// `observed` carries only nonzero-fallback packages; the totals carry
/// the full selection. Returns the list of violations (empty = green).
fn check_fallback_ledger(
    observed: &FallbackCounts,
    ledger: &FallbackCounts,
    total_fallbacks: usize,
    total_functions: usize,
) -> Vec<String> {
    let mut violations = Vec::new();
    for (pkg, counts) in observed {
        match ledger.get(pkg) {
            Some(listed) if listed == counts => {}
            Some(listed) => violations.push(format!(
                "undocumented fallback drift in {pkg}: observed {counts:?}, ledger lists {listed:?} \
                 — relist scripts/wild-dream-divergences.json deliberately"
            )),
            None => violations.push(format!(
                "undocumented fallbacks in {pkg}: observed {counts:?}, no ledger row \
                 — relist scripts/wild-dream-divergences.json deliberately"
            )),
        }
    }
    for (pkg, listed) in ledger {
        if observed.get(pkg) != Some(listed) {
            let now = observed
                .get(pkg)
                .map(|c| format!("{c:?}"))
                .unwrap_or_else(|| "zero fallbacks (delist the row)".to_string());
            violations.push(format!(
                "stale ledger row for {pkg}: ledger lists {listed:?}, observed {now} \
                 — a stale ledger can never silently rot"
            ));
        }
    }
    let rate = total_fallbacks as f64 / total_functions.max(1) as f64 * 100.0;
    if rate > FALLBACK_TRIPWIRE_PERCENT {
        violations.push(format!(
            "global fallback tripwire: {total_fallbacks}/{total_functions} = {rate:.3}% > \
             {FALLBACK_TRIPWIRE_PERCENT}% — the anti-rubber-stamp guard fired"
        ));
    }
    violations
}

/// Parse the committed ledger file (the `$comment` header is
/// provenance, not data).
fn load_ledger(path: &Path) -> FallbackCounts {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read the fallback ledger {}: {e}", path.display()));
    let ledger: FallbackLedger = serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("parse the fallback ledger {}: {e}", path.display()));
    ledger.fallback_counts
}

/// One module's pipeline outcome (the rayon loop's element type).
struct ModuleOut {
    /// The recompile-channel key: `<pkg path>#<entry name>`.
    rel: String,
    pkg: String,
    file_methods: usize,
    ir_functions: usize,
    functions_with_fallbacks: usize,
    hard_fallbacks: Vec<String>,
    is_module: bool,
    js: String,
}

/// Stage A + generation: decode → lift → verify → decompile
/// (`call_entry`) for one module. Any failure panics with the module
/// named — the standing laws make panics/lift/verify failures RED, and
/// rayon propagates the panic out of the parallel loop.
fn process_module(pkg: &str, entry: &str, data: &[u8]) -> ModuleOut {
    let rel = format!("{pkg}#{entry}");
    let file = abcd_file::decode(data).unwrap_or_else(|e| panic!("wild-gate decode {rel}: {e}"));
    let module =
        abcd_lift::lift_file(&file).unwrap_or_else(|e| panic!("wild-gate lift {rel}: {e:?}"));
    let report = abcd_ir::verify_module(&module);
    assert!(
        report.errors.is_empty(),
        "wild-gate verify {rel}: {} errors, first: {:?}",
        report.errors.len(),
        report.errors.first()
    );
    let opts = EmitOptions {
        call_entry: true,
        ..EmitOptions::default()
    };
    let d = decompile_module(&module, &opts);
    let is_module = !module.imports.is_empty()
        || !module.exports.is_empty()
        || !module.module_requests.is_empty();
    let hard_fallbacks = HARD7
        .iter()
        .filter(|op| d.stats.fallback_comments.contains_key(*op))
        .map(|op| op.to_string())
        .collect();
    ModuleOut {
        rel,
        pkg: pkg.to_string(),
        file_methods: file_method_count(&file),
        ir_functions: module.functions.len(),
        functions_with_fallbacks: d.stats.functions_with_fallbacks,
        hard_fallbacks,
        is_module,
        js: d.text,
    }
}

/// Load the wild manifest and select the embedded core-25 rows,
/// hard-asserting the selection's shape (all 25 present, all
/// `decode-ok`). Returns rows in CORE25 order.
fn select_core25(root: &Path) -> Option<Vec<WildPackage>> {
    let manifest_path = root.join("manifest.json");
    if !manifest_path.exists() {
        eprintln!("wild-gate: no wild corpus at {root:?}, skipping (corpus not exported)");
        return None;
    }
    let manifest: WildManifest =
        serde_json::from_str(&std::fs::read_to_string(&manifest_path).expect("read wild manifest"))
            .expect("parse wild manifest");
    let selected: Vec<WildPackage> = CORE25
        .iter()
        .map(|path| {
            let rows: Vec<_> = manifest
                .packages
                .iter()
                .filter(|p| &p.path == path)
                .collect();
            assert_eq!(
                rows.len(),
                1,
                "core-25 package {path} must appear exactly once in the wild manifest \
                 (found {}) — corpus drift is red",
                rows.len()
            );
            assert_eq!(
                rows[0].expectation, "decode-ok",
                "core-25 package {path} must stay decode-ok (the negative-11 are the \
                 hap-file gate's) — expectation drift is red"
            );
            WildPackage {
                path: rows[0].path.clone(),
                size: rows[0].size,
                expectation: rows[0].expectation.clone(),
            }
        })
        .collect();
    assert_eq!(
        selected.len(),
        25,
        "the core-25 selection is exactly 25 packages"
    );
    Some(selected)
}

/// Stage A + generation phase: run the per-module pipeline in parallel
/// (rayon; decompile is 98% of the gate's Rust time, evaluation §4),
/// write the dream-gate-layout JS tree + manifest, and return the
/// per-module outcomes in deterministic (CORE25, container) order.
fn generate(packages: &[WildPackage]) -> Vec<ModuleOut> {
    let root = wild_corpus_root();
    // The parallel loop's work list: (pkg, entry, module bytes), read
    // serially (extract is sub-millisecond per package, evaluation §3.1).
    let mut work: Vec<(String, String, Vec<u8>)> = Vec::new();
    for pkg in packages {
        let bytes = std::fs::read(root.join(&pkg.path))
            .unwrap_or_else(|e| panic!("wild-gate read {}: {e}", pkg.path));
        assert_eq!(
            bytes.len() as u64,
            pkg.size,
            "wild-gate {}: byte size {} != manifest {} — corpus drift is red",
            pkg.path,
            bytes.len(),
            pkg.size
        );
        let modules = abcd_hap::abc_modules(&bytes)
            .unwrap_or_else(|e| panic!("wild-gate container {}: {e}", pkg.path));
        for m in &modules {
            work.push((
                pkg.path.clone(),
                m.entry_name.clone(),
                m.data.as_slice().to_vec(),
            ));
        }
    }
    assert_eq!(
        work.len(),
        EXPECTED_MODULES,
        "the core-25 selection is exactly {EXPECTED_MODULES} modules (found {}) — \
         corpus drift is red",
        work.len()
    );

    work.par_iter()
        .map(|(pkg, entry, data)| process_module(pkg, entry, data))
        .collect()
}

/// The es2abc recompile channel, driven by `scripts/dream-gate.py`
/// exactly as the dream gate drives it (same docker invocation: pinned
/// image, `--network none`, 900s per-compile timeout inside the
/// script), `--jobs 4` for the GH 4-vCPU runner. The gate root carries
/// a dummy `compare-stdout.json` because `--skip-compare` still reads
/// it for the (informational here) triage histogram.
fn recompile(jobs: usize) {
    let gate = gate_root();
    std::fs::write(
        gate.join("compare-stdout.json"),
        r#"{"results": [], "passed": 0, "missing": []}"#,
    )
    .expect("write dummy compare-stdout.json");
    let script = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("scripts")
        .join("dream-gate.py");
    let out = std::process::Command::new("python3")
        .arg(&script)
        .arg("--gate-dir")
        .arg(&gate)
        .arg("--skip-compare")
        .arg("--jobs")
        .arg(jobs.to_string())
        .output()
        .expect("run scripts/dream-gate.py (docker es2abc recompile)");
    let text =
        String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr);
    eprintln!("{text}");
    assert!(out.status.success(), "scripts/dream-gate.py failed: {text}");
}

/// The main gate: A (recompile acceptance) + B (fallback ledger +
/// tripwire) + the standing laws, over the core-25 wild set.
#[test]
#[ignore = "requires the exported wild corpus, python3, and docker (CI wild-gate job / dabai)"]
fn wild_gate() {
    let root = wild_corpus_root();
    let Some(packages) = select_core25(&root) else {
        return; // skip-by-absence: no exported wild corpus.
    };
    let outs = generate(&packages);

    // ── write the dream-gate-layout artifacts ────────────────────────
    let gate = gate_root();
    let src_root = gate.join("src");
    std::fs::create_dir_all(&src_root).expect("create gate src root");
    let mut manifest = String::new();
    for out in &outs {
        let js_path = src_root.join(format!("{}.js", out.rel));
        std::fs::create_dir_all(js_path.parent().expect("parent")).expect("mkdirs");
        std::fs::write(&js_path, &out.js).expect("write js");
        let row = RecompileRow {
            abc: out.rel.clone(),
            case: out.pkg.clone(),
            // No producer pin for the wild set: newest es2abc.
            version: "24.0.0.0".to_string(),
            profile: "baseline".to_string(),
            module: out.is_module,
            hard_fallbacks: out.hard_fallbacks.clone(),
            functions: out.file_methods,
        };
        manifest.push_str(&serde_json::to_string(&row).expect("serialize row"));
        manifest.push('\n');
    }
    std::fs::write(gate.join("decompile-manifest.jsonl"), manifest).expect("write manifest");

    // ── B: fallback ledger + global tripwire ─────────────────────────
    // Per-package pairs over ALL of the package's modules (a fallback-
    // free module still contributes its IR functions to the pair).
    let mut per_pkg: FallbackCounts = BTreeMap::new();
    let mut total_fallbacks = 0usize;
    let mut total_functions = 0usize;
    for out in &outs {
        total_fallbacks += out.functions_with_fallbacks;
        total_functions += out.ir_functions;
        let entry = per_pkg.entry(out.pkg.clone()).or_insert([0, 0]);
        entry[0] += out.functions_with_fallbacks;
        entry[1] += out.ir_functions;
    }
    let observed: FallbackCounts = per_pkg.into_iter().filter(|(_, [fb, _])| *fb > 0).collect();
    // The observed counts land in target/ on EVERY run (green or red):
    // the relist workflow copies this map into the ledger.
    std::fs::write(
        gate.join("fallback-observed.json"),
        serde_json::to_string_pretty(&observed).expect("serialize observed"),
    )
    .expect("write observed fallback counts");
    let ledger = load_ledger(&ledger_path());
    let violations = check_fallback_ledger(&observed, &ledger, total_fallbacks, total_functions);
    let rate = total_fallbacks as f64 / total_functions.max(1) as f64 * 100.0;
    eprintln!(
        "WILD-GATE fallback accounting: {total_fallbacks}/{total_functions} = {rate:.3}% \
         (tripwire {FALLBACK_TRIPWIRE_PERCENT}%), ledger rows={}",
        ledger.len()
    );
    assert!(
        violations.is_empty(),
        "wild-gate fallback ledger violations:\n  {}",
        violations.join("\n  ")
    );

    // ── A: es2abc recompile acceptance ───────────────────────────────
    recompile(4);
    let results: BTreeMap<String, serde_json::Value> = serde_json::from_str(
        &std::fs::read_to_string(gate.join("compile-results.json")).expect("read compile results"),
    )
    .expect("parse compile results");
    assert_eq!(
        results.len(),
        outs.len(),
        "one compile record per module ({} != {})",
        results.len(),
        outs.len()
    );
    let mut rejections = Vec::new();
    for out in &outs {
        let res = &results[&out.rel];
        if !res["compiled"].as_bool().unwrap_or(false) {
            // A SyntaxError here is the N79/N80 capture surface: our
            // emitted text does not parse — RED, ours by the dream
            // gate's triage rule. Anything else is triaged the same
            // way on this gate: red with the compiler's first line.
            rejections.push(format!(
                "{}: {}",
                out.rel,
                res["error"].as_str().unwrap_or("<no error recorded>")
            ));
        }
    }
    assert!(
        rejections.is_empty(),
        "wild-gate es2abc rejections ({} module(s)):\n  {}",
        rejections.len(),
        rejections.join("\n  ")
    );

    // ── A: recompiled-artifact decode + function-count sanity ────────
    for out in &outs {
        let path = gate.join("abc").join(&out.rel);
        let bytes = std::fs::read(&path)
            .unwrap_or_else(|e| panic!("wild-gate recompiled artifact {}: {e}", out.rel));
        let file = abcd_file::decode(&bytes)
            .unwrap_or_else(|e| panic!("wild-gate recompiled decode {}: {e}", out.rel));
        let recompiled = file_method_count(&file);
        assert!(
            recompiled >= out.file_methods,
            "wild-gate function loss in {}: recompiled {recompiled} < original {}",
            out.rel,
            out.file_methods
        );
    }
    eprintln!(
        "WILD-GATE green: {} packages / {} modules, es2abc accepted {}, recompiled decode ok, \
         function counts >= original",
        packages.len(),
        outs.len(),
        outs.len()
    );
}

/// Red-path proof #1 (the A channel): feed the recompile pipeline a
/// deliberately broken JS and assert the channel reports it EXACTLY the
/// way the main gate turns red on — `compiled: false` with a
/// `SyntaxError` from es2abc. If this test ever goes green-by-accident
/// (es2abc accepting garbage, or the error shape changing), the main
/// gate's failure path is silently broken and this test catches it.
#[test]
#[ignore = "requires python3 and docker (the es2abc recompile channel)"]
fn wild_gate_red_proof_es2abc_rejection() {
    let root = wild_corpus_root();
    if !root.join("manifest.json").exists() {
        eprintln!(
            "wild-gate red proof: no wild corpus at {root:?}, skipping (corpus not exported)"
        );
        return;
    }
    let gate = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("wild-gate-red-proof");
    let src_root = gate.join("src");
    std::fs::create_dir_all(&src_root).expect("create red-proof src root");
    // Deliberately unparseable: an unclosed parameter list.
    std::fs::write(src_root.join("bad.js"), "function broken( { return 1; }\n")
        .expect("write bad js");
    std::fs::write(
        gate.join("decompile-manifest.jsonl"),
        "{\"abc\": \"bad\", \"case\": \"red-proof\", \"version\": \"24.0.0.0\", \
         \"profile\": \"baseline\", \"module\": false, \"hard_fallbacks\": []}\n",
    )
    .expect("write red-proof manifest");
    std::fs::write(
        gate.join("compare-stdout.json"),
        r#"{"results": [], "passed": 0, "missing": []}"#,
    )
    .expect("write dummy compare-stdout.json");
    let script = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("scripts")
        .join("dream-gate.py");
    let out = std::process::Command::new("python3")
        .arg(&script)
        .arg("--gate-dir")
        .arg(&gate)
        .arg("--skip-compare")
        .arg("--jobs")
        .arg("1")
        .output()
        .expect("run scripts/dream-gate.py (docker es2abc recompile)");
    eprintln!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let results: BTreeMap<String, serde_json::Value> = serde_json::from_str(
        &std::fs::read_to_string(gate.join("compile-results.json")).expect("read compile results"),
    )
    .expect("parse compile results");
    let bad = &results["bad"];
    assert_eq!(
        bad["compiled"].as_bool(),
        Some(false),
        "es2abc must reject the injected bad JS: {bad}"
    );
    let error = bad["error"].as_str().unwrap_or("");
    assert!(
        error.contains("SyntaxError"),
        "the rejection must surface as a SyntaxError (the main gate's red signal), got: {error}"
    );
    eprintln!("WILD-GATE red proof #1: es2abc rejected the injected bad JS with: {error}");
}

/// Red-path proof #2 (the B channel), pure-data unit tests of the
/// ledger gate: unregistered drift, stale rows, and the global
/// tripwire must all hard-error; an exact match must pass. These run
/// in plain `cargo test` (no corpus, no docker) so the ledger's red
/// paths are exercised on every lane.
mod ledger_red_tests {
    use super::*;

    fn observed(pairs: &[(&str, [usize; 2])]) -> FallbackCounts {
        pairs.iter().map(|(k, v)| (k.to_string(), *v)).collect()
    }

    #[test]
    fn green_on_exact_match() {
        let obs = observed(&[("a/One.hap", [3, 100]), ("b/Two.hap", [1, 50])]);
        let violations = check_fallback_ledger(&obs, &obs.clone(), 4, 1000);
        assert!(violations.is_empty(), "{violations:?}");
    }

    #[test]
    fn red_on_unregistered_fallbacks() {
        let obs = observed(&[("a/One.hap", [3, 100])]);
        let violations = check_fallback_ledger(&obs, &FallbackCounts::new(), 3, 1000);
        assert_eq!(violations.len(), 1, "{violations:?}");
        assert!(
            violations[0].contains("undocumented fallbacks"),
            "{violations:?}"
        );
    }

    #[test]
    fn red_on_count_drift_without_relist() {
        let obs = observed(&[("a/One.hap", [4, 100])]);
        let ledger = observed(&[("a/One.hap", [3, 100])]);
        let violations = check_fallback_ledger(&obs, &ledger, 4, 1000);
        // Both directions fire: the observed pair is undocumented AND
        // the listed pair is stale.
        assert_eq!(violations.len(), 2, "{violations:?}");
    }

    #[test]
    fn red_on_stale_row_after_fallback_fix() {
        // The self-cleaning property: a fallback got fixed, the
        // package dropped to zero, the listed row is now stale = red
        // until delisted.
        let ledger = observed(&[("a/One.hap", [3, 100])]);
        let violations = check_fallback_ledger(&FallbackCounts::new(), &ledger, 0, 1000);
        assert_eq!(violations.len(), 1, "{violations:?}");
        assert!(violations[0].contains("stale ledger row"), "{violations:?}");
    }

    #[test]
    fn red_on_global_tripwire() {
        // 11/1000 = 1.1% > 1% even though the per-package rows match.
        let obs = observed(&[("a/One.hap", [11, 1000])]);
        let violations = check_fallback_ledger(&obs, &obs.clone(), 11, 1000);
        assert_eq!(violations.len(), 1, "{violations:?}");
        assert!(violations[0].contains("tripwire"), "{violations:?}");
    }

    #[test]
    fn committed_ledger_parses() {
        // The committed ledger must stay well-formed on every lane.
        let ledger = load_ledger(&ledger_path());
        for (pkg, [fb, ir]) in &ledger {
            assert!(
                *fb > 0,
                "zero-fallback rows do not belong in the ledger: {pkg}"
            );
            assert!(*fb <= *ir, "fallbacks > functions is nonsense: {pkg}");
        }
    }
}
