//! Opt-in corpus test (requires the exported GHCR corpus): for every
//! manifest row with `runtime.status == "passed"` (1149 fixtures),
//! decode → `abcd_lift::lift_file` (v0.2 lift) → ir2 verify → lower →
//! encode, writing the result to `$ABCD_LOWERED_DIR/<variant>/` for the
//! black-box VM oracle (`scripts/compare-rewritten-corpus.py`).
//!
//! Two variants are produced per fixture (mirroring the v0.1 driver's
//! `lift`/`opt` pair):
//!
//! - `v2lift`: decode → lift → verify → `abcd_lower::lower_function` +
//!   `to_method_body` every function → splice → `abcd_file::encode` —
//!   also the byte-identity faithfulness baseline against the v0.1
//!   pipeline's `lift` tree.
//! - `v2opt`: decode → lift → verify → `abcd_opt::optimize_module` →
//!   RE-VERIFY (post-optimize; N27/N28 hygiene gate) → lower → encode —
//!   the byte-identity comparison target for the v0.1 pipeline's `opt`
//!   tree.
//! - `v2inline` (v2-P3b, D2): decode → lift → verify →
//!   `abcd_opt::inline::inline_module` (OPT-IN — never part of
//!   `optimize_module`, so the v2lift/v2opt gates are untouched) →
//!   RE-VERIFY → lower → encode. Byte output WILL differ from v2lift
//!   (that is the point); the gate is the VM oracle (inlining must not
//!   change observable behavior) plus determinism. Aggregate inline
//!   statistics (sites inlined, instructions cloned, skip-reason
//!   histogram) are printed at the end as `INLINE-STATS`/`INLINE-SKIP`
//!   lines. The v2inline determinism double-run (re-run the whole rewrite
//!   per fixture from a fresh front-end, assert byte-identical encodes)
//!   is ON by default (W6, q-P2); `ABCD_INLINE_DETERMINISM=0` opts out.
//!
//! ## Gate 2 (v2opt vs v0.1 opt byte-identity) — ACCEPTED form
//!
//! Maintainer ruling (2026-09-21, v2-P3): the accepted divergence set is
//! **1149/1149 minus the 53 N62 files minus 90 v2-P3 files**, all
//! attributed (mechanisms documented in `abcd-opt/src/lib.rs`):
//!
//! - **P3-M1 (72 files)**: v0.1's fold engines re-materialize a folded
//!   NaN/+∞ as `LiteralNumber` → isel `fldai`; v0.2's pooled
//!   `Const::Number` keeps the canonical bits → `ldnan`/`ldinfinity`.
//!   v0.2 preserves the opcode identity v0.1 degrades; VM-identical.
//! - **P3-M2 (12 files)**: v0.1's ADCE hand-list marked `DefineFunc`
//!   essential; the v0.2 effects table derives honest effects
//!   (vendor `RuntimeDefinefunc` runs no user code,
//!   runtime_stubs-inl.h:2459-2505), so ADCE deletes dead
//!   definefunc+closure chains. Sound dead-code removal.
//! - **N63 (6 files)**: v0.1's SCCP lattice left exception-param values
//!   at Top (the lattice identity), folding phis that mix a constant
//!   with the exception object to the constant; v0.2 resolves
//!   `ValueDef::ExceptionParam` to Bottom and keeps the phi — strictly
//!   more sound (v0.1 frozen; superseded).
//!
//! All three are VM-neutral: the v2opt tree passes the VM oracle
//! 1149/1149 (image sha256:5e7627…).
//!
//! Per fixture and variant this is all-or-nothing: if ANY function fails
//! to lower/relocate (`LowerError`, including `UnsupportedInstruction` /
//! `UntraceableEntity`) or encode fails, that variant is not written and
//! the skip is reported as:
//!
//! ```text
//! SKIP <variant> <path> | <category> | <reason>
//! ```
//!
//! with the SAME fixed category vocabulary as the v0.1 driver: `lift`
//! (front-end: read/decode/lift), `verify` (ir2 structural verifier,
//! pre- or post-optimize), `lower-unsupported:<instruction>`
//! (`LowerError::UnsupportedInstruction`),
//! `lower-untraceable:<EntityKind>` (`LowerError::UntraceableEntity`),
//! `lower-other` (any other lower/to_method_body error), `encode`, and
//! `panic` (caught by `catch_unwind`). Successful rewrites are reported
//! as `WROTE <variant> <path> (N functions)`. At the end a sorted
//! category → count histogram is printed per variant.
//!
//! Selection: by default ALL passed rows are processed. Setting
//! `ABCD_LOWERED_CASE` to a comma-separated case list (e.g.
//! `ABCD_LOWERED_CASE=local/arithmetic`) restricts the run to those
//! cases.
//!
//! Fresh output tree per run: a full run (no `ABCD_LOWERED_CASE`) wipes
//! `$ABCD_LOWERED_DIR/{v2lift,v2opt}` entirely; a filtered run deletes
//! only the selected fixtures' target files, so stale files from an
//! earlier run never survive a fixture that now skips.
//!
//! The test asserts the expected fixture count was processed; it does NOT
//! assert that all fixtures lowered — skips are data for the oracle run.
//!
//! Run:
//!
//! ```text
//! ABCD_LOWERED_DIR=/tmp/abcd-lowered-full \
//!   cargo test -p abcd-lower --test corpus_lower_oracle --offline -- --ignored --nocapture
//! python3 scripts/compare-rewritten-corpus.py \
//!   exports/corpus/index.jsonl /tmp/abcd-lowered-full/v2opt --allow-missing
//! ```

use std::collections::BTreeMap;
use std::fmt;
use std::path::PathBuf;
use std::process::Command;

use abcd_file::File;
use abcd_ir::{FuncId, Module, verify_module};
use abcd_lift::lift_file;
use abcd_lower::{LowerError, LowerOptions, lower_function_with_options, to_method_body};
use abcd_opt::inline::{InlinePolicy, InlineReport, inline_module};
use abcd_opt::optimize_module;

/// The three rewrite variants, in driver order.
const VARIANTS: [&str; 3] = ["v2lift", "v2opt", "v2inline"];

/// Fixed SKIP category vocabulary (mirrors the v0.1 driver's; the
/// histogram keys are gate evidence — keep them stable).
enum SkipCategory {
    /// Front-end failure: read, decode, or lift.
    Lift,
    /// Structural verifier failure.
    Verify,
    /// `LowerError::UnsupportedInstruction` — payload is the instruction.
    LowerUnsupported(String),
    /// `LowerError::UntraceableEntity` — payload is the `EntityKind`.
    LowerUntraceable(String),
    /// Any other lower / to_method_body (relocation) error.
    LowerOther,
    /// `abcd_file::encode` failure.
    Encode,
    /// A panic caught by `catch_unwind`.
    Panic,
}

impl fmt::Display for SkipCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SkipCategory::Lift => write!(f, "lift"),
            SkipCategory::Verify => write!(f, "verify"),
            SkipCategory::LowerUnsupported(inst) => write!(f, "lower-unsupported:{inst}"),
            SkipCategory::LowerUntraceable(kind) => write!(f, "lower-untraceable:{kind}"),
            SkipCategory::LowerOther => write!(f, "lower-other"),
            SkipCategory::Encode => write!(f, "encode"),
            SkipCategory::Panic => write!(f, "panic"),
        }
    }
}

type Skip = (SkipCategory, String);

/// Classify a `LowerError` into the fixed category vocabulary.
fn lower_category(error: &LowerError) -> SkipCategory {
    match error {
        LowerError::UnsupportedInstruction { message, .. } => {
            SkipCategory::LowerUnsupported(message.clone())
        }
        LowerError::UntraceableEntity { kind, .. } => {
            SkipCategory::LowerUntraceable(format!("{kind:?}"))
        }
        _ => SkipCategory::LowerOther,
    }
}

/// Front-end stage: read → decode → v0.2 lift → ir2 verify.
fn front_end(path: &std::path::Path) -> Result<(File, Module), Skip> {
    let data = std::fs::read(path).map_err(|e| (SkipCategory::Lift, format!("read: {e}")))?;
    let file =
        abcd_file::decode(&data).map_err(|e| (SkipCategory::Lift, format!("decode: {e}")))?;
    let module = lift_file(&file).map_err(|e| (SkipCategory::Lift, format!("lift: {e}")))?;
    let report = verify_module(&module);
    if !report.is_ok() {
        return Err((SkipCategory::Verify, format!("verify: {:?}", report.errors)));
    }
    Ok((file, module))
}

/// Lower every function of `module`, splice the bodies into a clone of
/// `file`, and encode. Returns the encoded bytes and the function count.
/// All-or-nothing: the first lower/relocate/encode error aborts the
/// fixture; nothing is written by the caller in that case.
///
/// `options` selects the v0.1 parity target: default (lift) for
/// `v2lift`; `prune_unused_frame_init_consts` for `v2opt` — the
/// optimizer deletes the last use of a frame-initial constant, and the
/// v0.1 pipeline's ADCE swept the seed INSTRUCTION in that case (the
/// v0.2 seed is instruction-less, so the lower must skip the
/// materialization — see `LowerOptions`).
fn rewrite_fixture(
    module: &Module,
    file: &File,
    options: abcd_lower::LowerOptions,
) -> Result<(Vec<u8>, usize), Skip> {
    // Function i corresponds to the i-th method in lift order (classes in
    // file order, methods in declaration order — the lift's pass-1
    // reservation order, which is `File::all_methods()` order).
    //
    // Bodyless functions (external/native declarations, lifted as
    // block-less external FunctionData) keep their `None` body; every
    // other function lowers to a fresh MethodBody.
    let mut bodies = Vec::new();
    for index in 0..module.functions.len() {
        let func_id = FuncId::new(index as u32);
        let func = module.func(func_id).expect("function-table index");
        if func.blocks.is_empty() {
            bodies.push(None);
            continue;
        }
        let name = module.sym.resolve(func.name).unwrap_or("?").to_string();
        let lowered = lower_function_with_options(module, func_id, options)
            .map_err(|e| (lower_category(&e), format!("lower {name}: {e}")))?;
        let body = to_method_body(module, func_id, &lowered, file)
            .map_err(|e| (lower_category(&e), format!("to_method_body {name}: {e}")))?;
        bodies.push(Some(body));
    }
    let functions = bodies.iter().filter(|b| b.is_some()).count();

    let mut rebuilt = file.clone();
    let mut cursor = bodies.into_iter();
    for class in rebuilt.classes.values_mut() {
        for method in &mut class.methods {
            let body = cursor.next().expect("one slot per method");
            if method.body.is_some() {
                method.body = Some(body.expect("a lowered body for every method that had one"));
            }
        }
    }
    assert!(cursor.next().is_none());

    let encoded =
        abcd_file::encode(&rebuilt).map_err(|e| (SkipCategory::Encode, format!("encode: {e}")))?;
    Ok((encoded, functions))
}

/// Catch panics from an arbitrary stage so one bad fixture reports as a
/// skip instead of aborting the whole evidence run.
fn guarded<T>(stage: impl FnOnce() -> Result<T, Skip>) -> Result<T, Skip> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(stage)) {
        Ok(result) => result,
        Err(payload) => {
            let reason = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "unknown panic".to_string());
            Err((SkipCategory::Panic, format!("panic: {reason}")))
        }
    }
}

#[test]
#[ignore = "requires exported GHCR corpus and docker"]
fn passed_corpus_lowered_bodies_written_for_vm_oracle() {
    let root = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        });

    // Selection: every row with runtime.status == "passed", optionally
    // restricted to the comma-separated cases in ABCD_LOWERED_CASE.
    // Paths are sorted so reports are deterministic. (Same python3 JSON
    // pattern as the v0.1 driver.)
    let output = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, os, sys
cases = set(filter(None, (c.strip() for c in os.environ.get("ABCD_LOWERED_CASE", "").split(","))))
paths = []
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        if row["runtime"]["status"] != "passed":
            continue
        if cases and row["case"] not in cases:
            continue
        paths.append(row["abc"])
for path in sorted(paths):
    assert "\n" not in path and "\t" not in path
    print(path)
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
    let paths = String::from_utf8(output.stdout).expect("UTF-8 fixture paths");

    let case_filter = std::env::var("ABCD_LOWERED_CASE").unwrap_or_default();
    let full_run = case_filter.trim().is_empty();

    // Fresh output tree per run: stale files from an earlier run must not
    // survive a fixture that now skips (the oracle script would otherwise
    // compare outdated bytes). A full run wipes both variant trees; a
    // filtered run deletes only the selected fixtures' target files.
    let out_root = std::env::var_os("ABCD_LOWERED_DIR").map(PathBuf::from);
    if let Some(dir) = &out_root {
        if full_run {
            for variant in VARIANTS {
                let sub = dir.join(variant);
                if sub.exists() {
                    std::fs::remove_dir_all(&sub).expect("clear previous oracle output");
                }
            }
        } else {
            for relative in paths.lines() {
                for variant in VARIANTS {
                    let target = dir.join(variant).join(relative);
                    if target.exists() {
                        std::fs::remove_file(&target).expect("clear stale oracle output");
                    }
                }
            }
        }
    }

    let mut fixtures = 0usize;
    let mut wrote = [0usize; 3];
    let mut histograms: [BTreeMap<String, usize>; 3] =
        [BTreeMap::new(), BTreeMap::new(), BTreeMap::new()];
    let mut inline_stats = InlineReport::default();
    // W6 (q-P2): the inline determinism double-run is ON by default — it
    // is the only in-cargo guard against a nondeterministic inline pass.
    // ABCD_INLINE_DETERMINISM=0 opts out (debugging speed).
    let determinism = std::env::var("ABCD_INLINE_DETERMINISM").as_deref() != Ok("0");

    let record_skip = |variant: usize,
                       name: &str,
                       relative: &str,
                       (category, reason): Skip,
                       histograms: &mut [BTreeMap<String, usize>; 3]| {
        let key = category.to_string();
        eprintln!("SKIP {name} {relative} | {key} | {reason}");
        *histograms[variant].entry(key).or_insert(0) += 1;
    };

    for relative in paths.lines() {
        fixtures += 1;

        // Front-end stage shared by all variants.
        let (file, module) = match guarded(|| front_end(&root.join(relative))) {
            Ok(pair) => pair,
            Err(skip) => {
                let reason = skip.1;
                let key = skip.0.to_string();
                for (variant, name) in VARIANTS.iter().enumerate() {
                    eprintln!("SKIP {name} {relative} | {key} | {reason}");
                    *histograms[variant].entry(key.clone()).or_insert(0) += 1;
                }
                continue;
            }
        };

        // Variant: lift-only.
        match guarded(|| rewrite_fixture(&module, &file, LowerOptions::default())) {
            Ok((encoded, functions)) => {
                eprintln!("WROTE v2lift {relative} ({functions} functions)");
                if let Some(dir) = &out_root {
                    let target = dir.join("v2lift").join(relative);
                    std::fs::create_dir_all(target.parent().unwrap()).unwrap();
                    std::fs::write(target, encoded).expect("write oracle candidate");
                }
                wrote[0] += 1;
            }
            Err(skip) => record_skip(0, "v2lift", relative, skip, &mut histograms),
        }

        // Variant: lift + optimize (optimize mutates the module; re-verify
        // before lowering — the N27/N28 post-opt hygiene gate).
        let opt_result = guarded(|| {
            let mut optimized = module.clone();
            optimize_module(&mut optimized);
            let report = verify_module(&optimized);
            if !report.is_ok() {
                return Err((
                    SkipCategory::Verify,
                    format!("post-optimize verify: {:?}", report.errors),
                ));
            }
            Ok(optimized)
        });
        let optimized = match opt_result {
            Ok(optimized) => optimized,
            Err(skip) => {
                record_skip(1, "v2opt", relative, skip, &mut histograms);
                continue;
            }
        };
        match guarded(|| {
            rewrite_fixture(
                &optimized,
                &file,
                LowerOptions {
                    prune_unused_frame_init_consts: true,
                },
            )
        }) {
            Ok((encoded, functions)) => {
                eprintln!("WROTE v2opt {relative} ({functions} functions)");
                if let Some(dir) = &out_root {
                    let target = dir.join("v2opt").join(relative);
                    std::fs::create_dir_all(target.parent().unwrap()).unwrap();
                    std::fs::write(target, encoded).expect("write oracle candidate");
                }
                wrote[1] += 1;
            }
            Err(skip) => record_skip(1, "v2opt", relative, skip, &mut histograms),
        }

        // Variant: lift + inline (OPT-IN — the D2 inline pass, never
        // part of optimize_module; re-verify after inlining — zero
        // verifier errors is the hard gate). LowerOptions::default():
        // inline does not optimize, so no frame-init pruning.
        let inline_result = guarded(|| {
            let mut inlined = module.clone();
            let report = inline_module(&mut inlined, &InlinePolicy::default());
            let verify = verify_module(&inlined);
            if !verify.is_ok() {
                return Err((
                    SkipCategory::Verify,
                    format!("post-inline verify: {:?}", verify.errors),
                ));
            }
            Ok((inlined, report))
        });
        let (inlined, report) = match inline_result {
            Ok(pair) => pair,
            Err(skip) => {
                record_skip(2, "v2inline", relative, skip, &mut histograms);
                continue;
            }
        };
        inline_stats.merge(&report);
        match guarded(|| rewrite_fixture(&inlined, &file, LowerOptions::default())) {
            Ok((encoded, functions)) => {
                eprintln!("WROTE v2inline {relative} ({functions} functions)");
                if determinism {
                    // Two inline-on rewrites of the same fixture must be
                    // byte-identical (fresh front-end: decode → lift →
                    // inline → lower → encode again).
                    let second = guarded(|| {
                        let (file2, module2) = front_end(&root.join(relative))?;
                        let mut inlined2 = module2;
                        inline_module(&mut inlined2, &InlinePolicy::default());
                        let verify2 = verify_module(&inlined2);
                        if !verify2.is_ok() {
                            return Err((
                                SkipCategory::Verify,
                                format!("post-inline re-verify: {:?}", verify2.errors),
                            ));
                        }
                        rewrite_fixture(&inlined2, &file2, LowerOptions::default())
                    });
                    match second {
                        Ok((encoded2, _)) => assert_eq!(
                            encoded, encoded2,
                            "inline-on rewrite must be deterministic: {relative}"
                        ),
                        Err((category, reason)) => panic!(
                            "determinism re-run failed for {relative}: {category} | {reason}"
                        ),
                    }
                }
                if let Some(dir) = &out_root {
                    let target = dir.join("v2inline").join(relative);
                    std::fs::create_dir_all(target.parent().unwrap()).unwrap();
                    std::fs::write(target, encoded).expect("write oracle candidate");
                }
                wrote[2] += 1;
            }
            Err(skip) => record_skip(2, "v2inline", relative, skip, &mut histograms),
        }
    }

    if full_run {
        // 1119 original runtime-passed fixtures + 30 P4-T6 opcode-coverage
        // fixtures (private-property-store/-in, 5 versions x 3 profiles).
        assert_eq!(fixtures, 1149, "expected 1149 runtime-passed fixtures");
    }
    assert!(fixtures > 0, "no fixtures selected");
    eprintln!(
        "corpus lower oracle rewrite: v2lift wrote {} skipped {}; \
         v2opt wrote {} skipped {}; v2inline wrote {} skipped {} (fixtures: {})",
        wrote[0],
        histograms[0].values().sum::<usize>(),
        wrote[1],
        histograms[1].values().sum::<usize>(),
        wrote[2],
        histograms[2].values().sum::<usize>(),
        fixtures
    );
    for (variant, name) in VARIANTS.iter().enumerate() {
        eprintln!("HISTOGRAM {name}:");
        for (category, count) in &histograms[variant] {
            eprintln!("  {category}: {count}");
        }
    }
    eprintln!(
        "INLINE-STATS sites_inlined={} insts_inlined={} (fixtures: {})",
        inline_stats.sites_inlined, inline_stats.insts_inlined, fixtures
    );
    eprintln!("INLINE-SKIP-HISTOGRAM:");
    for (reason, count) in &inline_stats.skips {
        eprintln!("  {}: {count}", reason.label());
    }
    if full_run {
        // W8 (q-P2, maintainer-approved 2026-09-25): a lowering regression
        // that starts SKIPPING fixtures must fail here — not only two steps
        // later in the python VM oracle (missing-candidate). The skip
        // histograms stay printed above for forensics; zero is now gated.
        for (variant, name) in VARIANTS.iter().enumerate() {
            let skipped: usize = histograms[variant].values().sum();
            assert_eq!(
                skipped, 0,
                "{name}: {skipped} fixture(s) skipped lowering — a skip is a regression, not data"
            );
        }
    }
}
