//! hap-file — wild OHOS `.hap` corpus gate (container extraction × decode).
//!
//! The corpus is the 156-package wild-OHOS set baked into the digest-pinned
//! arkcompiler-test image and exported by `export-wild` to
//! `exports/corpus/wild/wild-haps/` (see the hap-file job in ci.yml). The
//! manifest (`manifest.json`) is the oracle: each package carries an
//! expectation (`decode-ok` — all 156 packages / 276 `.abc` modules since
//! `0.0.0.2` legacy ISA decode landed — or `negative-invalid-opcode` if the
//! image ever adds negative fixtures). The gate is self-contained: the
//! expected package total (`156`) and manifest self-consistency are
//! hard-asserted, so corpus drift goes red without any ledger.
//!
//! Gated in CI by the hap-file job; locally:
//!
//! ```text
//! cargo test -p abcd-rs --test hap-file --release -- --ignored --nocapture
//! ```
//!
//! Like modules.abc (tests/file-isa Group J) and abcd-hap's wild_ohos
//! instrument, the gate SKIPS silently when the corpus directory is absent
//! (local checkouts without the export, the coverage job's other targets).

mod wild_manifest;

use rayon::prelude::*;
use std::path::{Path, PathBuf};
use wild_manifest::{Expectation, Manifest};

/// The corpus shape lives in the image's manifest (the digest pin in ci.yml
/// is the change-control point). The gate asserts per-package expectations
/// and manifest self-consistency only — expectation flips (like the 2026-10
/// legacy-opcode one) are image-only changes, never code edits.
const EXPECTED_TOTAL: usize = 156;

/// The exported wild corpus root; override for off-layout runs.
fn wild_corpus_root() -> PathBuf {
    std::env::var_os("ABCD_CORPUS_WILD_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus/wild/wild-haps")
        })
}

#[test]
#[ignore = "requires the exported wild corpus (image export-wild)"]
fn exported_corpus_wild_hap_gates() {
    let root = wild_corpus_root();
    let manifest_path = root.join("manifest.json");
    if !manifest_path.exists() {
        // Skip-by-absence: no corpus on this host. Never a failure — the
        // CI job always exports first, so CI never reaches this arm.
        eprintln!("hap-file: no wild corpus at {root:?}, skipping (corpus not exported)");
        return;
    }
    let manifest = Manifest::load(&manifest_path).unwrap_or_else(|e| {
        panic!("wild manifest at {manifest_path:?} is unreadable/invalid: {e}");
    });

    // Manifest self-consistency: every package is present on disk with a
    // known expectation and the pinned total. Per-package behavior is
    // asserted against the manifest's own expectation below, so a flip in
    // the image never requires a code edit here.
    assert_eq!(
        manifest.packages.len(),
        EXPECTED_TOTAL,
        "wild manifest package count drifted (expected {EXPECTED_TOTAL})"
    );
    let decode_ok: Vec<_> = manifest
        .packages
        .iter()
        .filter(|p| p.expectation == Expectation::DecodeOk)
        .collect();
    let negative: Vec<_> = manifest
        .packages
        .iter()
        .filter(|p| p.expectation == Expectation::NegativeInvalidOpcode)
        .collect();

    // ── decode-ok gate: container extraction AND every module decode (rayon) ──
    let per_pkg: Vec<(usize, Vec<String>)> = decode_ok
        .par_iter()
        .map(|pkg| {
            let bytes = std::fs::read(root.join(&pkg.path))
                .unwrap_or_else(|e| panic!("{}: unreadable package: {e}", pkg.path));
            match abcd_hap::abc_modules(&bytes) {
                Ok(modules) => {
                    let mut errs = Vec::new();
                    for m in &modules {
                        if let Err(e) = abcd_file::decode(m.data.as_slice()) {
                            errs.push(format!("{}: {}: {e}", pkg.path, m.entry_name));
                        }
                    }
                    (modules.len(), errs)
                }
                Err(e) => (0, vec![format!("{}: container: {e}", pkg.path)]),
            }
        })
        .collect();
    let mut failures: Vec<String> = Vec::new();
    let mut modules_total = 0usize;
    for (count, errs) in per_pkg {
        modules_total += count;
        failures.extend(errs);
    }
    assert!(
        failures.is_empty(),
        "decode-ok gate: {} failures across {} packages / {modules_total} modules:\n{}",
        failures.len(),
        decode_ok.len(),
        failures.join("\n")
    );

    // ── negative gate: container parses, ≥1 module dies on an invalid
    // opcode ──
    let mut negative_misses: Vec<String> = Vec::new();
    for pkg in &negative {
        let bytes = std::fs::read(root.join(&pkg.path))
            .unwrap_or_else(|e| panic!("{}: unreadable package: {e}", pkg.path));
        let modules = match abcd_hap::abc_modules(&bytes) {
            Ok(m) => m,
            Err(e) => {
                negative_misses.push(format!("{}: container failed: {e}", pkg.path));
                continue;
            }
        };
        let mut ok = 0usize;
        let mut opcode_hits = 0usize;
        let mut other_errors: Vec<String> = Vec::new();
        for m in &modules {
            match abcd_file::decode(m.data.as_slice()) {
                Ok(_) => ok += 1,
                Err(e) => {
                    let msg = e.to_string();
                    // Spelling owned by abcd-file's BytecodeDecode wrapper
                    // over abcd_isa::DecodeError::InvalidOpcode.
                    if msg.contains("invalid opcode") {
                        opcode_hits += 1;
                    } else {
                        other_errors.push(format!("{}: {msg}", m.entry_name));
                    }
                }
            }
        }
        eprintln!(
            "negative {}: {} modules, {ok} decode-ok, {opcode_hits} invalid-opcode, {} other",
            pkg.path,
            modules.len(),
            other_errors.len()
        );
        for e in &other_errors {
            eprintln!("  other-error: {e}");
        }
        if opcode_hits == 0 {
            negative_misses.push(format!(
                "{}: no module failed with \"invalid opcode\" ({} modules, {ok} decode-ok)",
                pkg.path,
                modules.len()
            ));
        }
    }
    assert!(
        negative_misses.is_empty(),
        "negative gate: {} of {} packages did not hit the expected invalid-opcode decode failure:\n{}",
        negative_misses.len(),
        negative.len(),
        negative_misses.join("\n")
    );

    eprintln!(
        "hap-file gate: {} decode-ok packages ({} modules) all decoded; {} negative packages all hit invalid-opcode",
        decode_ok.len(),
        modules_total,
        negative.len()
    );
}

fn splice_and_encode(file: &abcd_file::File, module: &abcd_ir::Module) -> Result<Vec<u8>, String> {
    let rebuilt = abcd_lower::rewrite_file(module, file, abcd_lower::LowerOptions::default())
        .map_err(|e| format!("rewrite_file: {e}"))?;
    abcd_file::encode(&rebuilt).map_err(|e| format!("encode: {e}"))
}

/// Full wild-OHOS `.hap` rewrite gate (#32): exercises `decode → lift → verify
/// → [opt → verify →] lower → encode → decode → lift → verify` across every
/// `.abc` module in all 156 wild `.hap` packages (`276` modules total:
/// `242` modern modules rewritten end-to-end in both `v2lift` and `v2opt`,
/// `14` legacy `0.0.0.2` read-only modules, and `20` `N54`
/// `deprecated.defineclasswithbuffer` hard-error modules).
#[test]
#[ignore = "requires the exported wild corpus (image export-wild)"]
fn exported_corpus_wild_hap_rewrite_gates() {
    let root = wild_corpus_root();
    let manifest_path = root.join("manifest.json");
    if !manifest_path.exists() {
        eprintln!("hap-file rewrite: no wild corpus at {root:?}, skipping (corpus not exported)");
        return;
    }
    let manifest = Manifest::load(&manifest_path).unwrap_or_else(|e| {
        panic!("wild manifest at {manifest_path:?} is unreadable/invalid: {e}");
    });
    let decode_ok: Vec<_> = manifest
        .packages
        .iter()
        .filter(|p| p.expectation == Expectation::DecodeOk)
        .collect();

    #[derive(Default)]
    struct RewriteTally {
        rewritten_ok: usize,
        n8_type_summary: usize,
        legacy_v002: usize,
        n54_deprecated: usize,
        failures: Vec<String>,
    }

    let tallies: Vec<RewriteTally> = decode_ok
        .par_iter()
        .map(|pkg| {
            let mut tally = RewriteTally::default();
            let bytes = std::fs::read(root.join(&pkg.path))
                .unwrap_or_else(|e| panic!("{}: unreadable package: {e}", pkg.path));
            let modules = match abcd_hap::abc_modules(&bytes) {
                Ok(m) => m,
                Err(e) => {
                    tally.failures.push(format!("{}: container: {e}", pkg.path));
                    return tally;
                }
            };
            for m in &modules {
                let label = format!("{}#{}", pkg.path, m.entry_name);
                let mut file = match abcd_file::decode(m.data.as_slice()) {
                    Ok(f) => f,
                    Err(e) => {
                        tally.failures.push(format!("{label}: decode: {e}"));
                        continue;
                    }
                };
                if file.version == abcd_file::Version::new(0, 0, 0, 2) {
                    match abcd_file::encode(&file) {
                        Err(abcd_file::Error::UnsupportedOutputVersion(_)) => {
                            tally.legacy_v002 += 1;
                        }
                        other => tally.failures.push(format!(
                            "{label}: expected UnsupportedOutputVersion(0.0.0.2), got {}",
                            other
                                .err()
                                .map(|e| e.to_string())
                                .unwrap_or_else(|| "Ok".to_string())
                        )),
                    }
                    match abcd_lift::lift_file(&file) {
                        Ok(ir) => {
                            let r = abcd_ir::verify_module(&ir);
                            if !r.is_ok() {
                                tally.failures.push(format!(
                                    "{label}: legacy 0.0.0.2 verify: {:?}",
                                    r.errors
                                ));
                            }
                        }
                        Err(abcd_lift::LiftError::UnsupportedDeprecatedDefineClassWithBuffer) => {
                            tally.n54_deprecated += 1;
                        }
                        Err(e) => {
                            tally
                                .failures
                                .push(format!("{label}: legacy 0.0.0.2 lift: {e}"));
                        }
                    }
                    continue;
                }

                let has_type_summary = file.classes.values().any(|cls| {
                    cls.fields.iter().any(|f| {
                        matches!(
                            f.initial_value,
                            Some(abcd_file::FieldValue::TypeSummaryOffset(_))
                        )
                    })
                });
                if has_type_summary {
                    match abcd_file::encode(&file) {
                        Err(abcd_file::Error::TypeSummaryOffset { .. }) => {
                            tally.n8_type_summary += 1;
                        }
                        other => {
                            tally.failures.push(format!(
                                "{label}: expected N8 TypeSummaryOffset error, got {}",
                                other
                                    .err()
                                    .map(|e| e.to_string())
                                    .unwrap_or_else(|| "Ok".to_string())
                            ));
                            continue;
                        }
                    }
                    // Clear the opaque N8 field in the test harness so the full
                    // rewrite + `_TypeOfInstruction` nested-literal-array encode +
                    // post-rewrite lift/verify pipeline is exercised on all 77
                    // typeSummary-bearing system apps too.
                    for cls in file.classes.values_mut() {
                        for field in &mut cls.fields {
                            if matches!(
                                field.initial_value,
                                Some(abcd_file::FieldValue::TypeSummaryOffset(_))
                            ) {
                                field.initial_value = None;
                            }
                        }
                    }
                }

                let ir = match abcd_lift::lift_file(&file) {
                    Ok(ir) => ir,
                    Err(e) => {
                        tally.failures.push(format!("{label}: lift: {e}"));
                        continue;
                    }
                };
                let pre = abcd_ir::verify_module(&ir);
                if !pre.is_ok() {
                    tally
                        .failures
                        .push(format!("{label}: pre-rewrite verify: {:?}", pre.errors));
                    continue;
                }

                // 1) v2lift roundtrip + re-lift + re-verify
                let v2lift_bytes = match splice_and_encode(&file, &ir) {
                    Ok(b) => b,
                    Err(e) => {
                        tally.failures.push(format!("{label}: v2lift {e}"));
                        continue;
                    }
                };
                let relift_ok = abcd_file::decode(&v2lift_bytes)
                    .map_err(|e| format!("re-decode: {e}"))
                    .and_then(|f2| abcd_lift::lift_file(&f2).map_err(|e| format!("re-lift: {e}")))
                    .and_then(|ir2| {
                        let r = abcd_ir::verify_module(&ir2);
                        if r.is_ok() {
                            Ok(())
                        } else {
                            Err(format!("re-verify: {:?}", r.errors))
                        }
                    });
                if let Err(e) = relift_ok {
                    tally
                        .failures
                        .push(format!("{label}: v2lift post-check {e}"));
                    continue;
                }

                // 2) v2opt roundtrip + re-lift + re-verify
                let mut opt_ir = ir;
                abcd_opt::optimize_module(&mut opt_ir);
                let post_opt = abcd_ir::verify_module(&opt_ir);
                if !post_opt.is_ok() {
                    tally
                        .failures
                        .push(format!("{label}: post-opt verify: {:?}", post_opt.errors));
                    continue;
                }
                let v2opt_bytes = match splice_and_encode(&file, &opt_ir) {
                    Ok(b) => b,
                    Err(e) => {
                        tally.failures.push(format!("{label}: v2opt {e}"));
                        continue;
                    }
                };
                let relift_opt_ok = abcd_file::decode(&v2opt_bytes)
                    .map_err(|e| format!("re-decode: {e}"))
                    .and_then(|f2| abcd_lift::lift_file(&f2).map_err(|e| format!("re-lift: {e}")))
                    .and_then(|ir2| {
                        let r = abcd_ir::verify_module(&ir2);
                        if r.is_ok() {
                            Ok(())
                        } else {
                            Err(format!("re-verify: {:?}", r.errors))
                        }
                    });
                if let Err(e) = relift_opt_ok {
                    tally
                        .failures
                        .push(format!("{label}: v2opt post-check {e}"));
                    continue;
                }

                tally.rewritten_ok += 1;
            }
            tally
        })
        .collect();

    let mut total = RewriteTally::default();
    for t in tallies {
        total.rewritten_ok += t.rewritten_ok;
        total.n8_type_summary += t.n8_type_summary;
        total.legacy_v002 += t.legacy_v002;
        total.n54_deprecated += t.n54_deprecated;
        total.failures.extend(t.failures);
    }

    assert!(
        total.failures.is_empty(),
        "wild .hap rewrite gate: {} failures (rewritten_ok={}, n8={}, legacy_v002={}, n54={}):\n{}",
        total.failures.len(),
        total.rewritten_ok,
        total.n8_type_summary,
        total.legacy_v002,
        total.n54_deprecated,
        total.failures.join("\n")
    );
    assert_eq!(
        (
            total.rewritten_ok,
            total.n8_type_summary,
            total.legacy_v002,
            total.n54_deprecated,
        ),
        (242, 77, 34, 20),
        "wild .hap rewrite module partition drifted"
    );
    eprintln!(
        "hap-file rewrite gate: {} modern modules rewritten cleanly (incl. {} N8 typeSummary-checked), {} legacy 0.0.0.2 ({} N54 deprecated-class)",
        total.rewritten_ok, total.n8_type_summary, total.legacy_v002, total.n54_deprecated
    );
}
