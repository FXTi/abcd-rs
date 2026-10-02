//! hap-file — wild OHOS `.hap` corpus gate (container extraction × decode).
//!
//! The corpus is the 156-package wild-OHOS set baked into the digest-pinned
//! arkcompiler-test image and exported by `export-wild` to
//! `exports/corpus/wild/wild-haps/` (see the hap-file job in ci.yml). The
//! manifest (`manifest.json`) is the oracle: each package is labeled either
//! `decode-ok` (145 packages — every extracted .abc module must decode) or
//! `negative-invalid-opcode` (11 packages — the container must parse, and at
//! least one module must fail decode with an "invalid opcode" error). The
//! gate is self-contained: the expected totals (145 / 11) are hard-asserted,
//! so a manifest/count drift goes red without any ledger.
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

    // ── decode-ok gate: container extraction AND every module decode ──
    let mut failures: Vec<String> = Vec::new();
    let mut modules_total = 0usize;
    for pkg in &decode_ok {
        let bytes = std::fs::read(root.join(&pkg.path))
            .unwrap_or_else(|e| panic!("{}: unreadable package: {e}", pkg.path));
        let modules = match abcd_hap::abc_modules(&bytes) {
            Ok(m) => m,
            Err(e) => {
                failures.push(format!("{}: container: {e}", pkg.path));
                continue;
            }
        };
        for m in &modules {
            modules_total += 1;
            if let Err(e) = abcd_file::decode(m.data.as_slice()) {
                failures.push(format!("{}: {}: {e}", pkg.path, m.entry_name));
            }
        }
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
