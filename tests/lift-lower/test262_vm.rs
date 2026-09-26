//! Opt-in test262 VM-oracle suite (test262 P2): for every manifest row
//! with `origin.kind == "test262"` (2685 fixtures, all
//! `runtime.status == "recorded"` — a raw behavior record baked into the
//! image, never a pass/fail judgment), decode → `abcd_lift::lift_file`
//! (v0.2 lift) → ir2 verify → lower → encode through the SAME
//! `front_end` + `rewrite_fixture` pipeline as `corpus_lower_oracle`
//! (v2lift variant, default `LowerOptions`), writing candidates to
//! `$ABCD_TEST262_VM_DIR/v2lift/` plus a FILTERED index (test262 rows
//! only) at `$ABCD_TEST262_VM_DIR/index.jsonl` for
//! `scripts/compare-rewritten-corpus.py`.
//!
//! Unlike the project corpus there is exactly ONE variant (v2lift): the
//! gate is "the v0.2 lift→lower pipeline preserves whatever upstream
//! es2abc+ark_js_vm did" (design/test262-feasibility.md §3.3 — we never
//! claim test262 conformance, only behavior preservation).
//!
//! ## Comparison policy for test262 rows (empirically established)
//!
//! test262 runtime records are RAW: 2659/2685 rows exit 0 with empty
//! stderr; 26 rows exit 255 with an uncaught-error stderr that embeds
//! the baked corpus path (`/opt/arkcompiler-test/...`), which the
//! candidate run cannot reproduce byte-for-byte (it runs from
//! `/work/...`).
//!
//! Empirical first contact (image sha256:45f4daf6…, full 2685-row
//! compares, reports under `target/test262-vm/`):
//!
//! - **Identity baseline** (original .abc as its own candidate, exact
//!   stderr, 3m59s @ --jobs 8): 2659 exact pass + 26 stderr-ONLY
//!   mismatches, all 26 verified to be pure path-text differences
//!   (`/opt/arkcompiler-test/corpus/...` vs `/work/...` — diffing after
//!   path scrubbing leaves zero non-path lines) and all 26 reconciled
//!   by error-name normalization. ZERO exit_code/stdout/timeout
//!   mismatches — the environment is clean.
//! - **v2lift candidates** (exact stderr, 5m28s @ --jobs 4 / 3m59s @
//!   --jobs 8): 2606 exact pass + the same 26 stderr-only rows + 29
//!   exit_code divergences + 24 missing (rewrite skips below).
//!
//! Policy implemented by `compare-rewritten-corpus.py --recorded`:
//!
//! - exit_code, stdout, timeout: compared EXACTLY (no normalization).
//! - stderr: compared after ERROR-NAME normalization
//!   (`--recorded-stderr error-name`) — the first `<Name>Error:` token
//!   (the rule upstream's own test262 runner uses,
//!   `util_test262.py:163-166`): the constructor name must match, the
//!   rest of the text (messages, paths, stack frames, addresses) is
//!   ignored. Empty stderr must stay empty. Justified by the identity
//!   baseline above: exact-text stderr comparison fails ONLY on
//!   environment path text, never on error content.
//!
//! ## Documented divergences (hard gate, no unexplained rows)
//!
//! First contact found two REAL divergence classes. They are NOT
//! absorbed: each is named, counted, and listed per-row in
//! `scripts/test262-vm-divergences.json`, and the compare gate is
//! `passed + documented == compared (+ missing documented)` — a new
//! undocumented divergence OR a fixed row that was not delisted both
//! fail the run (`--expect-divergences`).
//!
//! - **encode-high-vreg-no-wide-form (24 rows)**: RESOLVED (N71). The
//!   rewrite used to skip these at the encode stage
//!   (`OperandOutOfRange`). True root cause (vendor-verified, supersedes
//!   the interim ">256-vregs into 8-bit register slots" diagnosis —
//!   neg/tonumber among the failing mnemonics have NO register operand):
//!   the per-function dense IC-slot counter pushed `eight_bit_ic`
//!   instructions' (isa.yaml `imm:u8`, no wide form) slot immediate past
//!   u8 once a method's total IC slots exceeded 256. The lower now
//!   mirrors upstream es2panda's `PandaGen::ReArrangeIc()`
//!   (`rearrange_ic_slots` in abcd-lower/src/isel.rs): one-byte-slot
//!   instructions re-allocate first from 0, sixteen-bit ones continue,
//!   one-byte overflow degrades to the runtime's INVALID_IC_SLOT (0xFF)
//!   no-cache sentinel. Regression-pinned by the `n71_ic_slots` suite
//!   over the exact 24-row set.
//! - **behavior-exit-code (29 rows)**: candidate runs but exit_code
//!   diverges from the baked record (exit 0 → 255, Test262Error×27 /
//!   TypeError×2): genuine semantic divergences of the lift→lower
//!   pipeline on constructs the 1149-row project corpus does not cover
//!   (arguments-object/parameter clusters, Array splice/concat,
//!   Reflect/set receiver semantics, builtin subclassing, astral-plane
//!   string iteration, …). Reported to the maintainer 2026-09-27; the
//!   per-row records (expected vs actual) are in
//!   `target/test262-vm/oracle-v2lift-exact.json`.
//!
//! Selection: by default ALL test262 rows are processed. Setting
//! `ABCD_TEST262_VM_CASE` to a comma-separated case list restricts the
//! run (debugging); a filtered run wipes only the selected fixtures'
//! target files and skips the count/zero-skip gates.
//!
//! Output root: `$ABCD_TEST262_VM_DIR` (must be absolute) or
//! `target/test262-vm/` under the repo root.
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-lower --release -- --ignored --nocapture test262_vm
//! python3 scripts/compare-rewritten-corpus.py \
//!   target/test262-vm/index.jsonl target/test262-vm/v2lift \
//!   --recorded --recorded-stderr error-name --allow-missing \
//!   --expect-divergences scripts/test262-vm-divergences.json \
//!   --image "$ARK_TEST_IMAGE" --jobs 4
//! ```

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::Command;

use abcd_lower::LowerOptions;

use super::rewrite_pipeline::{front_end, guarded, rewrite_fixture};

#[test]
#[ignore = "requires exported GHCR corpus and docker"]
fn test262_corpus_lowered_bodies_written_for_vm_oracle() {
    let root = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus"));

    // Output root: $ABCD_TEST262_VM_DIR (absolute) or target/test262-vm.
    let out_root = std::env::var_os("ABCD_TEST262_VM_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/test262-vm")
        });
    assert!(
        out_root.is_absolute(),
        "test262 VM output root must be absolute: {out_root:?}"
    );
    let out_candidates = out_root.join("v2lift");
    let out_index = out_root.join("index.jsonl");

    // Selection: every row with origin.kind == "test262", optionally
    // restricted to the comma-separated cases in ABCD_TEST262_VM_CASE.
    // Paths are sorted so reports are deterministic. The same python
    // invocation writes the FILTERED index (raw test262 JSONL lines,
    // sorted by abc path) that the compare step consumes. (Same python3
    // JSON pattern as corpus_lower_oracle.)
    std::fs::create_dir_all(&out_root).expect("create test262 VM output root");
    let output = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, os, sys
cases = set(filter(None, (c.strip() for c in os.environ.get("ABCD_TEST262_VM_CASE", "").split(","))))
rows = []
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        if row["origin"]["kind"] != "test262":
            continue
        if cases and row["case"] not in cases:
            continue
        rows.append((row["abc"], line))
rows.sort()
with open(sys.argv[2], "w", encoding="utf-8") as filtered:
    for _, line in rows:
        filtered.write(line)
for path, _ in rows:
    assert "\n" not in path and "\t" not in path
    print(path)
"#,
        )
        .arg(root.join("index.jsonl"))
        .arg(&out_index)
        .output()
        .expect("python3 is required by corpus tooling");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let paths = String::from_utf8(output.stdout).expect("UTF-8 fixture paths");

    let case_filter = std::env::var("ABCD_TEST262_VM_CASE").unwrap_or_default();
    let full_run = case_filter.trim().is_empty();

    // Fresh output tree per run (same stale-file discipline as
    // corpus_lower_oracle): a full run wipes the variant tree; a
    // filtered run deletes only the selected fixtures' target files.
    if full_run {
        if out_candidates.exists() {
            std::fs::remove_dir_all(&out_candidates).expect("clear previous oracle output");
        }
    } else {
        for relative in paths.lines() {
            let target = out_candidates.join(relative);
            if target.exists() {
                std::fs::remove_file(&target).expect("clear stale oracle output");
            }
        }
    }

    let mut fixtures = 0usize;
    let mut wrote = 0usize;
    let mut histogram: BTreeMap<String, usize> = BTreeMap::new();
    // (row, category) for every skip — the full-run gate checks the exact
    // set against EXPECTED_ENCODE_SKIPS.
    let mut skip_log: Vec<(&str, String)> = Vec::new();

    for relative in paths.lines() {
        fixtures += 1;

        // Front-end stage (shared pipeline with corpus_lower_oracle).
        let (file, module) = match guarded(|| front_end(&root.join(relative))) {
            Ok(pair) => pair,
            Err((category, reason)) => {
                let key = category.to_string();
                eprintln!("SKIP v2lift {relative} | {key} | {reason}");
                *histogram.entry(key.clone()).or_insert(0) += 1;
                skip_log.push((relative, key));
                continue;
            }
        };

        // The single v2lift variant: default LowerOptions.
        match guarded(|| rewrite_fixture(&module, &file, LowerOptions::default())) {
            Ok((encoded, functions)) => {
                eprintln!("WROTE v2lift {relative} ({functions} functions)");
                let target = out_candidates.join(relative);
                std::fs::create_dir_all(target.parent().unwrap()).unwrap();
                std::fs::write(target, encoded).expect("write oracle candidate");
                wrote += 1;
            }
            Err((category, reason)) => {
                let key = category.to_string();
                eprintln!("SKIP v2lift {relative} | {key} | {reason}");
                *histogram.entry(key.clone()).or_insert(0) += 1;
                skip_log.push((relative, key));
            }
        }
    }

    if full_run {
        // 2685 test262 rows (origin.kind == "test262"), all version
        // 24.0.0.0 / profile baseline.
        assert_eq!(fixtures, 2685, "expected 2685 test262 fixtures");
    }
    assert!(fixtures > 0, "no fixtures selected");
    let skipped: usize = histogram.values().sum();
    eprintln!(
        "test262 VM oracle rewrite: v2lift wrote {wrote} skipped {skipped} (fixtures: {fixtures})"
    );
    eprintln!("HISTOGRAM v2lift:");
    for (category, count) in &histogram {
        eprintln!("  {category}: {count}");
    }
    if full_run {
        // Hard gate (test262 P2, hard-error discipline): ZERO rewrite
        // skips. The 24-row encode-high-vreg-no-wide-form class was
        // resolved by the N71 fix (ReArrangeIc mirror in abcd-lower
        // isel) and delisted; any skip — new class or a regression of
        // the resolved one — fails here, so the gate can never
        // silently rot.
        let mut skipped_rows: Vec<&str> = skip_log.iter().map(|(row, _)| *row).collect();
        skipped_rows.sort_unstable();
        assert_eq!(
            skipped_rows,
            Vec::<&str>::new(),
            "v2lift: test262 rewrite skips are a regression, not data \
             (the N71 encode class is resolved — see the suite header)"
        );
    }
}
