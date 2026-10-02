//! Group K — whole-file pandasm byte-diff gate against upstream ark_disasm.
//!
//! `abcd dis` must be BYTE-IDENTICAL to upstream `ark_disasm` (design
//! cli-plan.md §4.1, maintainer ruling 2026-09-28). This test decodes every
//! corpus fixture, renders it with [`abcd_file::pandasm::emit_file`], and
//! compares against the image-provided `reference.pa` BYTE BY BYTE — the
//! instruction-level comparison in `main.rs` normalizes both sides; this
//! gate normalizes nothing.
//!
//! Intentional divergences go through the self-cleaning ledger
//! `scripts/pandasm-dis-divergences.json` (N72 option B, same format and
//! discipline as `test262-vm-divergences.json`): a failing fixture must be
//! listed under exactly one divergence class (unlisted = red), and a listed
//! fixture that starts passing is stale (red). The empty ledger is the
//! healthy state.
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test file-isa -- --ignored --nocapture \
//!     pandasm_byte_identical
//! ```
//!
//! `ABCD_PANDASM_DIS_FILTER=<substring>` restricts to manifest rows whose
//! `abc` path contains the substring (iteration aid; full-corpus CI runs
//! unset).

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write as _;

use abcd_file::decode;
use rayon::prelude::*;

/// Ledger of documented byte-level divergences (class name → abc paths).
const LEDGER_PATH: &str = "scripts/pandasm-dis-divergences.json";

fn load_ledger() -> BTreeMap<String, BTreeSet<String>> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(LEDGER_PATH);
    let text =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let value: serde_json::Value = serde_json::from_str(&text).expect("ledger is valid JSON");
    let mut ledger: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (class, paths) in value.as_object().expect("ledger is an object") {
        if class == "$comment" {
            continue;
        }
        let set = paths
            .as_array()
            .unwrap_or_else(|| panic!("ledger class {class} must be an array"))
            .iter()
            .map(|p| p.as_str().expect("ledger paths are strings").to_owned())
            .collect();
        ledger.insert(class.clone(), set);
    }
    ledger
}

/// First-difference report for one mismatched fixture: byte offset, plus
/// the differing line from each side (lossy — reference.pa is raw bytes).
fn first_diff(rel: &str, ours: &[u8], reference: &[u8]) -> String {
    let pos = ours
        .iter()
        .zip(reference.iter())
        .position(|(a, b)| a != b)
        .unwrap_or(ours.len().min(reference.len()));
    let line_of = |bytes: &[u8]| {
        let start = bytes[..pos]
            .iter()
            .rposition(|&b| b == b'\n')
            .map_or(0, |i| i + 1);
        let end = bytes[pos..]
            .iter()
            .position(|&b| b == b'\n')
            .map_or(bytes.len(), |i| pos + i);
        String::from_utf8_lossy(&bytes[start..end]).into_owned()
    };
    format!(
        "{rel}: first diff at byte {pos} (ours {} bytes, reference {} bytes)\n  ours:      {:?}\n  reference: {:?}",
        ours.len(),
        reference.len(),
        line_of(ours),
        line_of(reference),
    )
}

/// The byte-diff gate: every corpus fixture's emitted pandasm must equal
/// the image's reference.pa byte for byte, or be ledgered.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn exported_corpus_pandasm_byte_identical() {
    let root = crate::exported_corpus_root();
    let rows = crate::manifest_select(&root, crate::SELECT_ABC_PANDASM);
    let filter = std::env::var("ABCD_PANDASM_DIS_FILTER").ok();
    let ledger = load_ledger();
    // Reverse index: path → divergence class (double-listing is red).
    let mut listed: BTreeMap<&str, &str> = BTreeMap::new();
    for (class, paths) in &ledger {
        for path in paths {
            assert!(
                listed.insert(path.as_str(), class.as_str()).is_none(),
                "ledger lists {path} under two classes"
            );
        }
    }
    let seen: BTreeSet<&str> = rows
        .iter()
        .map(|line| line.split_once('\t').expect("manifest paths").0)
        .collect();

    // In-scope rows, in manifest order (the filter preserves order).
    let scoped: Vec<(&str, &str)> = rows
        .iter()
        .map(|line| line.split_once('\t').expect("manifest paths"))
        .filter(|(rel, _)| filter.as_ref().is_none_or(|f| rel.contains(f.as_str())))
        .collect();

    // Parallel per-fixture render + byte compare (rayon). Each fixture
    // returns whether it byte-matched, plus its first-diff report when
    // it failed; the indexed collect keeps manifest row order, so the
    // serial fold below emits the identical report the serial loop did.
    let outcomes: Vec<Option<String>> = scoped
        .par_iter()
        .map(|&(rel, pandasm)| {
            let data = std::fs::read(root.join(rel)).expect("fixture");
            let file = decode(&data).unwrap_or_else(|e| panic!("{rel}: {e}"));
            let source_name = std::path::Path::new(rel)
                .file_name()
                .and_then(|n| n.to_str())
                .expect("fixture basename");
            let ours = abcd_file::pandasm::emit_file(&file, source_name);
            let reference = std::fs::read(root.join(pandasm)).expect("reference.pa");
            if ours == reference {
                None
            } else {
                Some(first_diff(rel, &ours, &reference))
            }
        })
        .collect();

    let total = scoped.len();
    let mut matched = 0usize;
    let mut documented: BTreeMap<&str, usize> = BTreeMap::new();
    let mut failing: BTreeSet<String> = BTreeSet::new();
    let mut undocumented: Vec<String> = Vec::new();
    let mut diffs: Vec<String> = Vec::new();
    for ((rel, _), diff) in scoped.iter().zip(outcomes) {
        let Some(diff) = diff else {
            matched += 1;
            continue;
        };
        failing.insert(rel.to_string());
        match listed.get(rel) {
            Some(class) => *documented.entry(class).or_default() += 1,
            None => {
                undocumented.push(rel.to_string());
                if diffs.len() < 20 {
                    diffs.push(diff);
                }
            }
        }
    }

    // Stale entries: ledgered in-scope paths that no longer fail — the
    // ledger self-cleans by turning red.
    let stale: Vec<String> = ledger
        .iter()
        .flat_map(|(class, paths)| paths.iter().map(move |p| (class, p)))
        .filter(|(_, path)| {
            filter.as_ref().is_none_or(|f| path.contains(f.as_str()))
                && seen.contains(path.as_str())
                && !failing.contains(path.as_str())
        })
        .map(|(class, path)| format!("{path} (class {class})"))
        .collect();

    std::io::stderr().flush().ok();
    eprintln!(
        "pandasm byte-diff: total {total} matched {matched} documented {} undocumented {}",
        documented.values().sum::<usize>(),
        undocumented.len()
    );
    for (class, n) in &documented {
        eprintln!("  documented[{class}]: {n}");
    }
    for u in &undocumented {
        eprintln!("  UNDOCUMENTED: {u}");
    }
    for record in &diffs {
        eprintln!("DIFF: {record}");
    }
    assert!(
        undocumented.is_empty(),
        "{} fixtures diverge from upstream ark_disasm without a ledger entry (first {} above)",
        undocumented.len(),
        diffs.len()
    );
    assert!(
        stale.is_empty(),
        "stale ledger entries (fixtures now byte-identical — delist): {stale:?}"
    );
    if filter.is_none() {
        assert_eq!(
            matched + documented.values().sum::<usize>(),
            total,
            "every fixture either byte-matches or is documented"
        );
        assert_eq!(total, rows.len(), "every manifest fixture must compare");
    }
}
