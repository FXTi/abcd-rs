//! Wild-OHOS corpus instrument (local-only, never runs in CI):
//! feed every .hap under a directory tree through abcd-hap extraction +
//! abcd-file decode, and report compatibility stats.
//!
//! Run on dabai (the collection lives outside the workspace):
//!
//! ```text
//! ABCD_HAP_WILD_DIR=/home/zjx/hap_collect/haps \
//!   scripts/remote-test.sh test -p abcd-hap --release \
//!     --test wild_ohos -- --ignored --nocapture
//! ```

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in rd.flatten() {
        let p = entry.path();
        if p.is_dir() {
            collect(&p, out);
        } else if p.extension().is_some_and(|e| e == "hap") {
            out.push(p);
        }
    }
}

#[test]
#[ignore]
fn wild_ohos_hap_and_abc_compatibility_sweep() {
    let root = std::env::var("ABCD_HAP_WILD_DIR")
        .unwrap_or_else(|_| "/home/zjx/hap_collect/haps".to_string());
    let mut haps = Vec::new();
    collect(Path::new(&root), &mut haps);
    haps.sort();
    assert!(!haps.is_empty(), "no haps under {root}");

    let mut hap_ok = 0usize;
    let mut abc_ok = 0usize;
    let mut abc_total = 0usize;
    let mut hap_errors: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut abc_errors: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut version_stats: BTreeMap<String, (usize, usize, usize)> = BTreeMap::new();

    for path in &haps {
        let version = path
            .components()
            .nth(path.components().count().saturating_sub(2))
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .unwrap_or_default();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let stat = version_stats.entry(version.clone()).or_default();
        stat.0 += 1;

        let bytes = match std::fs::read(path) {
            Ok(b) => b,
            Err(e) => {
                hap_errors
                    .entry(format!("read: {e}"))
                    .or_default()
                    .push(name.clone());
                continue;
            }
        };
        let modules = match abcd_hap::abc_modules(&bytes) {
            Ok(m) => m,
            Err(e) => {
                hap_errors
                    .entry(e.to_string())
                    .or_default()
                    .push(name.clone());
                continue;
            }
        };
        hap_ok += 1;
        stat.1 += 1;
        for m in &modules {
            abc_total += 1;
            match abcd_file::decode(m.data.as_slice()) {
                Ok(_) => {
                    abc_ok += 1;
                    stat.2 += 1;
                }
                Err(e) => {
                    abc_errors
                        .entry(e.to_string())
                        .or_default()
                        .push(format!("{version}/{name}"));
                }
            }
        }
    }

    eprintln!("\n=== WILD OHOS SWEEP ({root}) ===");
    eprintln!(
        "haps: {} files, container-parse ok {hap_ok}, failed {}",
        haps.len(),
        haps.len() - hap_ok
    );
    eprintln!(
        "abc modules: {abc_total}, decode ok {abc_ok}, failed {}",
        abc_total - abc_ok
    );
    eprintln!("\nper-version (haps / container-ok / abc-ok):");
    for (v, (n, h, a)) in &version_stats {
        eprintln!("  {v:30} {n:>4} {h:>4} {a:>4}");
    }
    if !hap_errors.is_empty() {
        eprintln!("\ncontainer errors ({} classes):", hap_errors.len());
        for (e, names) in &hap_errors {
            eprintln!(
                "  x{} {} :: {:?}",
                names.len(),
                e,
                &names[..names.len().min(3)]
            );
        }
    }
    if !abc_errors.is_empty() {
        eprintln!("\nabc decode errors ({} classes):", abc_errors.len());
        for (e, names) in &abc_errors {
            eprintln!(
                "  x{} {} :: {:?}",
                names.len(),
                e,
                &names[..names.len().min(3)]
            );
        }
    }
    // The instrument fails loudly when something regresses: on first contact
    // with a new collection, read the report instead of asserting numbers.
    assert!(abc_ok > 0, "nothing decoded at all — instrument is broken");
}
