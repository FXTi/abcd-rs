//! Group J — full-opcode decode coverage against a real production file.
//!
//! Uses a device stock `modules.abc` (21.6 MB, 12.0.6.0, 2035 classes).
//! That file is local-only and gitignored (Huawei distribution
//! restrictions), so this test is `#[ignore]`d in CI and run explicitly
//! whenever the corpus is present:
//!
//! ```text
//! cargo test --test real_module_abc -- --ignored
//! ```

use abcd_file::decode;
use abcd_isa::Version;

fn corpus_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("modules.abc")
}

/// The whole production file decodes with the vendored 24.0.0.0 opcode
/// table (see design/isa-compat.md: 12.0.6.0 is a strict subset of 24).
/// Any unknown opcode aborts `decode`, so merely reaching the asserts
/// proves full opcode coverage.
#[test]
#[ignore = "requires local-only modules.abc (gitignored)"]
fn modules_abc_decodes_fully_with_v24_table() {
    let path = corpus_path();
    let data = std::fs::read(&path)
        .unwrap_or_else(|e| panic!("corpus missing at {}: {e}", path.display()));

    let file = decode(&data).expect("decode modules.abc without errors");

    assert_eq!(file.version, Version::new(12, 0, 6, 0));

    let mut classes = 0usize;
    let mut methods = 0usize;
    let mut instructions = 0usize;
    for c in file.classes.values() {
        classes += 1;
        for m in &c.methods {
            methods += 1;
            if let Some(body) = &m.body {
                instructions += body.bytecodes.len();
            }
        }
    }

    // Snapshot floors recorded at 12.0.6.0 stock (2,946,777 instructions):
    // they exist to catch table regressions, not to track exact builds.
    assert!(classes >= 2000, "expected >=2000 classes, got {classes}");
    assert!(methods >= 12000, "expected >=12000 methods, got {methods}");
    assert!(
        instructions > 2_000_000,
        "expected >2,000,000 decoded instructions, got {instructions}"
    );
}
