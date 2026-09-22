//! Shared corpus harness helpers for `abcd-analysis` corpus tests
//! (opt-in; require the exported GHCR corpus + python3 — the same pattern
//! as `abcd-lift/tests/corpus_lift_verify.rs`).

use std::path::PathBuf;
use std::process::Command;

/// The corpus root: `$ABCD_CORPUS_ROOT` or `exports/corpus`.
pub fn corpus_root() -> PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        })
}

/// Every fixture path in the manifest (all 2787 rows, sorted for
/// determinism), parsed with python3's standard JSON library.
pub fn manifest_paths(root: &PathBuf) -> Vec<String> {
    let output = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, sys
paths = []
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        assert "\n" not in row["abc"] and "\t" not in row["abc"]
        paths.append(row["abc"])
for path in sorted(paths):
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
    String::from_utf8(output.stdout)
        .expect("UTF-8 fixture paths")
        .lines()
        .map(str::to_string)
        .collect()
}
