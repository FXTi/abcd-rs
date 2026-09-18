//! Opt-in corpus test (requires the exported GHCR corpus): for the
//! `local/arithmetic` fixtures (6 versions × 3 profiles = 18 rows),
//! decode → lift → verify → lower every function → splice the lowered
//! bodies into a cloned File → `abcd_file::encode` → write the result to
//! `$ABCD_LOWERED_DIR/<variant>/<manifest-relative abc path>` for the
//! black-box VM oracle (`scripts/compare-rewritten-corpus.py`).
//!
//! Two variants are produced per fixture:
//!
//! - `lift`: decode → lift → verify → lower → encode.
//! - `opt`: decode → lift → verify → `optimize_module` → re-verify →
//!   lower → encode.
//!
//! Per fixture and variant this is all-or-nothing: if ANY function fails
//! to lower/relocate (`LowerError`, including `UnsupportedInstruction` /
//! `UntraceableEntity`) or encode fails, that variant is not written and
//! the skip is reported as `SKIP <variant> <path>: <reason>`. Successful
//! rewrites are reported as `WROTE <variant> <path> (N functions)`. The
//! test asserts the expected fixture count was processed; it does NOT
//! assert that all fixtures lowered — skips are data for the oracle run.
//!
//! Run:
//!
//! ```text
//! ABCD_LOWERED_DIR=/tmp/abcd-lowered-oracle \
//!   cargo test -p abcd-ir --test corpus_lower_oracle --offline -- --ignored --nocapture
//! python3 scripts/compare-rewritten-corpus.py \
//!   exports/corpus/index.jsonl /tmp/abcd-lowered-oracle/lift --case local/arithmetic
//! ```

use std::path::PathBuf;
use std::process::Command;

use abcd_file::File;
use abcd_ir::entity::FuncId;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::{lower_function, to_method_body};
use abcd_ir::module::Module;
use abcd_ir::opt::optimize_module;
use abcd_ir::verify::verify_module;

/// Lower every function of `module`, splice the bodies into a clone of
/// `file`, and encode. Returns the encoded bytes and the function count.
/// All-or-nothing: the first lower/relocate/encode error aborts the
/// fixture; nothing is written by the caller in that case.
fn rewrite_fixture(module: &Module, file: &File) -> Result<(Vec<u8>, usize), String> {
    // Function i corresponds to the i-th method in lift order (classes in
    // BTreeMap order, methods in declaration order) — the same iteration
    // lift_file performs, and the same splice order the lower→encode
    // roundtrip test uses.
    let mut bodies = Vec::new();
    for index in 0..module.functions.len() {
        let func_id = FuncId::from_index(index);
        let name = module.strings.get(module.func(func_id).name).to_string();
        let lowered = lower_function(module, func_id).map_err(|e| format!("lower {name}: {e}"))?;
        let body = to_method_body(module, func_id, &lowered, file)
            .map_err(|e| format!("to_method_body {name}: {e}"))?;
        bodies.push(body);
    }
    let functions = bodies.len();

    let mut rebuilt = file.clone();
    let mut cursor = bodies.into_iter();
    for class in rebuilt.classes.values_mut() {
        for method in &mut class.methods {
            method.body = Some(cursor.next().expect("one body per method"));
        }
    }
    assert!(cursor.next().is_none());

    let encoded = abcd_file::encode(&rebuilt).map_err(|e| format!("encode: {e}"))?;
    Ok((encoded, functions))
}

/// Catch panics from lowering/encoding so one bad fixture reports as a
/// skip instead of aborting the whole evidence run.
fn rewrite_guarded(module: &Module, file: &File) -> Result<(Vec<u8>, usize), String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        rewrite_fixture(module, file)
    })) {
        Ok(result) => result,
        Err(payload) => {
            let reason = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "unknown panic".to_string());
            Err(format!("panic: {reason}"))
        }
    }
}

#[test]
#[ignore = "requires exported GHCR corpus and docker"]
fn arithmetic_corpus_lowered_bodies_written_for_vm_oracle() {
    let root = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        });

    // Corpus tooling already uses Python. Parse JSON with its standard
    // library instead of assuming a particular JSON whitespace/key order
    // (same pattern as abcd-ir/tests/corpus_entities.rs).
    let output = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, sys
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        if row["case"] == "local/arithmetic":
            assert "\n" not in row["abc"] and "\t" not in row["abc"]
            print(row["abc"])
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

    // Fresh output tree per run: stale files from an earlier run must not
    // survive a fixture that now skips (the oracle script would otherwise
    // compare outdated bytes).
    let out_root = std::env::var_os("ABCD_LOWERED_DIR").map(PathBuf::from);
    if let Some(dir) = &out_root {
        for variant in ["lift", "opt"] {
            let sub = dir.join(variant);
            if sub.exists() {
                std::fs::remove_dir_all(&sub).expect("clear previous oracle output");
            }
        }
    }

    let mut fixtures = 0usize;
    let mut wrote = [0usize; 2];
    let mut skipped = [0usize; 2];

    for relative in paths.lines() {
        fixtures += 1;
        let data = std::fs::read(root.join(relative)).expect("fixture");
        let file = abcd_file::decode(&data).expect("decode fixture");
        let module = lift_file(&file).expect("lift fixture");
        assert!(
            verify_module(&module).is_empty(),
            "{relative}: lifted module failed structural verification"
        );

        // Variant: lift-only.
        match rewrite_guarded(&module, &file) {
            Ok((encoded, functions)) => {
                eprintln!("WROTE lift {relative} ({functions} functions)");
                if let Some(dir) = &out_root {
                    let target = dir.join("lift").join(relative);
                    std::fs::create_dir_all(target.parent().unwrap()).unwrap();
                    std::fs::write(target, encoded).expect("write oracle candidate");
                }
                wrote[0] += 1;
            }
            Err(reason) => {
                eprintln!("SKIP lift {relative}: {reason}");
                skipped[0] += 1;
            }
        }

        // Variant: lift + optimize (optimize mutates the module; re-verify
        // before lowering).
        let mut optimized = module.clone();
        optimize_module(&mut optimized);
        let verify_errors = verify_module(&optimized);
        if !verify_errors.is_empty() {
            eprintln!("SKIP opt {relative}: post-optimize verify: {verify_errors:?}");
            skipped[1] += 1;
            continue;
        }
        match rewrite_guarded(&optimized, &file) {
            Ok((encoded, functions)) => {
                eprintln!("WROTE opt {relative} ({functions} functions)");
                if let Some(dir) = &out_root {
                    let target = dir.join("opt").join(relative);
                    std::fs::create_dir_all(target.parent().unwrap()).unwrap();
                    std::fs::write(target, encoded).expect("write oracle candidate");
                }
                wrote[1] += 1;
            }
            Err(reason) => {
                eprintln!("SKIP opt {relative}: {reason}");
                skipped[1] += 1;
            }
        }
    }

    assert_eq!(fixtures, 18, "expected 18 local/arithmetic fixtures");
    eprintln!(
        "corpus lower oracle rewrite: lift wrote {} skipped {}; \
         opt wrote {} skipped {} (fixtures: {})",
        wrote[0], skipped[0], wrote[1], skipped[1], fixtures
    );
}
