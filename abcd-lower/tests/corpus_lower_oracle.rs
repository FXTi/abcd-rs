//! Opt-in corpus test (requires the exported GHCR corpus): for every
//! manifest row with `runtime.status == "passed"` (1149 fixtures),
//! decode → `abcd_lift::lift_file` (v0.2 lift) → ir2 verify →
//! `abcd_lower::lower_function` + `to_method_body` every function →
//! splice the lowered bodies into a cloned File → `abcd_file::encode` →
//! write the result to `$ABCD_LOWERED_DIR/v2lift/<manifest-relative abc
//! path>` for the black-box VM oracle
//! (`scripts/compare-rewritten-corpus.py`) and for the byte-identity
//! faithfulness diff against the v0.1 pipeline's `lift` tree
//! (`abcd-ir`'s corpus_lower_oracle).
//!
//! Per fixture this is all-or-nothing: if ANY function fails to
//! lower/relocate (`LowerError`, including `UnsupportedInstruction` /
//! `UntraceableEntity`) or encode fails, the fixture is not written and
//! the skip is reported as:
//!
//! ```text
//! SKIP v2lift <path> | <category> | <reason>
//! ```
//!
//! with the SAME fixed category vocabulary as the v0.1 driver: `lift`
//! (front-end: read/decode/lift), `verify` (ir2 structural verifier),
//! `lower-unsupported:<instruction>` (`LowerError::UnsupportedInstruction`),
//! `lower-untraceable:<EntityKind>` (`LowerError::UntraceableEntity`),
//! `lower-other` (any other lower/to_method_body error), `encode`, and
//! `panic` (caught by `catch_unwind`). Successful rewrites are reported
//! as `WROTE v2lift <path> (N functions)`. At the end a sorted
//! category → count histogram is printed.
//!
//! Selection: by default ALL passed rows are processed. Setting
//! `ABCD_LOWERED_CASE` to a comma-separated case list (e.g.
//! `ABCD_LOWERED_CASE=local/arithmetic`) restricts the run to those
//! cases.
//!
//! Fresh output tree per run: a full run (no `ABCD_LOWERED_CASE`) wipes
//! `$ABCD_LOWERED_DIR/v2lift` entirely; a filtered run deletes only the
//! selected fixtures' target files, so stale files from an earlier run
//! never survive a fixture that now skips.
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
//!   exports/corpus/index.jsonl /tmp/abcd-lowered-full/v2lift --allow-missing
//! ```

use std::collections::BTreeMap;
use std::fmt;
use std::path::PathBuf;
use std::process::Command;

use abcd_file::File;
use abcd_ir2::{FuncId, Module, verify_module};
use abcd_lift::lift_file;
use abcd_lower::{LowerError, lower_function, to_method_body};

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
        return Err((
            SkipCategory::Verify,
            format!("verify: {:?}", report.errors),
        ));
    }
    Ok((file, module))
}

/// Lower every function of `module`, splice the bodies into a clone of
/// `file`, and encode. Returns the encoded bytes and the function count.
/// All-or-nothing: the first lower/relocate/encode error aborts the
/// fixture; nothing is written by the caller in that case.
fn rewrite_fixture(module: &Module, file: &File) -> Result<(Vec<u8>, usize), Skip> {
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
        let lowered = lower_function(module, func_id)
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
                method.body =
                    Some(body.expect("a lowered body for every method that had one"));
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
    // compare outdated bytes). A full run wipes the variant tree; a
    // filtered run deletes only the selected fixtures' target files.
    let out_root = std::env::var_os("ABCD_LOWERED_DIR").map(PathBuf::from);
    if let Some(dir) = &out_root {
        let sub = dir.join("v2lift");
        if full_run {
            if sub.exists() {
                std::fs::remove_dir_all(&sub).expect("clear previous oracle output");
            }
        } else {
            for relative in paths.lines() {
                let target = sub.join(relative);
                if target.exists() {
                    std::fs::remove_file(&target).expect("clear stale oracle output");
                }
            }
        }
    }

    let mut fixtures = 0usize;
    let mut wrote = 0usize;
    let mut histogram: BTreeMap<String, usize> = BTreeMap::new();

    for relative in paths.lines() {
        fixtures += 1;

        // Front-end stage.
        let (file, module) = match guarded(|| front_end(&root.join(relative))) {
            Ok(pair) => pair,
            Err((category, reason)) => {
                let key = category.to_string();
                eprintln!("SKIP v2lift {relative} | {key} | {reason}");
                *histogram.entry(key).or_insert(0) += 1;
                continue;
            }
        };

        // Rewrite.
        match guarded(|| rewrite_fixture(&module, &file)) {
            Ok((encoded, functions)) => {
                eprintln!("WROTE v2lift {relative} ({functions} functions)");
                if let Some(dir) = &out_root {
                    let target = dir.join("v2lift").join(relative);
                    std::fs::create_dir_all(target.parent().unwrap()).unwrap();
                    std::fs::write(target, encoded).expect("write oracle candidate");
                }
                wrote += 1;
            }
            Err((category, reason)) => {
                let key = category.to_string();
                eprintln!("SKIP v2lift {relative} | {key} | {reason}");
                *histogram.entry(key).or_insert(0) += 1;
            }
        }
    }

    if full_run {
        // 1119 original runtime-passed fixtures + 30 P4-T6 opcode-coverage
        // fixtures (private-property-store/-in, 5 versions x 3 profiles).
        assert_eq!(fixtures, 1149, "expected 1149 runtime-passed fixtures");
    }
    assert!(fixtures > 0, "no fixtures selected");
    eprintln!(
        "corpus lower oracle rewrite: v2lift wrote {} skipped {} (fixtures: {})",
        wrote,
        histogram.values().sum::<usize>(),
        fixtures
    );
    eprintln!("HISTOGRAM v2lift:");
    for (category, count) in &histogram {
        eprintln!("  {category}: {count}");
    }
}
