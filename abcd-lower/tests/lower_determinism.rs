//! Opt-in determinism harness (N20, v0.2 port of
//! `abcd-ir/tests/lower_determinism.rs`): the v0.2 lift → lower →
//! MethodBody → encode path must be byte-reproducible.
//!
//! For every selected fixture this test performs:
//!
//! - **E2E pair**: two independent `decode → lift → verify → lower → encode`
//!   runs; the encoded bytes must be identical (catches decode/lift/lower
//!   nondeterminism end-to-end).
//! - **Lower pair**: the same lifted module lowered twice; the encoded bytes
//!   must be identical (isolates lower-stage nondeterminism from front-end
//!   nondeterminism).
//!
//! On a mismatch the harness pinpoints the first differing function and the
//! first differing instruction inside it (per-function `abcd_isa::encode`
//! comparison), so the failing stage and shape are visible in the log.
//!
//! Selection: all `runtime.status == "passed"` manifest rows, optionally
//! restricted by `ABCD_DETERMINISM_CASES` (comma-separated substrings of the
//! manifest-relative abc path). (The v0.1 harness's opt variant has no v0.2
//! counterpart at P2 — passes land at P3.)
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-lower --test lower_determinism --offline -- --ignored --nocapture
//! ABCD_DETERMINISM_CASES=destructuring,exception-finally \
//!   cargo test -p abcd-lower --test lower_determinism --offline -- --ignored --nocapture
//! ```

use std::path::PathBuf;
use std::process::Command;

use abcd_file::File;
use abcd_ir::{FuncId, Module, verify_module};
use abcd_lift::lift_file;
use abcd_lower::{lower_function, to_method_body};

/// Read → decode → v0.2 lift → verify (same front end as
/// corpus_lower_oracle).
fn front_end(path: &std::path::Path) -> Option<(File, Module)> {
    let data = std::fs::read(path).ok()?;
    let file = abcd_file::decode(&data).ok()?;
    let module = lift_file(&file).ok()?;
    if !verify_module(&module).is_ok() {
        return None;
    }
    Some((file, module))
}

/// Lower every function and encode the spliced file (same shape as
/// corpus_lower_oracle::rewrite_fixture). `None` on any stage failure.
fn rewrite_fixture(module: &Module, file: &File) -> Option<Vec<u8>> {
    let mut bodies = Vec::new();
    for index in 0..module.functions.len() {
        let func_id = FuncId::new(index as u32);
        let func = module.func(func_id)?;
        if func.blocks.is_empty() {
            bodies.push(None);
            continue;
        }
        let lowered = lower_function(module, func_id).ok()?;
        bodies.push(Some(to_method_body(module, func_id, &lowered, file).ok()?));
    }
    let mut rebuilt = file.clone();
    let mut cursor = bodies.into_iter();
    for class in rebuilt.classes.values_mut() {
        for method in &mut class.methods {
            let body = cursor.next()?;
            if method.body.is_some() {
                method.body = Some(body?);
            }
        }
    }
    abcd_file::encode(&rebuilt).ok()
}

/// First difference between two byte slices: (index, a, b) or length diff.
fn first_diff(a: &[u8], b: &[u8]) -> Option<String> {
    for (i, (x, y)) in a.iter().zip(b.iter()).enumerate() {
        if x != y {
            return Some(format!("byte {i}: 0x{x:02x} vs 0x{y:02x}"));
        }
    }
    if a.len() != b.len() {
        return Some(format!("length {} vs {}", a.len(), b.len()));
    }
    None
}

/// Per-function lowered-bytecode comparison; reports the first differing
/// function and instruction window.
fn pinpoint(module_a: &Module, module_b: &Module, file: &File) -> String {
    let mut report = String::new();
    for index in 0..module_a.functions.len().min(module_b.functions.len()) {
        let func_id = FuncId::new(index as u32);
        let name = module_a
            .func(func_id)
            .and_then(|f| module_a.sym.resolve(f.name))
            .unwrap_or("?")
            .to_string();
        if module_a.func(func_id).is_none_or(|f| f.blocks.is_empty()) {
            continue;
        }
        let (Ok(la), Ok(lb)) = (
            lower_function(module_a, func_id),
            lower_function(module_b, func_id),
        ) else {
            continue;
        };
        let ea = abcd_isa::encode(&la.bytecodes).map(|(b, _)| b);
        let eb = abcd_isa::encode(&lb.bytecodes).map(|(b, _)| b);
        match (ea, eb) {
            (Ok(ba), Ok(bb)) if ba == bb => {}
            (Ok(ba), Ok(bb)) => {
                let detail = first_diff(&ba, &bb).unwrap_or_default();
                report.push_str(&format!(
                    "    func {index} <{name}>: lowered bytecode differs ({detail}; {} vs {} insns)\n",
                    la.bytecodes.len(),
                    lb.bytecodes.len()
                ));
                // Show the first differing instruction pair.
                let at = ba.iter().zip(&bb).position(|(x, y)| x != y).unwrap_or(0);
                let ia = la
                    .bytecodes
                    .get(at.min(la.bytecodes.len().saturating_sub(1)));
                let ib = lb
                    .bytecodes
                    .get(at.min(lb.bytecodes.len().saturating_sub(1)));
                report.push_str(&format!("      around insn {at}: {ia:?} vs {ib:?}\n"));
                // Also surface try-block differences.
                let ta = to_method_body(module_a, func_id, &la, file).map(|b| b.try_blocks);
                let tb = to_method_body(module_b, func_id, &lb, file).map(|b| b.try_blocks);
                if format!("{ta:?}") != format!("{tb:?}") {
                    report.push_str(&format!("      try_blocks: {ta:?} vs {tb:?}\n"));
                }
            }
            _ => report.push_str(&format!(
                "    func {index} <{name}>: encode failed in one run\n"
            )),
        }
        if report.lines().count() > 24 {
            report.push_str("    ... (truncated)\n");
            break;
        }
    }
    report
}

#[test]
#[ignore = "requires exported GHCR corpus"]
fn corpus_lower_is_byte_deterministic() {
    let root = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        });

    let output = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, os, sys
filters = list(filter(None, (c.strip() for c in os.environ.get("ABCD_DETERMINISM_CASES", "").split(","))))
paths = []
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        if row["runtime"]["status"] != "passed":
            continue
        if filters and not any(f in row["abc"] for f in filters):
            continue
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
    let paths = String::from_utf8(output.stdout).expect("UTF-8 fixture paths");

    let mut fixtures = 0usize;
    let mut skipped = 0usize;
    let mut e2e_mismatch = 0usize;
    let mut lower_mismatch = 0usize;

    for relative in paths.lines() {
        fixtures += 1;
        let path = root.join(relative);

        let Some((file1, module1)) = front_end(&path) else {
            skipped += 1;
            continue;
        };
        let Some((file2, module2)) = front_end(&path) else {
            skipped += 1;
            continue;
        };

        let bytes1 = rewrite_fixture(&module1, &file1);
        // Same module lowered a second time: isolates lower-stage
        // nondeterminism (front end shared).
        let bytes1b = rewrite_fixture(&module1, &file1);
        let bytes2 = rewrite_fixture(&module2, &file2);

        let (Some(b1), Some(b1c), Some(b2)) = (bytes1, bytes1b, bytes2) else {
            skipped += 1;
            continue;
        };

        if b1 != b1c {
            lower_mismatch += 1;
            eprintln!(
                "LOWER-NONDET {relative} ({} vs {} bytes)",
                b1.len(),
                b1c.len()
            );
        }
        if b1 != b2 {
            e2e_mismatch += 1;
            eprintln!("E2E-NONDET {relative} ({} vs {} bytes)", b1.len(), b2.len());
            eprint!("{}", pinpoint(&module1, &module2, &file1));
        }
    }

    eprintln!(
        "determinism harness: {fixtures} fixtures, {skipped} skipped, \
         {lower_mismatch} lower-stage mismatches, {e2e_mismatch} end-to-end mismatches"
    );
    assert_eq!(
        lower_mismatch + e2e_mismatch,
        0,
        "{lower_mismatch} lower-stage + {e2e_mismatch} end-to-end nondeterministic fixtures"
    );
}
