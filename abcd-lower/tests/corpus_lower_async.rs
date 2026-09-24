//! N68/G6 corpus pin (opt-in, requires the exported GHCR corpus): the
//! async opcode family exists ONLY in the `not-applicable` fixtures
//! (`local/async-await` × 6 versions × 3 profiles, `local/async-generator`
//! × 24.0.0.0 × 3 profiles), which the passed-set oracle
//! (`corpus_lower_oracle`) never rewrites. This gate closes that
//! evidence hole: decode → lift → verify → lower → encode each async
//! fixture TWICE and assert (a) every function lowers (zero skips) and
//! (b) the two runs are byte-identical (determinism).
//!
//! Byte-identity against the ORIGINAL `input.abc` is NOT asserted: it
//! was never a property of these fixtures under the v0.2 pipeline (the
//! pre-N68 rewrite already differed wholesale — try-region placement,
//! unfused `isfalse`+`jnez` for the resume-mode dispatch, register
//! renumbering — independent of the async arms), and the N68 fix
//! deliberately changes the acc dataflow: pre-fix the rewrite left the
//! branch-condition value in the accumulator at `asyncfunctionresolve`
//! (the dropped acc read — semantically broken), post-fix the
//! resumption value is explicitly reloaded (`lda` before resolve /
//! `sta` of the exception before reject). The pre/post pandasm
//! attribution is the evidence artifact; the standing byte-neutrality
//! gate for the rest of the corpus is `corpus_lower_oracle` (1149-set
//! pre/post diff EMPTY under N68).
//!
//! Setting `ABCD_ASYNC_OUT=<dir>` switches to write-out mode (the tree
//! mirrors the corpus layout for `diff -r`) — the pre/post evidence
//! vehicle.
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-lower --test corpus_lower_async --release -- --ignored --nocapture
//! ```

use std::path::PathBuf;
use std::process::Command;

use abcd_ir::{FuncId, verify_module};
use abcd_lift::lift_file;
use abcd_lower::{lower_function, to_method_body};

/// Decode → lift → verify → lower → encode one fixture.
fn rewrite(root: &std::path::Path, relative: &str) -> Vec<u8> {
    let data = std::fs::read(root.join(relative)).expect("read fixture");
    let file = abcd_file::decode(&data).expect("decode fixture");
    let module = lift_file(&file).expect("lift fixture");
    let report = verify_module(&module);
    assert!(report.is_ok(), "verify {relative}: {:?}", report.errors);

    let mut bodies = Vec::new();
    for index in 0..module.functions.len() {
        let func_id = FuncId::new(index as u32);
        let func = module.func(func_id).expect("function-table index");
        if func.blocks.is_empty() {
            bodies.push(None);
            continue;
        }
        let lowered =
            lower_function(&module, func_id).unwrap_or_else(|e| panic!("lower {relative}: {e}"));
        let body = to_method_body(&module, func_id, &lowered, &file)
            .unwrap_or_else(|e| panic!("to_method_body {relative}: {e}"));
        bodies.push(Some(body));
    }
    let mut rebuilt = file.clone();
    let mut cursor = bodies.into_iter();
    for class in rebuilt.classes.values_mut() {
        for method in &mut class.methods {
            let body = cursor.next().expect("one slot per method");
            if method.body.is_some() {
                method.body = Some(body.expect("a lowered body for every method that had one"));
            }
        }
    }
    assert!(cursor.next().is_none());
    abcd_file::encode(&rebuilt).expect("encode fixture")
}

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn async_fixtures_lower_and_deterministic() {
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
import json, sys
paths = []
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        if row["case"] in ("local/async-await", "local/async-generator"):
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
    let paths: Vec<String> = String::from_utf8(output.stdout)
        .expect("UTF-8 fixture paths")
        .lines()
        .map(|l| l.to_string())
        .collect();
    assert_eq!(paths.len(), 21, "18 async-await + 3 async-generator rows");

    let out_dir = std::env::var_os("ABCD_ASYNC_OUT").map(PathBuf::from);
    for relative in &paths {
        let a = rewrite(&root, relative);
        if let Some(dir) = &out_dir {
            // Write-out mode (pre/post evidence): the tree mirrors the
            // corpus layout for `diff -r`.
            let dest = dir.join(relative);
            std::fs::create_dir_all(dest.parent().expect("parent")).expect("mkdir");
            std::fs::write(&dest, &a).expect("write rewrite");
            eprintln!("N68-ASYNC-REWRITE {relative}");
            continue;
        }
        let b = rewrite(&root, relative);
        assert_eq!(a, b, "determinism: two rewrites of {relative} differ");
        eprintln!("N68-ASYNC-OK {relative}");
    }
    eprintln!("N68-ASYNC-GATE fixtures={} lowered=all", paths.len());
}
