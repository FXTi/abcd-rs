//! N68/G6 node evidence (synthetic, no corpus required): three async
//! mini-cases built through the `abcd_file::Builder` (real .abc files),
//! lifted, decompiled, and executed under `node` — the dream gate's VM
//! oracle is not-applicable for async (ark_js_vm does not schedule the
//! host promise loop), so node carries the behavior evidence.
//!
//! Each case pins BOTH the lift's acc-value operand (N68) and the
//! Stage-B async fold (resolve → `return`, reject → `throw`,
//! awaituncaught → `await` of the VALUE):
//!
//! - A (`f`): `return 1 + 41` completion — `asyncfunctionresolve` with
//!   the sum in the acc. `f()` must resolve to 42.
//! - B (`g`): `throw 7` rejection — `asyncfunctionreject` with 7 in the
//!   acc. `g()` must reject with 7.
//! - C (`h`): `return await 5` — `asyncfunctionawaituncaught` awaits the
//!   acc-carried VALUE 5 (pre-N68 the funcobj register was misread as
//!   the operand), then resolves with the awaited value. `h()` must
//!   resolve to 5.
//!
//! The decompiled text is also `node --check`-ed per case. When node is
//! absent the behavior assertions skip (reported); the text-shape pins
//! always run.

use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_file::{AccessFlags, Builder, FunctionKind as FileKind, Type, decode};
use abcd_isa::{Bytecode, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;

/// Build a 12.x file whose global class carries one static ASYNC method
/// with the given bytecodes; decode and lift it.
fn build_async(name: &str, bytecodes: &[Bytecode], num_vregs: u32) -> abcd_ir::Module {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _offsets) = encode_bytecodes(bytecodes).unwrap();
    let m = b.class_add_method(cls, name, proto, AccessFlags::STATIC, &code, num_vregs, 0);
    b.method_set_function_kind(m, FileKind::AsyncFunction);
    let file = decode(&b.finalize().unwrap()).unwrap();
    lift_file(&file).expect("lift")
}

/// Case A: async completion — `async function f() { return 1 + 41; }`.
fn case_a() -> abcd_ir::Module {
    build_async(
        "f",
        &[
            Bytecode::Asyncfunctionenter,
            Bytecode::Sta(Reg(0)), // v0 = async funcobj (context)
            Bytecode::Ldai(Imm(41)),
            Bytecode::Sta(Reg(1)),
            Bytecode::Ldai(Imm(1)),
            Bytecode::Add2(Imm(0), Reg(1)),         // acc = 1 + 41
            Bytecode::Asyncfunctionresolve(Reg(0)), // value = acc (42), funcobj = v0
            Bytecode::Return,
        ],
        4,
    )
}

/// Case B: async rejection — `async function g() { throw 7; }`.
fn case_b() -> abcd_ir::Module {
    build_async(
        "g",
        &[
            Bytecode::Asyncfunctionenter,
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(7)),
            Bytecode::Asyncfunctionreject(Reg(0)), // value = acc (7), funcobj = v0
            Bytecode::Return,
        ],
        4,
    )
}

/// Case C: awaited value — `async function h() { return await 5; }`.
fn case_c() -> abcd_ir::Module {
    build_async(
        "h",
        &[
            Bytecode::Asyncfunctionenter,
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(5)),
            Bytecode::Asyncfunctionawaituncaught(Reg(0)), // awaits acc (5) — the VALUE, not v0
            Bytecode::Asyncfunctionresolve(Reg(0)),       // resolves with acc (the await result)
            Bytecode::Return,
        ],
        4,
    )
}

fn decompile(module: &abcd_ir::Module) -> String {
    decompile_module(module, &EmitOptions::default()).text
}

#[test]
fn async_fold_shapes_are_return_throw_await_of_value() {
    let a = decompile(&case_a());
    let b = decompile(&case_b());
    let c = decompile(&case_c());
    eprintln!("── case A ──\n{a}\n── case B ──\n{b}\n── case C ──\n{c}");
    assert!(a.contains("async function f("), "async kind: {a}");
    assert!(b.contains("async function g("), "async kind: {b}");
    assert!(c.contains("async function h("), "async kind: {c}");
    // The fold landed: completion is a plain return of the VALUE, the
    // rejection is a plain throw of the REASON, the await reads the
    // VALUE 5 (not the funcobj).
    assert!(a.contains("return"), "{a}");
    assert!(!a.contains("AsyncResolve"), "no residual fallback: {a}");
    assert!(b.contains("throw 7") || b.contains("throw 7.0"), "{b}");
    assert!(!b.contains("AsyncReject"), "no residual fallback: {b}");
    assert!(c.contains("await 5"), "await reads the acc value: {c}");
    assert!(c.contains("return"), "{c}");
}

/// node behavior evidence: the three decompiled bodies, run.
#[test]
fn async_fold_node_behavior() {
    let texts = [
        decompile(&case_a()),
        decompile(&case_b()),
        decompile(&case_c()),
    ];

    let node = std::process::Command::new("which")
        .arg("node")
        .output()
        .ok()
        .filter(|o| o.status.success());
    let Some(node) = node else {
        eprintln!("NODE-EVIDENCE node not found on this host — behavior run skipped");
        return;
    };
    let node = String::from_utf8_lossy(&node.stdout).trim().to_string();

    let dir = std::env::temp_dir().join("abcd-n68-node");
    std::fs::create_dir_all(&dir).expect("tempdir");

    // Per-case syntax check on the pure decompiled text.
    for (i, text) in texts.iter().enumerate() {
        let out = dir.join(format!("case{i}.js"));
        std::fs::write(&out, text).expect("write case");
        let check = std::process::Command::new(&node)
            .arg("--check")
            .arg(&out)
            .output()
            .expect("run node --check");
        assert!(
            check.status.success(),
            "node --check case{i}: {}",
            String::from_utf8_lossy(&check.stderr)
        );
    }

    // Behavior: f() resolves 42, g() rejects 7, h() resolves 5.
    let driver = dir.join("driver.js");
    let mut program = texts.concat();
    program.push_str(
        "\nf().then(x => console.log(\"A:\" + x));\n\
         g().catch(e => console.log(\"B:\" + e));\n\
         h().then(x => console.log(\"C:\" + x));\n",
    );
    std::fs::write(&driver, &program).expect("write driver");
    let run = std::process::Command::new(&node)
        .arg(&driver)
        .output()
        .expect("run node");
    let stdout = String::from_utf8_lossy(&run.stdout).to_string();
    let stderr = String::from_utf8_lossy(&run.stderr).to_string();
    eprintln!(
        "NODE-EVIDENCE exit={} stdout={:?} stderr={:?}",
        run.status, stdout, stderr
    );
    assert!(run.status.success(), "node run failed: {stderr}");
    assert_eq!(stdout, "A:42\nB:7\nC:5\n", "async behavior mismatch");
}

// ── Corpus async recompile evidence (opt-in) ─────────────────────────

mod common;

/// Decompile the 21 corpus async fixtures (`local/async-await`,
/// `local/async-generator` — the ONLY carriers of the async opcode
/// family, all runtime `not-applicable`) and write the JS tree to
/// `target/dream-gate-async/src/` (plus `manifest.tsv` rows
/// `abc<TAB>version<TAB>profile<TAB>module`) for the es2abc recompile
/// evidence run:
///
/// ```text
/// cargo test -p abcd-decompile --test async_node --release -- \
///   --ignored --nocapture async_corpus_emit
/// python3 scripts/dream-gate.py …  # the recompile step is driven
/// # ad hoc per scripts/dream-gate.py's compile_one flags
/// ```
#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn async_corpus_emit() {
    let root = common::corpus_root();
    let out_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("target")
        .join("dream-gate-async");
    let src_root = out_root.join("src");
    std::fs::create_dir_all(&src_root).expect("create src root");

    // Select the async rows (any runtime status — they are all
    // not-applicable) with version/profile/module facts for the
    // recompile driver.
    let output = std::process::Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, sys
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        if row["case"] in ("local/async-await", "local/async-generator"):
            print("\t".join([row["abc"], row["version"], row["profile"]]))
"#,
        )
        .arg(root.join("index.jsonl"))
        .output()
        .expect("python3 is required by corpus tooling");
    assert!(output.status.success());
    let rows = String::from_utf8(output.stdout).expect("UTF-8");
    let rows: Vec<&str> = rows.lines().collect();
    assert_eq!(rows.len(), 21, "18 async-await + 3 async-generator rows");

    let mut manifest = String::new();
    for row in &rows {
        let f: Vec<&str> = row.split('\t').collect();
        let (abc, version, profile) = (f[0], f[1], f[2]);
        let data = std::fs::read(root.join(abc)).expect("read fixture");
        let file = abcd_file::decode(&data).expect("decode fixture");
        let module = lift_file(&file).expect("lift fixture");
        let d = decompile_module(
            &module,
            &EmitOptions {
                call_entry: true,
                ..EmitOptions::default()
            },
        );
        let is_module = !module.imports.is_empty()
            || !module.exports.is_empty()
            || !module.module_requests.is_empty();
        let js_path = src_root.join(format!("{abc}.js"));
        std::fs::create_dir_all(js_path.parent().expect("parent")).expect("mkdirs");
        std::fs::write(&js_path, &d.text).expect("write js");
        manifest.push_str(&format!("{abc}\t{version}\t{profile}\t{is_module}\n"));
        eprintln!("ASYNC-EMIT {abc}");
    }
    std::fs::write(out_root.join("manifest.tsv"), manifest).expect("write manifest");
    eprintln!("ASYNC-EMIT fixtures=21 -> {}", src_root.display());
}
