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

    // Probe node by SPAWNING it (not `which` — `which` is a Git-Bash
    // idiom that prints MSYS paths like `/c/Program Files/…/node.exe`,
    // which std::process::Command cannot use on Windows; Command itself
    // searches PATH+PATHEXT correctly). Windows CI failure N68-followup.
    let node_ok = std::process::Command::new("node")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !node_ok {
        eprintln!("NODE-EVIDENCE node not found on this host — behavior run skipped");
        return;
    }
    let node = "node";

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

// ── N68-remainder node evidence: the suspend/resume machinery fold ────
//
// Cases D/E/E2 are built DIRECTLY as IR modules (the `common`
// scaffold, golden_async.rs's shapes): the fold under test is Stage-B,
// so the IR is the honest input. Each carries the FULL vendor await
// machinery (es2panda `functionBuilder.cpp` `Await`:
// `AsyncFunctionAwaitUncaught` + `SuspendGenerator` +
// `ResumeGenerator`/`GetResumeMode` + the THROW-only `HandleCompletion`
// dispatch) inside the `AsyncFunctionEnter`/catch-all entry protocol —
// the decompiled text only parses and runs correctly under node if the
// fold dissolved the machinery into plain `await` control flow.

use abcd_ir::module::FunctionKind;
use abcd_ir::op::{BinOp, CmpOp, UnOp};
use abcd_ir::{Edge, EdgeKind, FuncId, Module, Op, ValueId};
use common::*;

/// `AsyncFunctionAwaitUncaught(funcobj, acc=v)` + `SuspendGenerator` +
/// the completion pair; returns (resume, mode).
fn await_site(
    m: &mut Module,
    b: abcd_ir::BlockId,
    funcobj: ValueId,
    v: ValueId,
) -> (ValueId, ValueId) {
    let aw = emit(m, b, Op::AwaitUncaught { funcobj, value: v });
    emit(
        m,
        b,
        Op::SuspendGenerator {
            genobj: funcobj,
            value: aw,
        },
    );
    let r = emit(m, b, Op::ResumeGenerator { genobj: funcobj });
    let mode = emit(m, b, Op::GetResumeMode { genobj: funcobj });
    (r, mode)
}

/// The ASYNC `HandleCompletion`: `if (mode == THROW) throw resume;`
/// else continue at the returned block.
fn await_dispatch(
    m: &mut Module,
    b: abcd_ir::BlockId,
    mode: ValueId,
    resume: ValueId,
    throw_b: abcd_ir::BlockId,
    cont: abcd_ir::BlockId,
) {
    let one = load_number(m, b, 1.0);
    let eq = emit(
        m,
        b,
        Op::Compare {
            op: CmpOp::Eq,
            left: mode,
            right: one,
        },
    );
    let t = emit(
        m,
        b,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq,
        },
    );
    emit_void(
        m,
        b,
        Op::CondBranch {
            cond: t,
            true_dest: cont,
            false_dest: throw_b,
        },
    );
    emit_void(m, throw_b, Op::Throw { value: resume });
    emit_void(m, throw_b, Op::Unreachable);
    link(m, b, cont);
    link(m, b, throw_b);
}

/// `AsyncFunctionResolve(funcobj, acc=v)` + return (`DirectReturn`).
fn async_resolve_return(m: &mut Module, b: abcd_ir::BlockId, funcobj: ValueId, v: ValueId) {
    let res = emit(m, b, Op::AsyncResolve { funcobj, value: v });
    emit_void(m, b, Op::Return { value: Some(res) });
}

/// The catch-all rejection wrapper over the protected blocks.
fn async_catch_all(m: &mut Module, f: FuncId, funcobj: ValueId, protected: Vec<abcd_ir::BlockId>) {
    let handler = add_block(m, f);
    let exc = add_exception_param(m, handler);
    let rej = emit(
        m,
        handler,
        Op::AsyncReject {
            funcobj,
            value: exc,
        },
    );
    emit_void(m, handler, Op::Return { value: Some(rej) });
    add_try(m, f, protected, handler, exc);
}

/// Case D: awaits inside a real loop — `async function d() {
/// let s = 0; let i = 3; while (i != 0) { s = s + await 5; i = i - 1; }
/// return s; }` — resolves 15.
fn case_d() -> abcd_ir::Module {
    let mut m = mk_module();
    let f = add_func_kind(&mut m, "d", FunctionKind::Async);
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let funcobj = emit(&mut m, b0, Op::AsyncFunctionEnter);
    let s0 = load_number(&mut m, b0, 0.0);
    let i0 = load_number(&mut m, b0, 3.0);
    let hdr = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let back = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let throw_b = add_block(&mut m, f);
    emit_void(&mut m, b0, Op::Branch { dest: hdr });
    link(&mut m, b0, hdr);
    let norm = |from| Edge {
        from,
        kind: EdgeKind::Normal,
    };
    let s_phi = emit(
        &mut m,
        hdr,
        Op::Phi {
            entries: vec![(norm(b0), s0), (norm(back), s0)], // back: placeholder
        },
    );
    let i_phi = emit(
        &mut m,
        hdr,
        Op::Phi {
            entries: vec![(norm(b0), i0), (norm(back), i0)], // back: placeholder
        },
    );
    let zero = load_number(&mut m, hdr, 0.0);
    let eq = emit(
        &mut m,
        hdr,
        Op::Compare {
            op: CmpOp::Eq,
            left: i_phi,
            right: zero,
        },
    );
    let cond = emit(
        &mut m,
        hdr,
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand: eq,
        },
    );
    emit_void(
        &mut m,
        hdr,
        Op::CondBranch {
            cond,
            true_dest: body,
            false_dest: exit,
        },
    );
    link(&mut m, hdr, body);
    link(&mut m, hdr, exit);
    // Body: `await 5` with the full machinery.
    let five = load_number(&mut m, body, 5.0);
    let (r, mode) = await_site(&mut m, body, funcobj, five);
    await_dispatch(&mut m, body, mode, r, throw_b, back);
    // Back edge: accumulate + count down. (N36: the IR's BinaryOp
    // stores left=acc/right=vreg and the semantic expression is
    // `right OP left` — the operands below are wired accordingly.)
    let s2 = emit(
        &mut m,
        back,
        Op::BinaryOp {
            op: BinOp::Add,
            left: r,
            right: s_phi,
        },
    );
    let one = load_number(&mut m, back, 1.0);
    let i2 = emit(
        &mut m,
        back,
        Op::BinaryOp {
            op: BinOp::Sub,
            left: one,
            right: i_phi,
        },
    );
    emit_void(&mut m, back, Op::Branch { dest: hdr });
    link(&mut m, back, hdr);
    // Wire the back-edge phi incomings.
    for (phi, v) in [(s_phi, s2), (i_phi, i2)] {
        let iid = match m.value(phi).expect("value").def {
            abcd_ir::ValueDef::Inst(iid) => iid,
            _ => panic!("phi must be an inst"),
        };
        if let Op::Phi { entries } = &mut m.inst_mut(iid).expect("inst").op {
            entries[1].1 = v;
        }
    }
    async_resolve_return(&mut m, exit, funcobj, s_phi);
    async_catch_all(&mut m, f, funcobj, vec![b0, hdr, body, back, exit, throw_b]);
    m
}

/// Case E: `async function e(x) { return await x; }` — resolves/rejects
/// with whatever the awaited promise settles to.
fn case_e() -> abcd_ir::Module {
    let mut m = mk_module();
    let f = add_func_kind(&mut m, "e", FunctionKind::Async);
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let x = add_param(&mut m, f);
    let funcobj = emit(&mut m, b0, Op::AsyncFunctionEnter);
    let cont = add_block(&mut m, f);
    let throw_b = add_block(&mut m, f);
    let (r, mode) = await_site(&mut m, b0, funcobj, x);
    await_dispatch(&mut m, b0, mode, r, throw_b, cont);
    async_resolve_return(&mut m, cont, funcobj, r);
    async_catch_all(&mut m, f, funcobj, vec![b0, cont, throw_b]);
    m
}

/// Case E2: a rejection crossing the dispatch's THROW arm into a USER
/// catch — `async function e2(x) { try { return await x; } catch (u) {
/// return u + 100; } }` — `e2(Promise.reject(9))` resolves 109.
fn case_e2() -> abcd_ir::Module {
    let mut m = mk_module();
    let f = add_func_kind(&mut m, "e2", FunctionKind::Async);
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let x = add_param(&mut m, f);
    let funcobj = emit(&mut m, b0, Op::AsyncFunctionEnter);
    let cont = add_block(&mut m, f);
    let throw_b = add_block(&mut m, f);
    let (r, mode) = await_site(&mut m, b0, funcobj, x);
    await_dispatch(&mut m, b0, mode, r, throw_b, cont);
    async_resolve_return(&mut m, cont, funcobj, r);
    // The user catch: `return u + 100`.
    let user_h = add_block(&mut m, f);
    let u = add_exception_param(&mut m, user_h);
    let hundred = load_number(&mut m, user_h, 100.0);
    let sum = emit(
        &mut m,
        user_h,
        Op::BinaryOp {
            op: BinOp::Add,
            left: u,
            right: hundred,
        },
    );
    async_resolve_return(&mut m, user_h, funcobj, sum);
    add_try(&mut m, f, vec![b0, cont, throw_b], user_h, u);
    // The compiler catch-all wraps everything (including the user
    // handler).
    async_catch_all(&mut m, f, funcobj, vec![b0, cont, throw_b, user_h]);
    m
}

/// node behavior evidence for the suspend/resume fold: awaits through a
/// real loop, resolved/rejected promise propagation, and a rejection
/// caught by a user `catch`.
#[test]
fn async_machine_fold_node_behavior() {
    let texts = [
        decompile(&case_d()),
        decompile(&case_e()),
        decompile(&case_e2()),
    ];
    eprintln!(
        "── case D ──\n{}\n── case E ──\n{}\n── case E2 ──\n{}",
        texts[0], texts[1], texts[2]
    );
    // Text-shape pins (always run): the machinery is GONE.
    for (i, text) in texts.iter().enumerate() {
        assert!(!text.contains("ResumeGenerator"), "case{i}: {text}");
        assert!(!text.contains("GetResumeMode"), "case{i}: {text}");
        assert!(!text.contains("async-machinery suspend"), "case{i}: {text}");
        assert!(
            !text.contains("fallback AsyncFunctionEnter"),
            "case{i}: {text}"
        );
        assert!(text.contains("await"), "case{i}: {text}");
    }
    assert!(texts[0].contains("async function d("), "{}", texts[0]);
    assert!(texts[0].contains("while"), "a real loop: {}", texts[0]);
    assert!(texts[1].contains("async function e(p1)"), "{}", texts[1]);
    assert!(texts[2].contains("async function e2(p1)"), "{}", texts[2]);
    assert!(texts[2].contains("catch"), "the user catch: {}", texts[2]);

    let node_ok = std::process::Command::new("node")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !node_ok {
        eprintln!("NODE-EVIDENCE node not found on this host — behavior run skipped");
        return;
    }

    let dir = std::env::temp_dir().join("abcd-n68r-node");
    std::fs::create_dir_all(&dir).expect("tempdir");

    // Per-case syntax check on the pure decompiled text.
    for (i, text) in texts.iter().enumerate() {
        let out = dir.join(format!("case{i}.js"));
        std::fs::write(&out, text).expect("write case");
        let check = std::process::Command::new("node")
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

    // Behavior, chained sequentially for a deterministic line order:
    // e(resolve 3)→3, e(reject 9)→reject 9, e2(reject 9)→109 (user
    // catch), e2(resolve 7)→7, d()→15 (three awaited iterations).
    let driver = dir.join("driver.js");
    let mut program = texts.concat();
    program.push_str(
        "\ne(Promise.resolve(3)).then(x => console.log(\"E:\" + x))\n\
         .then(() => e(Promise.reject(9))).catch(x => console.log(\"F:\" + x))\n\
         .then(() => e2(Promise.reject(9))).then(x => console.log(\"G:\" + x))\n\
         .then(() => e2(Promise.resolve(7))).then(x => console.log(\"H:\" + x))\n\
         .then(() => d()).then(x => console.log(\"D:\" + x));\n",
    );
    std::fs::write(&driver, &program).expect("write driver");
    let run = std::process::Command::new("node")
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
    assert_eq!(
        stdout, "E:3\nF:9\nG:109\nH:7\nD:15\n",
        "async behavior mismatch"
    );
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
