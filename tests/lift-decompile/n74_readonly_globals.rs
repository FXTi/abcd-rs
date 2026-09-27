//! N74-W2 node evidence (synthetic, no corpus required): a temp whose
//! name hint is a NON-WRITABLE GLOBAL (`Number.NaN` → `NaN`,
//! a `globalThis.Infinity` load → `Infinity`, `Number.undefined` →
//! `undefined`)
//! must never be DECLARED under that name — es2abc resolves the
//! identifier to the global record and compiles the initializer as a
//! store to the read-only global (`TypeError: Cannot assign to read
//! only property` at runtime; verified against the pinned image with
//! `function f(){ const NaN = 5; … }`). The names are legal JS bindings
//! per spec (Node accepts them), so the text-shape pins below — not the
//! node run — carry the bug signal; the node run keeps the renamed
//! output semantically honest.
//!
//! The general rule (ECMA-262 §19.1): the global object's VALUE
//! properties with [[Writable]]: false are exactly `undefined`, `NaN`,
//! `Infinity` — `undefined` was already in the legalizer's
//! shadow-hostile set; N74 adds the other two. Property ACCESSES
//! (`Number.NaN`) are unaffected.
//!
//! Not registered in `main.rs` (concurrent N74 workers); run
//! stand-alone by temporarily adding `mod n74_readonly_globals;`.

use abcd_decompile::emit::{decompile_module, EmitOptions};
use abcd_file::{decode, AccessFlags, Builder, CodeEntity, Type};
use abcd_isa::{encode as encode_bytecodes, Bytecode, EntityId, Imm, Reg};
use abcd_lift::lift_file;

/// A 12.x file whose global class carries one static method
/// `f() { return Number.<prop> + Number.<prop>; }` — the property-load
/// result has TWO uses, so the decompiler declares it as a named temp
/// (hint: the property name) instead of inlining it.
fn build_prop_temp(prop: &str) -> abcd_ir::Module {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = encode_bytecodes(&[
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // acc = Number
        Bytecode::Sta(Reg(0)),                            // v0 = Number
        Bytecode::Lda(Reg(0)),
        Bytecode::Ldobjbyname(Imm(0), placeholder), // acc = Number.<prop>
        Bytecode::Sta(Reg(1)),                      // v1 = the temp under test
        Bytecode::Lda(Reg(1)),
        Bytecode::Add2(Imm(0), Reg(1)), // acc = v1 + v1 (second use)
        Bytecode::Return,
    ])
    .unwrap();
    let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 4, 0);
    let number = b.add_string("Number");
    let name = b.add_string(prop);
    b.relocate_code_id(m, offsets[0], 0, CodeEntity::String(number))
        .unwrap();
    b.relocate_code_id(m, offsets[3], 0, CodeEntity::String(name))
        .unwrap();
    b.deduplicate();
    let file = decode(&b.finalize().unwrap()).unwrap();
    lift_file(&file).expect("lift")
}

/// `f() { return <global> + <global>; }` — the TryGetGlobal name is the
/// temp hint (the `const Infinity = globalThis.Infinity;` shape of
/// test262 built-ins/Infinity/S15.1.1.2_A1).
fn build_global_temp(name: &str) -> abcd_ir::Module {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = encode_bytecodes(&[
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // acc = <global>
        Bytecode::Sta(Reg(0)),                            // v0 = the temp
        Bytecode::Lda(Reg(0)),
        Bytecode::Add2(Imm(0), Reg(0)), // acc = v0 + v0 (second use)
        Bytecode::Return,
    ])
    .unwrap();
    let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 4, 0);
    let global = b.add_string(name);
    b.relocate_code_id(m, offsets[0], 0, CodeEntity::String(global))
        .unwrap();
    b.deduplicate();
    let file = decode(&b.finalize().unwrap()).unwrap();
    lift_file(&file).expect("lift")
}

fn decompile(module: &abcd_ir::Module) -> String {
    decompile_module(module, &EmitOptions::default()).text
}

/// The declaration-shape pin: no `const|let|var|function <name>` for any
/// non-writable global; the temps must be renamed (`NaN_`, …).
#[test]
fn nonwritable_global_hints_are_never_declared() {
    // `Number.NaN` — the property-hint channel (25 of the 26 rows).
    // `Infinity` — the global-hint channel (built-ins/Infinity row).
    for (module, prop, renamed) in [
        (build_prop_temp("NaN"), "NaN", "NaN_"),
        (build_global_temp("Infinity"), "Infinity", "Infinity_"),
    ] {
        let text = decompile(&module);
        eprintln!("── {prop} ──\n{text}");
        for kw in ["const", "let", "var"] {
            assert!(
                !text.contains(&format!("{kw} {prop} ="))
                    && !text.contains(&format!("{kw} {prop};")),
                "{kw} {prop} declaration must not be emitted: {text}"
            );
        }
        assert!(
            !text.contains(&format!("function {prop}(")),
            "function {prop} declaration must not be emitted: {text}"
        );
        assert!(
            text.contains(&format!("const {renamed}")),
            "the temp must be renamed to {renamed}[…]: {text}"
        );
    }
    // Regression pin: `undefined` was already shadow-hostile.
    let text = decompile(&build_prop_temp("undefined"));
    assert!(
        !text.contains("const undefined ="),
        "undefined stays renamed: {text}"
    );
    // Property ACCESS keeps the verbatim name (dot form).
    let text = decompile(&build_prop_temp("NaN"));
    assert!(
        text.contains(".NaN"),
        "member access is not a binding and keeps its name: {text}"
    );
}

/// node behavior evidence: the renamed temps still compute the real
/// values (NaN, Infinity, NaN-from-undefined+undefined).
#[test]
fn nonwritable_global_node_behavior() {
    let node_ok = std::process::Command::new("node")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !node_ok {
        eprintln!("NODE-EVIDENCE node not found on this host — behavior run skipped");
        return;
    }
    let dir = std::env::temp_dir().join("abcd-n74-node");
    std::fs::create_dir_all(&dir).expect("tempdir");
    let cases: Vec<(String, abcd_ir::Module, &str)> = vec![
        ("NaN".to_string(), build_prop_temp("NaN"), "NaN"),
        (
            "Infinity".to_string(),
            build_global_temp("Infinity"),
            "Infinity",
        ),
        ("undefined".to_string(), build_prop_temp("undefined"), "NaN"),
    ];
    for (prop, module, want) in cases {
        let text = decompile(&module);
        let case = dir.join(format!("{prop}.js"));
        std::fs::write(&case, format!("{text}\nconsole.log(String(f()));\n")).expect("write");
        let run = std::process::Command::new("node")
            .arg(&case)
            .output()
            .expect("run node");
        let stdout = String::from_utf8_lossy(&run.stdout).to_string();
        let stderr = String::from_utf8_lossy(&run.stderr).to_string();
        eprintln!("NODE-EVIDENCE {prop} stdout={stdout:?} stderr={stderr:?}");
        assert!(run.status.success(), "node run failed for {prop}: {stderr}");
        assert_eq!(stdout, format!("{want}\n"), "{prop} behavior mismatch");
    }
}
