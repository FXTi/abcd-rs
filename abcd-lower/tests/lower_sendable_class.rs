//! N53 evidence (v2-P2b): `callruntime.definesendableclass` keeps its
//! opcode identity through the WHOLE v2 pipeline — decode → v0.2 lift
//! (`Op::DefineSendableClass`) → abcd-lower isel
//! (`Bytecode::CallruntimeDefinesendableclass`) → encode → decode.
//!
//! v0.1 collapsed the opcode into `InstData::DefineClassWithBuffer`
//! and its isel re-emitted the CONTEMPORARY `defineclasswithbuffer` —
//! opcode-identity corruption. The sendable fixtures are runtime-N/A
//! (structural only, not in the 1149-fixture VM set), so the strongest
//! available evidence is this structural round-trip plus the upstream
//! ark_disasm rendering of the rewritten fixture (collected out of
//! band via the docker toolchain image — the rewritten bytes are
//! written to `$ABCD_N53_REWRITE` when set).
//!
//! Vendor grounding:
//! - `callruntime.definesendableclass imm1:u16, method_id,
//!   literalarray_id, imm2:u16, v:in:top`
//!   (abcd-isa-sys/vendor/isa/isa.yaml:861-866);
//! - the runtime builds the class through
//!   `SlowRuntimeStub::CreateSharedClass`
//!   (arkcompiler_ets_runtime-master/ecmascript/interpreter/
//!   interpreter_assembly.cpp:6157-6180,
//!   `HandleCallRuntimeDefineSendableClassPrefImm16Id16Id16Imm16V8` —
//!   `ASSERT(res.IsJSSharedFunction())`), NOT the contemporary
//!   `defineclasswithbuffer`'s `SlowRuntimeStub::CreateClassWithBuffer`
//!   (interpreter_assembly.cpp:6007/6033).

use std::path::PathBuf;

use abcd_file::File;
use abcd_ir2::{FuncId, Module, Op, verify_module};
use abcd_isa::Bytecode;
use abcd_lift::lift_file;
use abcd_lower::{lower_function, to_method_body};

fn corpus_root() -> PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        })
}

/// Recursively collect every `input.abc` under `dir` (sorted).
fn collect_abc(dir: &std::path::Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .expect("corpus dir")
        .map(|e| e.expect("dir entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            collect_abc(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "abc") {
            out.push(path);
        }
    }
}

/// Count `callruntime.definesendableclass` in a decoded file's methods.
fn sendable_opcode_count(file: &File) -> usize {
    file.all_methods()
        .flat_map(|(_, m)| m.body.iter())
        .flat_map(|b| b.bytecodes.iter())
        .filter(|bc| matches!(bc, Bytecode::CallruntimeDefinesendableclass(..)))
        .count()
}

/// Count lifted `Op::DefineSendableClass` instructions in a module.
fn sendable_op_count(module: &Module) -> usize {
    (0..module.functions.len())
        .map(|i| FuncId::new(i as u32))
        .flat_map(|f| {
            module
                .func(f)
                .map(|func| {
                    func.blocks
                        .iter()
                        .filter_map(|&bb| module.block(bb))
                        .flat_map(|block| block.insts.iter().copied())
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default()
        })
        .filter(|&iid| {
            module
                .inst(iid)
                .is_some_and(|inst| matches!(inst.op, Op::DefineSendableClass { .. }))
        })
        .count()
}

#[test]
#[ignore = "requires exported GHCR corpus"]
fn sendable_class_opcode_identity_roundtrips_v2() {
    let root = corpus_root();
    let mut candidates = Vec::new();
    collect_abc(&root.join("24.0.0.0"), &mut candidates);
    candidates.retain(|p| p.to_string_lossy().contains("sendable"));
    assert!(
        !candidates.is_empty(),
        "24.0.0.0 sendable fixtures must exist in the corpus"
    );

    // The first 24.0.0.0 sendable fixture that (a) carries the opcode
    // and (b) lifts through the v0.2 pipeline. The 57-fixture
    // registered-pending set fails with LiteralArrayOutOfRange (the
    // v2-P1a file-model gap) — unrelated to N53; skip those.
    let mut used: Option<(PathBuf, File, Module, usize)> = None;
    for path in &candidates {
        let data = std::fs::read(path).expect("fixture");
        let file = abcd_file::decode(&data).expect("decode");
        let source_count = sendable_opcode_count(&file);
        if source_count == 0 {
            continue;
        }
        let module = match lift_file(&file) {
            Ok(m) => m,
            Err(abcd_lift::LiftError::LiteralArrayOutOfRange(_)) => continue,
            Err(e) => panic!("v0.2 lift {}: {e}", path.display()),
        };
        used = Some((path.clone(), file, module, source_count));
        break;
    }
    let (path, file, module, source_count) =
        used.expect("at least one 24.0.0.0 sendable fixture must lift (non-pending)");
    eprintln!("N53 fixture: {}", path.display());

    // (1) The v0.2 lift surfaces the sendable distinction, one op per
    // source opcode.
    let lifted = sendable_op_count(&module);
    assert_eq!(
        lifted,
        source_count,
        "lift must produce one Op::DefineSendableClass per source \
         callruntime.definesendableclass (fixture: {})",
        path.display()
    );
    let report = verify_module(&module);
    assert!(report.errors.is_empty(), "verify: {:?}", report.errors);

    // (2) Lower every function; the lowered stream must re-emit the
    // SENDABLE opcode (never the contemporary defineclasswithbuffer).
    let mut bodies = Vec::new();
    let mut lowered_sendable = 0usize;
    for index in 0..module.functions.len() {
        let func_id = FuncId::new(index as u32);
        let func = module.func(func_id).expect("function-table index");
        if func.blocks.is_empty() {
            bodies.push(None);
            continue;
        }
        let lowered = lower_function(&module, func_id).expect("lower");
        lowered_sendable += lowered
            .bytecodes
            .iter()
            .filter(|bc| matches!(bc, Bytecode::CallruntimeDefinesendableclass(..)))
            .count();
        bodies.push(Some(
            to_method_body(&module, func_id, &lowered, &file).expect("to_method_body"),
        ));
    }
    assert_eq!(
        lowered_sendable, source_count,
        "isel must re-emit callruntime.definesendableclass (NOT the \
         contemporary defineclasswithbuffer) for every sendable class"
    );

    // (3) Splice + encode + decode: the opcode identity survives the
    // full rewrite (structural decode check).
    let mut rebuilt = file.clone();
    let mut cursor = bodies.into_iter();
    for class in rebuilt.classes.values_mut() {
        for method in &mut class.methods {
            let body = cursor.next().expect("one slot per method");
            if method.body.is_some() {
                method.body = Some(body.expect("lowered body"));
            }
        }
    }
    let encoded = abcd_file::encode(&rebuilt).expect("encode");
    let rewritten = abcd_file::decode(&encoded).expect("decode rewritten");
    assert_eq!(
        sendable_opcode_count(&rewritten),
        source_count,
        "rewritten file must still carry callruntime.definesendableclass"
    );

    // Out-of-band ark_disasm evidence: with $ABCD_N53_REWRITE set,
    // drop the rewritten bytes for the docker toolchain's ark_disasm.
    if let Some(out) = std::env::var_os("ABCD_N53_REWRITE") {
        let out = PathBuf::from(out);
        std::fs::write(&out, &encoded).expect("write rewritten fixture");
        eprintln!("N53 rewritten fixture written to {}", out.display());
    }
}
