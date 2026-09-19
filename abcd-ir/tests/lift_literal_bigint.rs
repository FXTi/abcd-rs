//! N35 regression (P3-T21): `ldbigint` must round-trip as a BIGINT
//! literal, not collapse into a string literal.
//!
//! Vendor facts:
//! - `ldbigint string_id` (abcd-isa-sys/vendor/isa/isa.yaml:1622-1626):
//!   `acc: out:top`, format `op_id_16`, properties `[string_id]`. The
//!   runtime handler builds a BigInt from the constant-pool entry
//!   (`SlowRuntimeStub::LdBigInt`, arkcompiler_ets_runtime-master/
//!   ecmascript/interpreter/interpreter_assembly.cpp:2915-2930) — NOT a
//!   string.
//! - Corpus corroboration
//!   (exports/corpus/9.0.0.0/local/bigint/baseline/reference.pa:24,26):
//!   `ldbigint "123"` / `ldbigint "2"`.
//!
//! Pre-N35 the lift mapped `Bytecode::Ldbigint` to
//! `InstData::LiteralString` (translate.rs's arm was a copy of the
//! `LdaStr` arm), so the lowered stream emitted `lda.str` where the
//! source had `ldbigint` — the VM saw a String where the program needed
//! a BigInt (bigint×18 VM failures).

use abcd_file::decode;
use abcd_ir::entity::FuncId;
use abcd_ir::inst::InstData;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::lower_function;
use abcd_ir::verify::verify_module;
use abcd_isa::Bytecode;

fn corpus_root() -> std::path::PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        })
}

fn bigint_fixture() -> std::path::PathBuf {
    corpus_root().join("9.0.0.0/local/bigint/baseline/input.abc")
}

/// The lowered stream must contain `ldbigint` exactly as many times as
/// the source (opcode-for-opcode round-trip). Pre-N35 the count was 0:
/// every `ldbigint` came back as `lda.str`.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn lowered_bigint_fixture_preserves_ldbigint() {
    let data = std::fs::read(bigint_fixture()).expect("bigint fixture");
    let file = decode(&data).expect("decode bigint fixture");
    let mut src_ldbigint = 0usize;
    let mut src_ldastr = 0usize;
    for (_, method) in file.all_methods() {
        if let Some(body) = &method.body {
            for bc in &body.bytecodes {
                match bc {
                    Bytecode::Ldbigint(..) => src_ldbigint += 1,
                    Bytecode::LdaStr(..) => src_ldastr += 1,
                    _ => {}
                }
            }
        }
    }
    assert!(src_ldbigint > 0, "fixture must exercise ldbigint");

    let module = lift_file(&file).expect("lift bigint fixture");
    assert!(verify_module(&module).is_empty());

    let (mut out_ldbigint, mut out_ldastr) = (0usize, 0usize);
    for index in 0..module.functions.len() {
        let lowered =
            lower_function(&module, FuncId::from_index(index)).expect("bigint fixture must lower");
        for bc in &lowered.bytecodes {
            match bc {
                Bytecode::Ldbigint(..) => out_ldbigint += 1,
                Bytecode::LdaStr(..) => out_ldastr += 1,
                _ => {}
            }
        }
    }
    assert_eq!(
        out_ldbigint, src_ldbigint,
        "every source ldbigint must lower back to ldbigint (not lda.str)"
    );
    assert_eq!(
        out_ldastr, src_ldastr,
        "no extra lda.str may appear from collapsed bigint literals"
    );
}

/// Lift must model `ldbigint` as a BIGINT literal carrying the decimal
/// string ("123", "2"), never as `LiteralString`.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn lifted_bigint_is_a_bigint_literal_not_a_string() {
    let data = std::fs::read(bigint_fixture()).expect("bigint fixture");
    let file = decode(&data).expect("decode bigint fixture");
    let module = lift_file(&file).expect("lift bigint fixture");

    let mut bigints: Vec<String> = Vec::new();
    for index in 0..module.functions.len() {
        let func = module.func(FuncId::from_index(index));
        for &bb in &func.blocks {
            let block = module.block(bb);
            for &inst_id in block.phis.iter().chain(block.insts.iter()) {
                if let InstData::LiteralBigInt(s) = &module.inst(inst_id).data {
                    bigints.push(module.strings.get(*s).to_string());
                }
            }
        }
    }
    assert!(
        bigints.iter().any(|s| s == "123") && bigints.iter().any(|s| s == "2"),
        "lift must produce LiteralBigInt for the fixture's ldbigint \
         (got {bigints:?})"
    );
}

/// A hand-built `LiteralBigInt` lowers to `Bytecode::Ldbigint` on the
/// same entity channel as `LiteralString` (StringId constant-pool
/// operand), never to `LdaStr`. Not corpus-bound: runs everywhere.
#[test]
fn hand_built_bigint_literal_lowers_to_ldbigint() {
    use abcd_file::{FileType, FunctionKind, Version};
    use abcd_ir::builder::IRBuilder;
    use abcd_ir::lower::isel;
    use abcd_ir::lower::regalloc::{self, RegAlloc, RegSlot};
    use abcd_ir::module::Module;
    use abcd_ir::types::IrType;
    use abcd_isa::{EntityId, Reg};
    use std::collections::HashMap;

    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let sid = module.strings.intern("9007199254740993");

    let bigint;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        bigint = builder.emit_val(InstData::LiteralBigInt(sid), IrType::default());
        builder.emit_void(InstData::Return {
            value: Some(bigint),
        });
    }

    let alloc = RegAlloc {
        allocation: HashMap::from([(bigint, RegSlot::Reg(0))]),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 1,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    };
    let rpo = regalloc::compute_rpo(&module, func);
    let string_map: HashMap<abcd_ir::entity::StringId, EntityId> = HashMap::new();
    let result = isel::select(&module, func, &alloc, &rpo, &string_map)
        .expect("selection must succeed for a consistent allocation");

    assert_eq!(result.unsupported, None);
    let (_, codes) = &result.block_codes[0];
    assert!(
        matches!(codes.first(), Some(Bytecode::Ldbigint(_))),
        "LiteralBigInt must emit ldbigint, got {codes:?}"
    );
    // The result has a use (Return) → homed with Sta(R0) per `acc: out`.
    assert!(
        matches!(codes.get(1), Some(Bytecode::Sta(Reg(0)))),
        "the bigint result must be homed after ldbigint, got {codes:?}"
    );
    assert!(
        !codes.iter().any(|bc| matches!(bc, Bytecode::LdaStr(_))),
        "a bigint literal must never come back as lda.str, got {codes:?}"
    );
}
