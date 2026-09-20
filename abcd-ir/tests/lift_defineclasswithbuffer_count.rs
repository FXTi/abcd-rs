//! N15 regression (P5-T2): `defineclasswithbuffer`'s imm2 (`_count`) must
//! round-trip — lift dropped it and isel hardcoded `Imm(0)`.
//!
//! Vendor facts:
//! - `defineclasswithbuffer imm1:u16, method_id, literalarray_id, imm2:u16,
//!   v:in:top` (abcd-isa-sys/vendor/isa/isa.yaml:1234-1238).
//! - The runtime DOES consume imm2: both modern handlers read `length` and
//!   pass it to `SlowRuntimeStub::CreateClassWithBuffer`
//!   (arkcompiler_ets_runtime-master/ecmascript/interpreter/
//!   interpreter_assembly.cpp:5990-6018), which ends in
//!   `RuntimeSetClassConstructorLength(thread, cls, length)`
//!   (ecmascript/stubs/runtime_stubs-inl.h:1037 -> :1227-1240) — imm2 is
//!   the class constructor's `.length`. (The P3-T8 "runtime ignores it"
//!   registration was wrong.)
//! - Corpus corroboration: `local/module-exports` (9.0.0.0, all profiles)
//!   carries `defineclasswithbuffer 0x1, Box:(any,any,any,any), {...}, 0x1,
//!   v6` — imm2 = 1 (reference.pa); the pre-fix rewrite emitted imm2 = 0.

use abcd_ir::entity::FuncId;
use abcd_ir::inst::InstData;
use abcd_ir::module::Module;

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

/// A hand-built `DefineClassWithBuffer` with `count = 3` must lower with
/// `imm2 = 3`, not the pre-N15 hardcoded `Imm(0)`. Not corpus-bound: runs
/// everywhere.
#[test]
fn hand_built_defineclasswithbuffer_preserves_count() {
    use abcd_file::{FileType, FunctionKind, Version};
    use abcd_ir::builder::IRBuilder;
    use abcd_ir::lower::isel;
    use abcd_ir::lower::regalloc::{self, RegAlloc, RegSlot};
    use abcd_ir::types::IrType;
    use abcd_isa::{Bytecode, EntityId, Reg};
    use std::collections::HashMap;

    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let name = module.strings.intern("C");

    let (base, result);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        base = builder.emit_val(InstData::LiteralUndefined, IrType::default());
        result = builder.emit_val(
            InstData::DefineClassWithBuffer {
                method_id: name,
                method_offset: 0x1234,
                literal_array: 0,
                count: 3,
                base,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return {
            value: Some(result),
        });
    }

    let alloc = RegAlloc {
        allocation: HashMap::from([(base, RegSlot::Reg(0)), (result, RegSlot::Reg(1))]),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 2,
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
    let counts: Vec<i64> = codes
        .iter()
        .filter_map(|bc| match bc {
            Bytecode::Defineclasswithbuffer(_, _, _, count, _) => Some(count.0),
            _ => None,
        })
        .collect();
    assert_eq!(
        counts,
        vec![3],
        "the lowered defineclasswithbuffer must carry the modeled imm2, got {codes:?}"
    );
    // Sanity: the base operand keeps its register.
    assert!(
        codes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Defineclasswithbuffer(_, _, _, _, Reg(0)))),
        "base operand must be v0, got {codes:?}"
    );
}

/// Lift+lower of the corpus fixture carrying imm2 = 1: the lifted InstData
/// must carry `count = 1` and the lowered bytecode must re-emit imm2 = 1.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn corpus_defineclasswithbuffer_count_roundtrips() {
    use abcd_ir::lift::lift_file;
    use abcd_ir::lower::lower_function;
    use abcd_ir::verify::verify_module;
    use abcd_isa::Bytecode;

    let data = std::fs::read(corpus_root().join("9.0.0.0/local/module-exports/baseline/input.abc"))
        .expect("module-exports fixture");
    let file = abcd_file::decode(&data).expect("decode");
    // The fixture must actually exercise nonzero imm2 (guard against fixture
    // drift making this test vacuous).
    let src_counts: Vec<i64> = file
        .all_methods()
        .flat_map(|(_, m)| m.body.iter())
        .flat_map(|b| b.bytecodes.iter())
        .filter_map(|bc| match bc {
            Bytecode::Defineclasswithbuffer(_, _, _, count, _) => Some(count.0),
            _ => None,
        })
        .collect();
    assert!(
        src_counts.iter().any(|&c| c != 0),
        "fixture must carry a nonzero imm2, got {src_counts:?}"
    );

    let module = lift_file(&file).expect("lift module-exports");
    assert!(verify_module(&module).is_empty());

    let lifted: Vec<u16> = (0..module.functions.len())
        .map(FuncId::from_index)
        .flat_map(|f| module.func(f).blocks.iter().copied().collect::<Vec<_>>())
        .flat_map(|bb| module.block(bb).insts.iter().copied().collect::<Vec<_>>())
        .filter_map(|id| match &module.inst(id).data {
            InstData::DefineClassWithBuffer { count, .. } => Some(*count),
            _ => None,
        })
        .collect();
    assert!(
        lifted.iter().any(|&c| c != 0),
        "lift must preserve a nonzero imm2, got {lifted:?} (source: {src_counts:?})"
    );

    let mut lowered_counts = Vec::new();
    for f in 0..module.functions.len() {
        let func = FuncId::from_index(f);
        let Ok(result) = lower_function(&module, func) else {
            continue;
        };
        lowered_counts.extend(result.bytecodes.iter().filter_map(|bc| match bc {
            Bytecode::Defineclasswithbuffer(_, _, _, count, _) => Some(count.0),
            _ => None,
        }));
    }
    assert!(
        lowered_counts.iter().any(|&c| c != 0),
        "lowered stream must keep a nonzero imm2, got {lowered_counts:?}"
    );
}
