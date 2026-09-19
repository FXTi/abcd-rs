//! N14 regression (P3-T15): the generator trio's acc operands and
//! getresumemode must be modeled, not dropped/merged.
//!
//! Vendor facts (abcd-isa-sys/vendor/isa/isa.yaml):
//! - `resumegenerator` (0xbf, isa.yaml:1261-1264): `acc: inout:top`, NO
//!   register operand — the generator object is read from acc, the resume
//!   result is written back to acc.
//! - `getresumemode` (0xc0, isa.yaml:1270-1273): `acc: inout:top`, NO
//!   register operand — genobj from acc, resume mode (a number) to acc.
//! - `suspendgenerator v:in:top` (0xc3, isa.yaml:1302-1305): the register
//!   operand is the generator object and the ACC carries the YIELD VALUE
//!   (`acc: inout:top`; after resume the acc holds the resume result).
//!
//! Corpus corroboration
//! (exports/corpus/9.0.0.0/local/generator/baseline/reference.pa:88-96):
//!
//! ```text
//! creategeneratorobj v0
//! sta v3                      # v3 = genobj
//! ldundefined                 # acc = YIELD VALUE
//! suspendgenerator v3         # reg = genobj, acc = yield value
//! lda v3                      # acc = genobj
//! resumegenerator             # acc = resume result
//! sta v5
//! lda v3                      # acc = genobj
//! getresumemode               # acc = resume mode
//! sta v4
//! ```
//!
//! Pre-N14 the lift mapped `getresumemode` to `InstData::ResumeGenerator`
//! ("model as ResumeGenerator") and dropped every acc operand of the
//! trio, so the lowered stream emitted `resumegenerator` where the source
//! had `getresumemode`, and `SuspendGenerator` held the genobj register
//! operand while the acc yield value had no use — DCE could delete its
//! producer (the opt-variant SIGSEGV mechanism pinned by P3-T8).

use abcd_file::decode;
use abcd_ir::analysis::inst_operands;
use abcd_ir::entity::FuncId;
use abcd_ir::inst::InstData;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::lower_function;
use abcd_ir::opt::optimize_module;
use abcd_ir::verify::verify_module;
use abcd_isa::Bytecode;

mod common;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::module::Module;
use abcd_ir::types::IrType;

use common::{Halt, Machine};

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

fn generator_fixture() -> std::path::PathBuf {
    corpus_root().join("9.0.0.0/local/generator/baseline/input.abc")
}

/// Count the trio's opcodes across every decoded method body.
fn source_trio_counts(file: &abcd_file::File) -> (usize, usize, usize) {
    let (mut suspend, mut resume, mut mode) = (0, 0, 0);
    for (_, method) in file.all_methods() {
        if let Some(body) = &method.body {
            for bc in &body.bytecodes {
                match bc {
                    Bytecode::Suspendgenerator(..) => suspend += 1,
                    Bytecode::Resumegenerator => resume += 1,
                    Bytecode::Getresumemode => mode += 1,
                    _ => {}
                }
            }
        }
    }
    (suspend, resume, mode)
}

/// (a) The lowered stream must contain `getresumemode` exactly where the
/// source had it (and the same number of `resumegenerator` /
/// `suspendgenerator`): the trio round-trips opcode-for-opcode.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn lowered_generator_fixture_preserves_getresumemode() {
    let data = std::fs::read(generator_fixture()).expect("generator fixture");
    let file = decode(&data).expect("decode generator fixture");
    let (src_suspend, src_resume, src_mode) = source_trio_counts(&file);
    assert_eq!((src_suspend, src_resume, src_mode), (3, 3, 3));

    let module = lift_file(&file).expect("lift generator fixture");
    assert!(verify_module(&module).is_empty());

    let (mut out_suspend, mut out_resume, mut out_mode) = (0, 0, 0);
    for index in 0..module.functions.len() {
        let lowered = lower_function(&module, FuncId::from_index(index))
            .expect("generator fixture must lower");
        for bc in &lowered.bytecodes {
            match bc {
                Bytecode::Suspendgenerator(..) => out_suspend += 1,
                Bytecode::Resumegenerator => out_resume += 1,
                Bytecode::Getresumemode => out_mode += 1,
                _ => {}
            }
        }
    }
    assert_eq!(
        (out_suspend, out_resume, out_mode),
        (src_suspend, src_resume, src_mode),
        "lowered stream must preserve the trio opcode-for-opcode \
         (getresumemode must not come back as resumegenerator)"
    );
}

/// (b) `SuspendGenerator` must carry BOTH vendor operands: the genobj
/// register operand AND the acc yield value. Pre-N14 it held only the
/// genobj and the yield value had no use at all.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn suspend_generator_models_genobj_and_acc_yield_value() {
    let data = std::fs::read(generator_fixture()).expect("generator fixture");
    let file = decode(&data).expect("decode generator fixture");
    let module = lift_file(&file).expect("lift generator fixture");
    assert!(verify_module(&module).is_empty());

    let mut suspends = 0usize;
    let mut undefined_yield_seen = false;
    for index in 0..module.functions.len() {
        let func = FuncId::from_index(index);
        for &bb in &module.func(func).blocks {
            for &inst_id in &module.block(bb).insts {
                let node = module.inst(inst_id);
                if let InstData::SuspendGenerator { .. } = &node.data {
                    suspends += 1;
                    let operands = inst_operands(&node.data);
                    assert_eq!(
                        operands.len(),
                        2,
                        "suspendgenerator has two inputs per vendor \
                         `suspendgenerator v:in:top, acc: inout:top` — \
                         genobj (reg) and the yield value (acc)"
                    );
                    assert_ne!(
                        operands[0], operands[1],
                        "genobj and yield value are distinct SSA values"
                    );
                    // The first suspend in `seq` yields `ldundefined`
                    // (reference.pa:90-91): its acc operand is defined by
                    // LiteralUndefined, not by the genobj producer.
                    undefined_yield_seen |= module.func(func).blocks.iter().any(|&b| {
                        module.block(b).insts.iter().any(|&id| {
                            module.inst(id).result == Some(operands[1])
                                && matches!(module.inst(id).data, InstData::LiteralUndefined)
                        })
                    });
                }
            }
        }
    }
    assert_eq!(suspends, 3, "the fixture suspends three times");
    assert!(
        undefined_yield_seen,
        "the first suspend's acc operand must be the ldundefined yield \
         value, not the genobj"
    );
}

/// (c) Opt smoke: lift → optimize → verify keeps the yield-value producer
/// alive — it now has a real use (the SuspendGenerator acc operand), so
/// DCE cannot delete it (the pre-N14 opt-variant SIGSEGV mechanism).
#[test]
#[ignore = "requires exported GHCR corpus"]
fn optimized_generator_keeps_yield_value_producer() {
    let data = std::fs::read(generator_fixture()).expect("generator fixture");
    let file = decode(&data).expect("decode generator fixture");
    let mut module = lift_file(&file).expect("lift generator fixture");
    assert!(verify_module(&module).is_empty());

    optimize_module(&mut module);
    let errors = verify_module(&module);
    assert!(errors.is_empty(), "post-optimize verify: {errors:?}");

    let mut suspends = 0usize;
    for index in 0..module.functions.len() {
        let func = FuncId::from_index(index);
        for &bb in &module.func(func).blocks {
            for &inst_id in &module.block(bb).insts {
                let node = module.inst(inst_id);
                if let InstData::SuspendGenerator { .. } = &node.data {
                    suspends += 1;
                    let operands = inst_operands(&node.data);
                    assert_eq!(
                        operands.len(),
                        2,
                        "post-optimize suspendgenerator still carries genobj \
                         and the acc yield value"
                    );
                }
            }
        }
    }
    assert_eq!(
        suspends, 3,
        "DCE must keep all three side-effecting suspend points"
    );
}

// ─── Synthetic simulator tests (no corpus required) ────────────────────

const GEN: i64 = 0x6e67;

/// `f(genobj) { return suspendgenerator(genobj, 42) }` — the single
/// parameter arrives in the ABI top slot Reg(num_regs).
fn build_suspend() -> (Module, FuncId) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "gen", FunctionKind::Function, 1);
    let mut builder = IRBuilder::new(&mut module, func);
    let genobj = builder.create_func_param(0, IrType::default());
    let value = builder.emit_val(InstData::LiteralNumber(42.0), IrType::default());
    let resumed = builder.emit_val(
        InstData::SuspendGenerator { genobj, value },
        IrType::default(),
    );
    builder.emit_void(InstData::Return {
        value: Some(resumed),
    });
    (module, func)
}

/// (d) Vendor `suspendgenerator v:in:top, acc: inout:top`: the lowered
/// instruction takes the genobj as its register operand while the acc
/// holds the yield value. The simulator records both at the opcode.
#[test]
fn suspend_lowers_genobj_register_operand_and_acc_yield_value() {
    let (module, func) = build_suspend();
    let result = lower_function(&module, func).expect("suspend must lower");
    abcd_isa::encode(&result.bytecodes).expect("suspend must encode");

    let mut machine = Machine::new().with_reg(result.num_regs, GEN);
    let halt = machine.run(&result.bytecodes);
    let Halt::SuspendGenerator { genobj, value } = halt else {
        panic!(
            "expected execution to stop at suspendgenerator, got {halt:?} \
             (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(
        genobj, GEN,
        "the register operand is the generator object (bytecodes: {:?})",
        result.bytecodes
    );
    assert_eq!(
        value, 42,
        "the acc carries the yield value (bytecodes: {:?})",
        result.bytecodes
    );
}

/// `f(genobj) { return resumegenerator(genobj) }`.
fn build_resume() -> (Module, FuncId) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "gen", FunctionKind::Function, 1);
    let mut builder = IRBuilder::new(&mut module, func);
    let genobj = builder.create_func_param(0, IrType::default());
    let resumed = builder.emit_val(InstData::ResumeGenerator { genobj }, IrType::default());
    builder.emit_void(InstData::Return {
        value: Some(resumed),
    });
    (module, func)
}

/// (e) Vendor `resumegenerator` has NO register operand: the genobj is
/// read from the acc (`acc: inout:top`). The lowered stream must be the
/// bare opcode with the genobj Lda'd into acc first.
#[test]
fn resume_lowers_genobj_through_acc_with_no_register_operand() {
    let (module, func) = build_resume();
    let result = lower_function(&module, func).expect("resume must lower");
    abcd_isa::encode(&result.bytecodes).expect("resume must encode");

    let mut machine = Machine::new().with_reg(result.num_regs, GEN);
    let halt = machine.run(&result.bytecodes);
    let Halt::ResumeGenerator { genobj } = halt else {
        panic!(
            "expected execution to stop at resumegenerator, got {halt:?} \
             (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(
        genobj, GEN,
        "resumegenerator reads the genobj from the acc (bytecodes: {:?})",
        result.bytecodes
    );
}

/// `f(genobj) { return getresumemode(genobj) }`.
fn build_mode() -> (Module, FuncId) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "gen", FunctionKind::Function, 1);
    let mut builder = IRBuilder::new(&mut module, func);
    let genobj = builder.create_func_param(0, IrType::default());
    let mode = builder.emit_val(InstData::GetResumeMode { genobj }, IrType::default());
    builder.emit_void(InstData::Return { value: Some(mode) });
    (module, func)
}

/// (f) GetResumeMode lowers to `getresumemode` — never `resumegenerator`
/// (the pre-N14 mis-lift) — with the genobj in acc.
#[test]
fn getresumemode_lowers_to_getresumemode_not_resumegenerator() {
    let (module, func) = build_mode();
    let result = lower_function(&module, func).expect("getresumemode must lower");
    abcd_isa::encode(&result.bytecodes).expect("getresumemode must encode");

    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Getresumemode)),
        "GetResumeMode must lower to getresumemode (bytecodes: {:?})",
        result.bytecodes
    );
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Resumegenerator)),
        "GetResumeMode must never lower to resumegenerator (bytecodes: {:?})",
        result.bytecodes
    );

    let mut machine = Machine::new().with_reg(result.num_regs, GEN);
    let halt = machine.run(&result.bytecodes);
    let Halt::GetResumeMode { genobj } = halt else {
        panic!(
            "expected execution to stop at getresumemode, got {halt:?} \
             (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(
        genobj, GEN,
        "getresumemode reads the genobj from the acc (bytecodes: {:?})",
        result.bytecodes
    );
}

/// (g) Opt smoke: suspend AND resume are side-effecting (essential), so
/// DCE keeps them even with unused results, and the yield-value producer
/// keeps its real use — the pre-N14 SIGSEGV mechanism (DCE deletes the
/// yield-value producer) is closed. GetResumeMode is a pure read and MAY
/// be folded away when unused; only verify cleanliness is asserted for
/// it.
#[test]
fn generator_trio_survives_optimize_and_verify() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "gen", FunctionKind::Function, 1);
    let (genobj, suspended);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        genobj = builder.create_func_param(0, IrType::default());
        let value = builder.emit_val(InstData::LiteralNumber(7.0), IrType::default());
        suspended = builder.emit_val(
            InstData::SuspendGenerator { genobj, value },
            IrType::default(),
        );
        // Unused results: DCE may only drop the pure GetResumeMode.
        builder.emit_val(InstData::ResumeGenerator { genobj }, IrType::default());
        builder.emit_val(InstData::GetResumeMode { genobj }, IrType::default());
        builder.emit_void(InstData::Return {
            value: Some(suspended),
        });
    }
    assert!(verify_module(&module).is_empty());

    optimize_module(&mut module);
    let errors = verify_module(&module);
    assert!(errors.is_empty(), "post-optimize verify: {errors:?}");

    let mut suspends = 0usize;
    let mut resumes = 0usize;
    let mut literals = 0usize;
    for &bb in &module.func(func).blocks {
        for &inst_id in &module.block(bb).insts {
            let node = module.inst(inst_id);
            match &node.data {
                InstData::SuspendGenerator { .. } => {
                    suspends += 1;
                    assert_eq!(
                        inst_operands(&node.data).len(),
                        2,
                        "post-optimize suspendgenerator keeps genobj + yield value"
                    );
                }
                InstData::ResumeGenerator { .. } => resumes += 1,
                InstData::LiteralNumber(n) if *n == 7.0 => literals += 1,
                _ => {}
            }
        }
    }
    assert_eq!(suspends, 1, "DCE must keep the side-effecting suspend");
    assert_eq!(
        resumes, 1,
        "DCE must keep the side-effecting resume even with an unused result"
    );
    assert_eq!(
        literals, 1,
        "the yield-value producer has a real use and must not be DCE'd"
    );
    let _ = genobj;
    let _ = suspended;

    let result = lower_function(&module, func).expect("optimized trio must lower");
    let mut machine = Machine::new().with_reg(result.num_regs, GEN);
    let halt = machine.run(&result.bytecodes);
    assert!(
        matches!(
            halt,
            Halt::SuspendGenerator {
                genobj: GEN,
                value: 7
            }
        ),
        "the optimized suspend still records genobj + yield value, got {halt:?} \
         (bytecodes: {:?})",
        result.bytecodes
    );
}
