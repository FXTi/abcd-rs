//! N25 regression (P4-T1): `throw.constassignment` must carry the
//! variable NAME as the SSA VALUE held by its register operand, not a
//! fabricated synthetic string.
//!
//! Vendor facts:
//! - `throw.constassignment v:in:top`, `acc: none`
//!   (abcd-isa-sys/vendor/isa/isa.yaml:987-991, opcode_idx 0x04, format
//!   `pref_op_v_8`): the register operand holds the variable name AS A
//!   STRING VALUE produced at runtime (es2abc emits `lda.str <name>;
//!   sta vX; throw.constassignment vX`); the VM reads the name from the
//!   register to build the TypeError message
//!   (`RuntimeStubs::RuntimeThrowConstAssignment`).
//! - The instruction does NOT read or write the accumulator.
//!
//! Pre-N25 the lift read the register but discarded the value and
//! fabricated a synthetic name `const_assign_N` (an S3-class untraceable
//! synthetic string), and the Phase-1 unsupported marker rejected every
//! function containing the instruction outright
//! (`LowerError::UnsupportedInstruction`, isel.rs "throw const
//! assignment"); the stale fallback arm behind it hardcoded `Reg(0)`.

mod common;

use abcd_file::{AccessFlags, Builder, File, FileType, FunctionKind, Type, Version};
use abcd_ir::analysis::inst_operands;
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::FuncId;
use abcd_ir::inst::InstData;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::lower_function;
use abcd_ir::module::{Module, ValueDef};
use abcd_ir::opt::optimize_module;
use abcd_ir::types::IrType;
use abcd_ir::verify::verify_module;
use abcd_isa::{Bytecode, Imm, Reg, encode as encode_bytecodes};

use common::{Halt, Machine};

/// Sentinel standing in for the name string value (the i64 simulator has
/// no tagged strings; a real source carries `lda.str`'s result).
const NAME: i64 = 0x4e41;

/// Build a 12.x file whose global class carries one static method `f`
/// with the given code-header frame and raw bytecodes.
fn build_file(bytecodes: &[Bytecode], num_vregs: u32, num_args: u32) -> File {
    let mut builder = Builder::new();
    builder.set_api(12, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(bytecodes).unwrap();
    builder.class_add_method(
        class,
        "f",
        proto,
        AccessFlags::STATIC,
        &code,
        num_vregs,
        num_args,
    );
    builder.deduplicate();
    abcd_file::decode(&builder.finalize().unwrap()).unwrap()
}

fn func_by_name(module: &Module, name: &str) -> FuncId {
    (0..module.functions.len())
        .map(FuncId::from_index)
        .find(|&f| module.strings.get(module.func(f).name) == name)
        .unwrap_or_else(|| panic!("function {name}"))
}

/// (a) Synthetic lift: `ldai NAME; sta v1; throw.constassignment v1;
/// return.undefined`. The instruction's single SSA operand must be the
/// VALUE stored into v1 (the name string value), not a fabricated
/// synthetic StringId.
#[test]
fn lift_models_name_as_the_register_value() {
    let file = build_file(
        &[
            Bytecode::Ldai(Imm(NAME)),
            Bytecode::Sta(Reg(1)),
            Bytecode::ThrowConstassignment(Reg(1)),
            Bytecode::Returnundefined,
        ],
        2,
        0,
    );
    let module = lift_file(&file).expect("lift synthetic throw.constassignment");
    assert!(verify_module(&module).is_empty());
    let func = func_by_name(&module, "f");

    let mut operands = Vec::new();
    for &bb in &module.func(func).blocks {
        for &id in &module.block(bb).insts {
            let node = module.inst(id);
            if matches!(node.data, InstData::ThrowConstAssignment { .. }) {
                operands.extend(inst_operands(&node.data));
            }
        }
    }
    assert_eq!(
        operands.len(),
        1,
        "vendor `throw.constassignment v:in:top` (acc: none) has exactly \
         one SSA input: the name VALUE in the register operand"
    );
    let ValueDef::Inst(def_inst) = module.value(operands[0]).def else {
        panic!("the name operand must be defined by an instruction")
    };
    assert!(
        matches!(
            module.inst(def_inst).data,
            InstData::LiteralNumber(n) if n == NAME as f64
        ),
        "the name operand must be the value `sta v1` wrote (the ldai \
         sentinel standing in for the name string) — got {:?}",
        module.inst(def_inst).data
    );
}

/// (b) Round-trip: the lowered stream must carry `throw.constassignment`
/// with the REAL name register (mov-filled from the name value's home),
/// never a hardcoded Reg(0) and never an UnsupportedInstruction error.
#[test]
fn lowered_const_assignment_reads_the_name_register() {
    let file = build_file(
        &[
            Bytecode::Ldai(Imm(NAME)),
            Bytecode::Sta(Reg(1)),
            Bytecode::ThrowConstassignment(Reg(1)),
            Bytecode::Returnundefined,
        ],
        2,
        0,
    );
    let module = lift_file(&file).expect("lift synthetic throw.constassignment");
    let func = func_by_name(&module, "f");
    let result = lower_function(&module, func)
        .expect("vendor-supported throw.constassignment must lower (no unsupported marker)");
    abcd_isa::encode(&result.bytecodes).expect("throw.constassignment must encode");

    let throws: Vec<u16> = result
        .bytecodes
        .iter()
        .filter_map(|bc| match bc {
            Bytecode::ThrowConstassignment(r) => Some(r.0),
            _ => None,
        })
        .collect();
    assert_eq!(
        throws.len(),
        1,
        "exactly one throw.constassignment must be emitted (bytecodes: {:?})",
        result.bytecodes
    );

    let mut machine = Machine::new();
    let halt = machine.run(&result.bytecodes);
    let Halt::ThrowConstAssignment { name } = halt else {
        panic!(
            "expected execution to stop at throw.constassignment, got \
             {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(
        name, NAME,
        "the register operand must hold the name VALUE, not the pre-N25 \
         hardcoded Reg(0) (bytecodes: {:?})",
        result.bytecodes
    );
}

/// `f(name) { throw.constassignment v(name); return.undefined }` — the
/// name arrives as the single parameter (ABI top slot).
fn build_const_assignment() -> (Module, FuncId) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 1);
    let mut builder = IRBuilder::new(&mut module, func);
    let name = builder.create_func_param(0, IrType::default());
    builder.emit_void(InstData::ThrowConstAssignment { name });
    builder.emit_void(InstData::Return { value: None });
    (module, func)
}

/// (c) Opt smoke: the throw is essential (DCE keeps it), its name operand
/// is a real use (the producer cannot be deleted), and the instruction
/// survives optimize → verify → lower with the name intact.
#[test]
fn const_assignment_survives_optimize_and_verify() {
    let (mut module, func) = build_const_assignment();
    assert!(verify_module(&module).is_empty());

    optimize_module(&mut module);
    let errors = verify_module(&module);
    assert!(errors.is_empty(), "post-optimize verify: {errors:?}");

    let count = module
        .func(func)
        .blocks
        .iter()
        .flat_map(|&bb| module.block(bb).insts.iter())
        .filter(|&&id| matches!(module.inst(id).data, InstData::ThrowConstAssignment { .. }))
        .count();
    assert_eq!(count, 1, "DCE must keep the throwing instruction");

    let result = lower_function(&module, func).expect("optimized throw must lower");
    let mut machine = Machine::new().with_reg(result.num_regs, NAME);
    let halt = machine.run(&result.bytecodes);
    let Halt::ThrowConstAssignment { name } = halt else {
        panic!(
            "expected execution to stop at throw.constassignment, got \
             {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(name, NAME, "the parameter name value must reach the VM");
}
