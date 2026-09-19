//! N26 regression (P4-T1): the TWO-REGISTER form
//! `throw.undefinedifhole v1, v2` must round-trip as that opcode — not as
//! the DIFFERENT `throw.undefinedifholewithname` (string_id + acc).
//!
//! Vendor facts:
//! - `throw.undefinedifhole v1:in:top, v2:in:top`, `acc: none`,
//!   `properties: [conditional_throw]` (abcd-isa-sys/vendor/isa/isa.yaml
//!   :998-1002, opcode_idx 0x06, format `pref_op_v1_8_v2_8`): v1 holds the
//!   variable name AS A RUNTIME STRING VALUE, v2 the value being
//!   hole-checked; the accumulator is untouched.
//! - `throw.undefinedifholewithname string_id`, `acc: in:top`
//!   (isa.yaml:1010-1015, opcode_idx 0x09, format `pref_op_id_16`,
//!   properties `[string_id, conditional_throw]`) is a DIFFERENT
//!   instruction: the name is a compile-time string constant and the
//!   checked value rides the accumulator.
//!
//! Pre-N26 the lift of the two-register form fabricated a synthetic name
//! `hole_check_N` and dropped the v1 value, and isel re-emitted EVERY
//! `ThrowUndefinedIfHole` as `throw.undefinedifholewithname` — the
//! round-trip silently swapped the register form for the acc form (the
//! N14 getresumemode class of opcode-identity corruption).

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

/// Sentinels for the name string value (v1) and the checked value (v2).
const NAME: i64 = 0x4e41;
const VALUE: i64 = 0x7a1;

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

/// The source sequence for the two-register form: name into v1, value
/// into v2, then `throw.undefinedifhole v1, v2`.
fn two_reg_source() -> Vec<Bytecode> {
    vec![
        Bytecode::Ldai(Imm(NAME)),
        Bytecode::Sta(Reg(1)),
        Bytecode::Ldai(Imm(VALUE)),
        Bytecode::Sta(Reg(2)),
        Bytecode::ThrowUndefinedifhole(Reg(1), Reg(2)),
        Bytecode::Returnundefined,
    ]
}

/// (a) Synthetic lift: the instruction's SSA operands must be BOTH
/// register values — v1 (the name VALUE) first, v2 (the checked value)
/// second, in vendor operand order.
#[test]
fn lift_models_both_register_operands() {
    let file = build_file(&two_reg_source(), 3, 0);
    let module = lift_file(&file).expect("lift synthetic throw.undefinedifhole");
    assert!(verify_module(&module).is_empty());
    let func = func_by_name(&module, "f");

    let mut operands = Vec::new();
    for &bb in &module.func(func).blocks {
        for &id in &module.block(bb).insts {
            let node = module.inst(id);
            if matches!(node.data, InstData::ThrowUndefinedIfHole { .. }) {
                operands.extend(inst_operands(&node.data));
            }
        }
    }
    assert_eq!(
        operands.len(),
        2,
        "vendor `throw.undefinedifhole v1:in:top, v2:in:top` (acc: none) \
         has exactly two SSA inputs: the name value (v1) and the checked \
         value (v2)"
    );
    for (operand, sentinel, what) in [(operands[0], NAME, "name"), (operands[1], VALUE, "value")] {
        let ValueDef::Inst(def_inst) = module.value(operand).def else {
            panic!("the {what} operand must be defined by an instruction")
        };
        assert!(
            matches!(
                module.inst(def_inst).data,
                InstData::LiteralNumber(n) if n == sentinel as f64
            ),
            "the {what} operand must be the value stored into its source \
             register — got {:?}",
            module.inst(def_inst).data
        );
    }
}

/// (b) Round-trip: the lowered stream must carry the two-register
/// `throw.undefinedifhole v1, v2` — NEVER the string_id+acc
/// `throw.undefinedifholewithname` (a different opcode).
#[test]
fn lowered_hole_check_keeps_the_two_register_opcode() {
    let file = build_file(&two_reg_source(), 3, 0);
    let module = lift_file(&file).expect("lift synthetic throw.undefinedifhole");
    let func = func_by_name(&module, "f");
    let result = lower_function(&module, func).expect("throw.undefinedifhole must lower");
    abcd_isa::encode(&result.bytecodes).expect("throw.undefinedifhole must encode");

    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::ThrowUndefinedifholewithname(_))),
        "the two-register source must NOT come back as the string_id+acc \
         withname opcode (bytecodes: {:?})",
        result.bytecodes
    );

    let mut machine = Machine::new();
    let halt = machine.run(&result.bytecodes);
    let Halt::ThrowUndefinedIfHole { name, value } = halt else {
        panic!(
            "expected execution to stop at throw.undefinedifhole, got \
             {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(name, NAME, "v1 must hold the name VALUE");
    assert_eq!(value, VALUE, "v2 must hold the checked value");
}

/// `f(name, value) { throw.undefinedifhole v(name), v(value);
/// return.undefined }` via IRBuilder — both operands are parameters.
fn build_two_reg() -> (Module, FuncId) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 2);
    let mut builder = IRBuilder::new(&mut module, func);
    let name = builder.create_func_param(0, IrType::default());
    let value = builder.create_func_param(1, IrType::default());
    builder.emit_void(InstData::ThrowUndefinedIfHole { name, value });
    builder.emit_void(InstData::Return { value: None });
    (module, func)
}

/// (c) Opt smoke: the two-register throw is essential, BOTH operands are
/// real uses, and the instruction survives optimize → verify → lower with
/// name and value intact.
#[test]
fn two_reg_form_survives_optimize_and_verify() {
    let (mut module, func) = build_two_reg();
    assert!(verify_module(&module).is_empty());

    optimize_module(&mut module);
    let errors = verify_module(&module);
    assert!(errors.is_empty(), "post-optimize verify: {errors:?}");

    let count = module
        .func(func)
        .blocks
        .iter()
        .flat_map(|&bb| module.block(bb).insts.iter())
        .filter(|&&id| matches!(module.inst(id).data, InstData::ThrowUndefinedIfHole { .. }))
        .count();
    assert_eq!(count, 1, "DCE must keep the throwing instruction");

    let result = lower_function(&module, func).expect("optimized throw must lower");
    let mut machine = Machine::new()
        .with_reg(result.num_regs, NAME)
        .with_reg(result.num_regs + 1, VALUE);
    let halt = machine.run(&result.bytecodes);
    let Halt::ThrowUndefinedIfHole { name, value } = halt else {
        panic!(
            "expected execution to stop at throw.undefinedifhole, got \
             {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(name, NAME);
    assert_eq!(value, VALUE);
}

/// (d) The withname form (string_id + acc) is a DIFFERENT instruction
/// that keeps its own lowering path: a hand-built
/// `ThrowUndefinedIfHoleWithName` lowers to
/// `throw.undefinedifholewithname` with the name's entity id and the
/// checked value in the acc — never to the two-register form.
#[test]
fn withname_form_lowers_to_withname_with_acc_value() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 1);
    let mut builder = IRBuilder::new(&mut module, func);
    let value = builder.create_func_param(0, IrType::default());
    let name = builder.intern("x");
    builder.emit_void(InstData::ThrowUndefinedIfHoleWithName { name, value });
    builder.emit_void(InstData::Return { value: None });
    assert!(verify_module(&module).is_empty());

    let result = lower_function(&module, func).expect("withname must lower");
    abcd_isa::encode(&result.bytecodes).expect("withname must encode");

    let ids: Vec<u32> = result
        .bytecodes
        .iter()
        .filter_map(|bc| match bc {
            Bytecode::ThrowUndefinedifholewithname(eid) => Some(eid.0),
            _ => None,
        })
        .collect();
    assert_eq!(
        ids.len(),
        1,
        "exactly one throw.undefinedifholewithname must be emitted \
         (bytecodes: {:?})",
        result.bytecodes
    );
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::ThrowUndefinedifhole(..))),
        "a withname source must never come back as the two-register \
         opcode (bytecodes: {:?})",
        result.bytecodes
    );

    let mut machine = Machine::new().with_reg(result.num_regs, VALUE);
    let halt = machine.run(&result.bytecodes);
    let Halt::ThrowUndefinedIfHoleWithName { value: seen } = halt else {
        panic!(
            "expected execution to stop at throw.undefinedifholewithname, \
             got {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(seen, VALUE, "the acc must hold the checked value");
}
