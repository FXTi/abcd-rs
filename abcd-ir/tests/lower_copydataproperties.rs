//! S3 regression: `InstData::CopyDataProperties` lowering and optimizer
//! treatment.
//!
//! Operand roles follow the vendor signature `copydataproperties v:in:top,
//! acc: inout:top` (abcd-isa-sys/vendor/isa/isa.yaml): the register operand
//! is the TARGET object, the accumulator carries the SOURCE and receives
//! the result. The simulator halts at the `Copydataproperties` instruction
//! (record-and-stop), so the test asserts exactly which value sits in which
//! slot at that point.

mod common;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::inst::InstData;
use abcd_ir::lower::lower_function;
use abcd_ir::module::Module;
use abcd_ir::opt::optimize_module;
use abcd_ir::types::IrType;
use abcd_ir::verify::verify_module;
use abcd_isa::Bytecode;

use common::{Halt, Machine};

const DST: i64 = 111; // target object sentinel
const SRC: i64 = 222; // source object sentinel

/// Build a two-parameter function `f(dst, src)` whose body is a single
/// `CopyDataProperties { dst, src }` followed by `return undefined`.
/// Parameters are pre-assigned register homes R0/R1, so the lowered body
/// is deterministic: copy-in prologue, `Lda R1`, `Copydataproperties(R0)`.
fn build_spread_function() -> (Module, abcd_ir::entity::FuncId) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "spread", FunctionKind::Function, 2);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let dst = builder.create_func_param(0, IrType::default());
        let src = builder.create_func_param(1, IrType::default());
        builder.emit_void(InstData::CopyDataProperties { dst, src });
        builder.emit_void(InstData::Return { value: None });
    }
    (module, func)
}

/// End-to-end through `lower_function`: the target must reach the register
/// operand and the source the accumulator, in spill-before-load order.
#[test]
fn copydataproperties_lowers_with_dst_in_register_and_src_in_acc() {
    let (module, func) = build_spread_function();

    let result = lower_function(&module, func).expect("spread must lower");

    // The opcode is the modern real one; no entity operands are involved.
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Copydataproperties(_))),
        "lowered body must contain Copydataproperties, got {:?}",
        result.bytecodes
    );
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Stobjbyname(..))),
        "no Stobjbyname impersonation, got {:?}",
        result.bytecodes
    );

    // Simulate with the ABI frame layout: num_regs = 2 (both params
    // Reg-colored, no spill slot needed), so the arguments arrive in the
    // top slots v2/v3 and the copy-in prologue moves them into R0/R1.
    assert_eq!(
        result.num_regs, 2,
        "expected exactly the two parameter homes, got {} (bytecodes: {:?})",
        result.num_regs, result.bytecodes
    );
    let mut machine = Machine::new().with_reg(2, DST).with_reg(3, SRC);
    let halt = machine.run(&result.bytecodes);

    let Halt::CopyDataProperties { dst, src } = halt else {
        panic!(
            "expected execution to stop at Copydataproperties, got {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(
        dst, DST,
        "register operand must be the target (bytecodes: {:?})",
        result.bytecodes
    );
    assert_eq!(
        src, SRC,
        "accumulator must carry the source (bytecodes: {:?})",
        result.bytecodes
    );
}

/// Optimizer smoke: `CopyDataProperties` is a side-effecting store-like
/// operation — DCE must keep it, SCCP/copyprop must treat both operands as
/// uses, and the function must survive `optimize_module` + `verify_module`
/// structurally unchanged (one CopyDataProperties with the same operands,
/// still lowerable to the real opcode).
#[test]
fn copydataproperties_survives_optimize_and_verify() {
    let (mut module, func) = build_spread_function();
    assert!(verify_module(&module).is_empty());

    optimize_module(&mut module);
    let errors = verify_module(&module);
    assert!(errors.is_empty(), "post-optimize verify: {errors:?}");

    let copies: Vec<_> = module
        .func(func)
        .blocks
        .iter()
        .flat_map(|&bb| module.block(bb).insts.iter())
        .filter_map(|&inst_id| match &module.inst(inst_id).data {
            InstData::CopyDataProperties { dst, src } => Some((*dst, *src)),
            _ => None,
        })
        .collect();
    assert_eq!(
        copies.len(),
        1,
        "DCE must keep the side-effecting CopyDataProperties"
    );

    // Both operands must still be the two parameter values (uses, not
    // rewritten away).
    let (dst, src) = copies[0];
    let params = &module.func(func).param_values;
    assert!(
        params.contains(&dst) && params.contains(&src) && dst != src,
        "operands must remain the parameter uses, got dst={dst} src={src}"
    );

    // And the optimized function still lowers to the real opcode.
    let result = lower_function(&module, func).expect("optimized spread must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Copydataproperties(_))),
        "optimized lowering must emit Copydataproperties, got {:?}",
        result.bytecodes
    );
}
