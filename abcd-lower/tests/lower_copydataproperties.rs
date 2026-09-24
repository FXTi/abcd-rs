//! S3 regression (v0.2 port of `abcd-ir/tests/lower_copydataproperties.rs`):
//! `Op::CopyDataProps` lowering.
//!
//! Operand roles follow the vendor signature `copydataproperties v:in:top,
//! acc: inout:top` (abcd-isa-sys/arkcompiler_runtime_core/isa/isa.yaml): the register operand
//! is the TARGET object, the accumulator carries the SOURCE and receives
//! the result. The simulator halts at the `Copydataproperties` instruction
//! (record-and-stop), so the test asserts exactly which value sits in which
//! slot at that point.

mod common;

use abcd_ir::{FunctionKind, Module, Op, verify_module};
use abcd_isa::Bytecode;
use abcd_lower::lower_function;

use common::{Halt, Machine, V2Builder};

const DST: i64 = 111; // target object sentinel
const SRC: i64 = 222; // source object sentinel

/// Build a two-parameter function `f(dst, src)` whose body is a single
/// `CopyDataProps { dst, src }` followed by `return undefined`.
fn build_spread_function() -> (Module, abcd_ir::FuncId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "spread", FunctionKind::Function);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let dst = builder.create_param();
        let src = builder.create_param();
        builder.emit_void(Op::CopyDataProps { dst, src });
        builder.emit_void(Op::Return { value: None });
    }
    (module, func)
}

/// End-to-end through `lower_function`: the target must reach the register
/// operand and the source the accumulator.
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
        "no stobjbyname impersonation, got {:?}",
        result.bytecodes
    );

    // Simulate with the ABI frame layout: the two arguments arrive in the
    // top slots; the copy-in prologue moves them into the homes R0/R1.
    let mut machine = Machine::new()
        .with_reg(result.num_regs, DST)
        .with_reg(result.num_regs + 1, SRC);
    let halt = machine.run(&result.bytecodes);
    let Halt::CopyDataProperties { dst, src } = halt else {
        panic!(
            "expected execution to stop at Copydataproperties, got {halt:?} \
             (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(dst, DST, "register operand must be the target object");
    assert_eq!(src, SRC, "acc must carry the source object");
}

/// The v0.1 opt-treatment pin (DCE keeps CopyDataProps as a side-effecting
/// store) has no v0.2 counterpart at P2 — the verifier pin stands in: the
/// op verifies and lowers.
#[test]
fn copydataproperties_verifies() {
    let (module, _func) = build_spread_function();
    let report = verify_module(&module);
    assert!(report.is_ok(), "verify: {:?}", report.errors);
}
