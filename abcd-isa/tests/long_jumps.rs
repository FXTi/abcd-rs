mod common;

use abcd_isa::*;
use common::assert_roundtrip;

/// Forward conditional jump over ~150 instructions, exceeding imm8 range (127).
/// Exercises ReserveSpaceForOffsets expanding imm8→imm16.
#[test]
fn long_forward_jump() {
    let filler_count = 150;
    let target = filler_count + 1; // index of the final Ldundefined
    let mut program = Vec::with_capacity(target + 1);
    program.push(insn::Jeqz::new(Label(target as u32)));
    for _ in 0..filler_count {
        program.push(insn::Ldundefined::new());
    }
    program.push(insn::Ldundefined::new()); // jump target
    assert_roundtrip(&program);
}

/// Backward jump over ~150 instructions.
/// Exercises EstimateMaxDistance backward branch.
#[test]
fn long_backward_jump() {
    let filler_count = 150;
    let mut program = Vec::with_capacity(filler_count + 2);
    program.push(insn::Ldundefined::new()); // target at index 0
    for _ in 0..filler_count {
        program.push(insn::Ldundefined::new());
    }
    program.push(insn::Jmp::new(Label(0)));
    assert_roundtrip(&program);
}

/// Conditional jump over ~35000 instructions, exceeding imm16 range (32767).
/// Exercises DoReserveSpaceForOffset triggering jCC→jCC next/jmp far rewrite.
#[test]
fn very_long_conditional_jump() {
    let filler_count = 35000;
    let target = filler_count + 1;
    let mut program = Vec::with_capacity(target + 1);
    program.push(insn::Jeqz::new(Label(target as u32)));
    for _ in 0..filler_count {
        program.push(insn::Ldundefined::new());
    }
    program.push(insn::Ldundefined::new());
    assert_roundtrip(&program);
}

/// Mix of short and long jumps in the same program.
/// Exercises UpdateLabelTargets bias accumulation.
#[test]
fn multiple_long_jumps() {
    let filler_count = 150;
    let mut program = Vec::new();

    // Short forward jump (index 0 → index 3)
    program.push(insn::Jmp::new(Label(3)));
    program.push(insn::Ldundefined::new());
    program.push(insn::Ldundefined::new());
    program.push(insn::Ldundefined::new()); // target of short jump

    // Long forward conditional jump (index 4 → index 4+filler_count+1)
    let long_target = (4 + filler_count + 1) as u32;
    program.push(insn::Jeqz::new(Label(long_target)));
    for _ in 0..filler_count {
        program.push(insn::Ldundefined::new());
    }
    program.push(insn::Ldundefined::new()); // target of long jump

    // Another short jump back to index 3
    program.push(insn::Jmp::new(Label(3)));

    assert_roundtrip(&program);
}
