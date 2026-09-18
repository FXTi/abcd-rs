//! P1 regression (B1): phi copies of a conditional predecessor must execute
//! ONLY on their own edge.
//!
//! `lower::layout` used to insert the copy sequence keyed `(pred, succ)`
//! into `pred` immediately before its terminator — for every successor key.
//! When `pred` ends in `InstData::CondBranch`, the copies belonging to the
//! *not-taken* successor ran as well, clobbering registers the taken path
//! still reads. The fix routes each copy-bearing edge through a synthetic
//! trampoline (copy sequence + `Jmp succ`) and rewrites the branch target.
//!
//! The module below is real IR built with `IRBuilder` (entry ends in
//! `CondBranch`, successors s1/s2 end in `Return`). The `RegAlloc` and
//! `IselResult` are hand-constructed (all fields are public) to pin the exact
//! slot assignment the bug needs: s1's code reads R5, and the `(entry, s2)`
//! phi copy writes R5. The flat bytecode from `layout::layout` is executed on
//! a tiny deterministic interpreter taking the s1 edge, and the simulated
//! semantic result is asserted — R5 must still hold its original value.

mod common;

use std::collections::HashMap;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::Value;
use abcd_ir::inst::InstData;
use abcd_ir::lower::isel::IselResult;
use abcd_ir::lower::layout;
use abcd_ir::lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_ir::module::Module;
use abcd_ir::types::IrType;
use abcd_isa::{Bytecode, Imm, Label, Reg};

use common::{Halt, Machine};

/// Value a live-across-the-branch value holds in R5; s1 returns it.
const LIVE_INTO_S1: i64 = 5555;
/// Payload the s2-edge phi copy writes into R5 (v2's current value in R3).
const S2_EDGE_PAYLOAD: i64 = 3333;

#[test]
fn phi_copies_for_untaken_successor_clobber_taken_path() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let mut builder = IRBuilder::new(&mut module, func);
    let cond = builder.emit_val(InstData::LiteralBool(true), IrType::default());
    let s1 = builder.create_block();
    let s2 = builder.create_block();
    builder.add_predecessor(s1, entry);
    builder.add_predecessor(s2, entry);
    builder.emit_void(InstData::CondBranch {
        cond,
        true_dest: s1,
        false_dest: s2,
    });
    builder.set_insert_block(s1);
    builder.emit_void(InstData::Return { value: None });
    builder.set_insert_block(s2);
    builder.emit_void(InstData::Return { value: None });

    // Hand-written block codes: entry branches on a constant-true acc, s1
    // reads R5 and returns it, s2 returns undefined.
    let isel = IselResult {
        block_codes: vec![
            (
                entry,
                vec![Bytecode::Ldai(Imm(1)), Bytecode::Jnez(Label(s1.0))],
            ),
            (s1, vec![Bytecode::Lda(Reg(5)), Bytecode::Return]),
            (s2, vec![Bytecode::Returnundefined]),
        ],
        string_map: HashMap::new(),
        ic_size: 0,
        unsupported: None,
    };

    // Hand-pinned allocation. The (entry, s2) phi copy writes p2 into R5 —
    // the exact register s1's code reads.
    let (v1, p1, v2, p2) = (
        Value::from_index(100),
        Value::from_index(101),
        Value::from_index(102),
        Value::from_index(103),
    );
    let allocation = HashMap::from([
        (v1, RegSlot::Reg(1)),
        (p1, RegSlot::Reg(2)), // harmless destination on the s1 edge
        (v2, RegSlot::Reg(3)),
        (p2, RegSlot::Reg(5)), // clobbers the register s1 still needs
    ]);
    let phi_copies = HashMap::from([((entry, s1), vec![(v1, p1)]), ((entry, s2), vec![(v2, p2)])]);
    let alloc = RegAlloc {
        allocation,
        phi_copies,
        num_regs: 6,
        copy_temp: Some(RegSlot::Reg(15)),
    };

    let rpo = regalloc::compute_rpo(&module, func);
    let laid_out = layout::layout(&module, func, &isel, &alloc, &rpo).unwrap();

    // Simulate taking the s1 edge (acc = 1 from Ldai). Correct semantics:
    // only the (entry, s1) copy runs, R5 survives, s1 returns LIVE_INTO_S1.
    let mut machine = Machine::new()
        .with_reg(3, S2_EDGE_PAYLOAD)
        .with_reg(5, LIVE_INTO_S1);
    let halt = machine.run(&laid_out.bytecodes);

    assert_eq!(
        halt,
        Halt::Return(LIVE_INTO_S1),
        "s1 path must still see R5 = {LIVE_INTO_S1}; the (entry, s2) phi copy \
         must not execute on the s1 edge (bytecodes: {:?})",
        laid_out.bytecodes
    );
}
