//! P1 regression (B1, v0.2 port of
//! `abcd-ir/tests/lower_phi_copy_cond_branch.rs`): phi copies of a
//! conditional predecessor must execute ONLY on their own edge.
//!
//! The module below is real IR built with the v0.2 test builder (entry
//! ends in `CondBranch`, successors s1/s2 end in `Return`). The
//! `RegAlloc` and `IselResult` are hand-constructed (all fields are
//! public) to pin the exact slot assignment the bug needs: s1's code
//! reads R5, and the `(entry, s2)` phi copy writes R5. The flat bytecode
//! from `layout::layout` is executed on a tiny deterministic interpreter
//! taking the s1 edge, and the simulated semantic result is asserted —
//! R5 must still hold its original value.

mod common;

use std::collections::HashMap;

use abcd_ir::{FunctionKind, Module, Op, ValueId};
use abcd_isa::{Bytecode, Imm, Label, Reg};
use abcd_lower::isel::IselResult;
use abcd_lower::layout;
use abcd_lower::regalloc::{self, RegAlloc, RegSlot};

use common::{Halt, Machine, V2Builder};

/// Value a live-across-the-branch value holds in R5; s1 returns it.
const LIVE_INTO_S1: i64 = 5555;
/// Payload the s2-edge phi copy writes into R5 (v2's current value in R3).
const S2_EDGE_PAYLOAD: i64 = 3333;

#[test]
fn phi_copies_for_untaken_successor_clobber_taken_path() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let entry;
    let (s1, s2);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        let cid = builder.konst(abcd_ir::Const::Bool(true));
        let cond = builder.emit_val(Op::LoadConst(cid));
        s1 = builder.create_block();
        s2 = builder.create_block();
        builder.add_predecessor(s1, entry);
        builder.add_predecessor(s2, entry);
        builder.emit_void(Op::CondBranch {
            cond,
            true_dest: s1,
            false_dest: s2,
        });
        builder.set_insert_block(s1);
        builder.emit_void(Op::Return { value: None });
        builder.set_insert_block(s2);
        builder.emit_void(Op::Return { value: None });
    }

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
        entity_traces: HashMap::new(),
        ic_size: 0,
        unsupported: None,
    };

    // Hand-pinned allocation. The (entry, s2) phi copy writes p2 into R5 —
    // the exact register s1's code reads.
    let (v1, p1, v2, p2) = (
        ValueId::new(100),
        ValueId::new(101),
        ValueId::new(102),
        ValueId::new(103),
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
        handler_phi_stores: Vec::new(),
        num_regs: 6,
        copy_temp: Some(RegSlot::Reg(15)),
        call_window_base: None,
        low_scratch_base: None,
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
