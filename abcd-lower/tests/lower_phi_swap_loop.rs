//! P1 end-to-end regression (B2, v0.2 port of
//! `abcd-ir/tests/lower_phi_swap_loop.rs`): a real phi swap across a loop
//! back-edge, lowered through the full `lower_function` pipeline
//! (regalloc → isel → layout) and executed on the shared simulator.
//!
//! Unlike the crafted-alloc tests in `lower_parallel_copy_slots.rs`, this
//! test builds real IR with the v0.2 test builder and lets
//! `regalloc::allocate` pick the slots, produce the phi copy sets, and
//! reserve the `copy_temp` register — proving the regalloc → layout path,
//! not just crafted inputs.
//!
//! IR shape (4 params: a, b, n, one):
//!
//! ```text
//! entry:            br header
//! header:           px = phi [(entry, a), (latch, py)]   ┐ swap on the
//!                   py = phi [(entry, b), (latch, px)]   ┘ back-edge
//!                   i  = phi [(entry, n), (latch, dec)]
//!                   dummy0 = StoreProp { object: i, name: k0, value: i }
//!                   dec  = i - one
//!                   cond = i > one
//!                   CondBranch(cond, latch, exit)
//! latch:            dummy1 = StoreProp { object: dec, name: k1, value: dec }
//!                   br header
//! exit:             dummy2 = StoreProp { object: px, name: k2, value: py }
//!                   diff = px - py
//!                   return diff
//! ```
//!
//! The back-edge copy set `{(py → px), (px → py)}` is a cycle at the slot
//! level no matter which slots the allocator picks, so a correct lowering
//! must break it with the reserved temp. The loop swaps `px`/`py` once per
//! iteration; `exit` returns `px - py`, whose sign reveals the parity of
//! executed swaps.

mod common;

use abcd_ir2::{BinOp, CmpOp, Edge, EdgeKind, FunctionKind, Module, Op, ValueDef};
use abcd_lower::lower_function;

use common::{Halt, Machine, V2Builder};

const A: i64 = 3;
const B: i64 = 5;
const ONE: i64 = 1;

#[test]
fn phi_swap_across_loop_back_edge_executes_correctly() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "swap_loop", FunctionKind::Function);
    let entry;
    let (px, py);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        let a = builder.create_param();
        let b = builder.create_param();
        let n = builder.create_param();
        let one = builder.create_param();

        let header = builder.create_block();
        let latch = builder.create_block();
        let exit = builder.create_block();
        builder.add_predecessor(header, entry);
        builder.add_predecessor(latch, header);
        builder.add_predecessor(exit, header);
        builder.add_predecessor(header, latch);
        builder.emit_void(Op::Branch { dest: header });

        builder.set_insert_block(header);
        px = builder.emit_val(Op::Phi { entries: vec![] });
        py = builder.emit_val(Op::Phi { entries: vec![] });
        let i = builder.emit_val(Op::Phi { entries: vec![] });
        // Register-operand uses pin i to a register slot (see module docs).
        let k0 = builder.sym("dummy0");
        builder.emit_void(Op::StoreProp {
            object: i,
            name: k0,
            value: i,
        });
        let dec = builder.emit_val(Op::BinaryOp {
            op: BinOp::Sub,
            left: i,
            right: one,
        });
        let cond = builder.emit_val(Op::Compare {
            op: CmpOp::Greater,
            left: i,
            right: one,
        });
        builder.emit_void(Op::CondBranch {
            cond,
            true_dest: latch,
            false_dest: exit,
        });

        builder.set_insert_block(latch);
        let k1 = builder.sym("dummy1");
        builder.emit_void(Op::StoreProp {
            object: dec,
            name: k1,
            value: dec,
        });
        builder.emit_void(Op::Branch { dest: header });

        builder.set_insert_block(exit);
        let k2 = builder.sym("dummy2");
        builder.emit_void(Op::StoreProp {
            object: px,
            name: k2,
            value: py,
        });
        let diff = builder.emit_val(Op::BinaryOp {
            op: BinOp::Sub,
            left: px,
            right: py,
        });
        builder.emit_void(Op::Return { value: Some(diff) });

        // Fill the phi entries now that every value exists (same pattern as
        // the lift: emit empty phis, then set entries).
        let normal = |from: abcd_ir2::BlockId| Edge {
            from,
            kind: EdgeKind::Normal,
        };
        for (phi_val, entries) in [
            (px, vec![(normal(entry), a), (normal(latch), py)]),
            (py, vec![(normal(entry), b), (normal(latch), px)]),
            (i, vec![(normal(entry), n), (normal(latch), dec)]),
        ] {
            let phi_inst = match module.values[phi_val.index()].def {
                ValueDef::Inst(inst) => inst,
                _ => unreachable!("phi result must be an instruction result"),
            };
            module.insts[phi_inst.index()].op = Op::Phi { entries };
        }
    }

    let result = lower_function(&module, func).expect("swap_loop must lower");

    // Frame size includes the reserved copy temp: more than the 4 params.
    assert!(
        result.num_regs > 4,
        "expected registers for locals + reserved copy temp, got {}",
        result.num_regs
    );

    // Params are pinned to the R0..R3 vreg homes by the allocator's param
    // pre-assignment; the copy-in prologue moves the ABI top slots
    // (v[num_regs + i]) into those homes at entry, so the simulator seeds
    // the arguments at the top of the frame.
    let base = result.num_regs;
    let run = |n: i64| {
        let mut machine = Machine::new()
            .with_reg(base, A)
            .with_reg(base + 1, B)
            .with_reg(base + 2, n)
            .with_reg(base + 3, ONE);
        machine.run(&result.bytecodes)
    };

    // n = 1: back-edge never taken, no swap: px - py = A - B.
    assert_eq!(
        run(1),
        Halt::Return(A - B),
        "bytecodes: {:?}",
        result.bytecodes
    );
    // n = 3: two back-edge traversals, two swaps: px - py = A - B again.
    assert_eq!(
        run(3),
        Halt::Return(A - B),
        "bytecodes: {:?}",
        result.bytecodes
    );
    // n = 4: three traversals, odd number of swaps: px - py = B - A.
    assert_eq!(
        run(4),
        Halt::Return(B - A),
        "bytecodes: {:?}",
        result.bytecodes
    );
}
