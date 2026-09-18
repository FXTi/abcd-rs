//! P1 end-to-end regression (B2): a real phi swap across a loop back-edge,
//! lowered through the full `lower_function` pipeline (regalloc → isel →
//! layout) and executed on the shared simulator.
//!
//! Unlike the crafted-alloc tests in `lower_parallel_copy_slots.rs`, this
//! test builds real IR with `IRBuilder` and lets `regalloc::allocate` pick
//! the slots, produce the phi copy sets, and reserve the `copy_temp`
//! register — proving the regalloc → layout path, not just crafted inputs.
//!
//! IR shape (4 params: a, b, n, one):
//!
//! ```text
//! entry:            br header
//! header:           px = phi [(entry, a), (latch, py)]   ┐ swap on the
//!                   py = phi [(entry, b), (latch, px)]   ┘ back-edge
//!                   i  = phi [(entry, n), (latch, dec)]
//!                   dummy0 = StoreProperty { object: i, key: k0, value: i }
//!                   dec  = i - one
//!                   cond = i > one
//!                   CondBranch(cond, latch, exit)
//! latch:            dummy1 = StoreProperty { object: dec, key: k1, value: dec }
//!                   br header
//! exit:             dummy2 = StoreProperty { object: px, key: k2, value: py }
//!                   diff = px - py
//!                   return diff
//! ```
//!
//! The back-edge copy set `{(py → px), (px → py)}` is a cycle at the slot
//! level no matter which slots the allocator picks, so a correct lowering
//! must break it with the reserved temp. The loop swaps `px`/`py` once per
//! iteration; `exit` returns `px - py`, whose sign reveals the parity of
//! executed swaps.
//!
//! The `StoreProperty` instructions keep the loop-carried values in
//! registers: each use as a store object/value scores the value toward a
//! register slot, so the test does not depend on the (still-approximate,
//! B3-tracked) accumulator spill/liveness behavior. `Stobjbyname` is a
//! no-op in the simulator. Likewise `one` is a parameter (always a register)
//! so no binary operator reads a spilled literal.

mod common;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::inst::{BinOp, InstData, PropKind};
use abcd_ir::lower::lower_function;
use abcd_ir::module::{Module, ValueDef};
use abcd_ir::types::IrType;

use common::{Halt, Machine};

const A: i64 = 3;
const B: i64 = 5;
const ONE: i64 = 1;

#[test]
fn phi_swap_across_loop_back_edge_executes_correctly() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "swap_loop", FunctionKind::Function, 4);
    let entry = module.func(func).entry_block;

    let (px, py);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let a = builder.create_func_param(0, IrType::default());
        let b = builder.create_func_param(1, IrType::default());
        let n = builder.create_func_param(2, IrType::default());
        let one = builder.create_func_param(3, IrType::default());

        let header = builder.create_block();
        let latch = builder.create_block();
        let exit = builder.create_block();
        builder.add_predecessor(header, entry);
        builder.add_predecessor(latch, header);
        builder.add_predecessor(exit, header);
        builder.add_predecessor(header, latch);
        builder.emit_void(InstData::Branch { dest: header });

        builder.set_insert_block(header);
        px = builder.emit_val(InstData::Phi { entries: vec![] }, IrType::default());
        py = builder.emit_val(InstData::Phi { entries: vec![] }, IrType::default());
        let i = builder.emit_val(InstData::Phi { entries: vec![] }, IrType::default());
        // Register-operand uses pin i to a register slot (see module docs).
        let k0 = builder.intern("dummy0");
        builder.emit_void(InstData::StoreProperty {
            object: i,
            key: PropKind::ByName(k0),
            value: i,
        });
        let dec = builder.emit_val(
            InstData::BinaryOp {
                op: BinOp::Sub,
                left: i,
                right: one,
            },
            IrType::default(),
        );
        let cond = builder.emit_val(
            InstData::BinaryOp {
                op: BinOp::Greater,
                left: i,
                right: one,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::CondBranch {
            cond,
            true_dest: latch,
            false_dest: exit,
        });

        builder.set_insert_block(latch);
        let k1 = builder.intern("dummy1");
        builder.emit_void(InstData::StoreProperty {
            object: dec,
            key: PropKind::ByName(k1),
            value: dec,
        });
        builder.emit_void(InstData::Branch { dest: header });

        builder.set_insert_block(exit);
        let k2 = builder.intern("dummy2");
        builder.emit_void(InstData::StoreProperty {
            object: px,
            key: PropKind::ByName(k2),
            value: py,
        });
        let diff = builder.emit_val(
            InstData::BinaryOp {
                op: BinOp::Sub,
                left: px,
                right: py,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(diff) });

        // Fill the phi entries now that every value exists (same pattern as
        // lift/ssa.rs: emit empty phis, then set entries via inst_mut).
        for (phi_val, entries) in [
            (px, vec![(entry, a), (latch, py)]),
            (py, vec![(entry, b), (latch, px)]),
            (i, vec![(entry, n), (latch, dec)]),
        ] {
            let phi_inst = match module.value(phi_val).def {
                ValueDef::Inst(inst) => inst,
                _ => unreachable!("phi result must be an instruction result"),
            };
            module.inst_mut(phi_inst).data = InstData::Phi { entries };
        }
    }

    let result = lower_function(&module, func).expect("swap_loop must lower");

    // Frame size includes the reserved copy temp: more than the 4 params.
    assert!(
        result.num_regs > 4,
        "expected registers for locals + reserved copy temp, got {}",
        result.num_regs
    );

    // Params are pinned to R0..R3 by the allocator's param pre-assignment.
    let run = |n: i64| {
        let mut machine = Machine::new()
            .with_reg(0, A)
            .with_reg(1, B)
            .with_reg(2, n)
            .with_reg(3, ONE);
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
