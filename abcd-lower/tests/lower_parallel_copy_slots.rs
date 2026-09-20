//! P1 regressions (B2, v0.2 port of
//! `abcd-ir/tests/lower_parallel_copy_slots.rs`): value-level
//! parallel-copy resolution misses slot-level hazards.
//!
//! Coalescing lets distinct values share one register slot, so an order
//! that is safe in value space can be unsafe in slot space, and a slot
//! space cycle can exist where value space has none (so no temp was ever
//! allocated). The copies are re-resolved in SLOT space at the emission
//! point in `layout`, using the per-function reserved `copy_temp`
//! register.
//!
//! Both tests use a single unconditional edge pred -> succ (pred ends in
//! `Branch`). The copy lists are written in the exact order the
//! value-level resolver produces for `[(a, b), (c, d)]` — `(a, b)` first,
//! because b is not a value-level source. The flat bytecode from
//! `layout::layout` is executed on a tiny deterministic interpreter and
//! the simulated semantic results are asserted.

mod common;

use std::collections::HashMap;

use abcd_ir2::{FunctionKind, Module, Op, ValueId};
use abcd_isa::{Bytecode, Imm, Label, Reg};
use abcd_lower::isel::IselResult;
use abcd_lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_lower::layout;

use common::{Halt, Machine, V2Builder};

/// Build pred -> succ IR, hand-pin `slots` and `copies` (already in the
/// value-level resolver's emission order), run layout, then execute the flat
/// bytecode with the given initial register file.
fn run_edge_copies(
    slots: &[(ValueId, u16)],
    copies: &[(ValueId, ValueId)],
    succ_codes: Vec<Bytecode>,
    init_regs: &[(u16, i64)],
) -> (Halt, Machine, Vec<Bytecode>) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, succ);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        succ = builder.create_block();
        builder.add_predecessor(succ, entry);
        builder.emit_void(Op::Branch { dest: succ });
        builder.set_insert_block(succ);
        builder.emit_void(Op::Return { value: None });
    }

    let isel = IselResult {
        block_codes: vec![
            (
                entry,
                vec![Bytecode::Ldai(Imm(0)), Bytecode::Jmp(Label(succ.0))],
            ),
            (succ, succ_codes),
        ],
        entity_traces: HashMap::new(),
        ic_size: 0,
        unsupported: None,
    };

    let allocation: HashMap<ValueId, RegSlot> =
        slots.iter().map(|&(v, r)| (v, RegSlot::Reg(r))).collect();
    let phi_copies = HashMap::from([((entry, succ), copies.to_vec())]);
    let alloc = RegAlloc {
        allocation,
        phi_copies,
        handler_phi_stores: Vec::new(),
        num_regs: 16,
        copy_temp: Some(RegSlot::Reg(15)),
        call_window_base: None,
        low_scratch_base: None,
    };

    let rpo = regalloc::compute_rpo(&module, func);
    let laid_out = layout::layout(&module, func, &isel, &alloc, &rpo).unwrap();

    let mut machine = Machine::new();
    for &(reg, val) in init_regs {
        machine.regs.insert(reg, val);
    }
    let halt = machine.run(&laid_out.bytecodes);
    (halt, machine, laid_out.bytecodes)
}

/// (a) Slot-level WAR hazard invisible in value space.
///
/// Copies `[(a, b), (c, d)]` with slots a->R1, b->R2, c->R2, d->R3. The
/// value-level resolver emits `(a, b)` first (b is not a value-level source),
/// i.e. `Mov(R2, R1)` — but R2 still holds c's value, which `(c, d)` must
/// read: correct parallel semantics give d := old c, i.e. R3 = old R2.
#[test]
fn value_order_overwrites_shared_source_slot() {
    let (a, b, c, d) = (
        ValueId::new(100),
        ValueId::new(101),
        ValueId::new(102),
        ValueId::new(103),
    );
    let slots = [(a, 1), (b, 2), (c, 2), (d, 3)];
    // Exact emission order of regalloc's value-level topological sort.
    let copies = [(a, b), (c, d)];
    // succ returns d's slot (R3).
    let succ_codes = vec![Bytecode::Lda(Reg(3)), Bytecode::Return];

    let (halt, _machine, bytecodes) = run_edge_copies(
        &slots,
        &copies,
        succ_codes,
        &[(1, 10), (2, 20)], // R1 = a, R2 = c before the copies
    );

    assert_eq!(
        halt,
        Halt::Return(20),
        "parallel semantics: d := old c (R3 := old R2 = 20); \
         sequential value-order emission clobbered R2 first (bytecodes: {bytecodes:?})"
    );
}

/// (b) Slot-level cycle invisible in value space.
///
/// Same copies with slots a->R1, b->R2, c->R2, d->R1: at the slot level this
/// is a true swap R1 <-> R2. Value space has no cycle (b, d are not sources),
/// so the resolver allocates no temp and layout emits
/// `Mov(R2, R1); Mov(R1, R2)` — sequential emission corrupts the swap.
#[test]
fn slot_cycle_without_value_cycle_needs_temp() {
    let (a, b, c, d) = (
        ValueId::new(100),
        ValueId::new(101),
        ValueId::new(102),
        ValueId::new(103),
    );
    let slots = [(a, 1), (b, 2), (c, 2), (d, 1)];
    let copies = [(a, b), (c, d)];
    // succ snapshots R2 into R7, then returns R1.
    let succ_codes = vec![
        Bytecode::Lda(Reg(2)),
        Bytecode::Sta(Reg(7)),
        Bytecode::Lda(Reg(1)),
        Bytecode::Return,
    ];

    let (halt, machine, bytecodes) = run_edge_copies(
        &slots,
        &copies,
        succ_codes,
        &[(1, 1), (2, 2)], // R1 = a = 1, R2 = c = 2 before the copies
    );

    assert_eq!(
        halt,
        Halt::Return(2),
        "swap semantics: R1 := old R2 = 2 (bytecodes: {bytecodes:?})"
    );
    assert_eq!(
        machine.reg(7),
        1,
        "swap semantics: R2 := old R1 = 1 (bytecodes: {bytecodes:?})"
    );
}
