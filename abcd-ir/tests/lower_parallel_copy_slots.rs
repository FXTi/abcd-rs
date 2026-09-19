//! P1 regressions (B2): value-level parallel-copy resolution misses
//! slot-level hazards.
//!
//! `lower::regalloc` used to compute the sequential emission order over SSA
//! *Values* (topological sort + cycle breaking with a temp). But coalescing
//! lets distinct values share one register slot, so an order that is safe in
//! value space can be unsafe in slot space, and a slot space cycle can exist
//! where value space has none (so no temp was ever allocated). The fix
//! re-resolves the copies in SLOT space at the emission point in
//! `lower::layout`, using the per-function reserved `copy_temp` register.
//!
//! Both tests use a single unconditional edge pred -> succ (pred ends in
//! `InstData::Branch`). The copy lists are written in the exact order the
//! value-level resolver produces for `[(a, b), (c, d)]` — `(a, b)` first,
//! because b is not a value-level source. The flat bytecode from
//! `layout::layout` is executed on a tiny deterministic interpreter and the
//! simulated semantic results are asserted.

mod common;

use std::collections::HashMap;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::{Block, FuncId, Value};
use abcd_ir::inst::InstData;
use abcd_ir::lower::isel::IselResult;
use abcd_ir::lower::layout;
use abcd_ir::lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_ir::module::Module;
use abcd_isa::{Bytecode, Imm, Label, Reg};

use common::{Halt, Machine};

/// Build pred -> succ IR, hand-pin `slots` and `copies` (already in the
/// value-level resolver's emission order), run layout, then execute the flat
/// bytecode with the given initial register file.
fn run_edge_copies(
    slots: &[(Value, u16)],
    copies: &[(Value, Value)],
    succ_codes: Vec<Bytecode>,
    init_regs: &[(u16, i64)],
) -> (Halt, Machine, Vec<Bytecode>) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func: FuncId = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let mut builder = IRBuilder::new(&mut module, func);
    let succ = builder.create_block();
    builder.add_predecessor(succ, entry);
    builder.emit_void(InstData::Branch { dest: succ });
    builder.set_insert_block(succ);
    builder.emit_void(InstData::Return { value: None });

    let isel = IselResult {
        block_codes: vec![
            (
                entry,
                vec![Bytecode::Ldai(Imm(0)), Bytecode::Jmp(Label(succ.0))],
            ),
            (succ, succ_codes),
        ],
        string_map: HashMap::new(),
        entity_traces: HashMap::new(),
        ic_size: 0,
        unsupported: None,
    };

    let allocation: HashMap<Value, RegSlot> =
        slots.iter().map(|&(v, r)| (v, RegSlot::Reg(r))).collect();
    let phi_copies: HashMap<(Block, Block), Vec<(Value, Value)>> =
        HashMap::from([((entry, succ), copies.to_vec())]);
    let alloc = RegAlloc {
        allocation,
        phi_copies,
        handler_phi_stores: Vec::new(),
        num_regs: 16,
        copy_temp: Some(RegSlot::Reg(15)),
        // No Acc-colored values in this fixture.
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
        Value::from_index(100),
        Value::from_index(101),
        Value::from_index(102),
        Value::from_index(103),
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
        Value::from_index(100),
        Value::from_index(101),
        Value::from_index(102),
        Value::from_index(103),
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
