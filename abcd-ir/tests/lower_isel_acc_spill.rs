//! P1/P3 regression: an acc-held value needed as a register operand must
//! read its own content, never whatever the last acc write left behind.
//!
//! History: B3 was the intra-instruction form (the spill of an Acc-colored
//! register operand ran AFTER the acc operand's clobbering `Lda`, and into
//! a rotating out-of-frame slot); B4 was the cross-instruction form (an
//! Acc-colored value live across an intervening acc write read garbage).
//! Both are deleted by construction under acc-as-cache (Phase 3 finale):
//! `RegSlot::Acc` is gone, every value has a register home, register
//! operands always read their homes, and `ensure_acc` — the only acc
//! writer besides result homing — consults the emission-time acc tracker.
//!
//! What survives here as the pinned contract: `StoreProperty` with a
//! ByValue key (object/value as register operands, key in acc) must see
//! the COMPUTED object value in the object's register operand. The module
//! is real IR built with `IRBuilder` (one block: `p = k + v`, then
//! `StoreProperty { object: p, key: ByValue(k), value: v }`, then
//! `Return`). The `RegAlloc` is hand-constructed (all fields public) to
//! pin k->R0, v->R1, p->R2. The bytecodes produced by the public
//! `isel::select` are executed on a tiny deterministic interpreter with
//! the ABI argument slots (top of frame) seeded: the `Stobjbyvalue`
//! object operand must be p = k + v = OBJ.

mod common;

use std::collections::HashMap;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::StringId;
use abcd_ir::inst::{InstData, PropKind};
use abcd_ir::lower::isel;
use abcd_ir::lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_ir::lower::{LowerError, lower_function};
use abcd_ir::module::Module;
use abcd_ir::types::IrType;
use abcd_isa::{Bytecode, EntityId, Reg};

use common::{Halt, Machine};

const KEY: i64 = 111;
const OBJ: i64 = 333; // == KEY + VALUE, so p = k + v is the OBJ sentinel
const VALUE: i64 = 222;

#[test]
fn byvalue_store_reads_the_computed_object_from_its_home() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 2);
    let entry = module.func(func).entry_block;

    let mut builder = IRBuilder::new(&mut module, func);
    let k = builder.create_func_param(0, IrType::default());
    let v = builder.create_func_param(1, IrType::default());
    let p = builder.emit_val(
        InstData::BinaryOp {
            op: abcd_ir::inst::BinOp::Add,
            left: k,
            right: v,
        },
        IrType::default(),
    );
    builder.emit_void(InstData::StoreProperty {
        object: p,
        key: PropKind::ByValue(k),
        value: v,
    });
    builder.emit_void(InstData::Return { value: None });

    // Hand-pinned allocation (post-B4 shape: every value Reg-colored, no
    // spill slot — there is nothing to spill): key in R0, value in R1,
    // the computed object p in R2.
    let alloc = RegAlloc {
        allocation: HashMap::from([
            (k, RegSlot::Reg(0)),
            (v, RegSlot::Reg(1)),
            (p, RegSlot::Reg(2)),
        ]),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 3,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    };

    let rpo = regalloc::compute_rpo(&module, func);
    let string_map: HashMap<StringId, EntityId> = HashMap::new();
    let result = isel::select(&module, func, &alloc, &rpo, &string_map)
        .expect("selection must succeed for a consistent allocation");

    assert_eq!(result.unsupported, None);
    assert_eq!(result.block_codes.len(), 1);
    let (bb, codes) = &result.block_codes[0];
    assert_eq!(*bb, entry);

    // Copy-in prologue first: the two ABI top slots (num_regs = 3, so
    // v3/v4) are moved into the parameter homes R0/R1.
    assert!(
        matches!(codes.first(), Some(Bytecode::Mov(Reg(0), Reg(3)))),
        "expected copy-in Mov(home R0, arg slot R3) first, got {codes:?}"
    );
    assert!(
        matches!(codes.get(1), Some(Bytecode::Mov(Reg(1), Reg(4)))),
        "expected copy-in Mov(home R1, arg slot R4) second, got {codes:?}"
    );

    // New structural contract (acc-as-cache): the add's result is homed
    // with Sta(R2) immediately after the Add2 (p has a use), and the
    // store's key Lda reloads k from its home — the tracker knows the acc
    // holds p at that point, not k. No spill slot, no Sta anywhere else.
    assert!(
        matches!(codes.get(2), Some(Bytecode::Lda(Reg(0)))),
        "expected the add's left-operand Lda(R0), got {codes:?}"
    );
    assert!(
        matches!(codes.get(3), Some(Bytecode::Add2(_, Reg(1)))),
        "expected Add2 reading R1, got {codes:?}"
    );
    assert!(
        matches!(codes.get(4), Some(Bytecode::Sta(Reg(2)))),
        "expected the result-homing Sta(R2) right after the add, got {codes:?}"
    );
    assert!(
        matches!(codes.get(5), Some(Bytecode::Lda(Reg(0)))),
        "expected ensure_acc(key) = Lda(R0) — a tracker miss, the acc \
         holds p at this point — got {codes:?}"
    );
    let Some(Bytecode::Stobjbyvalue(_, obj_r, val_r)) = codes.get(6) else {
        panic!("expected Stobjbyvalue after the key's Lda, got {codes:?}");
    };
    let (obj_r, val_r) = (*obj_r, *val_r);
    assert_eq!(obj_r, Reg(2), "object operand must be p's home register");
    assert_eq!(val_r, Reg(1));

    // Simulate with the ABI frame layout: the arguments arrive in the top
    // slots (num_regs = 3, so v3 = k and v4 = v) and the copy-in prologue
    // moves them into the homes R0/R1.
    let mut machine = Machine::new().with_reg(3, KEY).with_reg(4, VALUE);
    let halt = machine.run(codes);

    let Halt::StObjByValue { key, obj, value } = halt else {
        panic!("expected execution to stop at Stobjbyvalue, got {halt:?}");
    };
    assert_eq!(key, KEY, "stobjbyvalue key operand = acc");
    assert_eq!(value, VALUE, "stobjbyvalue value operand = R1");
    assert_eq!(
        obj, OBJ,
        "stobjbyvalue object operand (R{}) must be p = k + v = OBJ, homed \
         after the add (bytecodes: {codes:?})",
        obj_r.0
    );
}

/// End-to-end through the full `lower_function` pipeline (regalloc picks
/// the slots itself — all Reg, no spill reservation since B4).
///
/// IR shape (4 params: o, k, q, r — pinned to R0..R3 by param
/// pre-assignment):
///
/// ```text
/// entry: p = q + r
///        StoreProperty { object: o, key: ByValue(k), value: p }
///        d = p + r
///        return d
/// ```
///
/// p is defined, then used as the store's value operand AFTER the key's
/// acc load — the exact B3/B4 clobber window. Under acc-as-cache p is
/// homed right after the add and the store reads that home. The simulator
/// halts at the `Stobjbyvalue`.
#[test]
fn store_byvalue_with_computed_value_lowers_correctly_end_to_end() {
    const Q: i64 = 7;
    const R: i64 = 35;

    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "store_byvalue", FunctionKind::Function, 4);

    let (o, k, q, r, p, d);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        o = builder.create_func_param(0, IrType::default());
        k = builder.create_func_param(1, IrType::default());
        q = builder.create_func_param(2, IrType::default());
        r = builder.create_func_param(3, IrType::default());

        p = builder.emit_val(
            InstData::BinaryOp {
                op: abcd_ir::inst::BinOp::Add,
                left: q,
                right: r,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::StoreProperty {
            object: o,
            key: PropKind::ByValue(k),
            value: p,
        });
        d = builder.emit_val(
            InstData::BinaryOp {
                op: abcd_ir::inst::BinOp::Add,
                left: p,
                right: r,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(d) });
    }

    // Post-B4 structural pin: every value has a register home; nothing is
    // acc-colored and no spill slot exists (the field is deleted).
    let alloc = regalloc::allocate(&module, func).expect("allocation must succeed");
    for value in [o, k, q, r, p, d] {
        assert!(
            matches!(alloc.allocation.get(&value), Some(RegSlot::Reg(_))),
            "every value must have a register home (acc-as-cache)"
        );
    }

    let result = lower_function(&module, func).expect("store_byvalue must lower");

    // p = Q + R = 42; the store must see (key = acc = K, object = R0, value
    // = p's home = 42). The simulator seeds the ABI top slots (num_regs,
    // so v[num_regs..num_regs+4) hold the four arguments); the copy-in
    // prologue moves them into the homes R0..R3.
    let mut machine = Machine::new()
        .with_reg(result.num_regs, OBJ)
        .with_reg(result.num_regs + 1, KEY)
        .with_reg(result.num_regs + 2, Q)
        .with_reg(result.num_regs + 3, R);
    let halt = machine.run(&result.bytecodes);

    let Halt::StObjByValue { key, obj, value } = halt else {
        panic!(
            "expected execution to stop at Stobjbyvalue, got {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(key, KEY, "stobjbyvalue key operand = acc");
    assert_eq!(obj, OBJ, "stobjbyvalue object operand = R0");
    assert_eq!(
        value,
        Q + R,
        "stobjbyvalue value operand must be p = q + r, read from its home \
         (bytecodes: {:?})",
        result.bytecodes
    );
}

/// An operand that register allocation never colored (dangling value
/// reference, constructible because `lower_function` does not verify the
/// module) must be a hard `LowerError`, not a silent "assume acc" fallback.
#[test]
fn unallocated_operand_is_a_hard_error() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 1);

    let dangling;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let v = builder.create_func_param(0, IrType::default());
        dangling = abcd_ir::entity::Value::from_index(777);
        let name = builder.intern("x");
        builder.emit_void(InstData::StoreProperty {
            object: dangling,
            key: PropKind::ByName(name),
            value: v,
        });
        builder.emit_void(InstData::Return { value: None });
    }

    assert!(
        matches!(
            lower_function(&module, func),
            Err(LowerError::UnallocatedOperand { value, .. }) if value == dangling
        ),
        "dangling operand must fail with UnallocatedOperand"
    );
}
