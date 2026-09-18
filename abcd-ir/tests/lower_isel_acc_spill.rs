//! P1 regression (B3): isel accumulator spill must capture the acc BEFORE
//! any `Lda` of the same instruction clobbers it.
//!
//! `lower::isel` lowers `InstData::StoreProperty { key: PropKind::ByValue(k), .. }`
//! with the key in the accumulator (`Lda`) and the object/value as register
//! operands. The old code emitted `ensure_acc(k)` (the clobbering `Lda`)
//! BEFORE `val_reg(object)` spilled an Acc-colored object with `Sta` — the
//! spill captured the *key*, not the object — into a rotating slot at
//! `TEMP_REG_BASE + len % 16`, outside any declared frame.
//!
//! The fixed contract: the (at most one, by the interference invariant)
//! Acc-colored register operand is spilled into the reserved in-frame
//! `RegAlloc::spill_slot` register BEFORE the acc operand's `Lda`.
//!
//! The module is real IR built with `IRBuilder` (one block:
//! `p = k + v`, then `StoreProperty { object: p, key: ByValue(k), value: v }`,
//! then `Return`). `p` is the Acc-colored object — a computed value, not a
//! parameter: since Phase 2.2 parameters must keep a register home for the
//! copy-in prologue (`LowerError::AccColoredParam` otherwise). The
//! `RegAlloc` is hand-constructed (all fields public) to pin k->R0, v->R1,
//! p->Acc, spill slot -> R2. The bytecodes produced by the public
//! `isel::select` are executed on a tiny deterministic interpreter with the
//! ABI argument slots (top of frame) seeded: the `Stobjbyvalue` object
//! operand must be p = k + v = OBJ.

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
fn acc_spill_before_ensure_acc_captures_object_not_key() {
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

    // Hand-pinned allocation: key in R0, value in R1, the computed object
    // p in the accumulator, and the reserved in-frame spill slot R2 (as
    // regalloc would reserve it: `num_regs` before reservation, then
    // bumped to 3).
    let alloc = RegAlloc {
        allocation: HashMap::from([
            (k, RegSlot::Reg(0)),
            (v, RegSlot::Reg(1)),
            (p, RegSlot::Acc),
        ]),
        phi_copies: HashMap::new(),
        num_regs: 3,
        copy_temp: None,
        spill_slot: Some(RegSlot::Reg(2)),
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

    // New structural contract: the object's spill Sta into the reserved
    // in-frame register R2 is emitted AFTER the add that leaves p in acc
    // and BEFORE the key's Lda (acc clobber); Stobjbyvalue reads the spill
    // register.
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
        "expected val_reg(object) = Sta(reserved spill R2) before the key's Lda, got {codes:?}"
    );
    assert!(
        matches!(codes.get(5), Some(Bytecode::Lda(Reg(0)))),
        "expected ensure_acc(key) = Lda(R0) after the spill, got {codes:?}"
    );
    let Some(Bytecode::Stobjbyvalue(_, obj_r, val_r)) = codes.get(6) else {
        panic!("expected Stobjbyvalue after the key's Lda, got {codes:?}");
    };
    let (obj_r, val_r) = (*obj_r, *val_r);
    assert_eq!(obj_r, Reg(2), "object operand must be the spill register");
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
        "stobjbyvalue object operand (R{}) must be p = k + v = OBJ held in \
         acc after the add; a B3 regression would spill the clobbered acc \
         (the key) instead (bytecodes: {codes:?})",
        obj_r.0
    );
}

/// End-to-end B3 reproduction through the full `lower_function` pipeline
/// (regalloc picks the slots itself, including the reserved spill slot).
///
/// IR shape (4 params: o, k, q, r — pinned to R0..R3 by param
/// pre-assignment):
///
/// ```text
/// entry: p = q + r                                          // result left in acc
///        StoreProperty { object: o, key: ByValue(k), value: p }
///        d = p + r        // score-shaping only: p's use as a binop left
///        return d         //   operand makes p prefer Acc (+2 result,
///                          //   +2 left operand, -3 store value = +1 > 0)
/// ```
///
/// `p` interferes only with the params (all Reg-colored), so the allocator
/// colors it Acc. The store is where B3 lived: the key's `Lda` must not
/// precede the spill of the acc-resident `p`. The simulator halts at the
/// `Stobjbyvalue`, so the trailing instructions (which would trip the
/// cross-instruction acc-clobber gap tracked separately as B4) are never
/// executed — they exist only to shape the acc-preference score.
#[test]
fn store_byvalue_with_acc_resident_value_lowers_correctly_end_to_end() {
    const Q: i64 = 7;
    const R: i64 = 35;

    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "store_byvalue", FunctionKind::Function, 4);

    {
        let mut builder = IRBuilder::new(&mut module, func);
        let o = builder.create_func_param(0, IrType::default());
        let k = builder.create_func_param(1, IrType::default());
        let q = builder.create_func_param(2, IrType::default());
        let r = builder.create_func_param(3, IrType::default());

        let p = builder.emit_val(
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
        let d = builder.emit_val(
            InstData::BinaryOp {
                op: abcd_ir::inst::BinOp::Add,
                left: p,
                right: r,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(d) });
    }

    let result = lower_function(&module, func).expect("store_byvalue must lower");

    // The frame is exactly the 4 params plus the one reserved spill
    // register: every SSA value in this function is Acc-colored and no phi
    // copy temp is needed.
    assert_eq!(
        result.num_regs, 5,
        "expected 4 params + 1 reserved spill register, got {} (bytecodes: {:?})",
        result.num_regs, result.bytecodes
    );

    // p = Q + R = 42; the store must see (key = acc = K, object = R0, value
    // = spilled p = 42). The simulator seeds the ABI top slots (num_regs =
    // 5, so v5..v8 hold the four arguments); the copy-in prologue moves
    // them into the homes R0..R3.
    let mut machine = Machine::new()
        .with_reg(5, OBJ)
        .with_reg(6, KEY)
        .with_reg(7, Q)
        .with_reg(8, R);
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
        "stobjbyvalue value operand must be p = q + r, spilled before the \
         key's Lda (bytecodes: {:?})",
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
