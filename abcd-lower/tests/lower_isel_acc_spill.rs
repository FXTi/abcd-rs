//! P1/P3 regression (v0.2 port of `abcd-ir/tests/lower_isel_acc_spill.rs`):
//! an acc-held value needed as a register operand must read its own
//! content, never whatever the last acc write left behind.
//!
//! Under acc-as-cache every value has a register home, register operands
//! always read their homes, and `ensure_acc` — the only acc writer
//! besides result homing — consults the emission-time acc tracker.

mod common;

use std::collections::HashMap;

use abcd_ir2::{BinOp, FunctionKind, Module, Op, ValueId};
use abcd_isa::{Bytecode, Reg};
use abcd_lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_lower::{LowerError, fusion, isel, lower_function};

use common::{Halt, Machine, V2Builder};

const KEY: i64 = 111;
const OBJ: i64 = 333; // == KEY + VALUE, so p = k + v is the OBJ sentinel
const VALUE: i64 = 222;

#[test]
fn byvalue_store_reads_the_computed_object_from_its_home() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, k, v, p);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        k = builder.create_param();
        v = builder.create_param();
        p = builder.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: k,
            right: v,
        });
        builder.emit_void(Op::StorePropDyn {
            object: p,
            key: k,
            value: v,
        });
        builder.emit_void(Op::Return { value: None });
    }

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

    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let rpo = regalloc::compute_rpo(&module, func);
    let result = isel::select(&module, func, &alloc, &rpo, &suppression)
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
    // store's VALUE Lda reloads v from its home — vendor `stobjbyvalue
    // imm, v1: receiver, v2: propKey, acc: value` (isa.yaml:1353-1357):
    // the register operands are object (R2) and key (R0), the acc
    // carries the value.
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
        matches!(codes.get(5), Some(Bytecode::Lda(Reg(1)))),
        "expected ensure_acc(value) = Lda(R1) — a tracker miss, the acc \
         holds p at this point — got {codes:?}"
    );
    let Some(Bytecode::Stobjbyvalue(_, obj_r, key_r)) = codes.get(6) else {
        panic!("expected Stobjbyvalue after the value's Lda, got {codes:?}");
    };
    let (obj_r, key_r) = (*obj_r, *key_r);
    assert_eq!(obj_r, Reg(2), "object operand must be p's home register");
    assert_eq!(key_r, Reg(0), "key operand must be k's home register");

    // Simulate with the ABI frame layout: the arguments arrive in the top
    // slots (num_regs = 3, so v3 = k and v4 = v) and the copy-in prologue
    // moves them into the homes R0/R1.
    let mut machine = Machine::new().with_reg(3, KEY).with_reg(4, VALUE);
    let halt = machine.run(codes);

    let Halt::StObjByValue { key, obj, value } = halt else {
        panic!("expected execution to stop at Stobjbyvalue, got {halt:?}");
    };
    assert_eq!(
        key, KEY,
        "stobjbyvalue key operand = the key register (vendor v2 = propKey)"
    );
    assert_eq!(
        value, VALUE,
        "stobjbyvalue value operand = acc (vendor acc = value)"
    );
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
///        StorePropDyn { object: o, key: k, value: p }
///        d = p + r
///        return d
/// ```
#[test]
fn store_byvalue_with_computed_value_lowers_correctly_end_to_end() {
    const Q: i64 = 7;
    const R: i64 = 35;

    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "store_byvalue", FunctionKind::Function);

    let (o, k, q, r, p, d);
    {
        let mut builder = V2Builder::new(&mut module, func);
        o = builder.create_param();
        k = builder.create_param();
        q = builder.create_param();
        r = builder.create_param();

        p = builder.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: q,
            right: r,
        });
        builder.emit_void(Op::StorePropDyn {
            object: o,
            key: k,
            value: p,
        });
        d = builder.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: p,
            right: r,
        });
        builder.emit_void(Op::Return { value: Some(d) });
    }

    // Post-B4 structural pin: every value has a register home; nothing is
    // acc-colored and no spill slot exists (the field is deleted).
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let alloc = regalloc::allocate(&module, func, &suppression).expect("allocation must succeed");
    for value in [o, k, q, r, p, d] {
        assert!(
            matches!(alloc.allocation.get(&value), Some(RegSlot::Reg(_))),
            "every value must have a register home (acc-as-cache)"
        );
    }

    let result = lower_function(&module, func).expect("store_byvalue must lower");

    // p = Q + R = 42; the store must see (object = R0, key = the key
    // register's home = K, value = acc = p = 42). The simulator seeds the
    // ABI top slots; the copy-in prologue moves them into the homes.
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
    assert_eq!(
        key, KEY,
        "stobjbyvalue key operand = the key register (vendor v2 = propKey)"
    );
    assert_eq!(obj, OBJ, "stobjbyvalue object operand = R0");
    assert_eq!(
        value,
        Q + R,
        "stobjbyvalue value operand = acc (vendor acc = value) must be \
         p = q + r, loaded from its home (bytecodes: {:?})",
        result.bytecodes
    );
}

/// An operand that register allocation never colored (dangling value
/// reference, constructible because `lower_function` does not verify the
/// module) must be a hard `LowerError`, not a silent "assume acc" fallback.
#[test]
fn unallocated_operand_is_a_hard_error() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);

    let dangling;
    {
        let mut builder = V2Builder::new(&mut module, func);
        let v = builder.create_param();
        dangling = ValueId::new(777);
        let name = builder.sym("x");
        builder.emit_void(Op::StoreProp {
            object: dangling,
            name,
            value: v,
        });
        builder.emit_void(Op::Return { value: None });
    }

    assert!(
        matches!(
            lower_function(&module, func),
            Err(LowerError::UnallocatedOperand { value, .. }) if value == dangling
        ),
        "dangling operand must fail with UnallocatedOperand"
    );
}
