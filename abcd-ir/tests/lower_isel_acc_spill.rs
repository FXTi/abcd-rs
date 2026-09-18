//! P1 red regression (B3): isel accumulator spill reads a clobbered acc.
//!
//! `lower::isel::select_inst` lowers
//! `InstData::StoreProperty { key: PropKind::ByValue(k), .. }` as
//! `ensure_acc(k)` then `val_reg(object)`. `ensure_acc(k)` emits `Lda`,
//! overwriting the accumulator; `val_reg` then spills an Acc-colored object
//! with `Sta` — capturing the *key*, not the object.
//!
//! The module is real IR built with `IRBuilder` (one block:
//! `StoreProperty { object: o, key: ByValue(k), value: v }`, then `Return`).
//! The `RegAlloc` is hand-constructed (all fields public) to pin k->R0,
//! o->Acc, v->R1. The bytecodes produced by the public `isel::select` are
//! executed on a tiny deterministic interpreter with the accumulator seeded
//! to an OBJ sentinel: the `Stobjbyvalue` object operand must be OBJ.

mod common;

use std::collections::HashMap;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::StringId;
use abcd_ir::inst::{InstData, PropKind};
use abcd_ir::lower::isel;
use abcd_ir::lower::regalloc::{self, RegAlloc, RegSlot, TEMP_REG_BASE};
use abcd_ir::module::Module;
use abcd_ir::types::IrType;
use abcd_isa::{Bytecode, EntityId, Reg};

use common::{Halt, Machine};

const KEY: i64 = 111;
const OBJ: i64 = 333;
const VALUE: i64 = 222;

#[test]
#[ignore = "P1 red: isel acc spill reads clobbered acc"]
fn acc_spill_after_ensure_acc_captures_key_not_object() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 3);
    let entry = module.func(func).entry_block;

    let mut builder = IRBuilder::new(&mut module, func);
    let k = builder.create_func_param(0, IrType::default());
    let o = builder.create_func_param(1, IrType::default());
    let v = builder.create_func_param(2, IrType::default());
    builder.emit_void(InstData::StoreProperty {
        object: o,
        key: PropKind::ByValue(k),
        value: v,
    });
    builder.emit_void(InstData::Return { value: None });

    // Hand-pinned allocation: key in R0, object in the accumulator, value in R1.
    let alloc = RegAlloc {
        allocation: HashMap::from([
            (k, RegSlot::Reg(0)),
            (o, RegSlot::Acc),
            (v, RegSlot::Reg(1)),
        ]),
        phi_copies: HashMap::new(),
        num_regs: 2,
        copy_temp: None,
    };

    let rpo = regalloc::compute_rpo(&module, func);
    let string_map: HashMap<StringId, EntityId> = HashMap::new();
    let result = isel::select(&module, func, &alloc, &rpo, &string_map);

    assert_eq!(result.unsupported, None);
    assert_eq!(result.block_codes.len(), 1);
    let (bb, codes) = &result.block_codes[0];
    assert_eq!(*bb, entry);

    // Structural precondition of the bug: the key's Lda (acc clobber) is
    // emitted BEFORE the object's spill Sta, and Stobjbyvalue reads the spill.
    assert!(
        matches!(codes.first(), Some(Bytecode::Lda(Reg(0)))),
        "expected ensure_acc(key) = Lda(R0) first, got {codes:?}"
    );
    assert!(
        matches!(codes.get(1), Some(Bytecode::Sta(r)) if r.0 >= TEMP_REG_BASE),
        "expected val_reg(object) = Sta(spill>=TEMP_REG_BASE) second, got {codes:?}"
    );
    let Some(Bytecode::Stobjbyvalue(_, obj_r, val_r)) = codes.get(2) else {
        panic!("expected Stobjbyvalue third, got {codes:?}");
    };
    let (obj_r, val_r) = (*obj_r, *val_r);
    assert_eq!(val_r, Reg(1));

    // Simulate: acc seeded to the OBJ sentinel (the object lives in acc per
    // the allocation), R0 = KEY, R1 = VALUE.
    let mut machine = Machine::new()
        .with_reg(0, KEY)
        .with_reg(1, VALUE)
        .with_acc(OBJ);
    let halt = machine.run(codes);

    let Halt::StObjByValue { key, obj, value } = halt else {
        panic!("expected execution to stop at Stobjbyvalue, got {halt:?}");
    };
    assert_eq!(key, KEY, "stobjbyvalue key operand = acc");
    assert_eq!(value, VALUE, "stobjbyvalue value operand = R1");
    assert_eq!(
        obj, OBJ,
        "stobjbyvalue object operand (R{}) must be the OBJ sentinel held in \
         acc on entry; the spill captured the clobbered acc instead \
         (bytecodes: {codes:?})",
        obj_r.0
    );
}
