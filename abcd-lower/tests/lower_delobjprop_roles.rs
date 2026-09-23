//! N65 pin: `Op::DeleteProp` lowers to `delobjprop v0` with the OBJECT
//! in the register operand and the KEY in acc (vendor isa.yaml:1293-1296
//! — `delobjprop v:in:top, acc: inout:top`). Both the lift and the lower
//! carried a mirrored inversion of the two roles; byte round-trips were
//! exact either way, so only this shape pin (and the d-P4 decompile
//! dream gate, where local/property-ops deleted the wrong property)
//! can catch it.

mod common;

use std::collections::HashMap;

use abcd_ir::{FunctionKind, Module, Op};
use abcd_isa::{Bytecode, Reg};
use abcd_lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_lower::{fusion, isel};

use common::V2Builder;

#[test]
fn delobjprop_object_in_register_key_in_acc() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, k, o);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        k = builder.create_param();
        o = builder.create_param();
        builder.emit_val(Op::DeleteProp { object: o, key: k });
        builder.emit_void(Op::Return { value: None });
    }

    // Homes: key k in R0, object o in R1.
    let alloc = RegAlloc {
        allocation: HashMap::from([(k, RegSlot::Reg(0)), (o, RegSlot::Reg(1))]),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 2,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    };

    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let rpo = regalloc::compute_rpo(&module, func);
    let result = isel::select(&module, func, &alloc, &rpo, &suppression)
        .expect("selection must succeed for a consistent allocation");
    assert_eq!(result.unsupported, None);
    let (bb, codes) = &result.block_codes[0];
    assert_eq!(*bb, entry);

    // After the copy-in prologue: the KEY must be in acc (Lda R0) and
    // the Delobjprop's register operand must be the OBJECT's home (R1).
    let pos = codes
        .iter()
        .position(|c| matches!(c, Bytecode::Delobjprop(_)))
        .expect("delobjprop emitted");
    let Some(Bytecode::Delobjprop(obj_r)) = codes.get(pos) else {
        unreachable!()
    };
    assert_eq!(
        *obj_r,
        Reg(1),
        "N65: the register operand is the OBJECT (vendor v0 role)"
    );
    assert!(
        matches!(codes.get(pos - 1), Some(Bytecode::Lda(Reg(0)))),
        "N65: the acc carries the KEY — expected Lda(R0) immediately before, got {codes:?}"
    );
}
