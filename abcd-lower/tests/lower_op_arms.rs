//! c-COV A9 sweep: isel op arms that the measured (L1-synthetic) lower
//! input never reaches — either because es2abc never emits the source
//! opcode (the lift arm is corpus-dark too) or because the shape is a
//! fusion-declined / robustness fallback the lift's output never hits.
//!
//! Every test builds the IR with `V2Builder` (or hand-pinned suppression
//! where the fusion analysis would otherwise rewrite the shape) and lowers
//! through the real pipeline (`lower_function`) unless the arm requires a
//! hand-crafted [`Suppression`]/[`RegAlloc`] (then `isel::select` is
//! called directly, the established pattern of `lower_cmp_branch_fusion.rs`).
//! Behavioral asserts run on the `common::Machine` interpreter wherever the
//! opcode is in its subset; otherwise the emitted bytecode is pinned
//! directly.

mod common;

use std::collections::HashMap;

use abcd_ir::{CallKind, Const, FunctionKind, InstId, Module, Op, UnOp, ValueId};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Reg};
use abcd_lower::regalloc::{RegAlloc, RegSlot};
use abcd_lower::{fusion, isel, lower_function};

use common::{Halt, Machine, V2Builder};

/// Sentinel value fed to a single-parameter function through the ABI top
/// slot (`Reg(num_regs)`).
const PARAM: i64 = 777;

/// A hand-pinned allocation: every value at its given register, no reserved
/// windows/scratches (the shapes here never need them).
fn pinned_alloc(slots: &[(ValueId, u16)], num_regs: u16) -> RegAlloc {
    RegAlloc {
        allocation: slots.iter().map(|&(v, r)| (v, RegSlot::Reg(r))).collect(),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    }
}

/// Run `isel::select` + `layout::layout` over a module's single function
/// with a hand-pinned allocation and suppression (fusion skipped by
/// default — pass a hand-built set for the fusion-declined arms).
fn select_and_layout(
    module: &Module,
    func: abcd_ir::FuncId,
    alloc: &RegAlloc,
    suppression: &fusion::Suppression,
) -> abcd_lower::LayoutResult {
    let rpo = vec![module.functions[func.index()].blocks[0]];
    let selected =
        isel::select(module, func, alloc, &rpo, suppression).expect("selection must succeed");
    abcd_lower::layout::layout(module, func, &selected, alloc, &rpo).expect("layout must succeed")
}

// ── UnOp::Void → ldundefined (isel.rs:1086) ─────────────────────────────

/// es2abc emits `ldundefined` directly for `void x`, so the lift never
/// produces `UnOp::Void`; the arm still lowers it per the vendor semantics.
#[test]
fn void_unop_lowers_to_ldundefined() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p = b.create_param();
        let v = b.emit_val(Op::UnaryOp {
            op: UnOp::Void,
            operand: p,
        });
        b.emit_void(Op::Return { value: Some(v) });
    }
    let result = lower_function(&module, func).expect("void unop must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldundefined)),
        "void x must lower to ldundefined: {:?}",
        result.bytecodes
    );
    let mut machine = Machine::new().with_reg(result.num_regs, PARAM);
    let halt = machine.run(&result.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(common::UNDEFINED),
        "void x returns undefined regardless of x (bytecodes: {:?})",
        result.bytecodes
    );
}

// ── Op::Mov (isel.rs:1093-1105) ─────────────────────────────────────────

/// `Op::Mov` is never produced by the lift ("lowered for robustness"):
/// a used result lowers to a real register `mov`. The source stays live
/// past the copy (a later global store), so the allocator gives the copy
/// its own slot and the `mov` is material.
#[test]
fn mov_op_copies_between_registers() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p = b.create_param();
        let m = b.emit_val(Op::Mov { src: p });
        // Keep the source live past the Mov's definition: distinct slots.
        let name = b.sym("g");
        b.emit_void(Op::StoreGlobal { name, value: p });
        b.emit_void(Op::Return { value: Some(m) });
    }
    let result = lower_function(&module, func).expect("mov must lower");
    let movs = result
        .bytecodes
        .iter()
        .filter(|bc| matches!(bc, Bytecode::Mov(..)))
        .count();
    assert_eq!(
        movs, 2,
        "the copy-in prologue mov plus the Op::Mov copy: {:?}",
        result.bytecodes
    );
    let mut machine = Machine::new().with_reg(result.num_regs, PARAM);
    let halt = machine.run(&result.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(PARAM),
        "the mov must copy the parameter's content (bytecodes: {:?})",
        result.bytecodes
    );
}

/// A dead `Op::Mov` result (no uses) emits nothing at all — the
/// used-guard half of the arm. (The one `mov` in the stream is the
/// parameter copy-in prologue.)
#[test]
fn dead_mov_result_emits_nothing() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p = b.create_param();
        b.emit_val(Op::Mov { src: p });
        b.emit_void(Op::Return { value: None });
    }
    let result = lower_function(&module, func).expect("dead mov must lower");
    assert!(
        !result.bytecodes[1..]
            .iter()
            .any(|bc| matches!(bc, Bytecode::Mov(..))),
        "past the copy-in prologue, a dead Op::Mov must not emit (bytecodes: {:?})",
        result.bytecodes
    );
    let mut machine = Machine::new().with_reg(result.num_regs, PARAM);
    assert_eq!(machine.run(&result.bytecodes), Halt::ReturnUndefined);
}

/// A used `Op::Mov` whose source the allocator co-locates with the result
/// (the source dies at the copy) emits NO `mov` — the identity-copy skip
/// half of the arm.
#[test]
fn co_located_mov_result_emits_no_copy() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p = b.create_param();
        // p is dead after the Mov: the result legally shares its slot.
        let m = b.emit_val(Op::Mov { src: p });
        b.emit_void(Op::Return { value: Some(m) });
    }
    let result = lower_function(&module, func).expect("co-located mov must lower");
    assert_eq!(
        result
            .bytecodes
            .iter()
            .filter(|bc| matches!(bc, Bytecode::Mov(..)))
            .count(),
        1,
        "only the copy-in prologue mov — the identity copy is skipped: {:?}",
        result.bytecodes
    );
    // Behavioral: the shared slot still returns the parameter's content.
    let mut machine = Machine::new().with_reg(result.num_regs, PARAM);
    assert_eq!(machine.run(&result.bytecodes), Halt::Return(PARAM));
}

// ── Op::AllocRegExp (isel.rs:1153-1159) ─────────────────────────────────

/// Corpus regex literals go through `RegExp` construction, so
/// `createregexpwithliteral` never fires there; hand-built IR pins the arm.
#[test]
fn alloc_regexp_emits_createregexpwithliteral() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let pattern;
    {
        let mut b = V2Builder::new(&mut module, func);
        pattern = b.sym("^a+$");
        let r = b.emit_val(Op::AllocRegExp { pattern, flags: 3 });
        b.emit_void(Op::Return { value: Some(r) });
    }
    let result = lower_function(&module, func).expect("regexp alloc must lower");
    let (ic, eid, flags) = result
        .bytecodes
        .iter()
        .find_map(|bc| match bc {
            Bytecode::Createregexpwithliteral(ic, eid, flags) => Some((*ic, *eid, *flags)),
            _ => None,
        })
        .expect("createregexpwithliteral must be emitted");
    assert_eq!(flags, Imm(3));
    assert_eq!(ic, Imm(0), "the first IC slot");
    assert_eq!(
        eid,
        EntityId(pattern.0),
        "the pattern operand is the raw Sym index"
    );
    assert_eq!(
        result.entity_traces[&(EntityKind::StringId, pattern.0)],
        isel::EntityTrace::Traced
    );
}

// ── Op::AllocClosure copy fallback (isel.rs:1194-1204) ─────────────────

/// A non-fused AllocClosure ("never from the lift"): the function object
/// already exists, so the closure result is a plain register copy. The
/// func value stays live past the closure (a later global store), so the
/// closure gets its own slot and the copy is material.
#[test]
fn non_fused_alloc_closure_is_a_register_copy() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p = b.create_param();
        let c = b.emit_val(Op::AllocClosure { func: p });
        // Keep the func value live past the closure's definition.
        let name = b.sym("g");
        b.emit_void(Op::StoreGlobal { name, value: p });
        b.emit_void(Op::Return { value: Some(c) });
    }
    // Fusion declines (the func value is a parameter, not a DefineFunc).
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    assert!(suppression.insts.is_empty() && suppression.values.is_empty());

    let result = lower_function(&module, func).expect("closure copy must lower");
    let movs = result
        .bytecodes
        .iter()
        .filter(|bc| matches!(bc, Bytecode::Mov(..)))
        .count();
    assert_eq!(
        movs, 2,
        "the copy-in prologue mov plus the closure copy: {:?}",
        result.bytecodes
    );
    let mut machine = Machine::new().with_reg(result.num_regs, PARAM);
    assert_eq!(
        machine.run(&result.bytecodes),
        Halt::Return(PARAM),
        "the closure copy must carry the function object (bytecodes: {:?})",
        result.bytecodes
    );
}

/// The same fallback with a dead closure result emits no copy at all.
/// (The one `mov` in the stream is the parameter copy-in prologue.)
#[test]
fn dead_non_fused_alloc_closure_emits_nothing() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p = b.create_param();
        b.emit_val(Op::AllocClosure { func: p });
        b.emit_void(Op::Return { value: None });
    }
    let result = lower_function(&module, func).expect("dead closure must lower");
    assert!(
        !result.bytecodes[1..]
            .iter()
            .any(|bc| matches!(bc, Bytecode::Mov(..))),
        "past the copy-in prologue, a dead closure copy must not emit \
         (bytecodes: {:?})",
        result.bytecodes
    );
}

/// The copy fallback with a RESULT-LESS AllocClosure (hand-built
/// inconsistent input — `V2Builder` always creates the result): the
/// `else if let Some(v) = result` guard declines and nothing emits.
#[test]
fn resultless_alloc_closure_fallback_emits_nothing() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, p);
    {
        let mut b = V2Builder::new(&mut module, func);
        entry = b.entry();
        p = b.create_param();
        b.emit_void(Op::Return { value: None });
    }
    // Splice a result-less AllocClosure in before the Return.
    let iid = InstId::new(module.insts.len() as u32);
    module.insts.push(abcd_ir::Inst {
        op: Op::AllocClosure { func: p },
        result: None,
        block: entry,
        loc: None,
    });
    let block_insts = &mut module.blocks[entry.index()].insts;
    block_insts.insert(block_insts.len() - 1, iid);

    let alloc = pinned_alloc(&[(p, 0)], 1);
    let rpo = vec![entry];
    let selected = isel::select(&module, func, &alloc, &rpo, &fusion::Suppression::default())
        .expect("a result-less AllocClosure must select");
    let codes = &selected.block_codes[0].1;
    // codes[0] is the parameter copy-in prologue mov.
    assert!(
        !codes[1..].iter().any(|bc| matches!(bc, Bytecode::Mov(..)))
            && !codes
                .iter()
                .any(|bc| matches!(bc, Bytecode::Definefunc(..))),
        "a result-less closure emits nothing past the copy-in prologue: {codes:?}"
    );
}

// ── Op::SetObjectWithProto (isel.rs:1234-1241 + ic-slot map :196) ───────

/// `setobjectwithproto imm:u16, v:proto, acc:obj` — two-slot IC, proto in
/// the register operand, object in the accumulator.
#[test]
fn set_object_with_proto_emits_vendor_opcode() {
    const OBJ: i64 = 4242;
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let proto = b.create_param();
        let cobj = b.konst(Const::number(OBJ as f64));
        let obj = b.emit_val(Op::LoadConst(cobj));
        b.emit_void(Op::SetObjectWithProto { proto, obj });
        b.emit_void(Op::Return { value: None });
    }
    let result = lower_function(&module, func).expect("setobjectwithproto must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Setobjectwithproto(..))),
        "expected setobjectwithproto: {:?}",
        result.bytecodes
    );
    let mut machine = Machine::new().with_reg(result.num_regs, PARAM);
    let halt = machine.run(&result.bytecodes);
    assert_eq!(
        halt,
        Halt::SetObjectWithProto {
            proto: PARAM,
            obj: OBJ
        },
        "proto rides the register operand, obj the accumulator (bytecodes: {:?})",
        result.bytecodes
    );
}

// ── Fused by-index property access (isel.rs:1284,1293-1295,1298-1300,1310-1312
//    + ic-slot map :199/:205) ─────────────────────────────────────────────

/// The lift's expansion (`LoadConst(number)` + `LoadPropIdx`) fuses back
/// to `ldobjbyindex imm` when the index is an adjacent single-use integral
/// constant — the real fusion path through `lower_function`.
#[test]
fn fused_load_prop_idx_emits_ldobjbyindex() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let obj = b.create_param();
        let c5 = b.konst(Const::number(5.0));
        let index = b.emit_val(Op::LoadConst(c5));
        let v = b.emit_val(Op::LoadPropIdx { object: obj, index });
        b.emit_void(Op::Return { value: Some(v) });
    }
    let result = lower_function(&module, func).expect("fused ldobjbyindex must lower");
    let imm = result
        .bytecodes
        .iter()
        .find_map(|bc| match bc {
            Bytecode::Ldobjbyindex(_, imm) => Some(*imm),
            _ => None,
        })
        .expect("ldobjbyindex must be emitted");
    assert_eq!(imm, Imm(5), "the fused immediate is the constant index");
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldai(_))),
        "the index constant must be fused away, not loaded: {:?}",
        result.bytecodes
    );
}

/// The store twin: `StorePropIdx` fuses to `stobjbyindex imm, v_obj` when
/// the index const immediately precedes the store (the value is staged
/// earlier — it rides the accumulator).
#[test]
fn fused_store_prop_idx_emits_stobjbyindex() {
    const VAL: i64 = 88;
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let obj = b.create_param();
        let cv = b.konst(Const::number(VAL as f64));
        let value = b.emit_val(Op::LoadConst(cv));
        // The index const is the store's IMMEDIATE predecessor (fusion's
        // adjacency rule).
        let c7 = b.konst(Const::number(7.0));
        let index = b.emit_val(Op::LoadConst(c7));
        b.emit_void(Op::StorePropIdx {
            object: obj,
            index,
            value,
        });
        b.emit_void(Op::Return { value: None });
    }
    let result = lower_function(&module, func).expect("fused stobjbyindex must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Stobjbyindex(_, _, imm) if *imm == Imm(7))),
        "stobjbyindex with the fused immediate 7 must be emitted: {:?}",
        result.bytecodes
    );
}

// ── TryGetGlobal fused-default check (isel.rs:1536-1539) ────────────────

/// The tolerant global load fuses when its default is the shared
/// frame-initial `undefined` constant (NOT a suppressed LoadConst): the
/// `matches!(.. ValueDef::Const .. Undefined)` half of the fused check.
#[test]
fn try_get_global_with_frame_initial_undefined_default_fuses() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let _anchor = b.create_param();
        let dflt = b.create_const_value(Const::Undefined);
        let name = b.sym("Global");
        let v = b.emit_val(Op::TryGetGlobal {
            name,
            default: Some(dflt),
        });
        b.emit_void(Op::Return { value: Some(v) });
    }
    let result = lower_function(&module, func).expect("tryldglobalbyname must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Tryldglobalbyname(..))),
        "a frame-initial undefined default must fuse to tryldglobalbyname: {:?}",
        result.bytecodes
    );
}

// ── Module / misc loaders (isel.rs:1618-1625,1784-1785) ─────────────────

/// `Op::GetModuleNamespace` → `getmodulenamespace imm` (the deprecated
/// source form never reaches the measured lower input).
#[test]
fn get_module_namespace_emits_vendor_opcode() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let ns = b.emit_val(Op::GetModuleNamespace { index: 2 });
        b.emit_void(Op::Return { value: Some(ns) });
    }
    let result = lower_function(&module, func).expect("getmodulenamespace must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Getmodulenamespace(imm) if *imm == Imm(2))),
        "expected getmodulenamespace 2: {:?}",
        result.bytecodes
    );
}

/// `Op::DynamicImport` → `dynamicimport` with the specifier in acc.
#[test]
fn dynamic_import_emits_vendor_opcode() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let spec = b.create_param();
        let p = b.emit_val(Op::DynamicImport { specifier: spec });
        b.emit_void(Op::Return { value: Some(p) });
    }
    let result = lower_function(&module, func).expect("dynamicimport must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Dynamicimport)),
        "expected dynamicimport: {:?}",
        result.bytecodes
    );
}

/// `Op::LoadFunction` → `ldfunction` (es2abc never emits the source form
/// for the corpus shapes).
#[test]
fn load_function_emits_ldfunction() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let f = b.emit_val(Op::LoadFunction);
        b.emit_void(Op::Return { value: Some(f) });
    }
    let result = lower_function(&module, func).expect("ldfunction must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldfunction)),
        "expected ldfunction: {:?}",
        result.bytecodes
    );
}

// ── Iterators (isel.rs:1811-1814, 1829-1833) ────────────────────────────

/// `Op::GetAsyncIterator` → `getasynciterator imm` — the DECISIVE suite-mix
/// arm: the lift arm IS corpus-covered (for-await fixtures) but the gated
/// corpus lower oracle is absent from the measured run.
#[test]
fn get_async_iterator_emits_vendor_opcode() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let obj = b.create_param();
        let it = b.emit_val(Op::GetAsyncIterator { obj });
        b.emit_void(Op::Return { value: Some(it) });
    }
    let result = lower_function(&module, func).expect("getasynciterator must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Getasynciterator(_))),
        "expected getasynciterator: {:?}",
        result.bytecodes
    );
}

/// `Op::IteratorReturn` (v0.1's CloseIterator) → `closeiterator imm, v`.
#[test]
fn iterator_return_emits_closeiterator() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let it = b.create_param();
        let r = b.emit_val(Op::IteratorReturn { iterator: it });
        b.emit_void(Op::Return { value: Some(r) });
    }
    let result = lower_function(&module, func).expect("closeiterator must lower");
    let home = result
        .bytecodes
        .iter()
        .find_map(|bc| match bc {
            Bytecode::Closeiterator(_, Reg(r)) => Some(*r),
            _ => None,
        })
        .expect("closeiterator must be emitted");
    assert_eq!(
        home, 0,
        "the iterator operand is the single parameter's home v0 (bytecodes: {:?})",
        result.bytecodes
    );
}

// ── Exception arms (isel.rs:1937-1943, 1969-1971) ───────────────────────

/// `Op::ThrowUndefinedIfHole` → `throw.undefinedifhole v_name, v_value`
/// (two register operands, no acc traffic). The corpus TDZ checks always
/// use the with-name form, so this two-register form is corpus-dark.
#[test]
fn throw_undefined_if_hole_emits_two_register_form() {
    const NAME: i64 = 11;
    const VALUE: i64 = 22;
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let cn = b.konst(Const::number(NAME as f64));
        let name = b.emit_val(Op::LoadConst(cn));
        let cv = b.konst(Const::number(VALUE as f64));
        let value = b.emit_val(Op::LoadConst(cv));
        b.emit_void(Op::ThrowUndefinedIfHole { name, value });
        b.emit_void(Op::Return { value: None });
    }
    let result = lower_function(&module, func).expect("throw.undefinedifhole must lower");
    let halt = Machine::new().run(&result.bytecodes);
    assert_eq!(
        halt,
        Halt::ThrowUndefinedIfHole {
            name: NAME,
            value: VALUE
        },
        "v1 = name value, v2 = checked value (bytecodes: {:?})",
        result.bytecodes
    );
}

/// `Op::ThrowDeleteSuperProperty` → `throw.deletesuperproperty`
/// (es2abc never emits it for the corpus shapes).
#[test]
fn throw_delete_super_property_emits_vendor_opcode() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        b.emit_void(Op::ThrowDeleteSuperProperty);
        b.emit_void(Op::Return { value: None });
    }
    let result = lower_function(&module, func).expect("throw.deletesuperproperty must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::ThrowDeletesuperproperty)),
        "expected throw.deletesuperproperty: {:?}",
        result.bytecodes
    );
}

// ── Call arms (isel.rs:2176, 2286, 2288) ────────────────────────────────

/// A `super(...spread)` call with an EMPTY argument list (hand-built;
/// v0.1's arm takes the `args.is_empty()` fallback to `Reg(0)`).
#[test]
fn super_spread_with_empty_args_falls_back_to_reg0() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let callee = b.create_param();
        let c = b.emit_val(Op::Call {
            callee,
            this: None,
            args: Vec::new(),
            kind: CallKind::SuperSpread,
        });
        b.emit_void(Op::Return { value: Some(c) });
    }
    let result = lower_function(&module, func).expect("supercallspread must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Supercallspread(_, Reg(0)))),
        "an empty super-spread encodes the dead Reg(0) operand: {:?}",
        result.bytecodes
    );
}

/// A `this`-carrying call whose window holds 257 values (this + 256 args)
/// cannot encode argc in the narrow u8 field: `wide.callthisrange`.
#[test]
fn wide_callthisrange_when_the_window_exceeds_u8_argc() {
    const ARGC: usize = 256;
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let callee = b.create_param();
        let this = b.create_param();
        let args: Vec<_> = (0..ARGC)
            .map(|i| {
                let cid = b.konst(Const::number(i as f64));
                b.emit_val(Op::LoadConst(cid))
            })
            .collect();
        let c = b.emit_val(Op::Call {
            callee,
            this: Some(this),
            args,
            kind: CallKind::Dynamic,
        });
        b.emit_void(Op::Return { value: Some(c) });
    }
    let result = lower_function(&module, func).expect("wide.callthisrange must lower");
    abcd_isa::encode(&result.bytecodes).expect("the body must encode");
    let (argc, base) = result
        .bytecodes
        .iter()
        .find_map(|bc| match bc {
            Bytecode::WideCallthisrange(imm, Reg(start)) => Some((*imm, *start)),
            _ => None,
        })
        .expect("wide.callthisrange must be emitted for 256 args + this");
    assert_eq!(argc, Imm(ARGC as i64), "callthisrange argc excludes this");
    assert!(base <= 255, "the window start stays u8-encodable");
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Callthisrange(..))),
        "the narrow form cannot encode argc = {ARGC}"
    );
}

/// A `super(...)` call with explicit arguments past the narrow argc limit:
/// `wide.supercallthisrange`.
#[test]
fn wide_supercallthisrange_when_args_exceed_u8_argc() {
    const ARGC: usize = 256;
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let callee = b.create_param();
        let args: Vec<_> = (0..ARGC)
            .map(|i| {
                let cid = b.konst(Const::number(i as f64));
                b.emit_val(Op::LoadConst(cid))
            })
            .collect();
        let c = b.emit_val(Op::Call {
            callee,
            this: None,
            args,
            kind: CallKind::Super,
        });
        b.emit_void(Op::Return { value: Some(c) });
    }
    let result = lower_function(&module, func).expect("wide.supercallthisrange must lower");
    abcd_isa::encode(&result.bytecodes).expect("the body must encode");
    let (argc, base) = result
        .bytecodes
        .iter()
        .find_map(|bc| match bc {
            Bytecode::WideSupercallthisrange(imm, Reg(start)) => Some((*imm, *start)),
            _ => None,
        })
        .expect("wide.supercallthisrange must be emitted for 256 args");
    assert_eq!(argc, Imm(ARGC as i64));
    assert!(base <= 255, "the window start stays u8-encodable");
}

// ── fused_definefunc_body direct-DefineFunc arm (isel.rs:980) ───────────

/// `DefineMethod` whose `func` operand is a DIRECTLY suppressed
/// `DefineFunc` result (no AllocClosure wrapper — the lift always wraps,
/// so only a hand-built suppression reaches this arm): the method body
/// resolves straight to the DefineFunc's function-table entry.
#[test]
fn define_method_of_directly_fused_definefunc() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    // A second function for the DefineFunc body to reference.
    let body = V2Builder::create_function(&mut module, "g", FunctionKind::Function);
    let (obj, name);
    let definefunc_iid;
    let definefunc_val;
    {
        let mut b = V2Builder::new(&mut module, func);
        obj = b.create_param();
        name = b.sym("m");
        let (iid, val) = b.emit(Op::DefineFunc {
            body,
            captures: Vec::new(),
            length: 1,
        });
        definefunc_iid = iid;
        definefunc_val = val.expect("DefineFunc has a result");
        b.emit_val(Op::DefineMethod {
            object: obj,
            name,
            func: definefunc_val,
            length: 1,
        });
        b.emit_void(Op::Return { value: None });
    }
    // Hand-built suppression: the DefineFunc folds into the DefineMethod
    // (the real fusion analysis suppresses the instruction and its value
    // together; mirror both halves).
    let mut suppression = fusion::Suppression::default();
    suppression.insts.insert(definefunc_iid);
    suppression.values.insert(definefunc_val);

    let alloc = pinned_alloc(&[(obj, 0)], 1);
    let result = select_and_layout(&module, func, &alloc, &suppression);
    let (eid, len) = result
        .bytecodes
        .iter()
        .find_map(|bc| match bc {
            Bytecode::Definemethod(_, eid, len) => Some((*eid, *len)),
            _ => None,
        })
        .expect("definemethod must be emitted for the directly-fused DefineFunc");
    assert_eq!(eid, EntityId(body.0));
    assert_eq!(len, Imm(1));
}

/// Guard rail for the fused-index helper that this file's error battery
/// sibling exercises: a suppressed index defined by an INTEGRAL
/// `LoadConst` recovers the immediate (the `Some` half).
#[test]
fn fused_index_imm_recovers_integral_const() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (obj, index, load);
    {
        let mut b = V2Builder::new(&mut module, func);
        obj = b.create_param();
        let c9 = b.konst(Const::number(9.0));
        index = b.emit_val(Op::LoadConst(c9));
        load = b.emit_val(Op::LoadPropIdx { object: obj, index });
        b.emit_void(Op::Return { value: Some(load) });
    }
    // Hand-built suppression: fold the index VALUE without suppressing the
    // defining instruction (the real fusion analysis suppresses both; the
    // isel helper only consults the VALUE set).
    let mut suppression = fusion::Suppression::default();
    suppression.values.insert(index);

    // The suppressed index's home is never read; color the param and the
    // load result (the `definefunc`-style arms need the same pinning).
    let alloc = pinned_alloc(&[(obj, 0), (load, 1)], 2);
    let rpo = vec![module.functions[func.index()].blocks[0]];
    let selected =
        isel::select(&module, func, &alloc, &rpo, &suppression).expect("selection must succeed");
    let codes = &selected.block_codes[0].1;
    assert!(
        codes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldobjbyindex(_, imm) if *imm == Imm(9))),
        "a suppressed integral const index recovers the imm 9: {codes:?}"
    );
}
