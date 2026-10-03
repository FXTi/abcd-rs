//! c-COV A12: the fusion bail-out arms (fusion.rs). The lift's shapes
//! always satisfy every fusion precondition (adjacent, integral, single-use,
//! `LoadConst` payloads, no captures), so each early-return needs
//! hand-built IR. Every shape here must leave the candidate UNFUSED
//! (empty [`Suppression`]) — and the one end-to-end test pins that a
//! declined define-chain lowers to the unfused `definefunc` + `mov`.
//!
//! The dangling-id guards (fusion.rs:50,54,114,118,182,186) are covered by
//! hand-built modules carrying a dangling block/inst id — the analysis must
//! skip them, never panic.

mod common;

use abcd_ir::{
    BinOp, Const, FuncId, FunctionKind, InstId, Module, Op, Ty, Value, ValueDef, ValueId,
};
use abcd_isa::Bytecode;
use abcd_lower::fusion::{self, Suppression};
use abcd_lower::lower_function;

use common::V2Builder;

/// Build a one-block function from `build` (+ a trailing `return
/// undefined`) and run fusion analysis over it.
fn analyze1(build: impl FnOnce(&mut V2Builder)) -> Suppression {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        build(&mut b);
        b.emit_void(Op::Return { value: None });
    }
    fusion::analyze(&module, &module.functions[func.index()].blocks)
}

/// The shape must have fused NOTHING.
fn assert_unfused(suppression: &Suppression) {
    assert!(
        suppression.insts.is_empty() && suppression.values.is_empty(),
        "a precondition-breaking shape must not be suppressed: {suppression:?}"
    );
}

/// Push a value whose definition site does not exist.
fn dangling_value(b: &mut V2Builder, inst: u32) -> ValueId {
    let v = ValueId::new(b.module.values.len() as u32);
    b.module.values.push(Value {
        def: ValueDef::Inst(InstId::new(inst)),
        ty: Ty::Any,
    });
    v
}

// ── by-index family (LoadConst(number) + LoadPropIdx/StorePropIdx) ──────

/// Index defined by a non-instruction (a parameter): `def_inst` bails
/// (fusion.rs:88,131).
#[test]
fn by_index_bails_when_the_index_is_not_inst_defined() {
    let suppression = analyze1(|b| {
        let p = b.create_param();
        b.emit_val(Op::LoadPropIdx {
            object: p,
            index: p,
        });
    });
    assert_unfused(&suppression);
}

/// The index constant is not ADJACENT to its consumer (fusion.rs:134).
#[test]
fn by_index_bails_when_the_const_is_not_adjacent() {
    let suppression = analyze1(|b| {
        let p = b.create_param();
        let c3 = b.konst(Const::number(3.0));
        let index = b.emit_val(Op::LoadConst(c3));
        b.emit_void(Op::PopLexEnv); // breaks adjacency
        b.emit_val(Op::LoadPropIdx { object: p, index });
    });
    assert_unfused(&suppression);
}

/// The adjacent def is not a LoadConst (fusion.rs:68,137).
#[test]
fn by_index_bails_when_the_def_is_not_a_loadconst() {
    let suppression = analyze1(|b| {
        let p = b.create_param();
        let index = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: p,
            right: p,
        });
        b.emit_val(Op::LoadPropIdx { object: p, index });
    });
    assert_unfused(&suppression);
}

/// The adjacent LoadConst is FRACTIONAL — a by-index immediate is always
/// integral (fusion.rs:140).
#[test]
fn by_index_bails_on_a_fractional_const() {
    let suppression = analyze1(|b| {
        let p = b.create_param();
        let c = b.konst(Const::number(1.5));
        let index = b.emit_val(Op::LoadConst(c));
        b.emit_val(Op::LoadPropIdx { object: p, index });
    });
    assert_unfused(&suppression);
}

/// The index is used twice — the fused immediate would leave the second
/// consumer reading a suppressed home (fusion.rs:100,143). Also covers the
/// `StorePropIdx` pattern arm.
#[test]
fn by_index_bails_on_a_multi_use_index() {
    let suppression = analyze1(|b| {
        let p = b.create_param();
        let c3 = b.konst(Const::number(3.0));
        let index = b.emit_val(Op::LoadConst(c3));
        b.emit_val(Op::LoadPropIdx { object: p, index });
        b.emit_void(Op::StorePropIdx {
            object: p,
            index,
            value: p,
        });
    });
    assert_unfused(&suppression);
}

// ── TryGetGlobal family (LoadConst(undefined) + TryGetGlobal) ───────────

/// The default is not instruction-defined (fusion.rs:155).
#[test]
fn try_get_global_bails_when_the_default_is_not_inst_defined() {
    let suppression = analyze1(|b| {
        let p = b.create_param();
        let name = b.sym("G");
        b.emit_val(Op::TryGetGlobal {
            name,
            default: Some(p),
        });
    });
    assert_unfused(&suppression);
}

/// The default load is not adjacent to the TryGetGlobal (fusion.rs:158).
#[test]
fn try_get_global_bails_when_the_default_is_not_adjacent() {
    let suppression = analyze1(|b| {
        let name = b.sym("G");
        let cu = b.konst(Const::Undefined);
        let dflt = b.emit_val(Op::LoadConst(cu));
        b.emit_void(Op::PopLexEnv); // breaks adjacency
        b.emit_val(Op::TryGetGlobal {
            name,
            default: Some(dflt),
        });
    });
    assert_unfused(&suppression);
}

/// The adjacent default is not an `undefined` const — both halves of
/// `is_undefined_const_load`: a non-LoadConst def (fusion.rs:79) and a
/// non-undefined LoadConst (fusion.rs:161).
#[test]
fn try_get_global_bails_when_the_default_is_not_undefined() {
    // (a) default defined by a non-LoadConst instruction.
    let suppression = analyze1(|b| {
        let p = b.create_param();
        let name = b.sym("G");
        let dflt = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: p,
            right: p,
        });
        b.emit_val(Op::TryGetGlobal {
            name,
            default: Some(dflt),
        });
    });
    assert_unfused(&suppression);

    // (b) default is a LoadConst of a NUMBER (not undefined).
    let suppression = analyze1(|b| {
        let name = b.sym("G");
        let cn = b.konst(Const::number(0.0));
        let dflt = b.emit_val(Op::LoadConst(cn));
        b.emit_val(Op::TryGetGlobal {
            name,
            default: Some(dflt),
        });
    });
    assert_unfused(&suppression);
}

/// The default is used twice (fusion.rs:164).
#[test]
fn try_get_global_bails_on_a_multi_use_default() {
    let suppression = analyze1(|b| {
        let name = b.sym("G");
        let cu = b.konst(Const::Undefined);
        let dflt = b.emit_val(Op::LoadConst(cu));
        b.emit_val(Op::TryGetGlobal {
            name,
            default: Some(dflt),
        });
        // A second use of the same default value.
        b.emit_void(Op::StoreGlobal { name, value: dflt });
    });
    assert_unfused(&suppression);
}

/// The default's defining instruction id is dangling but adjacent in the
/// block list (fusion.rs:76 — plus the dangling-inst skips :54,:118,:186).
#[test]
fn try_get_global_bails_on_a_dangling_default_inst() {
    let suppression = analyze1(|b| {
        let entry = b.entry();
        // The dangling "previous instruction" of the TryGetGlobal.
        b.module.blocks[entry.index()]
            .insts
            .insert(0, InstId::new(999));
        let dflt = dangling_value(b, 999);
        let name = b.sym("G");
        b.emit_val(Op::TryGetGlobal {
            name,
            default: Some(dflt),
        });
    });
    assert_unfused(&suppression);
}

// ── define chains (DefineFunc + AllocClosure [+ DefineMethod]) ──────────

/// DefineMethod whose func is not instruction-defined (fusion.rs:202).
#[test]
fn define_chain_bails_when_the_closure_is_not_inst_defined() {
    let suppression = analyze1(|b| {
        let p = b.create_param();
        let name = b.sym("m");
        b.emit_val(Op::DefineMethod {
            object: p,
            name,
            func: p,
            length: 1,
        });
    });
    assert_unfused(&suppression);
}

/// DefineMethod whose AllocClosure is not adjacent (fusion.rs:205).
#[test]
fn define_chain_bails_when_the_closure_is_not_adjacent() {
    let suppression = analyze1(|b| {
        let p = b.create_param();
        let closure = b.emit_val(Op::AllocClosure { func: p });
        b.emit_void(Op::PopLexEnv); // breaks adjacency
        let name = b.sym("m");
        b.emit_val(Op::DefineMethod {
            object: p,
            name,
            func: closure,
            length: 1,
        });
    });
    assert_unfused(&suppression);
}

/// DefineMethod whose closure value's defining instruction is dangling but
/// adjacent (fusion.rs:208).
#[test]
fn define_chain_bails_on_a_dangling_closure_inst() {
    let suppression = analyze1(|b| {
        let entry = b.entry();
        b.module.blocks[entry.index()]
            .insts
            .insert(0, InstId::new(999));
        let p = b.create_param();
        let closure = dangling_value(b, 999);
        let name = b.sym("m");
        b.emit_val(Op::DefineMethod {
            object: p,
            name,
            func: closure,
            length: 1,
        });
    });
    assert_unfused(&suppression);
}

/// DefineMethod whose adjacent func producer is not an AllocClosure
/// (fusion.rs:211).
#[test]
fn define_chain_bails_when_the_func_producer_is_not_a_closure() {
    let suppression = analyze1(|b| {
        let p = b.create_param();
        let c1 = b.konst(Const::number(1.0));
        let notclosure = b.emit_val(Op::LoadConst(c1));
        let name = b.sym("m");
        b.emit_val(Op::DefineMethod {
            object: p,
            name,
            func: notclosure,
            length: 1,
        });
    });
    assert_unfused(&suppression);
}

/// DefineMethod whose closure has a second use (fusion.rs:214): the
/// DefineMethod cannot fold the chain — but the inner
/// DefineFunc+AllocClosure pair still fuses on its own (the closure result
/// is suppressed, never the multi-used DefineFunc boundary the method
/// needed).
#[test]
fn define_chain_bails_on_a_multi_use_closure() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (df, closure);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p = b.create_param();
        df = b.emit_val(Op::DefineFunc {
            body: FuncId::new(0),
            captures: Vec::new(),
            length: 0,
        });
        closure = b.emit_val(Op::AllocClosure { func: df });
        let name = b.sym("m");
        b.emit_val(Op::DefineMethod {
            object: p,
            name,
            func: closure,
            length: 1,
        });
        // A second use of the closure value.
        b.emit_void(Op::StoreGlobal {
            name,
            value: closure,
        });
        b.emit_void(Op::Return { value: None });
    }
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    assert!(
        !suppression.values.contains(&closure),
        "a multi-used closure must not be suppressed into DefineMethod"
    );
    assert!(
        suppression.values.contains(&df),
        "the inner DefineFunc still fuses into the AllocClosure"
    );
}

/// AllocClosure whose func is not instruction-defined (fusion.rs:224).
#[test]
fn define_chain_bails_when_the_definefunc_is_not_inst_defined() {
    let suppression = analyze1(|b| {
        let p = b.create_param();
        b.emit_val(Op::AllocClosure { func: p });
    });
    assert_unfused(&suppression);
}

/// AllocClosure whose DefineFunc id is dangling (fusion.rs:228).
#[test]
fn define_chain_bails_on_a_dangling_definefunc_inst() {
    let suppression = analyze1(|b| {
        let df = dangling_value(b, 999);
        b.emit_val(Op::AllocClosure { func: df });
    });
    assert_unfused(&suppression);
}

/// AllocClosure whose adjacent func producer is not a DefineFunc
/// (fusion.rs:231).
#[test]
fn define_chain_bails_when_the_func_producer_is_not_a_definefunc() {
    let suppression = analyze1(|b| {
        let c1 = b.konst(Const::number(1.0));
        let notdf = b.emit_val(Op::LoadConst(c1));
        b.emit_val(Op::AllocClosure { func: notdf });
    });
    assert_unfused(&suppression);
}

/// A DefineFunc with explicit captures has no vendor encoding — fusion
/// declines (fusion.rs:234) and the standalone DefineFunc arm hard-errors
/// at isel (covered in lower_errors.rs).
#[test]
fn define_chain_bails_on_explicit_captures() {
    let suppression = analyze1(|b| {
        let p = b.create_param();
        let cap = b.sym("captured");
        let df = b.emit_val(Op::DefineFunc {
            body: FuncId::new(0),
            captures: vec![(cap, p)],
            length: 0,
        });
        b.emit_val(Op::AllocClosure { func: df });
    });
    assert_unfused(&suppression);
}

/// A DefineFunc with a second use cannot fold (fusion.rs:237).
#[test]
fn define_chain_bails_on_a_multi_use_definefunc() {
    let suppression = analyze1(|b| {
        let name = b.sym("g");
        let df = b.emit_val(Op::DefineFunc {
            body: FuncId::new(0),
            captures: Vec::new(),
            length: 0,
        });
        b.emit_val(Op::AllocClosure { func: df });
        // A second use of the DefineFunc value.
        b.emit_void(Op::StoreGlobal { name, value: df });
    });
    assert_unfused(&suppression);
}

/// A DefineFunc separated from its closure by another instruction
/// (fusion.rs:247) — and the declined chain lowers UNFUSED end to end:
/// standalone `definefunc`, with the closure as a register copy of the
/// function object (here an IDENTITY copy — the allocator co-locates the
/// closure with the DefineFunc result whose live range ends at the
/// closure, so no `mov` is emitted; the disjoint-slot form is pinned in
/// lower_op_arms.rs).
#[test]
fn define_chain_bails_when_not_adjacent_and_lowers_unfused() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let body = V2Builder::create_function(&mut module, "g", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let df = b.emit_val(Op::DefineFunc {
            body,
            captures: Vec::new(),
            length: 0,
        });
        b.emit_void(Op::PopLexEnv); // breaks adjacency
        let closure = b.emit_val(Op::AllocClosure { func: df });
        b.emit_void(Op::Return {
            value: Some(closure),
        });
    }
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    assert_unfused(&suppression);

    let result = lower_function(&module, func).expect("the unfused chain must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Definefunc(..))),
        "the standalone DefineFunc emits definefunc: {:?}",
        result.bytecodes
    );
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Return)),
        "the closure value is returned: {:?}",
        result.bytecodes
    );
}

// ── dangling guards (fusion.rs:50,114,182) ──────────────────────────────

/// A dangling block id in the function's block list is skipped by all
/// three analysis walks (use-counts, by-index/TryGetGlobal, define-chain).
#[test]
fn dangling_block_in_the_block_list_is_skipped() {
    let suppression = {
        let mut module = Module::new();
        let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
        {
            let mut b = V2Builder::new(&mut module, func);
            b.emit_void(Op::Return { value: None });
            b.module.functions[func.index()]
                .blocks
                .push(abcd_ir::BlockId::new(999));
        }
        fusion::analyze(&module, &module.functions[func.index()].blocks)
    };
    assert_unfused(&suppression);
}
