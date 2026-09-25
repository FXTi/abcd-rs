//! Hand-built IR module scaffolding for the taint mechanism/probe tests
//! (verbatim from `abcd-taint/tests/common/mod.rs`; mirrors
//! `abcd-analysis`'s cfg(test)-private testutil — duplicated because that
//! one is not public).
//!
//! Kept separate from [`super::decompile_scaffold`]: the two look similar
//! but diverge semantically — here `add_param` takes an explicit index
//! and `add` stores `left`/`right` verbatim.

// Each test binary uses a different subset.
#![allow(dead_code)]

use abcd_ir::consts::Const;
use abcd_ir::function::{Block, Catch, FunctionData, Inst, TryRegion, Value};
use abcd_ir::module::{ClassData, FunctionKind, Modifiers, SourceLang};
use abcd_ir::ty::Ty;
use abcd_ir::{
    BlockId, ClassId, ConstId, Edge, EdgeKind, FuncId, InstId, Loc, Module, Op, Sym, ValueDef,
    ValueId,
};

/// A module with one empty class record (the function home).
pub fn mk_module() -> Module {
    let mut m = Module::new();
    let name = m.sym.intern("Ltest;");
    m.classes.push(ClassData {
        descriptor: name,
        name,
        modifiers: Modifiers::NONE,
        source_lang: SourceLang::EcmaScript,
        super_class: None,
        interfaces: Vec::new(),
        fields: Vec::new(),
        methods: Vec::new(),
        annotations: Vec::new(),
        source_file: None,
    });
    m
}

/// A fresh named function with one (entry) block, wired into class 0.
pub fn add_func_named(m: &mut Module, name: &str) -> FuncId {
    let name = m.sym.intern(name);
    let id = FuncId::new(m.functions.len() as u32);
    m.functions.push(FunctionData::new(
        ClassId::new(0),
        name,
        FunctionKind::Function,
    ));
    m.classes[0].methods.push(id);
    add_block(m, id); // entry
    id
}

/// A fresh empty block appended to `f`.
pub fn add_block(m: &mut Module, f: FuncId) -> BlockId {
    let id = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(id);
    id
}

/// Append an instruction without wiring a result, with a location.
pub fn push_inst_loc(m: &mut Module, b: BlockId, op: Op, loc: Option<Loc>) -> InstId {
    let id = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op,
        result: None,
        block: b,
        loc,
    });
    m.block_mut(b).unwrap().insts.push(id);
    id
}

/// Append an instruction without wiring a result.
pub fn push_inst(m: &mut Module, b: BlockId, op: Op) -> InstId {
    push_inst_loc(m, b, op, None)
}

/// Append an op that produces a value; returns the result value.
pub fn emit(m: &mut Module, b: BlockId, op: Op) -> ValueId {
    emit_loc(m, b, op, None)
}

/// Append an op with a location that produces a value; returns the
/// result value.
pub fn emit_loc(m: &mut Module, b: BlockId, op: Op, loc: Option<Loc>) -> ValueId {
    assert!(op.has_result());
    let inst = push_inst_loc(m, b, op, loc);
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Inst(inst),
        ty: Ty::Any,
    });
    m.inst_mut(inst).unwrap().result = Some(val);
    val
}

/// Append an op that produces no value; returns the instruction.
pub fn emit_void(m: &mut Module, b: BlockId, op: Op) -> InstId {
    assert!(!op.has_result());
    push_inst(m, b, op)
}

/// Append an op with a location that produces no value.
pub fn emit_void_loc(m: &mut Module, b: BlockId, op: Op, loc: Option<Loc>) -> InstId {
    assert!(!op.has_result());
    push_inst_loc(m, b, op, loc)
}

/// Append a parameter value (`params[0]` = `this` by convention).
pub fn add_param(m: &mut Module, f: FuncId, idx: u16) -> ValueId {
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Param(idx),
        ty: Ty::Any,
    });
    m.func_mut(f).unwrap().params.push(val);
    val
}

/// Append the exception-parameter value delivered at a handler entry.
pub fn add_exception_param(m: &mut Module, handler: BlockId) -> ValueId {
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::ExceptionParam(handler),
        ty: Ty::Any,
    });
    val
}

/// Record a Normal edge (on the successor side, as the IR stores them).
pub fn link(m: &mut Module, from: BlockId, to: BlockId) {
    m.block_mut(to).unwrap().preds.push(Edge {
        from,
        kind: EdgeKind::Normal,
    });
}

/// Add a try region protecting `protected` with a single catch-all
/// handler.
pub fn add_try(m: &mut Module, f: FuncId, protected: Vec<BlockId>, handler: BlockId, exc: ValueId) {
    for &p in &protected {
        m.block_mut(handler).unwrap().preds.push(Edge {
            from: p,
            kind: EdgeKind::Exceptional,
        });
    }
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected,
        catches: vec![Catch {
            handler,
            exception: exc,
            type_idx: None,
        }],
    });
}

/// The entry block of `f`.
pub fn entry_of(m: &Module, f: FuncId) -> BlockId {
    m.func(f).unwrap().blocks[0]
}

/// `left + right`.
pub fn add(m: &mut Module, b: BlockId, l: ValueId, r: ValueId) -> ValueId {
    emit(
        m,
        b,
        Op::BinaryOp {
            op: abcd_ir::BinOp::Add,
            left: l,
            right: r,
        },
    )
}

/// A number literal load.
pub fn load_number(m: &mut Module, b: BlockId, x: f64) -> ValueId {
    let c = m.consts.push(Const::number(x));
    emit(m, b, Op::LoadConst(c))
}

/// A string literal load; returns the value.
pub fn load_string(m: &mut Module, b: BlockId, s: &str) -> ValueId {
    let sym = m.sym.intern(s);
    let c = m.consts.push(Const::String(sym));
    emit(m, b, Op::LoadConst(c))
}

/// Intern a name.
pub fn intern(m: &mut Module, s: &str) -> Sym {
    m.sym.intern(s)
}

/// An `AllocObject` site.
pub fn alloc_object(m: &mut Module, b: BlockId) -> ValueId {
    let shape = m.consts.push(Const::ObjectLiteral {
        keys: Vec::new(),
        values: Vec::new(),
    });
    emit(m, b, Op::AllocObject { shape })
}

/// An `AllocArray` site (empty array).
pub fn alloc_array(m: &mut Module, b: BlockId) -> ValueId {
    emit(m, b, Op::AllocArray { shape: None })
}

/// `TryGetGlobal(name)` (no default).
pub fn try_get_global(m: &mut Module, b: BlockId, name: &str) -> ValueId {
    let sym = intern(m, name);
    emit(
        m,
        b,
        Op::TryGetGlobal {
            name: sym,
            default: None,
        },
    )
}

/// The ConstId of a pushed constant (for odd test needs).
pub fn push_const(m: &mut Module, c: Const) -> ConstId {
    m.consts.push(c)
}
