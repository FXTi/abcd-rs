//! Dominator agreement on crafted CFGs (gate 5, non-corpus half):
//! `abcd_analysis::control::Dominators` vs the verbatim port of
//! `abcd-ir::verify`'s private iterative dominator computation
//! (`tests/common`), over hand-built shapes: diamonds, loops, nested
//! loops, self-loops, try/handler (exceptional predecessors are not
//! Normal edges), dead code, and jump-into-loop.

mod common;

use abcd_ir::function::{Block, Catch, FunctionData, Inst, TryRegion, Value};
use abcd_ir::module::{ClassData, FunctionKind, Modifiers, SourceLang};
use abcd_ir::ty::Ty;
use abcd_ir::{
    BlockId, ClassId, Const, Edge, EdgeKind, FuncId, InstId, Module, Op, ValueDef, ValueId,
};

// ── Minimal module builders (integration tests can't use the crate's
//    #[cfg(test)] scaffolding) ─────────────────────────────────────────

fn mk_module() -> Module {
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

fn add_func(m: &mut Module) -> FuncId {
    let name = m.sym.intern("f");
    let id = FuncId::new(m.functions.len() as u32);
    m.functions.push(FunctionData::new(
        ClassId::new(0),
        name,
        FunctionKind::Function,
    ));
    id
}

fn add_block(m: &mut Module, f: FuncId) -> BlockId {
    let id = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(id);
    id
}

fn term(m: &mut Module, b: BlockId, op: Op) -> InstId {
    let id = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op,
        result: None,
        block: b,
        loc: None,
    });
    m.block_mut(b).unwrap().insts.push(id);
    id
}

fn link(m: &mut Module, from: BlockId, to: BlockId) {
    m.block_mut(to).unwrap().preds.push(Edge {
        from,
        kind: EdgeKind::Normal,
    });
}

fn add_try(m: &mut Module, f: FuncId, protected: Vec<BlockId>, handler: BlockId) {
    for &p in &protected {
        m.block_mut(handler).unwrap().preds.push(Edge {
            from: p,
            kind: EdgeKind::Exceptional,
        });
    }
    let exc = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::ExceptionParam(handler),
        ty: Ty::Any,
    });
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected,
        catches: vec![Catch {
            handler,
            exception: exc,
            type_idx: None,
        }],
    });
}

fn bool_const(m: &mut Module, v: bool) -> ValueId {
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Const(m.consts.push(Const::Bool(v))),
        ty: Ty::Any,
    });
    val
}

// ── Crafted shapes ─────────────────────────────────────────────────────

/// Diamond + join + exit.
#[test]
fn agreement_diamond() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = add_block(&mut m, f);
    let a = add_block(&mut m, f);
    let b = add_block(&mut m, f);
    let join = add_block(&mut m, f);

    let cond = bool_const(&mut m, true);
    term(
        &mut m,
        entry,
        Op::CondBranch {
            cond,
            true_dest: a,
            false_dest: b,
        },
    );
    term(&mut m, a, Op::Branch { dest: join });
    term(&mut m, b, Op::Branch { dest: join });
    term(&mut m, join, Op::Return { value: None });
    link(&mut m, entry, a);
    link(&mut m, entry, b);
    link(&mut m, a, join);
    link(&mut m, b, join);

    assert_eq!(common::check_function(&m, f, "crafted").0, 4);
}

/// Nested loops with two back edges and an exit from the outer latch.
#[test]
fn agreement_nested_loops() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = add_block(&mut m, f);
    let outer = add_block(&mut m, f);
    let inner = add_block(&mut m, f);
    let inner_back = add_block(&mut m, f);
    let outer_back = add_block(&mut m, f);
    let exit = add_block(&mut m, f);

    let c1 = bool_const(&mut m, true);
    let c2 = bool_const(&mut m, false);
    term(&mut m, entry, Op::Branch { dest: outer });
    term(&mut m, outer, Op::Branch { dest: inner });
    term(
        &mut m,
        inner,
        Op::CondBranch {
            cond: c1,
            true_dest: inner_back,
            false_dest: outer_back,
        },
    );
    term(&mut m, inner_back, Op::Branch { dest: inner });
    term(
        &mut m,
        outer_back,
        Op::CondBranch {
            cond: c2,
            true_dest: outer,
            false_dest: exit,
        },
    );
    term(&mut m, exit, Op::Return { value: None });
    link(&mut m, entry, outer);
    link(&mut m, outer, inner);
    link(&mut m, inner, inner_back);
    link(&mut m, inner_back, inner);
    link(&mut m, inner, outer_back);
    link(&mut m, outer_back, outer);
    link(&mut m, outer_back, exit);

    let (compared, _, total) = common::check_function(&m, f, "crafted");
    assert_eq!((compared, total), (6, 6));
}

/// Try/handler: the handler's only predecessors are Exceptional, so it is
/// unreachable over the Normal relation and excluded from the agreement
/// domain — the contract's boundary case.
#[test]
fn agreement_try_handler() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    let exit = add_block(&mut m, f);

    term(&mut m, entry, Op::Branch { dest: exit });
    term(&mut m, handler, Op::Return { value: None });
    term(&mut m, exit, Op::Return { value: None });
    link(&mut m, entry, exit);
    add_try(&mut m, f, vec![entry], handler);

    let (compared, _, total) = common::check_function(&m, f, "crafted");
    assert_eq!(
        (compared, total),
        (2, 3),
        "entry + exit only; the handler is Normal-unreachable"
    );
}

/// Dead code after the exit: unreachable blocks are excluded.
#[test]
fn agreement_dead_blocks() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = add_block(&mut m, f);
    let dead = add_block(&mut m, f);
    term(&mut m, entry, Op::Return { value: None });
    term(&mut m, dead, Op::Branch { dest: dead });
    link(&mut m, dead, dead);

    let (compared, _, _) = common::check_function(&m, f, "crafted");
    assert_eq!(compared, 1, "only the entry is Normal-reachable");
}

/// A self-loop at the entry plus an exit path.
#[test]
fn agreement_self_loop_entry() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let cond = bool_const(&mut m, true);
    term(
        &mut m,
        entry,
        Op::CondBranch {
            cond,
            true_dest: entry,
            false_dest: exit,
        },
    );
    term(&mut m, exit, Op::Return { value: None });
    link(&mut m, entry, entry);
    link(&mut m, entry, exit);

    assert_eq!(common::check_function(&m, f, "crafted").0, 2);
}

/// An irreducible shape: a jump into a loop body from outside its header
/// (entry → header, entry → body, header ⇄ body, body → exit).
#[test]
fn agreement_jump_into_loop() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = add_block(&mut m, f);
    let header = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let exit = add_block(&mut m, f);

    let c1 = bool_const(&mut m, true);
    let c2 = bool_const(&mut m, false);
    term(
        &mut m,
        entry,
        Op::CondBranch {
            cond: c1,
            true_dest: header,
            false_dest: body,
        },
    );
    term(&mut m, header, Op::Branch { dest: body });
    term(
        &mut m,
        body,
        Op::CondBranch {
            cond: c2,
            true_dest: header,
            false_dest: exit,
        },
    );
    term(&mut m, exit, Op::Return { value: None });
    link(&mut m, entry, header);
    link(&mut m, entry, body);
    link(&mut m, header, body);
    link(&mut m, body, header);
    link(&mut m, body, exit);

    assert_eq!(common::check_function(&m, f, "crafted").0, 4);
}
