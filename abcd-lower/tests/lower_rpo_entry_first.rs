//! N10 regression (v0.2 port of `abcd-ir/tests/lower_rpo_entry_first.rs`):
//! block ordering must be entry-first, unreachable blocks last.
//!
//! Catch handlers are unreachable in the terminator-successor model
//! (exception dispatch is implicit — no `block_succs` edge). The rpo
//! reverses the REACHABLE post-order first (entry lands at index 0), then
//! appends the never-visited blocks in stable `func.blocks` order.

mod common;

use abcd_ir2::{Catch, Edge, EdgeKind, FunctionKind, Module, Op, TryRegion, ValueDef};
use abcd_isa::{Bytecode, Imm};
use abcd_lower::analysis::compute_rpo;
use abcd_lower::lower_function;

use common::{Halt, Machine, V2Builder};

/// Value the entry (normal) path computes and returns.
const NORMAL_SENTINEL: i64 = 42;
/// Distinct value the catch handler computes and returns.
const HANDLER_SENTINEL: i64 = 777;

/// Unit-level pin: entry at index 0, unreachable blocks after ALL reachable
/// blocks.
#[test]
fn compute_rpo_places_entry_first_and_unreachable_blocks_last() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, b1, dead);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        b1 = builder.create_block();
        dead = builder.create_block();
        builder.add_predecessor(b1, entry);
        // entry -> b1; `dead` has no predecessors and no incoming edges.
        builder.emit_void(Op::Branch { dest: b1 });
        builder.set_insert_block(b1);
        builder.emit_void(Op::Return { value: None });
        builder.set_insert_block(dead);
        builder.emit_void(Op::Return { value: None });
    }

    let rpo = compute_rpo(&module, func);
    assert_eq!(rpo.len(), 3, "rpo must contain every block: {rpo:?}");
    assert_eq!(
        rpo[0], entry,
        "entry block must be at index 0 (got {rpo:?})"
    );
    let pos = |b| rpo.iter().position(|&x| x == b).unwrap();
    assert!(
        pos(entry) < pos(dead) && pos(b1) < pos(dead),
        "the unreachable block must come after ALL reachable blocks (got {rpo:?})"
    );
}

/// Byte-stability anchor at the rpo level: for a function whose blocks are
/// ALL reachable, the ordering is exactly the reversed DFS post-order.
#[test]
fn compute_rpo_reachable_only_order_is_reverse_post_order() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, a, b, join);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        let cid = builder.konst(abcd_ir2::Const::Bool(true));
        let cond = builder.emit_val(Op::LoadConst(cid));
        a = builder.create_block();
        b = builder.create_block();
        join = builder.create_block();
        builder.add_predecessor(a, entry);
        builder.add_predecessor(b, entry);
        builder.add_predecessor(join, a);
        builder.add_predecessor(join, b);
        builder.emit_void(Op::CondBranch {
            cond,
            true_dest: a,
            false_dest: b,
        });
        builder.set_insert_block(a);
        builder.emit_void(Op::Branch { dest: join });
        builder.set_insert_block(b);
        builder.emit_void(Op::Branch { dest: join });
        builder.set_insert_block(join);
        builder.emit_void(Op::Return { value: None });
    }

    // DFS from entry visits successors in terminator operand order
    // (true_dest a, then false_dest b): post-order = [join, a, b, entry],
    // reversed = [entry, b, a, join].
    let rpo = compute_rpo(&module, func);
    assert_eq!(rpo, vec![entry, b, a, join]);
}

/// The money test: a function with a try region whose handler writes a
/// distinct sentinel must, once lowered, start executing at the ENTRY
/// block's code at pc 0 — not the handler.
#[test]
fn lowered_try_function_executes_entry_code_at_pc0_not_handler() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, handler);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        // Entry (the try body): return the normal sentinel.
        let cn = builder.konst(abcd_ir2::Const::number(NORMAL_SENTINEL as f64));
        let normal = builder.emit_val(Op::LoadConst(cn));
        builder.emit_void(Op::Return {
            value: Some(normal),
        });
        // Catch handler: unreachable in the terminator-successor model.
        handler = builder.create_block();
        builder.add_exceptional_predecessor(handler, entry);
        let exception = builder.create_exception_param(handler);
        builder.set_insert_block(handler);
        let ch = builder.konst(abcd_ir2::Const::number(HANDLER_SENTINEL as f64));
        let caught = builder.emit_val(Op::LoadConst(ch));
        builder.emit_void(Op::Return {
            value: Some(caught),
        });
        module.functions[func.index()].try_regions.push(TryRegion {
            protected: vec![entry],
            catches: vec![Catch {
                handler,
                exception,
                type_idx: None,
            }],
        });
    }

    let result = lower_function(&module, func).expect("try function must lower");

    // pc 0 is the entry block's first instruction — the normal sentinel
    // load, NOT the handler's.
    assert!(
        matches!(&result.bytecodes[0], Bytecode::Ldai(Imm(v)) if *v == NORMAL_SENTINEL),
        "pc 0 must be the entry block's code, got {:?}",
        result.bytecodes
    );

    // Normal path simulates from pc 0 to completion with the entry's value.
    let halt = Machine::new().run(&result.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(NORMAL_SENTINEL),
        "calling the function must run the entry path (bytecodes: {:?})",
        result.bytecodes
    );

    // Structural: the handler lies after all reachable code, and the
    // reconstructed TryBlock covers exactly the try blocks — the handler
    // range is excluded from the try range and resolved by offset.
    let handler_pc = result
        .bytecodes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Ldai(Imm(v)) if *v == HANDLER_SENTINEL))
        .expect("handler sentinel load must be present");
    assert_eq!(result.try_blocks.len(), 1, "{:?}", result.try_blocks);
    let tb = &result.try_blocks[0];
    assert_eq!(tb.start, 0, "try region starts at the entry block");
    assert_eq!(
        tb.start as usize + tb.len as usize,
        handler_pc,
        "try range must cover exactly the try blocks (handler range excluded)"
    );
    assert_eq!(tb.catches.len(), 1, "{:?}", tb.catches);
    assert_eq!(tb.catches[0].type_idx, u32::MAX);
    assert_eq!(
        tb.catches[0].handler as usize, handler_pc,
        "catch entry must resolve to the handler's flat offset"
    );
    assert_eq!(
        tb.catches[0].handler as usize + tb.catches[0].len as usize,
        result.bytecodes.len(),
        "the handler is the last block in the stream (no trampolines in this fixture)"
    );

    // Handler semantics: simulating exception dispatch (entering at the
    // catch offset) yields the handler's sentinel.
    let halt = Machine::new().run_at(&result.bytecodes, handler_pc);
    assert_eq!(
        halt,
        Halt::Return(HANDLER_SENTINEL),
        "the handler path must return its own sentinel (bytecodes: {:?})",
        result.bytecodes
    );
}

/// Faithfulness pin: the diamond shape below must produce exactly the same
/// flat stream as the v0.1 pipeline produces for the same shape (captured
/// in v0.1's test suite at the B4 acc-as-cache refactor): the frame
/// collapses to ONE register (cond/phi/x/y never interfere and share v0)
/// and the copy-in prologue reads arg slot v1.
#[test]
fn reachable_only_diamond_matches_v0_1_byte_shape() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, p);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        let cond = builder.create_param();
        let a = builder.create_block();
        let b = builder.create_block();
        let join = builder.create_block();
        builder.add_predecessor(a, entry);
        builder.add_predecessor(b, entry);
        builder.add_predecessor(join, a);
        builder.add_predecessor(join, b);
        builder.emit_void(Op::CondBranch {
            cond,
            true_dest: a,
            false_dest: b,
        });

        builder.set_insert_block(a);
        let c7 = builder.konst(abcd_ir2::Const::number(7.0));
        let x = builder.emit_val(Op::LoadConst(c7));
        builder.emit_void(Op::Branch { dest: join });

        builder.set_insert_block(b);
        let c9 = builder.konst(abcd_ir2::Const::number(9.0));
        let y = builder.emit_val(Op::LoadConst(c9));
        builder.emit_void(Op::Branch { dest: join });

        builder.set_insert_block(join);
        let normal = |from: abcd_ir2::BlockId| Edge {
            from,
            kind: EdgeKind::Normal,
        };
        p = builder.emit_val(Op::Phi {
            entries: vec![(normal(a), x), (normal(b), y)],
        });
        builder.emit_void(Op::Return { value: Some(p) });
    }

    let result = lower_function(&module, func).expect("diamond must lower");

    // Byte-shape pin (Debug rendering — `Bytecode` has no PartialEq). This
    // is the exact stream v0.1's pipeline produces for this shape.
    let rendered = format!("{:?}", result.bytecodes);
    let expected = "[Bytecode(mov v0 v1), Bytecode(lda v0), Bytecode(jnez label_6), \
Bytecode(ldai 9), Bytecode(sta v0), Bytecode(jmp label_9), Bytecode(ldai 7), \
Bytecode(sta v0), Bytecode(jmp label_9), Bytecode(lda v0), Bytecode(return)]";
    assert_eq!(rendered, expected, "reachable-only lowering output drifted");

    // This fixture has phi copies on the two join edges but no CondBranch
    // predecessor copies, so no trampolines are emitted; the stream ends in
    // the join block's Return.
    assert!(
        matches!(result.bytecodes.last(), Some(Bytecode::Return)),
        "expected no trampolines in this fixture: {:?}",
        result.bytecodes
    );
    let _ = ValueDef::Param(0u16);
}
