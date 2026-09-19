//! N10 regression: block ordering must be entry-first, unreachable blocks last.
//!
//! `analysis::compute_rpo` used to append never-visited blocks to the DFS
//! post-order and THEN reverse the whole vector. Catch handlers are
//! unreachable in the terminator-successor model (exception dispatch is
//! implicit — no `block_succs` edge), so handlers landed BEFORE the entry
//! block in the "rpo". `lower::layout` flattens the rpo verbatim, which put
//! the handler's bytecodes at the function's pc 0: every lowered function
//! with a try region entered its HANDLER on call. Orchestrator-verified on
//! the lowered 9.0.0.0 local/exception-finally function `f`, which
//! disassembled to handler code at offset 0.
//!
//! The fix reverses the REACHABLE post-order first (entry lands at index 0),
//! then appends the never-visited blocks in stable `func.blocks` order.
//! Handler placement late in the stream is correct: `reconstruct_try_blocks`
//! resolves try/handler offsets from the block-offsets map, not from stream
//! position, and trampolines still append after every real block.

mod common;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::analysis::compute_rpo;
use abcd_ir::builder::IRBuilder;
use abcd_ir::inst::InstData;
use abcd_ir::lower::lower_function;
use abcd_ir::module::{CatchHandler, Module, TryRegion, ValueDef};
use abcd_ir::types::IrType;
use abcd_isa::{Bytecode, Imm};

use common::{Halt, Machine};

/// Value the entry (normal) path computes and returns.
const NORMAL_SENTINEL: i64 = 42;
/// Distinct value the catch handler computes and returns.
const HANDLER_SENTINEL: i64 = 777;

/// Unit-level pin: entry at index 0, unreachable blocks after ALL reachable
/// blocks. Red before the fix (the unreachable `dead` block sorted first).
#[test]
fn compute_rpo_places_entry_first_and_unreachable_blocks_last() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let b1;
    let dead;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        b1 = builder.create_block();
        dead = builder.create_block();
        builder.add_predecessor(b1, entry);
        // entry -> b1; `dead` has no predecessors and no incoming edges.
        builder.emit_void(InstData::Branch { dest: b1 });
        builder.set_insert_block(b1);
        builder.emit_void(InstData::Return { value: None });
        builder.set_insert_block(dead);
        builder.emit_void(InstData::Return { value: None });
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
/// ALL reachable, the fix must not change the ordering at all — the vector
/// is exactly the reversed DFS post-order. Layout flattens rpo verbatim, so
/// an unchanged rpo means byte-identical lowering output.
#[test]
fn compute_rpo_reachable_only_order_is_reverse_post_order() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let (a, b, join);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let cond = builder.emit_val(InstData::LiteralBool(true), IrType::default());
        a = builder.create_block();
        b = builder.create_block();
        join = builder.create_block();
        builder.add_predecessor(a, entry);
        builder.add_predecessor(b, entry);
        builder.add_predecessor(join, a);
        builder.add_predecessor(join, b);
        builder.emit_void(InstData::CondBranch {
            cond,
            true_dest: a,
            false_dest: b,
        });
        builder.set_insert_block(a);
        builder.emit_void(InstData::Branch { dest: join });
        builder.set_insert_block(b);
        builder.emit_void(InstData::Branch { dest: join });
        builder.set_insert_block(join);
        builder.emit_void(InstData::Return { value: None });
    }

    // DFS from entry visits successors in terminator operand order
    // (true_dest a, then false_dest b): post-order = [join, a, b, entry],
    // reversed = [entry, b, a, join]. No unreachable blocks exist, so the
    // fix must reproduce this exact vector.
    let rpo = compute_rpo(&module, func);
    assert_eq!(rpo, vec![entry, b, a, join]);
}

/// The money test: a function with a try region whose handler writes a
/// distinct sentinel must, once lowered, start executing at the ENTRY
/// block's code at pc 0 — not the handler.
#[test]
fn lowered_try_function_executes_entry_code_at_pc0_not_handler() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let handler;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        // Entry (the try body): return the normal sentinel.
        let normal = builder.emit_val(
            InstData::LiteralNumber(NORMAL_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Return {
            value: Some(normal),
        });
        // Catch handler: unreachable in the terminator-successor model —
        // exception dispatch transfers control here implicitly.
        handler = builder.create_block();
        builder.set_insert_block(handler);
        let caught = builder.emit_val(
            InstData::LiteralNumber(HANDLER_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Return {
            value: Some(caught),
        });
    }
    module.func_mut(func).try_regions.push(TryRegion {
        try_blocks: vec![entry],
        catches: vec![CatchHandler {
            type_idx: u32::MAX, // catch-all
            handler_block: handler,
        }],
    });

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

/// Byte-stability guard: lowering a function WITHOUT unreachable blocks must
/// produce byte-identical output before and after the fix. The expected
/// stream below was captured from the pre-fix build of this exact module;
/// layout is untouched and the rpo is unchanged for fully-reachable CFGs, so
/// any drift here means the fix perturbed reachable-only lowering.
#[test]
fn lowering_without_unreachable_blocks_is_byte_identical() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 1);
    let entry = module.func(func).entry_block;

    let p;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let cond = builder.create_func_param(0, IrType::default());
        let a = builder.create_block();
        let b = builder.create_block();
        let join = builder.create_block();
        builder.add_predecessor(a, entry);
        builder.add_predecessor(b, entry);
        builder.add_predecessor(join, a);
        builder.add_predecessor(join, b);
        builder.emit_void(InstData::CondBranch {
            cond,
            true_dest: a,
            false_dest: b,
        });

        builder.set_insert_block(a);
        let x = builder.emit_val(InstData::LiteralNumber(7.0), IrType::default());
        builder.emit_void(InstData::Branch { dest: join });

        builder.set_insert_block(b);
        let y = builder.emit_val(InstData::LiteralNumber(9.0), IrType::default());
        builder.emit_void(InstData::Branch { dest: join });

        builder.set_insert_block(join);
        p = builder.emit_val(InstData::Phi { entries: vec![] }, IrType::default());
        builder.emit_void(InstData::Return { value: Some(p) });

        let phi_inst = match module.value(p).def {
            ValueDef::Inst(inst) => inst,
            _ => unreachable!("phi result must be an instruction result"),
        };
        module.inst_mut(phi_inst).data = InstData::Phi {
            entries: vec![(a, x), (b, y)],
        };
    }

    let result = lower_function(&module, func).expect("diamond must lower");

    // Byte-identical pin (Debug rendering of the flat stream — `Bytecode`
    // has no PartialEq). Re-captured at the B4 acc-as-cache refactor: the
    // acc color and the spill-slot reservation are gone, so this fixture's
    // frame collapsed to ONE register (cond/phi/x/y never interfere and
    // share v0) and the copy-in prologue reads arg slot v1 instead of v3.
    // The instruction SHAPE is unchanged — same blocks, same order.
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
}
