//! N11 regression: the optimizer's unreachable-block removal must preserve
//! catch handlers.
//!
//! `opt::dce::remove_unreachable_blocks` BFSes from the entry following
//! TERMINATOR successors only (`block_succs`). Catch handlers have no
//! terminator-level incoming edges — exception dispatch is implicit — so
//! the pass deleted EVERY catch handler of every optimized function with a
//! try region and pruned the `try_regions` accordingly, silently deleting
//! the exceptional control-flow path. P3-T8 probe: the opt variant of
//! newtarget-this `func_main_0` lost the original's catchall entirely.
//!
//! Fix: reachability uses the augmented successor relation
//! (`analysis::augmented_succs`: terminator successors + try→handler
//! exception edges), the same relation the S6 fix added to regalloc
//! liveness.

mod common;

use abcd_file::{AccessFlags, Builder, CatchBlockDef, File, FileType, FunctionKind, Type, Version};
use abcd_ir::analysis::augmented_succs;
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::{Block, FuncId};
use abcd_ir::inst::InstData;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::lower_function;
use abcd_ir::module::{CatchHandler, Module, TryRegion};
use abcd_ir::opt::optimize_module;
use abcd_ir::types::IrType;
use abcd_ir::verify::verify_module;
use abcd_isa::{Bytecode, Imm, Label, encode as encode_bytecodes};

use common::{Halt, Machine};

/// Value the entry (normal) path computes and returns.
const NORMAL_SENTINEL: i64 = 42;
/// Distinct value the catch handler computes and returns.
const HANDLER_SENTINEL: i64 = 777;

/// Build a module whose only function returns `NORMAL_SENTINEL` on the
/// normal path, has a catch-all handler returning `HANDLER_SENTINEL`
/// (unreachable in the terminator-successor model), plus one genuinely
/// dead block referenced by nothing. Returns (module, func, entry,
/// handler, dead).
fn build_try_module() -> (Module, FuncId, Block, Block, Block) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let handler;
    let dead;
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
        // Catch handler: no terminator-level incoming edges — exception
        // dispatch transfers control here implicitly.
        handler = builder.create_block();
        builder.set_insert_block(handler);
        let caught = builder.emit_val(
            InstData::LiteralNumber(HANDLER_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Return {
            value: Some(caught),
        });
        // Genuinely dead block: no edges, not protected by any try region.
        dead = builder.create_block();
        builder.set_insert_block(dead);
        let junk = builder.emit_val(InstData::LiteralNumber(-1.0), IrType::default());
        builder.emit_void(InstData::Return { value: Some(junk) });
    }
    module.func_mut(func).try_regions.push(TryRegion {
        try_blocks: vec![entry],
        catches: vec![CatchHandler {
            type_idx: u32::MAX, // catch-all
            handler_block: handler,
        }],
    });
    (module, func, entry, handler, dead)
}

/// Unit-level pin of the augmented successor relation: terminator
/// successors plus, for every try region protecting the block, each
/// catch handler. Unprotected blocks see no exception edges.
#[test]
fn augmented_succs_adds_handler_edges_only_to_protected_blocks() {
    let (module, func, entry, handler, dead) = build_try_module();

    let entry_succs = augmented_succs(&module, func, entry);
    assert_eq!(
        entry_succs,
        vec![handler],
        "the protected entry block (terminator: Return, no terminator successors) \
         must see the catch handler as a successor"
    );
    assert!(
        augmented_succs(&module, func, handler).is_empty(),
        "the handler itself is not protected: terminator successors only (none)"
    );
    assert!(
        augmented_succs(&module, func, dead).is_empty(),
        "the dead block is not protected: terminator successors only (none)"
    );
}

/// The core N11 red test: after the full optimizer pipeline, the catch
/// handler block must still exist and the try region must still reference
/// it. Today the handler is deleted and the catch entry pruned.
#[test]
fn optimize_preserves_catch_handler_and_try_region() {
    let (mut module, func, entry, handler, _dead) = build_try_module();

    optimize_module(&mut module);

    let func_data = module.func(func);
    assert!(
        func_data.blocks.contains(&handler),
        "catch handler block deleted by the optimizer (N11): blocks={:?}",
        func_data.blocks
    );
    assert_eq!(
        func_data.try_regions.len(),
        1,
        "try region must survive: {:?}",
        func_data.try_regions
    );
    let region = &func_data.try_regions[0];
    assert!(
        region.try_blocks.contains(&entry),
        "try region must still protect the entry block: {region:?}"
    );
    assert_eq!(
        region.catches.len(),
        1,
        "catch entry pruned with its handler (N11): {region:?}"
    );
    assert_eq!(region.catches[0].type_idx, u32::MAX);
    assert_eq!(
        region.catches[0].handler_block, handler,
        "try region must still reference the handler block: {region:?}"
    );

    // The handler's code survives: its sentinel literal feeds its Return.
    let handler_block = module.block(handler);
    assert!(
        handler_block.insts.iter().any(|&id| matches!(
            &module.inst(id).data,
            InstData::LiteralNumber(n) if *n == HANDLER_SENTINEL as f64
        )),
        "handler sentinel instruction must survive: {:?}",
        handler_block.insts
    );
    assert!(
        handler_block
            .insts
            .last()
            .is_some_and(|&id| module.inst(id).data.is_terminator()),
        "handler must still end with a terminator"
    );

    let errors = verify_module(&module);
    assert!(
        errors.is_empty(),
        "optimized module with try region must verify: {errors:?}"
    );
}

/// Dead-code sanity pin: genuinely dead NON-handler blocks are still
/// removed by the same pass that now preserves handlers.
#[test]
fn optimize_still_removes_genuinely_dead_blocks() {
    let (mut module, func, _entry, handler, dead) = build_try_module();

    optimize_module(&mut module);

    let func_data = module.func(func);
    assert!(
        !func_data.blocks.contains(&dead),
        "genuinely dead block must still be removed: blocks={:?}",
        func_data.blocks
    );
    assert!(
        func_data.blocks.contains(&handler),
        "handler is not dead — exception edges keep it reachable (N11)"
    );

    let errors = verify_module(&module);
    assert!(errors.is_empty(), "module must verify: {errors:?}");
}

/// Build a 12.x file whose global class carries one static method `f`:
///
/// ```text
/// 0: ldai 42        ; try body
/// 1: jmp 4          ; normal path skips the handler
/// 2: ldai 777       ; catch-all handler
/// 3: return         ; handler return
/// 4: return         ; normal return (acc = 42)
/// ```
///
/// with a try region covering instructions 0..2 and a catch-all handler
/// at instruction 2 (try metadata uses instruction BYTE offsets).
fn build_try_file() -> File {
    let mut builder = Builder::new();
    builder.set_api(12, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let code_seq = [
        Bytecode::Ldai(Imm(NORMAL_SENTINEL)),
        Bytecode::Jmp(Label(4)),
        Bytecode::Ldai(Imm(HANDLER_SENTINEL)),
        Bytecode::Return,
        Bytecode::Return,
    ];
    let (bytes, offsets) = encode_bytecodes(&code_seq).unwrap();
    // Try blocks attach via a separate CodeHandle (inline code would
    // orphan); see abcd-file's encode path for the same pattern.
    let method = builder.class_add_method(class, "f", proto, AccessFlags::STATIC, &[], 0, 0);
    let code = builder.create_code(&bytes, 0, 0);
    builder.code_add_try_block(
        code,
        offsets[0],
        offsets[2] - offsets[0],
        &[CatchBlockDef {
            type_class: None, // catch-all
            handler_pc: offsets[2],
            code_size: offsets[4] - offsets[2],
        }],
    );
    builder.method_set_code(method, code);
    builder.deduplicate();
    abcd_file::decode(&builder.finalize().unwrap()).unwrap()
}

fn func_by_name(module: &Module, name: &str) -> FuncId {
    (0..module.functions.len())
        .map(FuncId::from_index)
        .find(|&f| module.strings.get(module.func(f).name) == name)
        .unwrap_or_else(|| panic!("function {name}"))
}

/// Build a module exercising CFG-merge candidacy across a try region:
///
/// ```text
/// entry -> a -> b -> c(Return)
/// region R protects [a, b]; handler h ends in `Return(phi)`.
/// ```
///
/// The handler phi is keyed by the individual protected blocks (the value
/// live at the point of exception). `distinct` selects whether the phi
/// carries DIFFERENT values for `a` and `b` (merge unsound) or the SAME
/// value (merge exception-neutral). Returns (module, func, a, b, handler).
fn build_merge_candidate_module(distinct: bool) -> (Module, FuncId, Block, Block, Block) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let a;
    let b;
    let handler;
    let phi;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        a = builder.create_block();
        b = builder.create_block();
        let c = builder.create_block();
        handler = builder.create_block();

        builder.add_predecessor(a, entry);
        builder.add_predecessor(b, a);
        builder.add_predecessor(c, b);
        builder.add_predecessor(handler, a);
        builder.add_predecessor(handler, b);

        builder.emit_void(InstData::Branch { dest: a });

        builder.set_insert_block(a);
        let va = builder.emit_val(InstData::LiteralNumber(1.0), IrType::default());
        builder.emit_void(InstData::Branch { dest: b });

        builder.set_insert_block(b);
        let vb = if distinct {
            builder.emit_val(InstData::LiteralNumber(2.0), IrType::default())
        } else {
            va
        };
        builder.emit_void(InstData::Branch { dest: c });

        builder.set_insert_block(c);
        builder.emit_void(InstData::Return { value: None });

        builder.set_insert_block(handler);
        phi = builder.emit_val(
            InstData::Phi {
                entries: vec![(a, va), (b, vb)],
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(phi) });
    }
    module.func_mut(func).try_regions.push(TryRegion {
        try_blocks: vec![a, b],
        catches: vec![CatchHandler {
            type_idx: u32::MAX,
            handler_block: handler,
        }],
    });
    let _ = phi;
    (module, func, a, b, handler)
}

/// Merge guard (negative): protected blocks whose handler phi entries
/// carry DIFFERENT values must not merge — the absorbed block's entry is
/// dropped by rebuild_predecessors, so merging would lose the value live
/// at the point of exception (and leave a phi/pred arity mismatch).
#[test]
fn merge_blocked_when_handler_phi_values_differ() {
    let (mut module, func, a, b, handler) = build_merge_candidate_module(true);
    assert!(
        verify_module(&module).is_empty(),
        "fixture must verify pre-opt: {:?}",
        verify_module(&module)
    );

    optimize_module(&mut module);

    let func_data = module.func(func);
    assert!(
        func_data.blocks.contains(&a) && func_data.blocks.contains(&b),
        "protected blocks with distinct handler-phi values must not merge: {:?}",
        func_data.blocks
    );
    assert!(func_data.blocks.contains(&handler));
    let errors = verify_module(&module);
    assert!(errors.is_empty(), "post-opt verify: {errors:?}");
}

/// Merge guard (positive): protected blocks with IDENTICAL region
/// membership whose handler phi entries carry the SAME value merge
/// cleanly — the surviving entry preserves the value, the region is
/// re-keyed onto the merged block, and verification passes.
#[test]
fn merge_allowed_when_handler_phi_values_agree() {
    let (mut module, func, a, b, handler) = build_merge_candidate_module(false);
    assert!(verify_module(&module).is_empty());

    optimize_module(&mut module);

    let func_data = module.func(func);
    assert!(
        func_data.blocks.contains(&a) && !func_data.blocks.contains(&b),
        "exception-neutral merge should absorb b into a: {:?}",
        func_data.blocks
    );
    assert!(func_data.blocks.contains(&handler));
    assert_eq!(
        func_data.try_regions[0].try_blocks,
        vec![a],
        "region must be re-keyed onto the merged block: {:?}",
        func_data.try_regions
    );
    let errors = verify_module(&module);
    assert!(errors.is_empty(), "post-opt verify: {errors:?}");
}

/// E2E red test: lift a real try/catch file → optimize → lower. The
/// handler's bytecodes must exist in the flat output, and the
/// reconstructed TryBlock/catch entries must match the handler's flat
/// offset (structural assertions reused from lower_rpo_entry_first.rs).
/// Today the optimizer deletes the handler, so the lowered function has
/// no handler code and no catch entry at all.
#[test]
fn lifted_try_function_optimized_lowers_with_handler() {
    let file = build_try_file();
    let mut module = lift_file(&file).expect("try file must lift");
    let func = func_by_name(&module, "f");

    assert_eq!(
        module.func(func).try_regions.len(),
        1,
        "lift must produce one try region: {:?}",
        module.func(func).try_regions
    );

    optimize_module(&mut module);

    let errors = verify_module(&module);
    assert!(
        errors.is_empty(),
        "optimized lifted module must verify: {errors:?}"
    );
    assert_eq!(
        module.func(func).try_regions.len(),
        1,
        "try region must survive the optimizer: {:?}",
        module.func(func).try_regions
    );
    assert_eq!(
        module.func(func).try_regions[0].catches.len(),
        1,
        "catch entry must survive the optimizer (N11): {:?}",
        module.func(func).try_regions
    );

    let result = lower_function(&module, func).expect("optimized try function must lower");

    // The handler's sentinel load is present in the flat stream.
    let handler_pc = result
        .bytecodes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Ldai(Imm(v)) if *v == HANDLER_SENTINEL))
        .expect("handler bytecodes must survive optimize+lower (N11)");

    // Structural: the reconstructed TryBlock covers exactly the try code
    // and its catch entry resolves to the handler's flat offset. The
    // normal-path return block sits between the try body and the handler
    // (CFG merges must not cross try-region boundaries — that would
    // change exception-dispatch ranges), so the try range ends before
    // the handler.
    assert_eq!(result.try_blocks.len(), 1, "{:?}", result.try_blocks);
    let tb = &result.try_blocks[0];
    assert_eq!(tb.start, 0, "try region starts at the entry block");
    assert!(
        (tb.start + tb.len) as usize <= handler_pc,
        "try range must exclude the handler range (try: {tb:?}, handler pc: {handler_pc})"
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

    // Semantics: normal path from pc 0 returns the normal sentinel;
    // simulated exception dispatch (entering at the catch offset) returns
    // the handler's sentinel.
    let halt = Machine::new().run(&result.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(NORMAL_SENTINEL),
        "normal path must return its sentinel (bytecodes: {:?})",
        result.bytecodes
    );
    let halt = Machine::new().run_at(&result.bytecodes, handler_pc);
    assert_eq!(
        halt,
        Halt::Return(HANDLER_SENTINEL),
        "handler path must return its sentinel (bytecodes: {:?})",
        result.bytecodes
    );
}
