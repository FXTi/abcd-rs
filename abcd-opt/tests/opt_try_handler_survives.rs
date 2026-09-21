//! N11 regression (v0.2 port of v0.1 `opt_try_handler_survives.rs`): the
//! optimizer's unreachable-block removal must preserve catch handlers.
//!
//! In the v0.2 IR the invariant is structural (T5): catch handlers are
//! reached through first-class `EdgeKind::Exceptional` edges sourced from
//! the function's `TryRegion`s. `remove_unreachable_blocks` and
//! `rebuild_predecessors` must use the AUGMENTED successor relation
//! (`abcd_opt::analysis::augmented_succs`) — a terminator-only BFS
//! deletes every catch handler and silently drops the exceptional
//! control-flow path.

mod common;

use abcd_file::{AccessFlags, Builder, CatchBlockDef, File, Type};
use abcd_ir::verify_module;
use abcd_ir::{BlockId, Edge, EdgeKind, FuncId, FunctionKind, Module, Op};
use abcd_isa::{Bytecode, Imm, Label, encode as encode_bytecodes};
use abcd_lift::lift_file;
use abcd_lower::lower_function;
use abcd_opt::optimize_module;

use common::{Halt, Machine, V2Builder};

/// Value the entry (normal) path computes and returns.
const NORMAL_SENTINEL: i64 = 42;
/// Distinct value the catch handler computes and returns.
const HANDLER_SENTINEL: i64 = 777;

/// Build a module whose only function returns `NORMAL_SENTINEL` on the
/// normal path, has a catch-all handler returning `HANDLER_SENTINEL`
/// (unreachable in the terminator-successor model), plus one genuinely
/// dead block referenced by nothing. Returns (module, func, entry,
/// handler, dead).
fn build_try_module() -> (Module, FuncId, BlockId, BlockId, BlockId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let entry;
    let handler;
    let dead;
    {
        let mut b = V2Builder::new(&mut module, func);
        entry = b.entry();
        // Entry (the try body): return the normal sentinel.
        let normal = b.emit_number(NORMAL_SENTINEL as f64);
        b.emit_void(Op::Return {
            value: Some(normal),
        });
        // Catch handler: no terminator-level incoming edges — exception
        // dispatch transfers control here implicitly.
        handler = b.create_block();
        b.set_insert_block(handler);
        let caught = b.emit_number(HANDLER_SENTINEL as f64);
        b.emit_void(Op::Return {
            value: Some(caught),
        });
        // Genuinely dead block: no edges, not protected by any try region.
        dead = b.create_block();
        b.set_insert_block(dead);
        let junk = b.emit_number(-1.0);
        b.emit_void(Op::Return { value: Some(junk) });

        b.add_try(vec![entry], handler);
    }
    (module, func, entry, handler, dead)
}

/// Unit-level pin of the augmented successor relation: terminator
/// successors plus, for every try region protecting the block, each
/// catch handler as an Exceptional edge. Unprotected blocks see no
/// exception edges.
#[test]
fn augmented_succs_adds_handler_edges_only_to_protected_blocks() {
    let (module, func, entry, handler, dead) = build_try_module();

    let entry_succs = abcd_opt::analysis::augmented_succs(&module, func, entry);
    assert_eq!(
        entry_succs,
        vec![(handler, EdgeKind::Exceptional)],
        "the protected entry block (terminator: Return, no terminator successors) \
         must see the catch handler as a successor"
    );
    assert!(
        abcd_opt::analysis::augmented_succs(&module, func, handler).is_empty(),
        "the handler itself is not protected: terminator successors only (none)"
    );
    assert!(
        abcd_opt::analysis::augmented_succs(&module, func, dead).is_empty(),
        "the dead block is not protected: terminator successors only (none)"
    );
}

/// The core N11 red test: after the full optimizer pipeline, the catch
/// handler block must still exist and the try region must still reference
/// it.
#[test]
fn optimize_preserves_catch_handler_and_try_region() {
    let (mut module, func, entry, handler, _dead) = build_try_module();

    optimize_module(&mut module);

    let func_data = module.func(func).unwrap();
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
        region.protected.contains(&entry),
        "try region must still protect the entry block: {region:?}"
    );
    assert_eq!(
        region.catches.len(),
        1,
        "catch entry pruned with its handler (N11): {region:?}"
    );
    assert_eq!(region.catches[0].type_idx, None);
    assert_eq!(
        region.catches[0].handler, handler,
        "try region must still reference the handler block: {region:?}"
    );

    // The handler's code survives: its sentinel literal feeds its Return.
    let handler_block = &module.blocks[handler.index()];
    assert!(
        handler_block.insts.iter().any(|&id| matches!(
            &module.insts[id.index()].op,
            Op::LoadConst(cid) if module.consts.get(*cid).and_then(abcd_ir::Const::as_f64)
                == Some(HANDLER_SENTINEL as f64)
        )),
        "handler sentinel instruction must survive: {:?}",
        handler_block.insts
    );
    assert!(
        handler_block
            .insts
            .last()
            .is_some_and(|&id| module.insts[id.index()].op.is_terminator()),
        "handler must still end with a terminator"
    );

    let report = verify_module(&module);
    assert!(
        report.is_ok(),
        "optimized module with try region must verify: {:?}",
        report.errors
    );
}

/// Dead-code sanity pin: genuinely dead NON-handler blocks are still
/// removed by the same pass that now preserves handlers.
#[test]
fn optimize_still_removes_genuinely_dead_blocks() {
    let (mut module, func, _entry, handler, dead) = build_try_module();

    optimize_module(&mut module);

    let func_data = module.func(func).unwrap();
    assert!(
        !func_data.blocks.contains(&dead),
        "genuinely dead block must still be removed: blocks={:?}",
        func_data.blocks
    );
    assert!(
        func_data.blocks.contains(&handler),
        "handler is not dead — exception edges keep it reachable (N11)"
    );

    let report = verify_module(&module);
    assert!(report.is_ok(), "module must verify: {:?}", report.errors);
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
        .map(|i| FuncId::new(i as u32))
        .find(|&f| module.sym.resolve(module.func(f).unwrap().name) == Some(name))
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
/// live at the point of exception) as Exceptional edges. `distinct`
/// selects whether the phi carries DIFFERENT values for `a` and `b`
/// (merge unsound) or the SAME value (merge exception-neutral). Returns
/// (module, func, a, b, handler).
fn build_merge_candidate_module(distinct: bool) -> (Module, FuncId, BlockId, BlockId, BlockId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let a;
    let b;
    let handler;
    {
        let mut bd = V2Builder::new(&mut module, func);
        a = bd.create_block();
        b = bd.create_block();
        let c = bd.create_block();
        handler = bd.create_block();

        bd.add_predecessor(a, bd.entry());
        bd.add_predecessor(b, a);
        bd.add_predecessor(c, b);

        bd.emit_void(Op::Branch { dest: a });

        bd.set_insert_block(a);
        let va = bd.emit_number(1.0);
        bd.emit_void(Op::Branch { dest: b });

        bd.set_insert_block(b);
        let vb = if distinct { bd.emit_number(2.0) } else { va };
        bd.emit_void(Op::Branch { dest: c });

        bd.set_insert_block(c);
        bd.emit_void(Op::Return { value: None });

        bd.set_insert_block(handler);
        let exc = |from: BlockId| Edge {
            from,
            kind: EdgeKind::Exceptional,
        };
        let phi = bd.emit_val(Op::Phi {
            entries: vec![(exc(a), va), (exc(b), vb)],
        });
        bd.emit_void(Op::Return { value: Some(phi) });

        bd.add_try(vec![a, b], handler);
    }
    (module, func, a, b, handler)
}

/// Merge guard (negative): protected blocks whose handler phi entries
/// carry DIFFERENT values must not merge — the absorbed block's entry is
/// dropped by rebuild_predecessors, so merging would lose the value live
/// at the point of exception (and leave a phi/pred arity mismatch).
#[test]
fn merge_blocked_when_handler_phi_values_differ() {
    let (mut module, func, a, b, handler) = build_merge_candidate_module(true);
    let pre = verify_module(&module);
    assert!(pre.is_ok(), "fixture must verify pre-opt: {:?}", pre.errors);

    optimize_module(&mut module);

    let func_data = module.func(func).unwrap();
    assert!(
        func_data.blocks.contains(&a) && func_data.blocks.contains(&b),
        "protected blocks with distinct handler-phi values must not merge: {:?}",
        func_data.blocks
    );
    assert!(func_data.blocks.contains(&handler));
    let report = verify_module(&module);
    assert!(report.is_ok(), "post-opt verify: {:?}", report.errors);
}

/// Merge guard (positive): protected blocks with IDENTICAL region
/// membership whose handler phi entries carry the SAME value merge
/// cleanly — the surviving entry preserves the value, the region is
/// re-keyed onto the merged block, and verification passes.
#[test]
fn merge_allowed_when_handler_phi_values_agree() {
    let (mut module, func, a, b, handler) = build_merge_candidate_module(false);
    let pre = verify_module(&module);
    assert!(pre.is_ok(), "fixture must verify pre-opt: {:?}", pre.errors);

    optimize_module(&mut module);

    let func_data = module.func(func).unwrap();
    assert!(
        func_data.blocks.contains(&a) && !func_data.blocks.contains(&b),
        "exception-neutral merge should absorb b into a: {:?}",
        func_data.blocks
    );
    assert!(func_data.blocks.contains(&handler));
    assert_eq!(
        func_data.try_regions[0].protected,
        vec![a],
        "region must be re-keyed onto the merged block: {:?}",
        func_data.try_regions
    );
    let report = verify_module(&module);
    assert!(report.is_ok(), "post-opt verify: {:?}", report.errors);
}

/// E2E red test: lift a real try/catch file → optimize → lower. The
/// handler's bytecodes must exist in the flat output, and the
/// reconstructed TryBlock/catch entries must match the handler's flat
/// offset.
#[test]
fn lifted_try_function_optimized_lowers_with_handler() {
    let file = build_try_file();
    let mut module = lift_file(&file).expect("try file must lift");
    let func = func_by_name(&module, "f");

    assert_eq!(
        module.func(func).unwrap().try_regions.len(),
        1,
        "lift must produce one try region: {:?}",
        module.func(func).unwrap().try_regions
    );

    optimize_module(&mut module);

    let report = verify_module(&module);
    assert!(
        report.is_ok(),
        "optimized lifted module must verify: {:?}",
        report.errors
    );
    assert_eq!(
        module.func(func).unwrap().try_regions.len(),
        1,
        "try region must survive the optimizer: {:?}",
        module.func(func).unwrap().try_regions
    );
    assert_eq!(
        module.func(func).unwrap().try_regions[0].catches.len(),
        1,
        "catch entry must survive the optimizer (N11): {:?}",
        module.func(func).unwrap().try_regions
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
