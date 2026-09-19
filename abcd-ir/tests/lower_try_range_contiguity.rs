//! N43 regression: reconstructed try ranges must cover ONLY protected
//! instructions — no contiguity assumption over the flattened (RPO) order.
//!
//! `lower::layout::reconstruct_try_blocks` used to emit ONE
//! `[min_start, max_end)` span per try region, implicitly assuming the
//! region's blocks are contiguous in the flattened stream. `compute_rpo`
//! gives no such guarantee: an unprotected block can interleave between two
//! protected blocks (shape: `try { if (c) return 1; } catch {…}; o.p` — the
//! after-try block sorts BETWEEN the protected entry and the protected
//! return block in RPO). The single span then covers the unprotected block,
//! and an exception raised there misdispatches to the region's handler:
//! the VM scans try blocks linearly and dispatches to the first range
//! containing the throw pc (vendored
//! arkcompiler_ets_runtime-master/ecmascript/method.cpp:86-107,
//! `Method::FindCatchBlock`).
//!
//! Fix: emit ONE TryBlock PER contiguous RUN of protected blocks, each
//! carrying the region's catch entries. The panda format stores a vector of
//! try blocks per code item (vendored
//! abcd-file-sys/vendor/libpandafile/file_items.h:1370-1373,1426 —
//! `CodeItem::AddTryBlock` / `std::vector<TryBlock> try_blocks_`), our
//! encode path emits one entry per model TryBlock
//! (abcd-file/src/encode.rs:1313-1348), and decode enumerates every try
//! block independently (abcd-file/src/decode.rs:1790-1839), so multiple
//! same-catch ranges round-trip. Contiguous regions still coalesce into a
//! single `[min_start, max_end)` span — byte-identical to the pre-N43
//! output for every corpus fixture whose regions were already contiguous.

mod common;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::inst::InstData;
use abcd_ir::lower::lower_function;
use abcd_ir::module::{CatchHandler, Module, TryRegion};
use abcd_ir::types::IrType;
use abcd_isa::{Bytecode, Imm};

use common::{Halt, Machine};

/// Distinct first-instruction sentinels used to locate each block's extent
/// in the flattened stream.
const ENTRY_SENTINEL: i64 = 10;
const UNPROTECTED_SENTINEL: i64 = 20;
const PROTECTED_SENTINEL: i64 = 30;
const HANDLER_SENTINEL: i64 = 70;

/// Find the index of the (unique) `Ldai(v)` in the flat stream.
fn find_ldai(bytecodes: &[Bytecode], v: i64) -> usize {
    bytecodes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Ldai(Imm(x)) if *x == v))
        .unwrap_or_else(|| panic!("ldai {v} must be present: {bytecodes:?}"))
}

/// True when instruction index `pc` lies inside any emitted try range —
/// exactly the containment test the VM's `FindCatchBlock` performs
/// (`start_pc <= pc && start_pc + length > pc`, method.cpp:99).
fn dispatches(try_blocks: &[abcd_file::TryBlock], pc: usize) -> bool {
    try_blocks
        .iter()
        .any(|tb| (tb.start as usize) <= pc && pc < (tb.start + tb.len) as usize)
}

/// The red shape: an unprotected after-try block interleaves between two
/// protected blocks in RPO.
///
/// ```text
/// entry  (PROTECTED):   ldai 10; istrue; jnez t1 / fallthrough t2
/// t2     (UNPROTECTED): ldai 20; return            <- RPO puts it BETWEEN
/// t1     (PROTECTED):   ldai 30; return               entry and t1
/// h      (handler):     ldai 70; return
/// ```
///
/// RPO = [entry, t2, t1, h]: the DFS visits true_dest t1 first, so t1
/// precedes t2 in post-order and t2 precedes t1 after the reverse. The try
/// region protects {entry, t1}; t2 is the after-try code.
///
/// Red evidence (pre-fix): the single `[0, t1_end)` span covers every t2
/// instruction, so `dispatches(tb, pc)` is true for the unprotected block.
#[test]
fn try_ranges_exclude_interleaved_unprotected_block() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let (t1, t2, h);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        t1 = builder.create_block();
        t2 = builder.create_block();
        h = builder.create_block();

        builder.add_predecessor(t1, entry);
        builder.add_predecessor(t2, entry);

        // entry (protected): branch to protected t1 or unprotected t2.
        let x = builder.emit_val(
            InstData::LiteralNumber(ENTRY_SENTINEL as f64),
            IrType::default(),
        );
        let cond = builder.emit_val(InstData::IsTrue { operand: x }, IrType::default());
        builder.emit_void(InstData::CondBranch {
            cond,
            true_dest: t1,
            false_dest: t2,
        });

        // t2 (UNPROTECTED after-try code).
        builder.set_insert_block(t2);
        let u = builder.emit_val(
            InstData::LiteralNumber(UNPROTECTED_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(u) });

        // t1 (protected early return).
        builder.set_insert_block(t1);
        let p = builder.emit_val(
            InstData::LiteralNumber(PROTECTED_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(p) });

        // Catch handler (unreachable in the terminator-successor model).
        builder.set_insert_block(h);
        let caught = builder.emit_val(
            InstData::LiteralNumber(HANDLER_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Return {
            value: Some(caught),
        });
    }
    module.func_mut(func).try_regions.push(TryRegion {
        try_blocks: vec![entry, t1],
        catches: vec![CatchHandler {
            type_idx: u32::MAX, // catch-all
            handler_block: h,
        }],
    });

    let result = lower_function(&module, func).expect("try function must lower");

    // Locate block extents in the flat stream via the sentinel loads.
    let entry_start = find_ldai(&result.bytecodes, ENTRY_SENTINEL);
    let t2_start = find_ldai(&result.bytecodes, UNPROTECTED_SENTINEL);
    let t1_start = find_ldai(&result.bytecodes, PROTECTED_SENTINEL);
    let h_start = find_ldai(&result.bytecodes, HANDLER_SENTINEL);
    assert!(
        entry_start < t2_start && t2_start < t1_start && t1_start < h_start,
        "the fixture requires the interleaving RPO [entry, t2, t1, h]: {:?}",
        result.bytecodes
    );

    // N43 core assertion — the VM dispatch test: no instruction of the
    // UNPROTECTED block [t2_start, t1_start) may lie inside any try range.
    for pc in t2_start..t1_start {
        assert!(
            !dispatches(&result.try_blocks, pc),
            "N43: unprotected after-try instruction at pc {pc} is covered by \
             a try range — an exception there would misdispatch to the \
             handler (try_blocks: {:?}, bytecodes: {:?})",
            result.try_blocks,
            result.bytecodes
        );
    }

    // The protected blocks must still be covered in full.
    for pc in entry_start..t2_start {
        assert!(
            dispatches(&result.try_blocks, pc),
            "protected entry instruction at pc {pc} lost its try coverage"
        );
    }
    for pc in t1_start..h_start {
        assert!(
            dispatches(&result.try_blocks, pc),
            "protected return-block instruction at pc {pc} lost its try coverage"
        );
    }

    // The handler itself must NOT be covered by any try range.
    for pc in h_start..result.bytecodes.len() {
        assert!(
            !dispatches(&result.try_blocks, pc),
            "handler instruction at pc {pc} must not be covered by the try range"
        );
    }

    // The non-contiguous region must be emitted as TWO try blocks, one per
    // contiguous run, each carrying the region's catch entry pointing at
    // the handler offset.
    assert_eq!(
        result.try_blocks.len(),
        2,
        "one TryBlock per contiguous run of protected blocks: {:?}",
        result.try_blocks
    );
    for tb in &result.try_blocks {
        assert_eq!(tb.catches.len(), 1, "{tb:?}");
        assert_eq!(tb.catches[0].type_idx, u32::MAX, "{tb:?}");
        assert_eq!(
            tb.catches[0].handler as usize, h_start,
            "every run must dispatch to the region's handler"
        );
    }

    // Normal-path behavior is unchanged: cond is truthy → protected t1
    // returns its sentinel.
    let halt = Machine::new().run(&result.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(PROTECTED_SENTINEL),
        "bytecodes: {:?}",
        result.bytecodes
    );
}

/// Contiguity preservation: when a region's blocks ARE contiguous in the
/// flat stream, the runs coalesce into exactly one `[min_start, max_end)`
/// TryBlock — byte-identical to the pre-N43 single-span output. This is
/// what keeps every corpus fixture with contiguous regions (all of them
/// today) byte-stable.
#[test]
fn contiguous_region_still_emits_single_span() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let (a, after, h);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        a = builder.create_block();
        after = builder.create_block();
        h = builder.create_block();

        builder.add_predecessor(a, entry);
        builder.add_predecessor(after, a);

        // entry (protected) -> a (protected) -> after (unprotected).
        let _x = builder.emit_val(
            InstData::LiteralNumber(ENTRY_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Branch { dest: a });

        builder.set_insert_block(a);
        let _p = builder.emit_val(
            InstData::LiteralNumber(PROTECTED_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Branch { dest: after });

        builder.set_insert_block(after);
        let u = builder.emit_val(
            InstData::LiteralNumber(UNPROTECTED_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(u) });

        builder.set_insert_block(h);
        let caught = builder.emit_val(
            InstData::LiteralNumber(HANDLER_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Return {
            value: Some(caught),
        });
    }
    module.func_mut(func).try_regions.push(TryRegion {
        try_blocks: vec![entry, a],
        catches: vec![CatchHandler {
            type_idx: u32::MAX,
            handler_block: h,
        }],
    });

    let result = lower_function(&module, func).expect("try function must lower");

    let after_start = find_ldai(&result.bytecodes, UNPROTECTED_SENTINEL);
    let h_start = find_ldai(&result.bytecodes, HANDLER_SENTINEL);

    // Contiguous region → exactly ONE TryBlock spanning [0, after_start).
    assert_eq!(
        result.try_blocks.len(),
        1,
        "a contiguous region must coalesce to the pre-N43 single span: {:?}",
        result.try_blocks
    );
    let tb = &result.try_blocks[0];
    assert_eq!(tb.start, 0, "{tb:?}");
    assert_eq!(
        tb.start as usize + tb.len as usize,
        after_start,
        "the single span covers exactly the two protected blocks"
    );
    assert_eq!(tb.catches.len(), 1, "{tb:?}");
    assert_eq!(tb.catches[0].handler as usize, h_start, "{tb:?}");
}

/// Nested regions: an inner region inside an outer one. Each region emits
/// its own run(s) carrying its own handler; region order in
/// `func.try_regions` is preserved in the output vector, so the
/// first-match-wins runtime scan (method.cpp:96-104) dispatches an
/// exception inside the inner block to the INNER handler — the same
/// ordering semantics the pre-N43 overlapping spans relied on.
#[test]
fn nested_regions_keep_first_match_dispatch_order() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    const INNER_HANDLER_SENTINEL: i64 = 90;

    let (inner, outer_h, inner_h);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        inner = builder.create_block();
        outer_h = builder.create_block();
        inner_h = builder.create_block();

        builder.add_predecessor(inner, entry);

        // entry (OUTER region only) -> inner (INNER region, also outer).
        let _x = builder.emit_val(
            InstData::LiteralNumber(ENTRY_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Branch { dest: inner });

        builder.set_insert_block(inner);
        let p = builder.emit_val(
            InstData::LiteralNumber(PROTECTED_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(p) });

        builder.set_insert_block(outer_h);
        let c1 = builder.emit_val(
            InstData::LiteralNumber(HANDLER_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(c1) });

        builder.set_insert_block(inner_h);
        let c2 = builder.emit_val(
            InstData::LiteralNumber(INNER_HANDLER_SENTINEL as f64),
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(c2) });
    }
    // Inner region FIRST: under the runtime's first-match-wins scan, the
    // inner handler must win for pcs covered by both regions.
    module.func_mut(func).try_regions.push(TryRegion {
        try_blocks: vec![inner],
        catches: vec![CatchHandler {
            type_idx: u32::MAX,
            handler_block: inner_h,
        }],
    });
    module.func_mut(func).try_regions.push(TryRegion {
        try_blocks: vec![entry, inner],
        catches: vec![CatchHandler {
            type_idx: u32::MAX,
            handler_block: outer_h,
        }],
    });

    let result = lower_function(&module, func).expect("nested try function must lower");

    let entry_start = find_ldai(&result.bytecodes, ENTRY_SENTINEL);
    let inner_start = find_ldai(&result.bytecodes, PROTECTED_SENTINEL);
    let outer_h_start = find_ldai(&result.bytecodes, HANDLER_SENTINEL);
    let inner_h_start = find_ldai(&result.bytecodes, INNER_HANDLER_SENTINEL);
    assert!(
        entry_start < inner_start && inner_start < outer_h_start && outer_h_start < inner_h_start,
        "fixture layout [entry, inner, outer_h, inner_h]: {:?}",
        result.bytecodes
    );

    // Both regions are contiguous, so each coalesces to one TryBlock; the
    // inner region's entry must come FIRST in the output vector.
    assert_eq!(
        result.try_blocks.len(),
        2,
        "one TryBlock per contiguous region: {:?}",
        result.try_blocks
    );
    let (inner_tb, outer_tb) = (&result.try_blocks[0], &result.try_blocks[1]);
    assert_eq!(
        inner_tb.catches[0].handler as usize, inner_h_start,
        "the inner region's try block must be emitted first so the \
         runtime's first-match scan dispatches to the inner handler"
    );
    assert_eq!(
        outer_tb.catches[0].handler as usize, outer_h_start,
        "{outer_tb:?}"
    );

    // Inner-region block: covered by BOTH ranges; the first match is the
    // inner handler (runtime FindCatchBlock semantics).
    let inner_pc = inner_start;
    let first_match = result
        .try_blocks
        .iter()
        .find(|tb| (tb.start as usize) <= inner_pc && inner_pc < (tb.start + tb.len) as usize)
        .expect("inner block must be covered");
    assert_eq!(
        first_match.catches[0].handler as usize, inner_h_start,
        "dispatch at an inner-block pc must reach the INNER handler"
    );

    // Entry block: covered only by the outer region.
    assert!(
        !dispatches(&[inner_tb.clone()], entry_start),
        "the entry block is outside the inner region"
    );
    assert!(
        dispatches(&[outer_tb.clone()], entry_start),
        "the entry block is protected by the outer region"
    );
}
