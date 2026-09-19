//! N38+N41 regression (P3-T22): SCCP exception soundness ×3, plus the
//! peephole `LiteralNull → 0.0` coercion.
//!
//! N38 — SCCP modeled the CFG with TERMINATOR successors only
//! (`block_succs`), while exception dispatch transfers control from ANY
//! protected instruction to the catch handler mid-block:
//!
//! (i) Catch handlers were never seeded/reached, so a merge phi below a
//!     try/catch only met the NORMAL-path values — the exceptional-path
//!     value was invisible and the phi folded to a constant that the
//!     handler path never produces. Fix: seed + first-reach traversal
//!     via `analysis::augmented_succs` (exception edges included).
//! (ii) Handler-block phi entries carry BLOCK-END values keyed by the
//!     protected pred, but exceptions dispatch mid-block — folding such
//!     a phi to the block-end constant is unsound. Fix: phis in
//!     catch-handler blocks are forced to lattice Bottom.
//! (iii) Eq/NotEq folded through `const_to_number`, which maps
//!     Undefined → NaN and Null → 0.0: `undefined == undefined` folded
//!     to FALSE (NaN != NaN) where JS loose equality says true —
//!     rewiring es2abc's finally guards. Fix: Eq/NotEq with a
//!     Null/Undefined constant operand do not fold (no ToNumber
//!     coercion on the equality path).
//!
//! N41 — peephole's `as_number` mapped `LiteralNull → 0.0`, so e.g.
//! `null == 0` folded to TRUE where JS loose equality says false
//! (null equals only null/undefined). Dropped; no eq-nullish fold is
//! added to peephole (proven unsound by P3-T19).

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::{Block, FuncId, Inst};
use abcd_ir::inst::{BinOp, InstData};
use abcd_ir::module::{CatchHandler, Module, TryRegion};
use abcd_ir::opt::FuncPass;
use abcd_ir::opt::peephole::Peephole;
use abcd_ir::opt::sccp::Sccp;
use abcd_ir::types::IrType;
use abcd_ir::verify::verify_module;

/// N38(i) fixture: a try/catch where a value differs on the exceptional
/// path.
///
/// ```text
/// entry -> a (try body) -> join
///          a ~~> h (catch-all handler, exception edge) -> join
/// join: phi[(a, 1.0), (h, 2.0)] -> Return
/// ```
///
/// Without exception edges SCCP never reaches `h`, so the phi meets
/// only 1.0 and is constant-replaced — but the exceptional path
/// produces 2.0.
fn build_try_merge_module() -> (Module, FuncId, Inst) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let a;
    let h;
    let phi_inst;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        a = builder.create_block();
        h = builder.create_block();
        let join = builder.create_block();

        builder.add_predecessor(a, entry);
        builder.add_predecessor(h, a);
        builder.add_predecessor(join, a);
        builder.add_predecessor(join, h);

        builder.emit_void(InstData::Branch { dest: a });

        builder.set_insert_block(a);
        let va = builder.emit_val(InstData::LiteralNumber(1.0), IrType::default());
        builder.emit_void(InstData::Branch { dest: join });

        builder.set_insert_block(h);
        let vh = builder.emit_val(InstData::LiteralNumber(2.0), IrType::default());
        builder.emit_void(InstData::Branch { dest: join });

        builder.set_insert_block(join);
        let (inst, result) = builder.emit(
            InstData::Phi {
                entries: vec![(a, va), (h, vh)],
            },
            IrType::default(),
        );
        phi_inst = inst;
        builder.emit_void(InstData::Return { value: result });
    }
    module.func_mut(func).try_regions.push(TryRegion {
        try_blocks: vec![a],
        catches: vec![CatchHandler {
            type_idx: u32::MAX,
            handler_block: h,
        }],
    });
    let _ = entry;
    (module, func, phi_inst)
}

/// N38(i) red pin: after Sccp the merge phi must NOT be
/// constant-replaced — the exceptional path carries a different value.
#[test]
fn sccp_does_not_fold_merge_phi_with_exceptional_value() {
    let (mut module, func, phi_inst) = build_try_merge_module();
    assert!(
        verify_module(&module).is_empty(),
        "fixture must verify pre-opt: {:?}",
        verify_module(&module)
    );

    Sccp.run(&mut module, func);

    assert!(
        matches!(&module.inst(phi_inst).data, InstData::Phi { .. }),
        "merge phi constant-replaced although the catch-handler path \
         carries a different value (N38(i)): {:?}",
        module.inst(phi_inst).data
    );
}

/// N38(ii) fixture: a catch handler whose phi entries carry the
/// protected preds' BLOCK-END values — both 7.0 here, so meet-over-
/// reachable-edges would fold the phi to the constant 7.0. But an
/// exception dispatches MID-block, before the block-end value exists,
/// so folding is unsound: handler-block phis must be forced to Bottom.
fn build_handler_phi_module() -> (Module, FuncId, Block, Inst) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let a;
    let b;
    let handler;
    let phi_inst;
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
        let va = builder.emit_val(InstData::LiteralNumber(7.0), IrType::default());
        builder.emit_void(InstData::Branch { dest: b });

        builder.set_insert_block(b);
        builder.emit_void(InstData::Branch { dest: c });

        builder.set_insert_block(c);
        builder.emit_void(InstData::Return { value: None });

        builder.set_insert_block(handler);
        let (inst, result) = builder.emit(
            InstData::Phi {
                entries: vec![(a, va), (b, va)],
            },
            IrType::default(),
        );
        phi_inst = inst;
        builder.emit_void(InstData::Return { value: result });
    }
    module.func_mut(func).try_regions.push(TryRegion {
        try_blocks: vec![a, b],
        catches: vec![CatchHandler {
            type_idx: u32::MAX,
            handler_block: handler,
        }],
    });
    (module, func, handler, phi_inst)
}

/// N38(ii): with exception edges the handler IS reachable and both phi
/// entries carry the same reachable constant — without the handler-phi
/// guard SCCP would fold it. The phi must survive.
#[test]
fn sccp_forces_handler_block_phis_to_bottom() {
    let (mut module, func, _handler, phi_inst) = build_handler_phi_module();
    assert!(
        verify_module(&module).is_empty(),
        "fixture must verify pre-opt: {:?}",
        verify_module(&module)
    );

    Sccp.run(&mut module, func);

    assert!(
        matches!(&module.inst(phi_inst).data, InstData::Phi { .. }),
        "handler-block phi folded to a block-end constant although \
         exceptions dispatch mid-block (N38(ii)): {:?}",
        module.inst(phi_inst).data
    );
}

/// N38(iii) fixture helper: `f() { return <lhs> OP <rhs> }` with both
/// operands literal instructions, run through Sccp, return the binop's
/// resulting data.
fn sccp_fold_nullish(op: BinOp, lhs: InstData, rhs: InstData) -> InstData {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let binop_inst;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let left = builder.emit_val(lhs, IrType::default());
        let right = builder.emit_val(rhs, IrType::default());
        let (inst, result) =
            builder.emit(InstData::BinaryOp { op, left, right }, IrType::default());
        binop_inst = inst;
        builder.emit_void(InstData::Return { value: result });
    }
    Sccp.run(&mut module, func);
    module.inst(binop_inst).data.clone()
}

/// N38(iii) red pins: Eq/NotEq with a Null/Undefined constant operand
/// must NOT fold through ToNumber — `undefined == undefined` is TRUE in
/// JS loose equality (the ToNumber path yields NaN == NaN → false,
/// rewiring es2abc's finally guards).
#[test]
fn sccp_eq_noteq_do_not_tonumber_coerce_nullish() {
    for (op, lhs, rhs, ctx) in [
        (
            BinOp::Eq,
            InstData::LiteralUndefined,
            InstData::LiteralUndefined,
            "undefined == undefined",
        ),
        (
            BinOp::NotEq,
            InstData::LiteralUndefined,
            InstData::LiteralUndefined,
            "undefined != undefined",
        ),
        (
            BinOp::Eq,
            InstData::LiteralNull,
            InstData::LiteralNull,
            "null == null",
        ),
        (
            BinOp::Eq,
            InstData::LiteralNull,
            InstData::LiteralUndefined,
            "null == undefined",
        ),
        (
            BinOp::Eq,
            InstData::LiteralNull,
            InstData::LiteralNumber(0.0),
            "null == 0 (false in JS, no fold allowed)",
        ),
        (
            BinOp::NotEq,
            InstData::LiteralNumber(1.0),
            InstData::LiteralUndefined,
            "1 != undefined",
        ),
    ] {
        let data = sccp_fold_nullish(op, lhs, rhs);
        assert!(
            matches!(&data, InstData::BinaryOp { .. }),
            "{ctx}: Eq/NotEq with a nullish constant must not be \
             ToNumber-folded (N38(iii)), got {data:?}"
        );
    }
}

/// N38(iii) sanity: pure-number Eq/NotEq still fold (both engines keep
/// their normal constant path).
#[test]
fn sccp_eq_noteq_still_fold_plain_numbers() {
    let data = sccp_fold_nullish(
        BinOp::Eq,
        InstData::LiteralNumber(1.0),
        InstData::LiteralNumber(1.0),
    );
    assert!(
        matches!(&data, InstData::LiteralBool(true)),
        "1 == 1 must still fold to true, got {data:?}"
    );
    let data = sccp_fold_nullish(
        BinOp::NotEq,
        InstData::LiteralNumber(1.0),
        InstData::LiteralNumber(2.0),
    );
    assert!(
        matches!(&data, InstData::LiteralBool(true)),
        "1 != 2 must still fold to true, got {data:?}"
    );
}

/// Peephole helper: fold `lhs OP rhs` with Peephole and return the
/// binop's resulting data.
fn peephole_fold(op: BinOp, lhs: InstData, rhs: InstData) -> InstData {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let binop_inst;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let left = builder.emit_val(lhs, IrType::default());
        let right = builder.emit_val(rhs, IrType::default());
        let (inst, result) =
            builder.emit(InstData::BinaryOp { op, left, right }, IrType::default());
        binop_inst = inst;
        builder.emit_void(InstData::Return { value: result });
    }
    Peephole.run(&mut module, func);
    module.inst(binop_inst).data.clone()
}

/// N41 red pins: peephole must not treat LiteralNull as 0.0 —
/// `null == 0` is FALSE in JS loose equality (it folded to true), and
/// `null` arithmetic must not constant-fold through a coerced zero.
#[test]
fn peephole_does_not_treat_null_as_zero() {
    let data = peephole_fold(
        BinOp::Eq,
        InstData::LiteralNull,
        InstData::LiteralNumber(0.0),
    );
    assert!(
        matches!(&data, InstData::BinaryOp { .. }),
        "null == 0 must not fold (N41), got {data:?}"
    );
    let data = peephole_fold(
        BinOp::Add,
        InstData::LiteralNull,
        InstData::LiteralNumber(5.0),
    );
    assert!(
        matches!(&data, InstData::BinaryOp { .. }),
        "null + 5 must not fold through coerced 0.0 (N41), got {data:?}"
    );
}
