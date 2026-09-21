//! N38+N41+N47 regression (v0.2 port of v0.1
//! `opt_sccp_exception_soundness.rs`): SCCP exception soundness ×3, the
//! N47 exception-edge fallthrough, plus the peephole `null → 0.0`
//! coercion ban.
//!
//! N38 — SCCP must model the CFG with the AUGMENTED successor relation
//! (terminator successors + first-class `EdgeKind::Exceptional` edges),
//! because exception dispatch transfers control from ANY protected
//! instruction to the catch handler mid-block:
//!
//! (i) Catch handlers must be seeded/reached, else a merge phi below a
//!     try/catch only meets the NORMAL-path values — the exceptional-path
//!     value is invisible and the phi folds to a constant the handler
//!     path never produces.
//! (ii) Handler-block phi entries carry BLOCK-END values keyed by the
//!     protected pred, but exceptions dispatch mid-block — folding such
//!     a phi to the block-end constant is unsound. Handler-block phis
//!     are forced to lattice Bottom.
//! (iii) Eq/NotEq must not fold through `const_to_number`, which maps
//!     Undefined → NaN and Null → 0.0: `undefined == undefined` would
//!     fold to FALSE (NaN != NaN) where JS loose equality says true —
//!     rewiring es2abc's finally guards. Eq/NotEq with a Null/Undefined
//!     constant operand do not fold.
//!
//! N47 — `add_cfg_edges` must not early-return on Return/Unreachable
//! terminators: the exception edge append runs for EVERY terminator.
//!
//! N41 — peephole must not treat `null` as 0.0: `null == 0` is FALSE in
//! JS loose equality, and null arithmetic must not fold through a
//! coerced zero.

mod common;

use abcd_ir2::verify_module;
use abcd_ir2::{
    BinOp, BlockId, CmpOp, Const, Edge, EdgeKind, FuncId, FunctionKind, InstId, Module, Op,
};
use abcd_opt::FuncPass;
use abcd_opt::peephole::Peephole;
use abcd_opt::sccp::Sccp;

use common::V2Builder;

fn n(from: BlockId) -> Edge {
    Edge {
        from,
        kind: EdgeKind::Normal,
    }
}

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
fn build_try_merge_module() -> (Module, FuncId, InstId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let a;
    let h;
    let phi_inst;
    {
        let mut b = V2Builder::new(&mut module, func);
        a = b.create_block();
        h = b.create_block();
        let join = b.create_block();

        b.add_predecessor(a, b.entry());
        b.add_predecessor(join, a);
        b.add_predecessor(join, h);

        b.emit_void(Op::Branch { dest: a });

        b.set_insert_block(a);
        let va = b.emit_number(1.0);
        b.emit_void(Op::Branch { dest: join });

        b.set_insert_block(h);
        let vh = b.emit_number(2.0);
        b.emit_void(Op::Branch { dest: join });

        b.set_insert_block(join);
        let (inst, _result) = b.emit(Op::Phi {
            entries: vec![(n(a), va), (n(h), vh)],
        });
        phi_inst = inst;
        b.emit_void(Op::Return {
            value: Some(_result.unwrap()),
        });

        // The try region (creates the exception param and the
        // exceptional pred edge a ~~> h).
        b.add_try(vec![a], h);
    }
    (module, func, phi_inst)
}

/// N38(i) red pin: after Sccp the merge phi must NOT be
/// constant-replaced — the exceptional path carries a different value.
#[test]
fn sccp_does_not_fold_merge_phi_with_exceptional_value() {
    let (mut module, func, phi_inst) = build_try_merge_module();
    let pre = verify_module(&module);
    assert!(pre.is_ok(), "fixture must verify pre-opt: {:?}", pre.errors);

    Sccp.run(&mut module, func);

    assert!(
        matches!(&module.insts[phi_inst.index()].op, Op::Phi { .. }),
        "merge phi constant-replaced although the catch-handler path \
         carries a different value (N38(i)): {:?}",
        module.insts[phi_inst.index()].op
    );
    let post = verify_module(&module);
    assert!(post.is_ok(), "post-SCCP verify: {:?}", post.errors);
}

/// N38(ii) fixture: a catch handler whose phi entries carry the
/// protected preds' BLOCK-END values — both 7.0 here, so meet-over-
/// reachable-edges would fold the phi to the constant 7.0. But an
/// exception dispatches MID-block, before the block-end value exists,
/// so folding is unsound: handler-block phis must be forced to Bottom.
fn build_handler_phi_module() -> (Module, FuncId, BlockId, InstId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let a;
    let b_;
    let handler;
    let phi_inst;
    {
        let mut b = V2Builder::new(&mut module, func);
        a = b.create_block();
        b_ = b.create_block();
        let c = b.create_block();
        handler = b.create_block();

        b.add_predecessor(a, b.entry());
        b.add_predecessor(b_, a);
        b.add_predecessor(c, b_);

        b.emit_void(Op::Branch { dest: a });

        b.set_insert_block(a);
        let va = b.emit_number(7.0);
        b.emit_void(Op::Branch { dest: b_ });

        b.set_insert_block(b_);
        b.emit_void(Op::Branch { dest: c });

        b.set_insert_block(c);
        b.emit_void(Op::Return { value: None });

        b.set_insert_block(handler);
        let exc = |from: BlockId| Edge {
            from,
            kind: EdgeKind::Exceptional,
        };
        let (inst, result) = b.emit(Op::Phi {
            entries: vec![(exc(a), va), (exc(b_), va)],
        });
        phi_inst = inst;
        b.emit_void(Op::Return { value: result });

        b.add_try(vec![a, b_], handler);
    }
    (module, func, handler, phi_inst)
}

/// N38(ii): with exception edges the handler IS reachable and both phi
/// entries carry the same reachable constant — without the handler-phi
/// guard SCCP would fold it. The phi must survive.
#[test]
fn sccp_forces_handler_block_phis_to_bottom() {
    let (mut module, func, _handler, phi_inst) = build_handler_phi_module();
    let pre = verify_module(&module);
    assert!(pre.is_ok(), "fixture must verify pre-opt: {:?}", pre.errors);

    Sccp.run(&mut module, func);

    assert!(
        matches!(&module.insts[phi_inst.index()].op, Op::Phi { .. }),
        "handler-block phi folded to a block-end constant although \
         exceptions dispatch mid-block (N38(ii)): {:?}",
        module.insts[phi_inst.index()].op
    );
    let post = verify_module(&module);
    assert!(post.is_ok(), "post-SCCP verify: {:?}", post.errors);
}

/// N47 fixture: a NON-ENTRY try-protected block whose terminator is not
/// a branch (Return here; the Throw+Unreachable corpus shape below), with
/// a catch handler feeding a downstream merge:
///
/// ```text
/// entry -> t (try body, ends in `Return`)     [t is protected]
///          t ~~> h (catch-all handler, exception edge)
/// h: x = 1.0; y = 2.0; z = x + y; -> join -> Return
/// ```
///
/// `add_cfg_edges` used to `return` early for any terminator that is not
/// Branch/CondBranch, so the exception edge `t ~~> h` was never pushed
/// and SCCP never reached `h`: the foldable `z = 1.0 + 2.0` stayed
/// unfolded. The handler MUST be reached and `z` MUST fold to 3.0.
/// (Handler phis stay Bottom per N38(ii), but plain instructions whose
/// operands are defined inside the handler fold normally.)
fn build_non_branch_terminated_try_module(terminator: &str) -> (Module, FuncId, InstId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let t;
    let h;
    let binop_inst;
    {
        let mut b = V2Builder::new(&mut module, func);
        t = b.create_block();
        h = b.create_block();
        let join = b.create_block();

        b.add_predecessor(t, b.entry());
        b.add_predecessor(join, h);

        b.emit_void(Op::Branch { dest: t });

        b.set_insert_block(t);
        match terminator {
            "return" => b.emit_void(Op::Return { value: None }),
            "throw" => {
                let v = b.emit_number(9.0);
                // Throw is not a terminator in the v0.2 taxonomy; the
                // block ends in the explicit Unreachable lift emits.
                b.emit_void(Op::Throw { value: v });
                b.emit_void(Op::Unreachable);
            }
            other => panic!("unknown terminator shape {other}"),
        }

        b.set_insert_block(h);
        let x = b.emit_number(1.0);
        let y = b.emit_number(2.0);
        let (inst, _result) = b.emit(Op::BinaryOp {
            op: BinOp::Add,
            left: x,
            right: y,
        });
        binop_inst = inst;
        b.emit_void(Op::Branch { dest: join });

        b.set_insert_block(join);
        b.emit_void(Op::Return { value: None });

        b.add_try(vec![t], h);
    }
    (module, func, binop_inst)
}

/// N47 red pin: SCCP must reach the catch handler of a try-protected
/// block even when that block's terminator is Return or
/// Throw+Unreachable — the exception-edge append must run for EVERY
/// terminator, not just Branch/CondBranch.
#[test]
fn sccp_reaches_handler_of_non_branch_terminated_try_block() {
    for shape in ["return", "throw"] {
        let (mut module, func, binop_inst) = build_non_branch_terminated_try_module(shape);
        let pre = verify_module(&module);
        assert!(
            pre.is_ok(),
            "{shape}: fixture must verify pre-opt: {:?}",
            pre.errors
        );

        Sccp.run(&mut module, func);

        let folded = match &module.insts[binop_inst.index()].op {
            Op::LoadConst(cid) => module.consts.get(*cid).and_then(Const::as_f64),
            _ => None,
        };
        assert!(
            folded == Some(3.0),
            "{shape}: handler never reached — foldable binop survived \
             (N47 exception-edge fallthrough missing): {:?}",
            module.insts[binop_inst.index()].op
        );
    }
}

/// N38(iii) fixture helper: `f() { return <lhs> OP <rhs> }` with both
/// operands constants, run through Sccp, return the module and the
/// compare's resulting op clone.
fn sccp_fold_nullish(op: CmpOp, lhs: Const, rhs: Const) -> (Module, Op) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let cmp_inst;
    {
        let mut b = V2Builder::new(&mut module, func);
        let lc = b.konst(lhs);
        let rc = b.konst(rhs);
        let left = b.emit_val(Op::LoadConst(lc));
        let right = b.emit_val(Op::LoadConst(rc));
        let (inst, result) = b.emit(Op::Compare { op, left, right });
        cmp_inst = inst;
        b.emit_void(Op::Return { value: result });
    }
    Sccp.run(&mut module, func);
    let op = module.insts[cmp_inst.index()].op.clone();
    (module, op)
}

/// N38(iii) red pins: Eq/NotEq with a Null/Undefined constant operand
/// must NOT fold through ToNumber — `undefined == undefined` is TRUE in
/// JS loose equality (the ToNumber path yields NaN == NaN → false,
/// rewiring es2abc's finally guards).
#[test]
fn sccp_eq_noteq_do_not_tonumber_coerce_nullish() {
    for (op, lhs, rhs, ctx) in [
        (
            CmpOp::Eq,
            Const::Undefined,
            Const::Undefined,
            "undefined == undefined",
        ),
        (
            CmpOp::NotEq,
            Const::Undefined,
            Const::Undefined,
            "undefined != undefined",
        ),
        (CmpOp::Eq, Const::Null, Const::Null, "null == null"),
        (
            CmpOp::Eq,
            Const::Null,
            Const::Undefined,
            "null == undefined",
        ),
        (
            CmpOp::Eq,
            Const::Null,
            Const::number(0.0),
            "null == 0 (false in JS, no fold allowed)",
        ),
        (
            CmpOp::NotEq,
            Const::number(1.0),
            Const::Undefined,
            "1 != undefined",
        ),
    ] {
        let (_m, data) = sccp_fold_nullish(op, lhs, rhs);
        assert!(
            matches!(&data, Op::Compare { .. }),
            "{ctx}: Eq/NotEq with a nullish constant must not be \
             ToNumber-folded (N38(iii)), got {data:?}"
        );
    }
}

/// N38(iii) sanity: pure-number Eq/NotEq still fold (both engines keep
/// their normal constant path).
#[test]
fn sccp_eq_noteq_still_fold_plain_numbers() {
    let folded_bool = |op: CmpOp, lhs: f64, rhs: f64, ctx: &str| {
        let (module, data) = sccp_fold_nullish(op, Const::number(lhs), Const::number(rhs));
        match &data {
            Op::LoadConst(cid) => match module.consts.get(*cid) {
                Some(Const::Bool(b)) => *b,
                other => panic!("{ctx}: expected Bool fold, got {other:?}"),
            },
            other => panic!("{ctx}: expected LoadConst fold, got {other:?}"),
        }
    };
    assert!(
        folded_bool(CmpOp::Eq, 1.0, 1.0, "1 == 1"),
        "1 == 1 must still fold to true"
    );
    assert!(
        folded_bool(CmpOp::NotEq, 1.0, 2.0, "1 != 2"),
        "1 != 2 must still fold to true"
    );
}

/// Peephole helper: fold `lhs CMP rhs` with Peephole and return the
/// resulting op clone.
fn peephole_fold_cmp(op: CmpOp, lhs: Const, rhs: Const) -> (Module, Op) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let cmp_inst;
    {
        let mut b = V2Builder::new(&mut module, func);
        let lc = b.konst(lhs);
        let rc = b.konst(rhs);
        let left = b.emit_val(Op::LoadConst(lc));
        let right = b.emit_val(Op::LoadConst(rc));
        let (inst, result) = b.emit(Op::Compare { op, left, right });
        cmp_inst = inst;
        b.emit_void(Op::Return { value: result });
    }
    Peephole.run(&mut module, func);
    let op = module.insts[cmp_inst.index()].op.clone();
    (module, op)
}

/// Peephole helper: fold `lhs BINOP rhs`.
fn peephole_fold_binop(op: BinOp, lhs: Const, rhs: Const) -> (Module, Op) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let binop_inst;
    {
        let mut b = V2Builder::new(&mut module, func);
        let lc = b.konst(lhs);
        let rc = b.konst(rhs);
        let left = b.emit_val(Op::LoadConst(lc));
        let right = b.emit_val(Op::LoadConst(rc));
        let (inst, result) = b.emit(Op::BinaryOp { op, left, right });
        binop_inst = inst;
        b.emit_void(Op::Return { value: result });
    }
    Peephole.run(&mut module, func);
    let op = module.insts[binop_inst.index()].op.clone();
    (module, op)
}

/// N41 red pins: peephole must not treat null as 0.0 — `null == 0` is
/// FALSE in JS loose equality (it folded to true), and `null` arithmetic
/// must not constant-fold through a coerced zero.
#[test]
fn peephole_does_not_treat_null_as_zero() {
    let (_m, data) = peephole_fold_cmp(CmpOp::Eq, Const::Null, Const::number(0.0));
    assert!(
        matches!(&data, Op::Compare { .. }),
        "null == 0 must not fold (N41), got {data:?}"
    );
    let (_m, data) = peephole_fold_binop(BinOp::Add, Const::Null, Const::number(5.0));
    assert!(
        matches!(&data, Op::BinaryOp { .. }),
        "null + 5 must not fold through coerced 0.0 (N41), got {data:?}"
    );
}
