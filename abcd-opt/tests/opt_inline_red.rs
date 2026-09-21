//! N44 red-first evidence (D2 inline rewrite, v2-P3b): the v0.1 inline
//! pass was quarantined because it produced module-INVALID IR —
//! parameters unmapped, call-site predecessors not rebuilt, try regions
//! lost. Before the real v0.2 rewrite landed, this test demonstrated
//! that a naive inliner with exactly those defect shapes produces
//! verifier errors on the v0.2 IR (`abcd_ir2::Module`), proving the
//! probe shapes below discriminate valid from invalid inline output.
//!
//! The deliberate defects of [`naive_inline`] (each one an N44 defect):
//!
//! 1. **Parameters unmapped**: the callee's blocks are appended to the
//!    caller's block list with their original (foreign) `ValueId`s —
//!    callee `Param` values are not bound to call-site operands.
//! 2. **Call-site predecessors not rebuilt**: the call block is split
//!    (post-call instructions moved to a fresh continuation block) but
//!    the old successors keep `Edge { from: call_block, Normal }` preds
//!    and phi entries that the call block's terminator no longer
//!    targets.
//! 3. **Try regions lost**: the caller's try regions are dropped while
//!    the handler blocks keep their Exceptional preds.
//!
//! The rewrite (`abcd_opt::inline::inline_module`) kills all three BY
//! CONSTRUCTION; `opt_inline.rs` pins the green side on the same probe
//! shapes. This file stays as the red evidence: it exercises ONLY the
//! naive routine (kept here, not in the crate) and must keep failing
//! verification forever.

mod common;

use abcd_ir2::verify_module;
use abcd_ir2::{BinOp, CallKind, FuncId, FunctionKind, Module, Op, ValueId, VerifyErrorKind};
use abcd_ir2::{BlockId, EdgeKind};

use common::V2Builder;

/// The N44 probe shape, rebuilt on the v0.2 IR:
///
/// ```text
/// g (static, 1 formal p):            f (static, 1 formal a):
///   g_entry:                           entry: c0 = 10; br b_call
///     v = p + 1                        b_call (PROTECTED by R → h):
///     return v                           df = DefineFunc g
///                                        cl = AllocClosure df
/// h (handler of R):                    t  = a + c0
///   return 777                           r  = Call(cl, args:[t])  <- mid-block
///                                        s  = r * c0
///                                        br b_next
///                                      b_next: phi[(b_call, s)]; return phi
/// ```
///
/// Returns (module, caller f, callee g, call block, continuation
/// successor, handler).
fn build_n44_probe() -> (Module, FuncId, FuncId, BlockId, BlockId, BlockId) {
    let mut module = Module::new();

    let g = V2Builder::create_function(&mut module, "g", FunctionKind::Function);
    module.functions[g.index()].modifiers = abcd_ir2::Modifiers::STATIC;
    {
        let mut b = V2Builder::new(&mut module, g);
        let p = b.create_param();
        let one = b.emit_number(1.0);
        let v = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: p,
            right: one,
        });
        b.emit_void(Op::Return { value: Some(v) });
    }

    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    module.functions[f.index()].modifiers = abcd_ir2::Modifiers::STATIC;
    let b_call;
    let b_next;
    let h;
    {
        let mut b = V2Builder::new(&mut module, f);
        let a = b.create_param();
        let entry = b.entry();
        b_call = b.create_block();
        b_next = b.create_block();
        h = b.create_block();

        b.add_predecessor(b_call, entry);
        b.add_predecessor(b_next, b_call);

        // entry: c0 = 10; br b_call
        let c0 = b.emit_number(10.0);
        b.emit_void(Op::Branch { dest: b_call });

        // b_call: define g, call it mid-block, then a post-call use.
        b.set_insert_block(b_call);
        let df = b.emit_val(Op::DefineFunc {
            body: g,
            captures: vec![],
            length: 1,
        });
        let cl = b.emit_val(Op::AllocClosure { func: df });
        let t = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: a,
            right: c0,
        });
        let r = b.emit_val(Op::Call {
            callee: cl,
            this: None,
            args: vec![t],
            kind: CallKind::Dynamic,
        });
        let s = b.emit_val(Op::BinaryOp {
            op: BinOp::Mul,
            left: r,
            right: c0,
        });
        b.emit_void(Op::Branch { dest: b_next });

        // b_next: a phi fed by the call block, then return.
        b.set_insert_block(b_next);
        let phi = b.emit_val(Op::Phi {
            entries: vec![(
                abcd_ir2::Edge {
                    from: b_call,
                    kind: EdgeKind::Normal,
                },
                s,
            )],
        });
        b.emit_void(Op::Return { value: Some(phi) });

        // h: catch-all handler of the region protecting b_call.
        b.set_insert_block(h);
        let caught = b.emit_number(777.0);
        b.emit_void(Op::Return { value: Some(caught) });
        b.add_try(vec![b_call], h);
    }

    (module, f, g, b_call, b_next, h)
}

/// A deliberately naive inliner carrying the three N44 defect shapes
/// (see the module docs). Returns the call-block split point's fresh
/// continuation block.
fn naive_inline(module: &mut Module, caller: FuncId, callee: FuncId) {
    let (call_block, call_pos, callee_entry) = {
        let caller_data = module.func(caller).unwrap();
        let mut found = None;
        'outer: for &bb in &caller_data.blocks {
            for (pos, &iid) in module.block(bb).unwrap().insts.iter().enumerate() {
                if matches!(&module.inst(iid).unwrap().op, Op::Call { .. }) {
                    found = Some((bb, pos));
                    break 'outer;
                }
            }
        }
        let (bb, pos) = found.expect("probe has a call");
        (bb, pos, module.func(callee).unwrap().blocks[0])
    };

    // DEFECT 2 (split without pred rebuild): move post-call insts to a
    // fresh continuation, branch into the callee — and leave every old
    // successor's preds/phi entries keyed on the call block.
    let cont = BlockId::new(module.blocks.len() as u32);
    module.blocks.push(abcd_ir2::Block::default());
    let post: Vec<_> = module.block(call_block).unwrap().insts[call_pos + 1..].to_vec();
    for &iid in &post {
        module.inst_mut(iid).unwrap().block = cont;
    }
    module.block_mut(cont).unwrap().insts = post;
    module.func_mut(caller).unwrap().blocks.push(cont);

    // DEFECT 1 (parameters unmapped): append the callee's blocks to the
    // caller with their original ValueIds — no cloning, no param/arg
    // binding. Also point the call's result at the callee's return
    // value (a value that does not dominate the call block).
    let callee_blocks = module.func(callee).unwrap().blocks.clone();
    for &gb in &callee_blocks {
        module.func_mut(caller).unwrap().blocks.push(gb);
    }
    let callee_ret_val: ValueId = {
        let gb = callee_blocks[0];
        let last = *module.block(gb).unwrap().insts.last().unwrap();
        let Op::Return { value } = &module.inst(last).unwrap().op else {
            panic!("probe callee ends in Return");
        };
        value.expect("probe callee returns a value")
    };
    let call_iid = module.block(call_block).unwrap().insts[call_pos];
    module.inst_mut(call_iid).unwrap().op = Op::Mov {
        src: callee_ret_val,
    };

    // Split branch into the callee entry (no loc — glue).
    let br = abcd_ir2::InstId::new(module.insts.len() as u32);
    module.insts.push(abcd_ir2::Inst {
        op: Op::Branch {
            dest: callee_entry,
        },
        result: None,
        block: call_block,
        loc: None,
    });
    module.block_mut(call_block).unwrap().insts.truncate(call_pos);
    module.block_mut(call_block).unwrap().insts.push(br);

    // DEFECT 3 (try regions lost): drop the caller's try regions while
    // the handler keeps its Exceptional preds.
    module.func_mut(caller).unwrap().try_regions.clear();
}

fn error_kinds(module: &Module) -> Vec<String> {
    verify_module(module)
        .errors
        .iter()
        .map(|e| format!("{:?}", e.kind))
        .collect()
}

/// The probe module itself is verifier-clean before any inlining — the
/// red below is caused by the naive pass, not by the fixture.
#[test]
fn n44_probe_verifies_clean_before_inline() {
    let (module, ..) = build_n44_probe();
    let report = verify_module(&module);
    assert!(
        report.is_ok(),
        "probe must verify before inline: {:?}",
        report.errors
    );
}

/// N44 red proof on the v0.2 IR: the naive inliner produces
/// module-invalid IR, with each defect shape surfacing as its verifier
/// error kind.
#[test]
fn naive_inline_produces_module_invalid_ir() {
    let (mut module, f, g, ..) = build_n44_probe();
    naive_inline(&mut module, f, g);

    let report = verify_module(&module);
    assert!(
        !report.is_ok(),
        "naive inline MUST produce invalid IR (that is the N44 red)"
    );
    let kinds: Vec<String> = error_kinds(&module);

    // DEFECT 1 — parameters unmapped: the callee's Param value is used
    // inside the caller but is not one of the caller's params.
    assert!(
        report.errors.iter().any(|e| matches!(
            e.kind,
            VerifyErrorKind::ForeignValue(_) | VerifyErrorKind::ParamDefMismatch { .. }
        )),
        "expected the unmapped-parameter defect (ForeignValue): {kinds:?}"
    );
    // DEFECT 1 (companion) — the call result rewired to the callee's
    // return value, which cannot dominate the call block.
    assert!(
        report.errors.iter().any(|e| matches!(
            e.kind,
            VerifyErrorKind::UseNotDominated { .. } | VerifyErrorKind::ForeignValue(_)
        )),
        "expected the unmapped return-value defect (UseNotDominated): {kinds:?}"
    );
    // DEFECT 2 — predecessors not rebuilt: the old successor still
    // lists the call block as a Normal pred, but the call block's
    // terminator now targets the callee entry.
    assert!(
        report.errors.iter().any(|e| matches!(
            e.kind,
            VerifyErrorKind::PredDoesNotTarget(_) | VerifyErrorKind::SuccessorMissingPred(_)
        )),
        "expected the predecessor-rebuild defect (PredDoesNotTarget): {kinds:?}"
    );
    // DEFECT 3 — try regions lost: the handler keeps Exceptional preds
    // no region dispatches to.
    assert!(
        report.errors.iter().any(|e| matches!(
            e.kind,
            VerifyErrorKind::ExceptionalPredWithoutRegion(_)
        )),
        "expected the lost-try-region defect (ExceptionalPredWithoutRegion): {kinds:?}"
    );
}
