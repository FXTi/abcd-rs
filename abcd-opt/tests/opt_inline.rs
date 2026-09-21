//! D2 inline rewrite (v2-P3b) — unit tests for `abcd_opt::inline`,
//! one per N44 defect shape plus the eligibility matrix. Every green
//! test runs `abcd_ir2::verify_module` after inlining: zero errors is
//! the hard gate. The red counterparts (naive inliner producing
//! module-invalid IR on the same probe shape) live in
//! `opt_inline_red.rs`.

mod common;

use abcd_ir2::verify_module;
use abcd_ir2::{
    BinOp, BlockId, CallKind, Const, Edge, EdgeKind, FuncId, FunctionKind, Loc, Module, Op, Sym,
    UnOp, ValueDef, ValueId,
};
use abcd_opt::inline::{InlinePolicy, InlineReport, SkipReason, inline_module};

use common::V2Builder;

// ─── Probe scaffolding ───────────────────────────────────────────────────────

fn verify_ok(module: &Module) {
    let report = verify_module(module);
    assert!(
        report.is_ok(),
        "module must verify after inline: {:?}",
        report.errors
    );
}

fn default_policy() -> InlinePolicy {
    InlinePolicy::default()
}

/// Create a STATIC function (params are all formals — no `this`).
fn create_static(module: &mut Module, name: &str) -> FuncId {
    let f = V2Builder::create_function(module, name, FunctionKind::Function);
    module.functions[f.index()].modifiers = abcd_ir2::Modifiers::STATIC;
    f
}

/// `g` callee: static, one formal `p`, body `return p + 1`.
fn build_add1_callee(module: &mut Module) -> FuncId {
    let g = create_static(module, "g");
    let mut b = V2Builder::new(module, g);
    let p = b.create_param();
    let one = b.emit_number(1.0);
    let v = b.emit_val(Op::BinaryOp {
        op: BinOp::Add,
        left: p,
        right: one,
    });
    b.emit_void(Op::Return { value: Some(v) });
    g
}

/// In `f`'s entry block: define a closure of `g` and call it; returns
/// (call inst, call result).
fn emit_closure_call(
    b: &mut V2Builder,
    g: FuncId,
    this: Option<ValueId>,
    args: Vec<ValueId>,
    kind: CallKind,
) -> (abcd_ir2::InstId, ValueId) {
    let df = b.emit_val(Op::DefineFunc {
        body: g,
        captures: vec![],
        length: args.len() as u16,
    });
    let cl = b.emit_val(Op::AllocClosure { func: df });
    let (iid, result) = b.emit(Op::Call {
        callee: cl,
        this,
        args,
        kind,
    });
    (iid, result.expect("Call has a result"))
}

/// The N44 probe (identical shape to the red test): caller `f` (static,
/// one formal `a`) calls `g` mid-block, the call block is protected by
/// a try region whose handler carries a phi keyed by the call block's
/// exceptional edge, and the call block's Normal successor carries a
/// phi keyed by the call block.
struct N44Probe {
    module: Module,
    caller: FuncId,
    call_block: BlockId,
    successor: BlockId,
    handler: BlockId,
    mul_inst: abcd_ir2::InstId,
    handler_phi_value: ValueId,
}

fn build_n44_probe() -> N44Probe {
    let mut module = Module::new();
    let g = build_add1_callee(&mut module);

    let f = create_static(&mut module, "f");
    let call_block;
    let successor;
    let handler;
    let mul_inst;
    let handler_phi_value;
    {
        let mut b = V2Builder::new(&mut module, f);
        let a = b.create_param();
        let entry = b.entry();
        call_block = b.create_block();
        successor = b.create_block();
        handler = b.create_block();

        b.add_predecessor(call_block, entry);
        b.add_predecessor(successor, call_block);

        let c0 = b.emit_number(10.0);
        b.emit_void(Op::Branch { dest: call_block });

        b.set_insert_block(call_block);
        let t = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: a,
            right: c0,
        });
        let (_call, r) = emit_closure_call(&mut b, g, None, vec![t], CallKind::Dynamic);
        let (mul, _) = b.emit(Op::BinaryOp {
            op: BinOp::Mul,
            left: r,
            right: c0,
        });
        mul_inst = mul;
        b.emit_void(Op::Branch { dest: successor });

        b.set_insert_block(successor);
        let phi = b.emit_val(Op::Phi {
            entries: vec![(
                Edge {
                    from: call_block,
                    kind: EdgeKind::Normal,
                },
                module_mul_result_placeholder(),
            )],
        });
        b.emit_void(Op::Return { value: Some(phi) });

        b.set_insert_block(handler);
        // The handler phi joins the exceptional edge out of the call
        // block, carrying the entry-defined constant (the caller
        // register state visible at the call).
        handler_phi_value = c0;
        let hphi = b.emit_val(Op::Phi {
            entries: vec![(
                Edge {
                    from: call_block,
                    kind: EdgeKind::Exceptional,
                },
                c0,
            )],
        });
        b.emit_void(Op::Return { value: Some(hphi) });
        b.add_try(vec![call_block], handler);
    }
    // Fix up the successor phi's value (the mul result) now that the
    // builder borrow is over.
    let mul_result = module.insts[mul_inst.index()].result.expect("mul result");
    let succ_phi = module.blocks[successor.index()].insts[0];
    if let Op::Phi { entries } = &mut module.insts[succ_phi.index()].op {
        entries[0].1 = mul_result;
    }

    N44Probe {
        module,
        caller: f,
        call_block,
        successor,
        handler,
        mul_inst,
        handler_phi_value,
    }
}

/// Placeholder for the successor phi value (patched after the builder
/// borrow ends); never survives construction.
fn module_mul_result_placeholder() -> ValueId {
    ValueId::new(0)
}

/// The block an instruction lives in.
fn block_of(module: &Module, iid: abcd_ir2::InstId) -> BlockId {
    module.insts[iid.index()].block
}

/// The (unique) Return instruction of a single-exit probe function —
/// found across blocks, since inlining moves it into the continuation.
fn return_inst(module: &Module, f: FuncId) -> abcd_ir2::InstId {
    module.functions[f.index()]
        .blocks
        .iter()
        .flat_map(|&bb| module.blocks[bb.index()].insts.iter().copied())
        .find(|&iid| matches!(&module.insts[iid.index()].op, Op::Return { .. }))
        .expect("probe function has a Return")
}

/// All `Op::Call` instructions in a function.
fn calls_in(module: &Module, f: FuncId) -> Vec<abcd_ir2::InstId> {
    let mut out = Vec::new();
    for &bb in &module.functions[f.index()].blocks {
        for &iid in &module.blocks[bb.index()].insts {
            if matches!(&module.insts[iid.index()].op, Op::Call { .. }) {
                out.push(iid);
            }
        }
    }
    out
}

fn skip_count(report: &InlineReport, reason: SkipReason) -> usize {
    report.skips.get(&reason).copied().unwrap_or(0)
}

// ─── Parameter mapping (N44 defect 1) ────────────────────────────────────────

/// Dynamic call WITH an explicit receiver (the `callthis*` shape): the
/// callee's `this` param binds to the receiver value.
#[test]
fn dynamic_call_with_receiver_binds_this_param() {
    let mut module = Module::new();
    // g (NON-static): params [this, x]; body `return this`.
    let g = V2Builder::create_function(&mut module, "g", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, g);
        let this_p = b.create_param();
        let _x = b.create_param();
        b.emit_void(Op::Return {
            value: Some(this_p),
        });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let recv = b.emit_number(42.0);
        let (_c, r) = emit_closure_call(&mut b, g, Some(recv), vec![], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }

    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);
    // f now returns the receiver's LoadConst result directly.
    let ret = return_inst(&module, f);
    let Op::Return { value } = &module.insts[ret.index()].op else {
        panic!("f ends in Return");
    };
    let v = value.expect("returns a value");
    let ValueDef::Inst(def) = module.values[v.index()].def else {
        panic!("return value is inst-defined");
    };
    assert!(
        matches!(&module.insts[def.index()].op, Op::LoadConst(c)
            if module.consts.get(*c).and_then(Const::as_f64) == Some(42.0)),
        "the call result must be replaced by the receiver value"
    );
    assert!(calls_in(&module, f).is_empty(), "the call is gone");
}

/// Dynamic call WITHOUT a receiver whose callee USES `this`: skipped —
/// the binding depends on the callee's strictness, which the IR cannot
/// prove.
#[test]
fn dynamic_call_without_receiver_using_this_is_skipped() {
    let mut module = Module::new();
    let g = V2Builder::create_function(&mut module, "g", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, g);
        let this_p = b.create_param();
        b.emit_void(Op::Return {
            value: Some(this_p),
        });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }

    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 0, "{report:?}");
    assert_eq!(skip_count(&report, SkipReason::ThisBindingUnprovable), 1);
    assert_eq!(calls_in(&module, f).len(), 1, "the call stays");
    verify_ok(&module);
}

/// Dynamic call without a receiver is fine when the callee never reads
/// its `this` param.
#[test]
fn dynamic_call_without_receiver_unused_this_inlines() {
    let mut module = Module::new();
    let g = V2Builder::create_function(&mut module, "g", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, g);
        let _this_p = b.create_param();
        let x = b.create_param();
        b.emit_void(Op::Return { value: Some(x) });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let arg = b.emit_number(7.0);
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![arg], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }

    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);
    let ret = return_inst(&module, f);
    let Op::Return { value } = &module.insts[ret.index()].op else {
        panic!("f ends in Return");
    };
    let v = value.expect("returns a value");
    let ValueDef::Inst(def) = module.values[v.index()].def else {
        panic!("inst-defined");
    };
    assert!(
        matches!(&module.insts[def.index()].op, Op::LoadConst(c)
            if module.consts.get(*c).and_then(Const::as_f64) == Some(7.0)),
        "the formal binds to the call argument"
    );
}

/// Direct call: the explicit receiver binds `this`; `Direct` with
/// `this: None` is malformed and skipped.
#[test]
fn direct_call_binding_rules() {
    // Direct + Some(this): inlines.
    let mut module = Module::new();
    let g = V2Builder::create_function(&mut module, "g", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, g);
        let this_p = b.create_param();
        b.emit_void(Op::Return {
            value: Some(this_p),
        });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let recv = b.emit_number(3.0);
        let (_c, r) = emit_closure_call(&mut b, g, Some(recv), vec![], CallKind::Direct);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);

    // Direct + None: skipped.
    let mut module = Module::new();
    let g = V2Builder::create_function(&mut module, "g", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, g);
        let this_p = b.create_param();
        b.emit_void(Op::Return {
            value: Some(this_p),
        });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![], CallKind::Direct);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 0, "{report:?}");
    assert_eq!(skip_count(&report, SkipReason::DirectWithoutThis), 1);
    verify_ok(&module);
}

/// Static callees: every param is a formal (no `this` slot); missing
/// arguments bind a pooled `undefined`; extra arguments drop.
#[test]
fn static_callee_arity_rules() {
    // Missing arg → undefined.
    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    {
        let mut b = V2Builder::new(&mut module, g);
        let _p0 = b.create_param();
        let p1 = b.create_param();
        b.emit_void(Op::Return { value: Some(p1) });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let arg = b.emit_number(1.0);
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![arg], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);
    let ret = return_inst(&module, f);
    let Op::Return { value } = &module.insts[ret.index()].op else {
        panic!("f ends in Return");
    };
    let v = value.expect("returns a value");
    assert!(
        matches!(module.values[v.index()].def, ValueDef::Const(c)
            if matches!(module.consts.get(c), Some(Const::Undefined))),
        "the missing formal must bind a pooled undefined: {:?}",
        module.values[v.index()].def
    );

    // Extra arg → dropped (callee cannot observe it; `arguments` users
    // are ineligible).
    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    {
        let mut b = V2Builder::new(&mut module, g);
        let p0 = b.create_param();
        b.emit_void(Op::Return { value: Some(p0) });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let a0 = b.emit_number(1.0);
        let a1 = b.emit_number(2.0);
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![a0, a1], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);
}

// ─── Predecessor rebuild (N44 defect 2) ──────────────────────────────────────

/// The N44 probe end to end: mid-block call in a protected block with
/// phi-carrying successors. After the inline every edge is rebuilt and
/// the module verifies.
#[test]
fn n44_probe_inlines_verifier_clean() {
    let probe = build_n44_probe();
    let mut module = probe.module;
    // The callee is created first (functions[0]).
    let callee_blocks_before = module.functions[0].blocks.clone();
    let pre = verify_module(&module);
    assert!(pre.is_ok(), "probe verifies pre-inline: {:?}", pre.errors);

    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);

    // The continuation owns the moved mul instruction and the successor
    // phi is re-keyed from the call block to the continuation.
    let cont = block_of(&module, probe.mul_inst);
    assert_ne!(cont, probe.call_block, "the call block was split");
    let succ_phi = module.blocks[probe.successor.index()].insts[0];
    let Op::Phi { entries } = &module.insts[succ_phi.index()].op else {
        panic!("successor still starts with a phi");
    };
    assert!(
        entries
            .iter()
            .all(|(e, _)| e.from == cont && e.kind == EdgeKind::Normal),
        "successor phi entries re-keyed to the continuation: {entries:?}"
    );
    // The call block now branches into the callee clone and no longer
    // lists the call.
    let cb = &module.blocks[probe.call_block.index()];
    let last = *cb.insts.last().unwrap();
    assert!(
        matches!(&module.insts[last.index()].op, Op::Branch { .. }),
        "call block ends in a branch into the clone"
    );
    assert!(
        calls_in(&module, probe.caller).is_empty(),
        "the call is gone"
    );
    // The original callee is untouched.
    let g = FuncId::new(0);
    assert_eq!(
        module.functions[g.index()].blocks,
        callee_blocks_before,
        "the callee's own body is never mutated"
    );
}

/// A call block whose terminator loops back to itself: the self-edge
/// and its phi entries must be re-keyed to the continuation.
#[test]
fn self_loop_successor_rekeyed_to_continuation() {
    let mut module = Module::new();
    let g = build_add1_callee(&mut module);
    let f = create_static(&mut module, "f");
    let loop_block;
    let cond_val;
    {
        let mut b = V2Builder::new(&mut module, f);
        let entry = b.entry();
        loop_block = b.create_block();
        let exit = b.create_block();
        b.add_predecessor(loop_block, entry);
        b.add_predecessor(loop_block, loop_block); // back edge
        b.add_predecessor(exit, loop_block);

        let seed = b.emit_number(0.0);
        b.emit_void(Op::Branch { dest: loop_block });

        b.set_insert_block(loop_block);
        let back = b.emit_number(1.0);
        cond_val = b.emit_val(Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: back,
        });
        let loop_phi = b.emit_val(Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: entry,
                        kind: EdgeKind::Normal,
                    },
                    seed,
                ),
                (
                    Edge {
                        from: loop_block,
                        kind: EdgeKind::Normal,
                    },
                    back,
                ),
            ],
        });
        let arg = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: loop_phi,
            right: back,
        });
        let (_c, _r) = emit_closure_call(&mut b, g, None, vec![arg], CallKind::Dynamic);
        b.emit_void(Op::CondBranch {
            cond: cond_val,
            true_dest: loop_block,
            false_dest: exit,
        });

        b.set_insert_block(exit);
        b.emit_void(Op::Return { value: None });
    }
    let pre = verify_module(&module);
    assert!(pre.is_ok(), "probe verifies pre-inline: {:?}", pre.errors);

    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);

    // The loop block's self-pred is re-keyed to the continuation (the
    // CondBranch moved there), including the loop phi's back entry.
    let cont = block_of(&module, {
        // any post-call inst: the CondBranch is the last of the loop
        // block's ORIGINAL insts — find it by scanning for the cond use.
        module.functions[f.index()]
            .blocks
            .iter()
            .flat_map(|&bb| module.blocks[bb.index()].insts.iter().copied())
            .find(|&iid| matches!(&module.insts[iid.index()].op, Op::CondBranch { .. }))
            .expect("cond branch survived")
    });
    let lb = &module.blocks[loop_block.index()];
    assert!(
        !lb.preds
            .iter()
            .any(|e| e.from == loop_block && e.kind == EdgeKind::Normal),
        "the self-pred moved to the continuation: {:?}",
        lb.preds
    );
    assert!(
        lb.preds
            .iter()
            .any(|e| e.from == cont && e.kind == EdgeKind::Normal),
        "the continuation is the back-edge source: {:?}",
        lb.preds
    );
    let loop_phi = lb.insts[0];
    let Op::Phi { entries } = &module.insts[loop_phi.index()].op else {
        panic!("loop phi survived");
    };
    assert!(
        entries
            .iter()
            .any(|(e, _)| e.from == cont && e.kind == EdgeKind::Normal),
        "loop phi back entry re-keyed: {entries:?}"
    );
}

// ─── Try-region caller (N44 defect 3 — the exception-edge rule) ─────────────

/// Protected call site: every cloned block and the continuation join
/// the region, handlers gain Exceptional preds, and handler phis gain
/// same-value entries for each new edge.
#[test]
fn try_region_caller_exception_participation() {
    let probe = build_n44_probe();
    let mut module = probe.module;
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);

    let cont = block_of(&module, probe.mul_inst);
    let f = probe.caller;
    let region = &module.functions[f.index()].try_regions[0];

    // Every cloned callee block plus the continuation is protected.
    // (The clone blocks are the caller's blocks that are neither the
    // original three nor the handler.)
    let originals = [probe.call_block, probe.successor, probe.handler];
    let entry = module.functions[f.index()].blocks[0];
    let cloned: Vec<BlockId> = module.functions[f.index()]
        .blocks
        .iter()
        .copied()
        .filter(|bb| !originals.contains(bb) && *bb != entry && *bb != cont)
        .collect();
    assert!(!cloned.is_empty(), "callee blocks were cloned in");
    for &bb in cloned.iter().chain([cont].iter()) {
        assert!(
            region.protected.contains(&bb),
            "block {bb} must join the protected set: {:?}",
            region.protected
        );
        let exc = Edge {
            from: bb,
            kind: EdgeKind::Exceptional,
        };
        assert!(
            module.blocks[probe.handler.index()].preds.contains(&exc),
            "handler must list the Exceptional pred {exc:?}"
        );
    }
    // The call block keeps its protection (its pre-call instructions
    // could already throw).
    assert!(region.protected.contains(&probe.call_block));

    // The handler phi carries the SAME value on every new exceptional
    // edge as on the original call-block edge (the caller register
    // state at the call) — and there are no new distinct values, so no
    // N38 warning appears.
    let hphi = module.blocks[probe.handler.index()].insts[0];
    let Op::Phi { entries } = &module.insts[hphi.index()].op else {
        panic!("handler still starts with a phi");
    };
    assert_eq!(
        entries.len(),
        module.blocks[probe.handler.index()].preds.len(),
        "phi arity tracks preds"
    );
    assert!(
        entries.iter().all(|(_, v)| *v == probe.handler_phi_value),
        "every exceptional edge carries the call-site value: {entries:?}"
    );
    let post = verify_module(&module);
    assert!(
        post.warnings.is_empty(),
        "no N38 imprecise-join warnings from same-value edges: {:?}",
        post.warnings
    );
}

// ─── Return-flow shapes ──────────────────────────────────────────────────────

/// A diamond callee with two returns: the call result is a phi in the
/// continuation keyed by the two cloned return blocks.
#[test]
fn multi_return_callee_flows_through_phi() {
    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    {
        let mut b = V2Builder::new(&mut module, g);
        let p = b.create_param();
        let t = b.create_block();
        let e = b.create_block();
        b.add_predecessor(t, b.entry());
        b.add_predecessor(e, b.entry());
        b.emit_void(Op::CondBranch {
            cond: p,
            true_dest: t,
            false_dest: e,
        });
        b.set_insert_block(t);
        let one = b.emit_number(1.0);
        b.emit_void(Op::Return { value: Some(one) });
        b.set_insert_block(e);
        let two = b.emit_number(2.0);
        b.emit_void(Op::Return { value: Some(two) });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let a = b.create_param();
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![a], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }

    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);

    // f's continuation begins with a two-entry phi merging the cloned
    // return constants 1 and 2.
    let f_entry = module.functions[f.index()].blocks[0];
    let cont = {
        // The continuation is the block whose Return uses the phi.
        module.functions[f.index()]
            .blocks
            .iter()
            .copied()
            .find(|&bb| {
                bb != f_entry && {
                    module.blocks[bb.index()]
                        .insts
                        .first()
                        .is_some_and(|&iid| matches!(&module.insts[iid.index()].op, Op::Phi { .. }))
                }
            })
            .expect("a continuation with a result phi exists")
    };
    let phi = module.blocks[cont.index()].insts[0];
    let Op::Phi { entries } = &module.insts[phi.index()].op else {
        panic!("continuation starts with a phi");
    };
    assert_eq!(entries.len(), 2, "one entry per return: {entries:?}");
    let mut consts: Vec<f64> = entries
        .iter()
        .map(|(_, v)| {
            let ValueDef::Inst(def) = module.values[v.index()].def else {
                panic!("return values are inst-defined");
            };
            let Op::LoadConst(c) = &module.insts[def.index()].op else {
                panic!("return values are constants");
            };
            module.consts.get(*c).and_then(Const::as_f64).unwrap()
        })
        .collect();
    consts.sort_by(f64::total_cmp);
    assert_eq!(consts, vec![1.0, 2.0]);
    assert!(
        entries
            .iter()
            .all(|(e, _)| e.kind == EdgeKind::Normal
                && module.blocks[e.from.index()].preds.len() >= 1),
        "phi edges come from cloned return blocks: {entries:?}"
    );
    // f's Return uses the phi.
    let ret = *module.blocks[cont.index()].insts.last().unwrap();
    assert!(
        matches!(&module.insts[ret.index()].op, Op::Return { value: Some(v) }
            if *v == module.insts[phi.index()].result.unwrap()),
        "the call result was replaced by the phi"
    );
}

/// A callee that never returns (throws-only body): the continuation is
/// unreachable but the module still verifies.
#[test]
fn never_returning_callee_leaves_unreachable_continuation() {
    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    {
        let mut b = V2Builder::new(&mut module, g);
        let v = b.emit_number(9.0);
        b.emit_void(Op::Throw { value: v });
        b.emit_void(Op::Unreachable);
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);
}

// ─── Skip matrix ─────────────────────────────────────────────────────────────

/// Direct self-recursion is never inlined.
#[test]
fn recursive_callee_is_skipped() {
    let mut module = Module::new();
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let a = b.create_param();
        let (_c, r) = emit_closure_call(&mut b, f, None, vec![a], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 0, "{report:?}");
    assert_eq!(skip_count(&report, SkipReason::SelfRecursive), 1);
    assert_eq!(calls_in(&module, f).len(), 1);
    verify_ok(&module);
}

/// Mutual recursion terminates by construction (each function is
/// processed once; cloned call sites are never revisited).
#[test]
fn mutual_recursion_is_bounded() {
    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    let f = create_static(&mut module, "f");
    // g calls f; f calls g. Both bodies are otherwise trivial.
    {
        let mut b = V2Builder::new(&mut module, g);
        let a = b.create_param();
        let (_c, r) = emit_closure_call(&mut b, f, None, vec![a], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    {
        let mut b = V2Builder::new(&mut module, f);
        let a = b.create_param();
        let one = b.emit_number(1.0);
        let v = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: a,
            right: one,
        });
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![v], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(
        report.sites_inlined, 2,
        "both directions inline exactly once: {report:?}"
    );
    verify_ok(&module);
}

/// `new.target`: bound to a pooled `undefined` for Dynamic calls.
#[test]
fn new_target_bound_to_undefined_for_dynamic_call() {
    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    {
        let mut b = V2Builder::new(&mut module, g);
        let nt = b.emit_val(Op::LoadNewTarget);
        b.emit_void(Op::Return { value: Some(nt) });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);
    // No LoadNewTarget survives in f; a LoadConst of Undefined exists.
    let mut saw_undefined = false;
    for &bb in &module.functions[f.index()].blocks {
        for &iid in &module.blocks[bb.index()].insts {
            match &module.insts[iid.index()].op {
                Op::LoadNewTarget => panic!("new.target must be bound, never cloned raw"),
                Op::LoadConst(c) if matches!(module.consts.get(*c), Some(Const::Undefined)) => {
                    saw_undefined = true;
                }
                _ => {}
            }
        }
    }
    assert!(saw_undefined, "new.target became a pooled undefined");
}

/// `New` call sites are ineligible in this iteration (the `new`
/// result-override semantics needs an OrdinaryCreateFromConstructor op
/// the IR does not have) — so a callee using `new.target` through a
/// `New` site is skipped, never mis-bound.
#[test]
fn new_kind_call_site_is_skipped() {
    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    {
        let mut b = V2Builder::new(&mut module, g);
        let nt = b.emit_val(Op::LoadNewTarget);
        b.emit_void(Op::Return { value: Some(nt) });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![], CallKind::New);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 0, "{report:?}");
    assert_eq!(skip_count(&report, SkipReason::UnsupportedCallKind), 1);
    verify_ok(&module);
}

/// Callees with their own try regions are a first-iteration exclusion.
#[test]
fn callee_with_try_regions_is_skipped() {
    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    {
        let mut b = V2Builder::new(&mut module, g);
        let entry = b.entry();
        let handler = b.create_block();
        let v = b.emit_number(1.0);
        b.emit_void(Op::Return { value: Some(v) });
        b.set_insert_block(handler);
        let hv = b.emit_number(2.0);
        b.emit_void(Op::Return { value: Some(hv) });
        b.add_try(vec![entry], handler);
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 0, "{report:?}");
    assert_eq!(skip_count(&report, SkipReason::CalleeHasTryRegions), 1);
    verify_ok(&module);
}

/// The forbidden-op eligibility exclusions, one probe per class.
#[test]
fn forbidden_callee_ops_are_skipped() {
    use abcd_ir2::SuperKey;
    let cases: Vec<(&str, Op, SkipReason)> = vec![
        (
            "lexenv",
            Op::NewLexEnv { num_vars: 1 },
            SkipReason::CalleeUsesLexEnv,
        ),
        (
            "getlexvar",
            Op::GetLexVar { level: 0, slot: 0 },
            SkipReason::CalleeUsesLexEnv,
        ),
        (
            "arguments",
            Op::GetUnmappedArgs,
            SkipReason::CalleeUsesArguments,
        ),
        (
            "restargs",
            Op::CopyRestArgs { start_index: 0 },
            SkipReason::CalleeUsesArguments,
        ),
        (
            "function-identity",
            Op::LoadFunction,
            SkipReason::CalleeUsesFunctionIdentity,
        ),
        (
            "private",
            Op::LoadPrivate {
                level: 0,
                slot: 0,
                obj: ValueId::new(0),
            },
            SkipReason::CalleeUsesPrivateNames,
        ),
        (
            "await",
            Op::Await {
                value: ValueId::new(0),
            },
            SkipReason::CalleeSuspends,
        ),
    ];

    for (name, op, expected) in cases {
        let mut module = Module::new();
        let g = create_static(&mut module, "g");
        {
            let mut b = V2Builder::new(&mut module, g);
            // Operand-carrying probes use a real const value.
            let cv = b.emit_number(0.0);
            let op = match op {
                Op::LoadPrivate { level, slot, .. } => Op::LoadPrivate {
                    level,
                    slot,
                    obj: cv,
                },
                Op::Await { .. } => Op::Await { value: cv },
                other => other,
            };
            b.emit(op);
            b.emit_void(Op::Return { value: None });
        }
        let f = create_static(&mut module, "f");
        {
            let mut b = V2Builder::new(&mut module, f);
            let (_c, r) = emit_closure_call(&mut b, g, None, vec![], CallKind::Dynamic);
            b.emit_void(Op::Return { value: Some(r) });
        }
        let report = inline_module(&mut module, &default_policy());
        assert_eq!(report.sites_inlined, 0, "{name}: {report:?}");
        assert_eq!(
            skip_count(&report, expected),
            1,
            "{name}: expected {expected:?}, got {:?}",
            report.skips
        );
        verify_ok(&module);
    }

    // super and nested-definition cases (need extra module plumbing).
    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    {
        let mut b = V2Builder::new(&mut module, g);
        let name = b.sym("x");
        b.emit(Op::LoadSuper {
            key: SuperKey::Name(name),
        });
        b.emit_void(Op::Return { value: None });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(
        skip_count(&report, SkipReason::CalleeUsesSuper),
        1,
        "{report:?}"
    );
    verify_ok(&module);

    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    let h = create_static(&mut module, "h");
    {
        // The nested body OBSERVES the captured environment — unsafe
        // to inline its parent.
        let mut b = V2Builder::new(&mut module, h);
        b.emit(Op::GetLexVar { level: 1, slot: 0 });
        b.emit_void(Op::Return { value: None });
    }
    {
        let mut b = V2Builder::new(&mut module, g);
        b.emit(Op::DefineFunc {
            body: h,
            captures: vec![],
            length: 0,
        });
        b.emit_void(Op::Return { value: None });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(
        skip_count(&report, SkipReason::CalleeDefinesClosure),
        1,
        "{report:?}"
    );
    verify_ok(&module);

    // Positive counterpart: a nested definition whose body never
    // observes the environment inlines fine.
    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    let h = create_static(&mut module, "h");
    {
        let mut b = V2Builder::new(&mut module, h);
        let v = b.emit_number(5.0);
        b.emit_void(Op::Return { value: Some(v) });
    }
    {
        let mut b = V2Builder::new(&mut module, g);
        let df = b.emit_val(Op::DefineFunc {
            body: h,
            captures: vec![],
            length: 0,
        });
        b.emit_val(Op::AllocClosure { func: df });
        b.emit_void(Op::Return { value: None });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);
}

/// Non-`Function` callee kinds are ineligible.
#[test]
fn generator_callee_is_skipped() {
    let mut module = Module::new();
    let g = V2Builder::create_function(&mut module, "g", FunctionKind::Generator);
    module.functions[g.index()].modifiers = abcd_ir2::Modifiers::STATIC;
    {
        let mut b = V2Builder::new(&mut module, g);
        b.emit_void(Op::Return { value: None });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 0, "{report:?}");
    assert_eq!(skip_count(&report, SkipReason::CalleeKind), 1);
    verify_ok(&module);
}

/// The documented size cap.
#[test]
fn oversized_callee_is_skipped() {
    let mut module = Module::new();
    let g = build_add1_callee(&mut module); // 3 instructions
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let a = b.create_param();
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![a], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let policy = InlinePolicy {
        max_callee_insts: 2,
        ..InlinePolicy::default()
    };
    let report = inline_module(&mut module, &policy);
    assert_eq!(report.sites_inlined, 0, "{report:?}");
    assert_eq!(skip_count(&report, SkipReason::CalleeTooLarge), 1);
    verify_ok(&module);
}

/// The per-caller inlined-instruction budget bounds fan-out.
#[test]
fn caller_budget_bounds_fanout() {
    let mut module = Module::new();
    let g = build_add1_callee(&mut module); // 3 instructions per inline
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let a = b.create_param();
        let (_c1, r1) = emit_closure_call(&mut b, g, None, vec![a], CallKind::Dynamic);
        let (_c2, r2) = emit_closure_call(&mut b, g, None, vec![r1], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r2) });
    }
    let policy = InlinePolicy {
        max_inlined_insts_per_caller: 3,
        ..InlinePolicy::default()
    };
    let report = inline_module(&mut module, &policy);
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    assert_eq!(skip_count(&report, SkipReason::CallerBudgetExhausted), 1);
    verify_ok(&module);
}

/// An unresolved callee (not AllocClosure→DefineFunc) is skipped.
#[test]
fn unresolved_callee_is_skipped() {
    let mut module = Module::new();
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let p = b.create_param();
        let (_c, r) = {
            let (iid, res) = b.emit(Op::Call {
                callee: p, // a param, not a closure of a known function
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            });
            (iid, res.expect("call result"))
        };
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 0, "{report:?}");
    assert_eq!(skip_count(&report, SkipReason::UnresolvedCallee), 1);
    verify_ok(&module);
}

/// Two call sites in one block: both inline (the second call moves to
/// the first's continuation and is found there).
#[test]
fn two_calls_in_one_block_both_inline() {
    let mut module = Module::new();
    let g = build_add1_callee(&mut module);
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let a = b.create_param();
        let (_c1, r1) = emit_closure_call(&mut b, g, None, vec![a], CallKind::Dynamic);
        let (_c2, r2) = emit_closure_call(&mut b, g, None, vec![r1], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r2) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 2, "{report:?}");
    assert!(calls_in(&module, f).is_empty());
    verify_ok(&module);
}

// ─── Loc fidelity (design §7) ────────────────────────────────────────────────

/// Cloned instructions keep their source locs; splice glue carries
/// `loc: None` — never fabricated.
#[test]
fn loc_fidelity() {
    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    let src_loc = Loc {
        line: 9,
        column: Some(3),
    };
    let g_add;
    {
        let mut b = V2Builder::new(&mut module, g);
        let p = b.create_param();
        let one = b.emit_number(1.0);
        let (add, v) = b.emit(Op::BinaryOp {
            op: BinOp::Add,
            left: p,
            right: one,
        });
        b.emit_void(Op::Return { value: v });
        g_add = add;
    }
    module.insts[g_add.index()].loc = Some(src_loc);
    let f = create_static(&mut module, "f");
    let call_block;
    {
        let mut b = V2Builder::new(&mut module, f);
        let a = b.create_param();
        call_block = b.entry();
        let (_c, r) = emit_closure_call(&mut b, g, None, vec![a], CallKind::Dynamic);
        b.emit_void(Op::Return { value: Some(r) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    verify_ok(&module);

    // The cloned add carries the callee's loc.
    let mut cloned_adds = 0;
    for &bb in &module.functions[f.index()].blocks {
        for &iid in &module.blocks[bb.index()].insts {
            if iid == g_add {
                continue;
            }
            if matches!(
                &module.insts[iid.index()].op,
                Op::BinaryOp { op: BinOp::Add, .. }
            ) {
                cloned_adds += 1;
                assert_eq!(
                    module.insts[iid.index()].loc,
                    Some(src_loc),
                    "the clone keeps the callee's loc"
                );
            }
        }
    }
    assert_eq!(cloned_adds, 1, "exactly one cloned add");
    // The call block's new branch (glue) has no loc.
    let last = *module.blocks[call_block.index()].insts.last().unwrap();
    assert!(matches!(&module.insts[last.index()].op, Op::Branch { .. }));
    assert_eq!(
        module.insts[last.index()].loc,
        None,
        "glue loc is never fabricated"
    );
}

// ─── Statistics ──────────────────────────────────────────────────────────────

/// The report counts what it did (the maintainer's fire-rate evidence).
#[test]
fn report_counts_sites_and_skips() {
    let mut module = Module::new();
    let g = build_add1_callee(&mut module);
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let a = b.create_param();
        let (_c1, r1) = emit_closure_call(&mut b, g, None, vec![a], CallKind::Dynamic);
        let (_c2, r2) = emit_closure_call(&mut b, g, None, vec![r1], CallKind::New);
        b.emit_void(Op::Return { value: Some(r2) });
    }
    let report = inline_module(&mut module, &default_policy());
    assert_eq!(report.sites_inlined, 1, "{report:?}");
    assert_eq!(report.insts_inlined, 3, "{report:?}");
    assert_eq!(skip_count(&report, SkipReason::UnsupportedCallKind), 1);
    verify_ok(&module);
}

/// Sym re-export sanity (used by the super probe).
#[test]
fn sym_roundtrip() {
    let mut module = Module::new();
    let s: Sym = module.sym.intern("x");
    assert_eq!(module.sym.resolve(s), Some("x"));
}
