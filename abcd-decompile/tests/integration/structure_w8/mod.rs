//! Stage-B structuring coverage (the 90%-coverage campaign, worker W8):
//! driver-level tests over hand-built modules.
//!
//! Construction: the regions→structure unit level — the region tree
//! comes from the real `structure_regions` analysis over a crafted CFG,
//! and Stage-A statements from the real `recover_func` unless a test
//! needs an exotic statement shape (then the `RecoveredFunc` is
//! hand-adjusted). Text-level assertions are used only where the text
//! matters; the drivers are pinned by `StructStats` + `SNode` shape.
//!
//! Every bail arm gets a near-miss test (maintainer ruling): the
//! fixture passes every guard but one, and the test asserts the honest
//! fallback fired (the bail counter moved; the legacy shape kept).

use crate::common;
use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_decompile::expr::{Expr, Lit};
use abcd_decompile::recover::{Stmt, recover_func};
use abcd_decompile::structure::{Leaf, SNode, Structured, is_terminal_node, negate};
use abcd_decompile::structure_func;
use abcd_ir::function::{Catch, TryRegion};
use abcd_ir::op::{CmpOp, UnOp};
use abcd_ir::{BlockId, Edge, EdgeKind, FuncId, Module, Op, ValueId};

use common::*;

// ── Local helpers ────────────────────────────────────────────────────

/// `cond`-terminated block helper (truthiness of `c`).
pub(super) fn cond_on(m: &mut Module, b: BlockId, c: ValueId, t: BlockId, f: BlockId) {
    emit_void(
        m,
        b,
        Op::CondBranch {
            cond: c,
            true_dest: t,
            false_dest: f,
        },
    );
}

/// An `istrue(x)` condition value.
pub(super) fn istrue(m: &mut Module, b: BlockId, x: ValueId) -> ValueId {
    emit(
        m,
        b,
        Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: x,
        },
    )
}

/// A plain no-arg call to `callee` (side-effect filler).
pub(super) fn call_p1(m: &mut Module, b: BlockId, callee: ValueId) -> ValueId {
    emit(
        m,
        b,
        Op::Call {
            callee,
            this: None,
            args: vec![],
            kind: abcd_ir::op::CallKind::Dynamic,
        },
    )
}

/// Stage A + Stage B over `f` (the real pipeline).
pub(super) fn structure(m: &Module, f: FuncId) -> Structured {
    let rf = recover_func(m, f);
    structure_func(m, &rf)
}

/// Pre-order flattening of a node list (emission order, descending
/// into arms/bodies).
pub(super) fn flat<'a>(nodes: &'a [SNode], out: &mut Vec<&'a SNode>) {
    let mut stack: Vec<&'a [SNode]> = vec![nodes];
    while let Some(slice) = stack.pop() {
        let Some((n, rest)) = slice.split_first() else {
            continue;
        };
        if !rest.is_empty() {
            stack.push(rest);
        }
        out.push(n);
        match n {
            SNode::If {
                then, otherwise, ..
            } => {
                stack.push(otherwise);
                stack.push(then);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            | SNode::Block(body) => stack.push(body),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                if let Some(f) = finally {
                    stack.push(f);
                }
                for c in catches.iter().rev() {
                    stack.push(&c.body);
                }
                stack.push(body);
            }
            _ => {}
        }
    }
}

/// Whether `pred` matches some node at or after the position of the
/// first node matching `anchor` (document order).
pub(super) fn after_in_doc(
    body: &[SNode],
    anchor: &dyn Fn(&SNode) -> bool,
    pred: &dyn Fn(&SNode) -> bool,
) -> bool {
    let mut all = Vec::new();
    flat(body, &mut all);
    let Some(pos) = all.iter().position(|n| anchor(n)) else {
        return false;
    };
    all[pos + 1..].iter().any(|n| pred(n))
}

/// The decompiled text of the module (header comment stripped).
pub(super) fn decompiled(m: &Module) -> String {
    let d = decompile_module(m, &EmitOptions::default());
    let mut lines: Vec<&str> = d.text.lines().collect();
    assert!(lines.len() >= 2, "header missing:\n{}", d.text);
    let mut out = lines.split_off(2).join("\n");
    if !out.is_empty() {
        out.push('\n');
    }
    out
}

/// The last instruction of a block (its terminator).
pub(super) fn last_inst(m: &Module, b: BlockId) -> abcd_ir::InstId {
    *m.block(b).unwrap().insts.last().unwrap()
}

/// Replace a block's terminator op.
pub(super) fn set_term(m: &mut Module, b: BlockId, op: Op) {
    let i = last_inst(m, b);
    m.inst_mut(i).unwrap().op = op;
}

/// Drop a recorded Normal edge (terminator edits must keep the
/// predecessor tables in sync — the analysis reads both).
pub(super) fn unlink(m: &mut Module, from: BlockId, to: BlockId) {
    m.block_mut(to)
        .unwrap()
        .preds
        .retain(|e| !(e.from == from && e.kind == EdgeKind::Normal));
}

/// Append an op with a result immediately BEFORE the block's
/// terminator (the CFG reads only the last instruction).
pub(super) fn emit_before_term(m: &mut Module, b: BlockId, op: Op) -> ValueId {
    let term = m.block_mut(b).unwrap().insts.pop().expect("a terminator");
    let v = emit(m, b, op);
    m.block_mut(b).unwrap().insts.push(term);
    v
}

mod loop_cut;
mod try_tower;
mod xarm_loops;
