//! Peephole optimization: local constant folding and conditional-branch
//! folding backed by [`crate::const_eval`] (`design/ir.md`,
//! `design/decisions.md` `N23`, `N36`–`N42`).
//!
//! Key design invariants:
//!
//! - Arithmetic, relational/equality, and unary folds delegate to the single
//!   shared ECMA-262 constant-evaluation kernel in [`crate::const_eval`].
//! - Folded value instructions become [`Op::LoadConst`] of a freshly interned
//!   [`Const`] (append-only pool; the instruction keeps its result
//!   [`abcd_ir::ValueId`], so no use rewrites are needed).
//! - Block-ending [`Op::CondBranch`] instructions fold to [`Op::Branch`] when
//!   `true_dest == false_dest` or when `cond`'s ECMA-262 `ToBoolean` truthiness
//!   is statically known, pruning any dropped normal predecessor edge and
//!   matching [`Op::Phi`] incoming entries (`N23`) while leaving `cond`'s
//!   producer instruction intact if it has observable effects.

use abcd_ir::{BlockId, Const, FuncId, InstId, Module, Op};

use crate::FuncPass;
use crate::const_eval::{
    block_phis, const_of_value, eval_binary_op, eval_compare_op, eval_truthiness, eval_unary_op,
    fold_cond_branch_to_jump, has_static_ty,
};

/// The peephole pass: local constant folding and branch simplification.
pub struct Peephole;

impl FuncPass for Peephole {
    fn run(&self, module: &mut Module, func: FuncId) -> bool {
        let mut changed = false;
        let Some(func_data) = module.func(func) else {
            return false;
        };
        let Some(entry) = func_data.entry() else {
            return false;
        };
        let blocks: Vec<BlockId> = func_data.blocks.clone();

        for bb in blocks {
            let Some(block) = module.block(bb) else {
                continue;
            };
            let insts: Vec<InstId> = block.insts.clone();
            for inst_id in insts {
                if let Some(folded) = try_fold(module, inst_id) {
                    let cid = module.consts.intern(folded);
                    if let Some(inst) = module.inst_mut(inst_id) {
                        inst.op = Op::LoadConst(cid);
                        changed = true;
                    }
                    continue;
                }
                if try_fold_cond_branch(module, entry, bb, inst_id) {
                    changed = true;
                }
            }
        }
        changed
    }
}

/// Try to fold a value-producing instruction into a scalar [`Const`].
fn try_fold(module: &Module, inst_id: InstId) -> Option<Const> {
    if has_static_ty(module, inst_id) {
        return None;
    }
    let inst = module.inst(inst_id)?;
    inst.result?;
    match &inst.op {
        Op::BinaryOp { op, left, right } => {
            let lc = const_of_value(module, *left)?;
            let rc = const_of_value(module, *right)?;
            eval_binary_op(*op, &lc, &rc)
        }
        Op::Compare { op, left, right } => {
            let lc = const_of_value(module, *left)?;
            let rc = const_of_value(module, *right)?;
            eval_compare_op(&module.sym, *op, &lc, &rc)
        }
        Op::UnaryOp { op, operand } => {
            let oc = const_of_value(module, *operand);
            eval_unary_op(module, *op, *operand, oc.as_ref())
        }
        _ => None,
    }
}

/// Try to fold a `CondBranch` (`true_dest == false_dest` or statically known
/// `ToBoolean` condition) into an unconditional `Branch`.
fn try_fold_cond_branch(module: &mut Module, entry: BlockId, bb: BlockId, inst_id: InstId) -> bool {
    let Some(inst) = module.inst(inst_id) else {
        return false;
    };
    let Op::CondBranch {
        cond,
        true_dest,
        false_dest,
    } = inst.op
    else {
        return false;
    };
    if true_dest == false_dest {
        return fold_cond_branch_to_jump(module, bb, inst_id, true_dest, false_dest);
    }
    let known_const = const_of_value(module, cond);
    let Some(is_true) = eval_truthiness(module, cond, known_const.as_ref()) else {
        return false;
    };
    let target = if is_true { true_dest } else { false_dest };
    let dead = if is_true { false_dest } else { true_dest };
    // Defensive guard for unverified IR: never leave a reachable zero-predecessor
    // phi on `entry` (`N27`).
    if dead == entry
        && !block_phis(module, entry).is_empty()
        && module.block(entry).is_some_and(|b| b.preds.len() <= 1)
    {
        return false;
    }
    fold_cond_branch_to_jump(module, bb, inst_id, target, dead)
}
