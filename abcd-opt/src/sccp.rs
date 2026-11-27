//! Sparse Conditional Constant Propagation (Wegman–Zadeck 1991; `design/ir.md`,
//! `design/decisions.md` `N23`, `N36`–`N42`, `N47`).
//!
//! Lattice: `Top → Constant(Const) → Bottom`.
//! Dual worklist: kinded CFG edges `(from, to, EdgeKind)` + SSA value users.
//! All operator, comparison, unary, and `ToBoolean` evaluations delegate to the
//! shared ECMA-262 kernel in [`crate::const_eval`].

use std::collections::{HashMap, HashSet, VecDeque};

use abcd_ir::{
    BlockId, Const, EdgeKind, ExceptionHandlerMap, FuncId, InstId, Module, Op, ValueDef, ValueId,
};

use crate::FuncPass;
use crate::const_eval::{
    block_phis, eval_binary_op, eval_compare_op, eval_truthiness, eval_unary_op,
    fold_cond_branch_to_jump, has_static_ty, is_sccp_lattice_const,
};

/// Lattice value for SCCP. [`Const::Number`] stores raw IEEE-754 `u64` bits so
/// `meet()` compares bit-exactly (`meet(+0.0, -0.0) == Bottom`, `R3-H5` / `N37`).
#[derive(Clone, Debug, PartialEq, Eq)]
enum LatticeVal {
    /// Unknown / not yet reached.
    Top,
    /// Known scalar constant.
    Constant(Const),
    /// Overdefined (multiple runtime values possible).
    Bottom,
}

/// The SCCP pass.
pub struct Sccp;

/// A kinded CFG edge in the reachability worklist: `(from, to, kind)`.
type CfgEdge = (BlockId, BlockId, EdgeKind);

impl FuncPass for Sccp {
    fn run(&self, module: &mut Module, func: FuncId) -> bool {
        let Some(func_data) = module.func(func) else {
            return false;
        };
        let Some(entry) = func_data.entry() else {
            return false;
        };
        let blocks: Vec<BlockId> = func_data.blocks.clone();

        // N38(ii): catch-handler blocks. Exception dispatch transfers control
        // mid-block, so handler phis are forced to lattice Bottom.
        let handler_blocks: HashSet<BlockId> = func_data
            .try_regions
            .iter()
            .flat_map(|region| region.catches.iter().map(|c| c.handler))
            .collect();
        let Some(exc_map) = ExceptionHandlerMap::build(module, func) else {
            return false;
        };

        let mut lattice: HashMap<ValueId, LatticeVal> = HashMap::new();
        for &val in module
            .func(func)
            .map(|f| f.params.as_slice())
            .unwrap_or(&[])
        {
            lattice.insert(val, LatticeVal::Bottom);
        }

        // Build use-list: Value → Vec<Inst> that use it.
        let mut use_list: HashMap<ValueId, Vec<InstId>> = HashMap::new();
        for &bb in &blocks {
            let Some(block) = module.block(bb) else {
                continue;
            };
            for &inst_id in &block.insts {
                let Some(inst) = module.inst(inst_id) else {
                    continue;
                };
                inst.op.for_each_operand(|val| {
                    use_list.entry(val).or_default().push(inst_id);
                });
            }
        }

        let mut cfg_worklist: VecDeque<CfgEdge> = VecDeque::new();
        let mut ssa_worklist: VecDeque<ValueId> = VecDeque::new();
        let mut reachable_edges: HashSet<CfgEdge> = HashSet::new();
        let mut reachable_blocks: HashSet<BlockId> = HashSet::new();

        // Seed entry block accurately: record `Exceptional` handler edges for
        // `entry`, evaluate its instructions in order, and seed outgoing Normal
        // edges via `add_cfg_edges` so an already-constant entry `CondBranch`
        // never marks its dead arm reachable.
        reachable_blocks.insert(entry);
        visit_block_first_time(
            module,
            entry,
            &exc_map,
            &mut lattice,
            &mut ssa_worklist,
            &mut cfg_worklist,
            &reachable_edges,
            &handler_blocks,
            true,
        );

        loop {
            if cfg_worklist.is_empty() && ssa_worklist.is_empty() {
                break;
            }

            while let Some((from, to, kind)) = cfg_worklist.pop_front() {
                if !reachable_edges.insert((from, to, kind)) {
                    continue;
                }
                let first_time = reachable_blocks.insert(to);

                for phi_id in block_phis(module, to) {
                    if let Some(new_val) =
                        evaluate_phi(module, phi_id, &lattice, &reachable_edges, &handler_blocks)
                    {
                        record_result(module, phi_id, new_val, &mut lattice, &mut ssa_worklist);
                    }
                }

                if first_time {
                    visit_block_first_time(
                        module,
                        to,
                        &exc_map,
                        &mut lattice,
                        &mut ssa_worklist,
                        &mut cfg_worklist,
                        &reachable_edges,
                        &handler_blocks,
                        false,
                    );
                }
            }

            while let Some(val) = ssa_worklist.pop_front() {
                let Some(users) = use_list.get(&val) else {
                    continue;
                };
                for &inst_id in users {
                    let Some(inst_block) = module.inst(inst_id).map(|i| i.block) else {
                        continue;
                    };
                    if !reachable_blocks.contains(&inst_block) {
                        continue;
                    }
                    let is_phi = module.inst(inst_id).is_some_and(|i| i.op.is_phi());
                    if is_phi {
                        if let Some(new_val) = evaluate_phi(
                            module,
                            inst_id,
                            &lattice,
                            &reachable_edges,
                            &handler_blocks,
                        ) {
                            record_result(
                                module,
                                inst_id,
                                new_val,
                                &mut lattice,
                                &mut ssa_worklist,
                            );
                        }
                    } else {
                        if let Some(new_val) = evaluate_inst(module, inst_id, &lattice) {
                            record_result(
                                module,
                                inst_id,
                                new_val,
                                &mut lattice,
                                &mut ssa_worklist,
                            );
                        }
                        add_cfg_edges(module, &exc_map, inst_id, &lattice, &mut cfg_worklist);
                    }
                }
            }
        }

        // Apply results: replace constants and fold dead or identical-target branches.
        let mut changed = false;

        for &bb in &blocks {
            if !reachable_blocks.contains(&bb) {
                continue;
            }
            let Some(block) = module.block(bb) else {
                continue;
            };
            let all_insts: Vec<InstId> = block.insts.clone();

            let mut folded_phis: Vec<InstId> = Vec::new();
            for inst_id in all_insts {
                let Some(result) = module.inst(inst_id).and_then(|i| i.result) else {
                    continue;
                };
                if let Some(LatticeVal::Constant(c)) = lattice.get(&result) {
                    let c = c.clone();
                    if inst_is_const(module, inst_id, &c) {
                        continue;
                    }
                    let was_phi = module.inst(inst_id).is_some_and(|i| i.op.is_phi());
                    let cid = module.consts.intern(c);
                    if let Some(inst) = module.inst_mut(inst_id) {
                        inst.op = Op::LoadConst(cid);
                    }
                    if was_phi {
                        folded_phis.push(inst_id);
                    }
                    changed = true;
                }
            }

            // Batch-move all folded phis out of the leading phi prefix in a
            // single `O(|insts|)` pass per block (`R3-X7`).
            if !folded_phis.is_empty()
                && let Some(block) = module.block(bb)
            {
                let folded_set: HashSet<InstId> = folded_phis.iter().copied().collect();
                let mut reordered = Vec::with_capacity(block.insts.len());
                let mut tail_start = 0usize;
                for (idx, &iid) in block.insts.iter().enumerate() {
                    if folded_set.contains(&iid) {
                        tail_start = idx + 1;
                        continue;
                    }
                    if module.inst(iid).is_some_and(|inst| inst.op.is_phi()) {
                        reordered.push(iid);
                        tail_start = idx + 1;
                    } else {
                        break;
                    }
                }
                reordered.extend(folded_phis.iter().copied());
                for &iid in &block.insts[tail_start..] {
                    if !folded_set.contains(&iid) {
                        reordered.push(iid);
                    }
                }
                if let Some(block) = module.block_mut(bb) {
                    block.insts = reordered;
                }
            }

            // Fold CondBranch when `true_dest == false_dest` or `cond` has known
            // `ToBoolean` truthiness (`R3-M6`, `N23`).
            let Some(&last) = module.block(bb).and_then(|b| b.insts.last()) else {
                continue;
            };
            let Some(Op::CondBranch {
                cond,
                true_dest,
                false_dest,
            }) = module.inst(last).map(|i| i.op.clone())
            else {
                continue;
            };
            if true_dest == false_dest {
                if fold_cond_branch_to_jump(module, bb, last, true_dest, false_dest) {
                    changed = true;
                }
                continue;
            }
            let cond_lat = get_lattice(module, &lattice, cond);
            let known_const = match &cond_lat {
                LatticeVal::Constant(c) => Some(c),
                _ => None,
            };
            if let Some(is_true) = eval_truthiness(module, cond, known_const) {
                let target = if is_true { true_dest } else { false_dest };
                let dead = if is_true { false_dest } else { true_dest };
                if dead == entry
                    && !block_phis(module, entry).is_empty()
                    && module.block(entry).is_some_and(|b| b.preds.len() <= 1)
                {
                    continue;
                }
                if fold_cond_branch_to_jump(module, bb, last, target, dead) {
                    changed = true;
                }
            }
        }

        changed
    }
}

/// Evaluate a newly reached block's instructions and seed its outgoing
/// normal and exceptional CFG edges.
#[expect(
    clippy::too_many_arguments,
    reason = "Wegman-Zadeck block visit threads module, exception map, lattice, and dual worklists"
)]
fn visit_block_first_time(
    module: &Module,
    bb: BlockId,
    exc_map: &ExceptionHandlerMap,
    lattice: &mut HashMap<ValueId, LatticeVal>,
    ssa_worklist: &mut VecDeque<ValueId>,
    cfg_worklist: &mut VecDeque<CfgEdge>,
    reachable_edges: &HashSet<CfgEdge>,
    handler_blocks: &HashSet<BlockId>,
    eval_leading_phis: bool,
) {
    // Seed implicit exception edges immediately when `bb` becomes reachable
    // (`N38(i)`, `N47`) so catch handlers are reached even if `bb` ends in
    // `Return`/`Unreachable` or lacks a terminator in unverified IR.
    for &handler in exc_map.handlers_of(bb) {
        cfg_worklist.push_back((bb, handler, EdgeKind::Exceptional));
    }

    let insts: Vec<InstId> = module
        .block(bb)
        .map(|b| b.insts.clone())
        .unwrap_or_default();
    for inst_id in insts {
        let is_phi = module.inst(inst_id).is_some_and(|i| i.op.is_phi());
        if is_phi {
            if eval_leading_phis
                && let Some(new_val) =
                    evaluate_phi(module, inst_id, lattice, reachable_edges, handler_blocks)
            {
                record_result(module, inst_id, new_val, lattice, ssa_worklist);
            }
            continue;
        }
        if let Some(new_val) = evaluate_inst(module, inst_id, lattice) {
            record_result(module, inst_id, new_val, lattice, ssa_worklist);
        }
        add_cfg_edges(module, exc_map, inst_id, lattice, cfg_worklist);
    }
}

/// Meet `new_val` into the lattice entry of `inst_id`'s result, pushing
/// the result onto the SSA worklist when the entry changed.
fn record_result(
    module: &Module,
    inst_id: InstId,
    new_val: LatticeVal,
    lattice: &mut HashMap<ValueId, LatticeVal>,
    ssa_worklist: &mut VecDeque<ValueId>,
) {
    let Some(result) = module.inst(inst_id).and_then(|i| i.result) else {
        return;
    };
    let old = lattice.get(&result).cloned().unwrap_or(LatticeVal::Top);
    let met = meet(&old, &new_val);
    if met != old {
        lattice.insert(result, met);
        ssa_worklist.push_back(result);
    }
}

/// Lattice meet: `Top ⊓ x = x`, `x ⊓ x = x`, else `Bottom`.
fn meet(a: &LatticeVal, b: &LatticeVal) -> LatticeVal {
    match (a, b) {
        (LatticeVal::Top, x) | (x, LatticeVal::Top) => x.clone(),
        (LatticeVal::Constant(ca), LatticeVal::Constant(cb)) if ca == cb => a.clone(),
        _ => LatticeVal::Bottom,
    }
}

/// Evaluate a non-phi instruction to a lattice value via [`crate::const_eval`].
fn evaluate_inst(
    module: &Module,
    inst_id: InstId,
    lattice: &HashMap<ValueId, LatticeVal>,
) -> Option<LatticeVal> {
    let inst = module.inst(inst_id)?;
    inst.result?;

    match &inst.op {
        Op::LoadConst(cid) => match module.consts.get(*cid) {
            Some(c) if is_sccp_lattice_const(c) => Some(LatticeVal::Constant(c.clone())),
            _ => Some(LatticeVal::Bottom),
        },

        Op::BinaryOp { op, left, right } => {
            if has_static_ty(module, inst_id) {
                return Some(LatticeVal::Bottom);
            }
            let lv = get_lattice(module, lattice, *left);
            let rv = get_lattice(module, lattice, *right);
            match (&lv, &rv) {
                (LatticeVal::Bottom, _) | (_, LatticeVal::Bottom) => Some(LatticeVal::Bottom),
                (LatticeVal::Top, _) | (_, LatticeVal::Top) => None,
                (LatticeVal::Constant(lc), LatticeVal::Constant(rc)) => Some(
                    eval_binary_op(*op, lc, rc).map_or(LatticeVal::Bottom, LatticeVal::Constant),
                ),
            }
        }

        Op::Compare { op, left, right } => {
            if has_static_ty(module, inst_id) {
                return Some(LatticeVal::Bottom);
            }
            let lv = get_lattice(module, lattice, *left);
            let rv = get_lattice(module, lattice, *right);
            match (&lv, &rv) {
                (LatticeVal::Bottom, _) | (_, LatticeVal::Bottom) => Some(LatticeVal::Bottom),
                (LatticeVal::Top, _) | (_, LatticeVal::Top) => None,
                (LatticeVal::Constant(lc), LatticeVal::Constant(rc)) => Some(
                    eval_compare_op(&module.sym, *op, lc, rc)
                        .map_or(LatticeVal::Bottom, LatticeVal::Constant),
                ),
            }
        }

        Op::UnaryOp { op, operand } => {
            if has_static_ty(module, inst_id) {
                return Some(LatticeVal::Bottom);
            }
            match get_lattice(module, lattice, *operand) {
                LatticeVal::Top => None,
                LatticeVal::Constant(c) => Some(
                    eval_unary_op(module, *op, *operand, Some(&c))
                        .map_or(LatticeVal::Bottom, LatticeVal::Constant),
                ),
                LatticeVal::Bottom => Some(
                    eval_unary_op(module, *op, *operand, None)
                        .map_or(LatticeVal::Bottom, LatticeVal::Constant),
                ),
            }
        }

        // Everything else: if any operand is Bottom → Bottom, else if any is
        // Top → None, else Bottom (`R3-A5`: zero Vec allocation).
        _ => {
            let mut any_operand = false;
            let mut has_bottom = false;
            let mut has_top = false;
            inst.op.for_each_operand(|val| {
                any_operand = true;
                if !has_bottom {
                    match get_lattice(module, lattice, val) {
                        LatticeVal::Bottom => has_bottom = true,
                        LatticeVal::Top => has_top = true,
                        LatticeVal::Constant(_) => {}
                    }
                }
            });
            if !any_operand || has_bottom || !has_top {
                Some(LatticeVal::Bottom)
            } else {
                None
            }
        }
    }
}

/// Evaluate a phi node considering only reachable incoming edges (`N38(ii)`).
fn evaluate_phi(
    module: &Module,
    phi_id: InstId,
    lattice: &HashMap<ValueId, LatticeVal>,
    reachable_edges: &HashSet<CfgEdge>,
    handler_blocks: &HashSet<BlockId>,
) -> Option<LatticeVal> {
    let phi_block = module.inst(phi_id)?.block;
    if handler_blocks.contains(&phi_block) {
        return Some(LatticeVal::Bottom);
    }
    if let Op::Phi { entries } = &module.inst(phi_id)?.op {
        let mut result = LatticeVal::Top;
        for (edge, val) in entries {
            if !reachable_edges.contains(&(edge.from, phi_block, edge.kind)) {
                continue;
            }
            let v = get_lattice(module, lattice, *val);
            result = meet(&result, &v);
        }
        Some(result)
    } else {
        None
    }
}

/// Add outgoing CFG edges from a terminator instruction based on lattice state,
/// plus protecting [`ExceptionHandlerMap`] edges (`N38(i)`, `N47`).
fn add_cfg_edges(
    module: &Module,
    exc_map: &ExceptionHandlerMap,
    inst_id: InstId,
    lattice: &HashMap<ValueId, LatticeVal>,
    cfg_worklist: &mut VecDeque<CfgEdge>,
) {
    let Some(inst) = module.inst(inst_id) else {
        return;
    };
    let block = inst.block;
    match &inst.op {
        Op::Branch { dest } => {
            cfg_worklist.push_back((block, *dest, EdgeKind::Normal));
        }
        Op::CondBranch {
            cond,
            true_dest,
            false_dest,
        } => {
            if *true_dest == *false_dest {
                cfg_worklist.push_back((block, *true_dest, EdgeKind::Normal));
            } else {
                let cond_lat = get_lattice(module, lattice, *cond);
                if matches!(cond_lat, LatticeVal::Top) && module.value(*cond).is_some() {
                    // Optimistic Wegman-Zadeck: wait until `cond` lowers from `Top`
                    // on `ssa_worklist` before seeding normal arms.
                } else {
                    let known_const = match &cond_lat {
                        LatticeVal::Constant(c) => Some(c),
                        _ => None,
                    };
                    match eval_truthiness(module, *cond, known_const) {
                        Some(true) => {
                            cfg_worklist.push_back((block, *true_dest, EdgeKind::Normal));
                        }
                        Some(false) => {
                            cfg_worklist.push_back((block, *false_dest, EdgeKind::Normal));
                        }
                        None => {
                            cfg_worklist.push_back((block, *true_dest, EdgeKind::Normal));
                            cfg_worklist.push_back((block, *false_dest, EdgeKind::Normal));
                        }
                    }
                }
            }
        }
        // Return / Unreachable: fall through so exception edges still seed (`N47`).
        _ if inst.op.is_terminator() => {}
        _ => return,
    }
    for &handler in exc_map.handlers_of(block) {
        cfg_worklist.push_back((block, handler, EdgeKind::Exceptional));
    }
}

/// Lattice lookup resolving `ValueDef::Const` and `ValueDef::ExceptionParam` on demand.
fn get_lattice(
    module: &Module,
    lattice: &HashMap<ValueId, LatticeVal>,
    val: ValueId,
) -> LatticeVal {
    if let Some(v) = lattice.get(&val) {
        return v.clone();
    }
    let Some(value) = module.value(val) else {
        return LatticeVal::Top;
    };
    match value.def {
        ValueDef::Const(cid) => match module.consts.get(cid) {
            Some(c) if is_sccp_lattice_const(c) => LatticeVal::Constant(c.clone()),
            _ => LatticeVal::Bottom,
        },
        ValueDef::ExceptionParam(_) => LatticeVal::Bottom,
        _ => LatticeVal::Top,
    }
}

/// Whether `inst_id` already loads a constant bit-identically equal to `c` (`N37`).
fn inst_is_const(module: &Module, inst_id: InstId, c: &Const) -> bool {
    let Some(inst) = module.inst(inst_id) else {
        return false;
    };
    let Op::LoadConst(cid) = inst.op else {
        return false;
    };
    module.consts.get(cid) == Some(c)
}
