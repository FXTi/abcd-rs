//! Sparse Conditional Constant Propagation (Wegman-Zadeck 1991) — the
//! v0.2 port of v0.1 `opt::sccp`.
//!
//! Lattice: Top → Constant(val) → Bottom.
//! Dual worklist: CFG edges (reachability) + SSA edges (value changes).
//! After convergence: replace constants, fold dead branches.
//!
//! v0.2 port notes:
//!
//! - CFG edges are kinded (T5): the worklist tracks
//!   `(from, to, kind)` triples and phi entries match on the full
//!   [`Edge`] — an exceptional in-edge and a normal in-edge from the
//!   same block are distinct lattice inputs.
//! - Constants surface in two definition forms: [`Op::LoadConst`]
//!   instructions (evaluated here) and [`ValueDef::Const`] values
//!   (resolved on demand — the frame-initial values are const-defined,
//!   not seeded instructions).
//! - Replacement writes [`Op::LoadConst`] of a freshly pooled [`Const`];
//!   a folded PHI is moved out of the block's phi prefix (the verifier
//!   requires phis to lead the block).

use std::collections::{HashMap, HashSet, VecDeque};

use abcd_ir2::{
    BinOp, BlockId, CmpOp, Const, Edge, EdgeKind, FuncId, InstId, Module, Op, UnOp, ValueDef,
    ValueId,
};

use crate::FuncPass;
use crate::{to_int32, to_uint32};

/// Lattice value for SCCP.
#[derive(Clone, Debug, PartialEq)]
enum LatticeVal {
    Top,                // Unknown / not yet reached
    Constant(ConstVal), // Known constant
    Bottom,             // Overdefined (multiple values possible)
}

/// Constant value representation. `Number` keeps the host `f64` (v0.1
/// parity: the lattice meet compares numbers with host `==`, so
/// `0.0 == -0.0` meet to whichever arrived first; conversion back to a
/// pooled [`Const::Number`] is bit-exact, preserving `-0.0`/NaN payloads
/// — N37).
#[derive(Clone, Debug, PartialEq)]
enum ConstVal {
    Number(f64),
    Bool(bool),
    Null,
    Undefined,
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

        // N38(ii): catch-handler blocks. Exception dispatch transfers
        // control from ANY protected instruction to the handler
        // mid-block, so a handler phi entry keyed by a protected pred
        // carries that pred's BLOCK-END value, which is not the value
        // live at the point of exception — folding handler phis is
        // unsound. They are forced to lattice Bottom in evaluate_phi.
        let handler_blocks: HashSet<BlockId> = func_data
            .try_regions
            .iter()
            .flat_map(|region| region.catches.iter().map(|c| c.handler))
            .collect();

        // Initialize lattice: all values start at Top.
        let mut lattice: HashMap<ValueId, LatticeVal> = HashMap::new();

        // Function params are Bottom (unknown input). `params` is the
        // authoritative parameter identity. (ExceptionParam values and
        // const-defined values need no seeding: `get_lattice` resolves
        // them on demand — Bottom and the scalar constant respectively.)
        for &val in &func_data.params {
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
                for val in inst.op.operands() {
                    use_list.entry(val).or_default().push(inst_id);
                }
            }
        }

        // Worklists.
        let mut cfg_worklist: VecDeque<CfgEdge> = VecDeque::new();
        let mut ssa_worklist: VecDeque<ValueId> = VecDeque::new();
        let mut reachable_edges: HashSet<CfgEdge> = HashSet::new();
        let mut reachable_blocks: HashSet<BlockId> = HashSet::new();

        // Seed: entry block is reachable. Process the entry block's
        // instructions (phis via evaluate_phi, the rest via
        // evaluate_inst — same split as newly reached blocks).
        reachable_blocks.insert(entry);
        if let Some(entry_block) = module.block(entry) {
            for &inst_id in &entry_block.insts.clone() {
                evaluate_and_record(
                    module,
                    inst_id,
                    &mut lattice,
                    &mut ssa_worklist,
                    &reachable_edges,
                    &handler_blocks,
                );
            }
        }
        // Seed CFG edges from entry — AUGMENTED successors (N38(i)):
        // exception edges included, so catch handlers are reachable.
        for edge in crate::analysis::augmented_succs(module, func, entry) {
            cfg_worklist.push_back((entry, edge.0, edge.1));
        }

        // Main loop.
        loop {
            let has_cfg = !cfg_worklist.is_empty();
            let has_ssa = !ssa_worklist.is_empty();
            if !has_cfg && !has_ssa {
                break;
            }

            // Process CFG edges.
            while let Some((from, to, kind)) = cfg_worklist.pop_front() {
                if !reachable_edges.insert((from, to, kind)) {
                    continue;
                }
                let first_time = reachable_blocks.insert(to);

                // Re-evaluate phis in `to` (new edge may change phi values).
                let phis: Vec<InstId> = module
                    .block(to)
                    .map(|b| {
                        b.insts
                            .iter()
                            .copied()
                            .take_while(|&id| module.inst(id).is_some_and(|i| i.op.is_phi()))
                            .collect()
                    })
                    .unwrap_or_default();
                for &phi_id in &phis {
                    if let Some(new_val) =
                        evaluate_phi(module, phi_id, &lattice, &reachable_edges, &handler_blocks)
                    {
                        record_result(module, phi_id, new_val, &mut lattice, &mut ssa_worklist);
                    }
                }

                if first_time {
                    // Evaluate all non-phi instructions.
                    let insts: Vec<InstId> = module
                        .block(to)
                        .map(|b| b.insts.clone())
                        .unwrap_or_default();
                    for &inst_id in &insts {
                        let is_phi = module.inst(inst_id).is_some_and(|i| i.op.is_phi());
                        if is_phi {
                            continue; // already evaluated above
                        }
                        if let Some(new_val) = evaluate_inst(module, inst_id, &lattice) {
                            record_result(
                                module,
                                inst_id,
                                new_val,
                                &mut lattice,
                                &mut ssa_worklist,
                            );
                        }
                        // Add CFG edges from terminators.
                        add_cfg_edges(module, func, inst_id, &lattice, &mut cfg_worklist);
                    }
                }
            }

            // Process SSA edges.
            while let Some(val) = ssa_worklist.pop_front() {
                if let Some(users) = use_list.get(&val) {
                    for &inst_id in users {
                        let inst_block = module.inst(inst_id).map(|i| i.block);
                        let Some(inst_block) = inst_block else {
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
                            add_cfg_edges(module, func, inst_id, &lattice, &mut cfg_worklist);
                        }
                    }
                }
            }
        }

        // Apply results: replace constants and fold dead branches.
        let mut changed = false;

        for &bb in &blocks {
            if !reachable_blocks.contains(&bb) {
                continue;
            }
            let Some(block) = module.block(bb) else {
                continue;
            };
            let all_insts: Vec<InstId> = block.insts.clone();

            for inst_id in all_insts {
                let Some(result) = module.inst(inst_id).and_then(|i| i.result) else {
                    continue;
                };
                if let Some(LatticeVal::Constant(c)) = lattice.get(&result) {
                    let c = c.clone();
                    // Skip when the instruction already loads an equal
                    // constant (bit-exact for numbers — N37).
                    if inst_is_const(module, inst_id, &c) {
                        continue;
                    }
                    let was_phi = module.inst(inst_id).is_some_and(|i| i.op.is_phi());
                    let cid = module.consts.push(const_to_const(&c));
                    if let Some(inst) = module.inst_mut(inst_id) {
                        inst.op = Op::LoadConst(cid);
                    }
                    if was_phi {
                        // Move the folded phi out of the phi prefix to
                        // just past the remaining phis (the verifier
                        // requires phis to lead the block).
                        if let Some(block) = module.block(bb) {
                            let insert_at =
                                if let Some(pos) = block.insts.iter().position(|&i| i == inst_id) {
                                    let mut rest: Vec<InstId> = block.insts.clone();
                                    rest.remove(pos);
                                    let insert_at = rest
                                        .iter()
                                        .take_while(|&&i| {
                                            module.inst(i).is_some_and(|inst| inst.op.is_phi())
                                        })
                                        .count();
                                    if let Some(block) = module.block_mut(bb) {
                                        block.insts = rest;
                                    }
                                    Some(insert_at)
                                } else {
                                    None
                                };
                            if let Some(insert_at) = insert_at {
                                if let Some(block) = module.block_mut(bb) {
                                    block.insts.insert(insert_at, inst_id);
                                }
                            }
                        }
                    }
                    changed = true;
                }
            }

            // Fold CondBranch with known condition.
            let Some(block) = module.block(bb) else {
                continue;
            };
            let Some(&last) = block.insts.last() else {
                continue;
            };
            let Some(inst) = module.inst(last) else {
                continue;
            };
            if let Op::CondBranch {
                cond,
                true_dest,
                false_dest,
            } = &inst.op
            {
                let cond = *cond;
                let true_dest = *true_dest;
                let false_dest = *false_dest;
                if let Some(LatticeVal::Constant(c)) = lattice.get(&cond) {
                    let is_true = const_is_truthy(c);
                    let target = if is_true { true_dest } else { false_dest };
                    let dead = if is_true { false_dest } else { true_dest };
                    if let Some(inst) = module.inst_mut(last) {
                        inst.op = Op::Branch { dest: target };
                    }
                    // Remove the Normal edge bb→dead from dead's preds AND
                    // from its phi entries (N23/N27): a stale entry keyed
                    // by bb survives on the IMPOSSIBLE path, and a later
                    // merge/dedup can resurrect its value over the value
                    // from the only live path. When both dests name the
                    // same block the edge is still live (the branch still
                    // targets it), so nothing is removed.
                    if dead != target {
                        let dead_edge = Edge {
                            from: bb,
                            kind: EdgeKind::Normal,
                        };
                        if let Some(dead_block) = module.block_mut(dead) {
                            dead_block.preds.retain(|e| *e != dead_edge);
                        }
                        let dead_phis: Vec<InstId> = module
                            .block(dead)
                            .map(|b| {
                                b.insts
                                    .iter()
                                    .copied()
                                    .take_while(|&id| {
                                        module.inst(id).is_some_and(|i| i.op.is_phi())
                                    })
                                    .collect()
                            })
                            .unwrap_or_default();
                        for phi_id in dead_phis {
                            if let Some(inst) = module.inst_mut(phi_id) {
                                if let Op::Phi { entries } = &mut inst.op {
                                    entries.retain(|(edge, _)| *edge != dead_edge);
                                }
                            }
                        }
                    }
                    changed = true;
                }
            }
        }

        changed
    }
}

/// Evaluate `inst_id` (phi or not) and record a lattice change.
fn evaluate_and_record(
    module: &Module,
    inst_id: InstId,
    lattice: &mut HashMap<ValueId, LatticeVal>,
    ssa_worklist: &mut VecDeque<ValueId>,
    reachable_edges: &HashSet<CfgEdge>,
    handler_blocks: &HashSet<BlockId>,
) {
    let is_phi = module.inst(inst_id).is_some_and(|i| i.op.is_phi());
    let new_val = if is_phi {
        evaluate_phi(module, inst_id, lattice, reachable_edges, handler_blocks)
    } else {
        evaluate_inst(module, inst_id, lattice)
    };
    if let Some(new_val) = new_val {
        record_result(module, inst_id, new_val, lattice, ssa_worklist);
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

/// Lattice meet: Top ⊓ x = x, x ⊓ x = x, else Bottom.
fn meet(a: &LatticeVal, b: &LatticeVal) -> LatticeVal {
    match (a, b) {
        (LatticeVal::Top, x) | (x, LatticeVal::Top) => x.clone(),
        (LatticeVal::Constant(ca), LatticeVal::Constant(cb)) if ca == cb => a.clone(),
        _ => LatticeVal::Bottom,
    }
}

/// Evaluate a non-phi instruction to a lattice value.
fn evaluate_inst(
    module: &Module,
    inst_id: InstId,
    lattice: &HashMap<ValueId, LatticeVal>,
) -> Option<LatticeVal> {
    let inst = module.inst(inst_id)?;
    // If the instruction doesn't produce a result, nothing to evaluate.
    if inst.result.is_none() {
        return None;
    }

    match &inst.op {
        Op::LoadConst(cid) => match module.consts.get(*cid) {
            // Only the scalar constants enter the lattice (v0.1 folded
            // LiteralNumber/Bool/Null/Undefined/NaN/Infinity and forced
            // everything else — strings, bigints, literal arrays, the
            // hole — to Bottom).
            Some(Const::Undefined) => Some(LatticeVal::Constant(ConstVal::Undefined)),
            Some(Const::Null) => Some(LatticeVal::Constant(ConstVal::Null)),
            Some(Const::Bool(b)) => Some(LatticeVal::Constant(ConstVal::Bool(*b))),
            Some(Const::Number(bits)) => Some(LatticeVal::Constant(ConstVal::Number(
                f64::from_bits(*bits),
            ))),
            Some(_) => Some(LatticeVal::Bottom),
            None => Some(LatticeVal::Bottom),
        },

        Op::BinaryOp { op, left, right } => {
            let lv = get_lattice(module, lattice, *left);
            let rv = get_lattice(module, lattice, *right);
            match (&lv, &rv) {
                (LatticeVal::Bottom, _) | (_, LatticeVal::Bottom) => Some(LatticeVal::Bottom),
                (LatticeVal::Top, _) | (_, LatticeVal::Top) => None, // not yet determined
                // Operand order (N36): IR `left` = acc, `right` = vreg,
                // while the vendored `*2` handlers compute `vreg OP acc`
                // (e.g. div2 interpreter_assembly.cpp:1095-1096) — evaluate
                // with (right, left).
                (LatticeVal::Constant(a), LatticeVal::Constant(b)) => eval_binop_lattice(*op, b, a),
            }
        }

        Op::Compare { op, left, right } => {
            let lv = get_lattice(module, lattice, *left);
            let rv = get_lattice(module, lattice, *right);
            match (&lv, &rv) {
                (LatticeVal::Bottom, _) | (_, LatticeVal::Bottom) => Some(LatticeVal::Bottom),
                (LatticeVal::Top, _) | (_, LatticeVal::Top) => None,
                // Same operand order as BinaryOp (N36 — vendored
                // comparisons compute `vreg CMP acc`).
                (LatticeVal::Constant(a), LatticeVal::Constant(b)) => {
                    eval_compare_lattice(*op, b, a)
                }
            }
        }

        Op::UnaryOp { op, operand } => {
            let v = get_lattice(module, lattice, *operand);
            match &v {
                LatticeVal::Bottom => Some(LatticeVal::Bottom),
                LatticeVal::Top => None,
                LatticeVal::Constant(c) => eval_unop_lattice(*op, c),
            }
        }

        // Everything else: if any operand is Bottom → Bottom, else Top.
        _ => {
            let ops = inst.op.operands();
            if ops.is_empty() {
                // No operands but produces a value (e.g. LoadNewTarget) → Bottom.
                Some(LatticeVal::Bottom)
            } else {
                let mut has_top = false;
                for val in ops {
                    match get_lattice(module, lattice, val) {
                        LatticeVal::Bottom => return Some(LatticeVal::Bottom),
                        LatticeVal::Top => has_top = true,
                        _ => {}
                    }
                }
                if has_top {
                    None
                } else {
                    Some(LatticeVal::Bottom)
                }
            }
        }
    }
}

/// Evaluate a phi node considering only reachable incoming edges.
///
/// Phis in catch-handler blocks are forced to Bottom (N38(ii)): their
/// entries carry the protected preds' BLOCK-END values, but exception
/// dispatch transfers control mid-block, so the value live at the point
/// of exception is not the block-end value — folding them is unsound.
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

/// Add CFG edges from a terminator instruction based on lattice state,
/// PLUS the implicit exception edges of any try region protecting the
/// block (N38(i)): catch handlers are reachable from every protected
/// block regardless of how the terminator folds. Non-terminator
/// instructions contribute no edges (the exception edge is added once,
/// at the block's terminator — enough for reachability, and the
/// mid-block dispatch unsoundness is covered by the handler-phi guard
/// in `evaluate_phi`).
fn add_cfg_edges(
    module: &Module,
    func: FuncId,
    inst_id: InstId,
    lattice: &HashMap<ValueId, LatticeVal>,
    cfg_worklist: &mut VecDeque<CfgEdge>,
) {
    let Some(inst) = module.inst(inst_id) else {
        return;
    };
    let block = inst.block;
    let mut dests: Vec<CfgEdge> = Vec::new();
    match &inst.op {
        Op::Branch { dest } => {
            dests.push((block, *dest, EdgeKind::Normal));
        }
        Op::CondBranch {
            cond,
            true_dest,
            false_dest,
        } => {
            match get_lattice(module, lattice, *cond) {
                LatticeVal::Constant(c) => {
                    if const_is_truthy(&c) {
                        dests.push((block, *true_dest, EdgeKind::Normal));
                    } else {
                        dests.push((block, *false_dest, EdgeKind::Normal));
                    }
                }
                _ => {
                    // Unknown or Bottom: both edges are possible.
                    dests.push((block, *true_dest, EdgeKind::Normal));
                    dests.push((block, *false_dest, EdgeKind::Normal));
                }
            }
        }
        // Non-branch terminators (Return/Unreachable): no CFG successors,
        // but the block may still be try-protected — FALL THROUGH to the
        // exception-edge append below (N47: an early `return` here skipped
        // the handler edge, so SCCP never reached the catch handler of a
        // protected block ending in Return/Unreachable — including the
        // corpus Throw+Unreachable shape — leaving foldable handler code
        // untouched).
        _ if inst.op.is_terminator() => {}
        // Non-terminator: no edges (the exception edge is added once, at
        // the block's terminator — enough for reachability).
        _ => return,
    }
    // Exception edges: handlers of the try regions protecting this
    // block (the exception half of `analysis::augmented_succs`; the
    // terminator half is computed above so lattice-pruned CondBranch
    // edges stay pruned).
    let Some(func_data) = module.func(func) else {
        return;
    };
    for region in &func_data.try_regions {
        if !region.protected.contains(&block) {
            continue;
        }
        for catch in &region.catches {
            let handler = catch.handler;
            let edge = (block, handler, EdgeKind::Exceptional);
            if func_data.blocks.contains(&handler) && !dests.contains(&edge) {
                dests.push(edge);
            }
        }
    }
    for dest in dests {
        cfg_worklist.push_back(dest);
    }
}

/// The lattice value of `val`, resolving definition forms that are known
/// without evaluation: const-defined values yield their scalar constant
/// (non-scalars are Bottom — v0.1's default arm forced them there),
/// exception parameters are Bottom (the exception object is unknown).
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
            Some(Const::Undefined) => LatticeVal::Constant(ConstVal::Undefined),
            Some(Const::Null) => LatticeVal::Constant(ConstVal::Null),
            Some(Const::Bool(b)) => LatticeVal::Constant(ConstVal::Bool(*b)),
            Some(Const::Number(bits)) => {
                LatticeVal::Constant(ConstVal::Number(f64::from_bits(*bits)))
            }
            _ => LatticeVal::Bottom,
        },
        ValueDef::ExceptionParam(_) => LatticeVal::Bottom,
        _ => LatticeVal::Top,
    }
}

/// Whether `inst_id` already loads a constant equal to `c` (numbers
/// compared bit-exactly — replacing LiteralNumber(-0.0) with +0.0 would
/// be an N37 violation).
fn inst_is_const(module: &Module, inst_id: InstId, c: &ConstVal) -> bool {
    let Some(inst) = module.inst(inst_id) else {
        return false;
    };
    let Op::LoadConst(cid) = inst.op else {
        return false;
    };
    match (module.consts.get(cid), c) {
        (Some(Const::Number(bits)), ConstVal::Number(n)) => *bits == n.to_bits(),
        (Some(Const::Bool(x)), ConstVal::Bool(y)) => x == y,
        (Some(Const::Null), ConstVal::Null) => true,
        (Some(Const::Undefined), ConstVal::Undefined) => true,
        _ => false,
    }
}

fn const_to_const(c: &ConstVal) -> Const {
    match c {
        ConstVal::Number(n) => Const::number(*n), // bit-exact (N37)
        ConstVal::Bool(b) => Const::Bool(*b),
        ConstVal::Null => Const::Null,
        ConstVal::Undefined => Const::Undefined,
    }
}

fn const_is_truthy(c: &ConstVal) -> bool {
    match c {
        ConstVal::Bool(b) => *b,
        ConstVal::Number(n) => *n != 0.0 && !n.is_nan(),
        ConstVal::Null | ConstVal::Undefined => false,
    }
}

fn const_to_number(c: &ConstVal) -> Option<f64> {
    match c {
        ConstVal::Number(n) => Some(*n),
        ConstVal::Bool(true) => Some(1.0),
        ConstVal::Bool(false) => Some(0.0),
        ConstVal::Null => Some(0.0),
        ConstVal::Undefined => Some(f64::NAN),
    }
}

fn eval_binop_lattice(op: BinOp, a: &ConstVal, b: &ConstVal) -> Option<LatticeVal> {
    let an = const_to_number(a)?;
    let bn = const_to_number(b)?;
    // Bitwise/shift operands convert with ECMA-262 ToInt32/ToUint32
    // (N42): WRAP mod 2^32 with NaN/±Infinity → 0, NOT Rust's saturating
    // `as` casts — matches vendored DoubleToInt (number_helper.cpp:1137).
    // The shift count is masked `& 0x1f` AFTER the wrap, so -1 → 31.
    match op {
        BinOp::Add => Some(LatticeVal::Constant(ConstVal::Number(an + bn))),
        BinOp::Sub => Some(LatticeVal::Constant(ConstVal::Number(an - bn))),
        BinOp::Mul => Some(LatticeVal::Constant(ConstVal::Number(an * bn))),
        BinOp::Div => Some(LatticeVal::Constant(ConstVal::Number(an / bn))),
        BinOp::Mod => Some(LatticeVal::Constant(ConstVal::Number(an % bn))),
        BinOp::Exp => Some(LatticeVal::Constant(ConstVal::Number(an.powf(bn)))),
        BinOp::Shl => Some(LatticeVal::Constant(ConstVal::Number(
            (to_int32(an) << (to_uint32(bn) & 0x1f)) as f64,
        ))),
        BinOp::Shr => Some(LatticeVal::Constant(ConstVal::Number(
            // JS `>>>`: vendored shr2 is the LOGICAL (unsigned) shift —
            // (uint32)ToInt32(v) >> shift, so the unsigned reinterpret
            // goes through i32 (a direct `as u32` saturates negatives).
            ((to_int32(an) as u32) >> (to_uint32(bn) & 0x1f)) as f64,
        ))),
        BinOp::Ashr => Some(LatticeVal::Constant(ConstVal::Number(
            // JS `>>`: vendored ashr2 is the ARITHMETIC (signed) shift.
            // The two arms were inverted.
            (to_int32(an) >> (to_uint32(bn) & 0x1f)) as f64,
        ))),
        BinOp::BitAnd => Some(LatticeVal::Constant(ConstVal::Number(
            (to_int32(an) & to_int32(bn)) as f64,
        ))),
        BinOp::BitOr => Some(LatticeVal::Constant(ConstVal::Number(
            (to_int32(an) | to_int32(bn)) as f64,
        ))),
        BinOp::BitXor => Some(LatticeVal::Constant(ConstVal::Number(
            (to_int32(an) ^ to_int32(bn)) as f64,
        ))),
    }
}

/// Evaluate a comparison to a lattice value (v0.1's comparison arms of
/// `eval_binop_lattice`, split out with the v0.2 taxonomy).
fn eval_compare_lattice(op: CmpOp, a: &ConstVal, b: &ConstVal) -> Option<LatticeVal> {
    // N38(iii): JS loose equality does NOT ToNumber-coerce nullish
    // operands — `undefined == undefined` and `null == undefined` are
    // true, `null == 0` is false. The ToNumber path below maps
    // Undefined → NaN (so undefined == undefined folded to FALSE,
    // rewiring es2abc's finally guards) and Null → 0.0 (so null == 0
    // folded to TRUE). Never fold Eq/NotEq when either operand is a
    // Null/Undefined constant.
    if matches!(op, CmpOp::Eq | CmpOp::NotEq)
        && matches!(
            (a, b),
            (ConstVal::Null | ConstVal::Undefined, _) | (_, ConstVal::Null | ConstVal::Undefined)
        )
    {
        return Some(LatticeVal::Bottom);
    }
    let an = const_to_number(a)?;
    let bn = const_to_number(b)?;
    match op {
        CmpOp::Eq => Some(LatticeVal::Constant(ConstVal::Bool(an == bn))),
        CmpOp::NotEq => Some(LatticeVal::Constant(ConstVal::Bool(an != bn))),
        CmpOp::Less => Some(LatticeVal::Constant(ConstVal::Bool(an < bn))),
        CmpOp::LessEq => Some(LatticeVal::Constant(ConstVal::Bool(an <= bn))),
        CmpOp::Greater => Some(LatticeVal::Constant(ConstVal::Bool(an > bn))),
        CmpOp::GreaterEq => Some(LatticeVal::Constant(ConstVal::Bool(an >= bn))),
        // StrictEq/StrictNotEq need type-aware comparison; In/InstanceOf are runtime-only.
        _ => Some(LatticeVal::Bottom),
    }
}

fn eval_unop_lattice(op: UnOp, c: &ConstVal) -> Option<LatticeVal> {
    match op {
        UnOp::Minus => {
            let n = const_to_number(c)?;
            Some(LatticeVal::Constant(ConstVal::Number(-n)))
        }
        UnOp::BitNot => {
            let n = const_to_number(c)?;
            // ECMA-262 ToInt32 (wrap, NaN/±Inf → 0), not saturating (N42).
            Some(LatticeVal::Constant(ConstVal::Number(!to_int32(n) as f64)))
        }
        UnOp::LogicalNot => Some(LatticeVal::Constant(ConstVal::Bool(!const_is_truthy(c)))),
        UnOp::IsTrue => Some(LatticeVal::Constant(ConstVal::Bool(const_is_truthy(c)))),
        UnOp::IsFalse => Some(LatticeVal::Constant(ConstVal::Bool(!const_is_truthy(c)))),
        UnOp::ToNumber | UnOp::ToNumeric => {
            let n = const_to_number(c)?;
            Some(LatticeVal::Constant(ConstVal::Number(n)))
        }
        UnOp::Void => Some(LatticeVal::Constant(ConstVal::Undefined)),
        _ => Some(LatticeVal::Bottom),
    }
}
