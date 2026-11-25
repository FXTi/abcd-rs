//! Sparse Conditional Constant Propagation (Wegman-Zadeck 1991; `design/ir.md`,
//! `design/decisions.md` `N36`–`N42`, `N47`).
//!
//! Lattice: Top → Constant(val) → Bottom.
//! Dual worklist: CFG edges (reachability) + SSA edges (value changes).
//! After convergence: replace constants, fold dead branches.
//!
//! Representation invariants:
//!
//! - CFG edges are kinded (`T5`): the worklist tracks
//!   `(from, to, kind)` triples and phi entries match on the full
//!   [`Edge`] — an exceptional in-edge and a normal in-edge from the
//!   same block are distinct lattice inputs.
//! - Constants surface in two definition forms: [`Op::LoadConst`]
//!   instructions (evaluated here) and [`ValueDef::Const`] values
//!   (resolved on demand — frame-initial values are const-defined,
//!   not seeded instructions).
//! - Replacement writes [`Op::LoadConst`] of a freshly pooled [`Const`];
//!   a folded PHI is moved out of the block's phi prefix (the verifier
//!   requires phis to lead the block).

use std::collections::{HashMap, HashSet, VecDeque};

use abcd_ir::{
    BinOp, BlockId, CmpOp, Const, Edge, EdgeKind, FuncId, InstId, Module, Op, Sym, UnOp, ValueDef,
    ValueId,
};

use crate::FuncPass;
use crate::{canonicalize_f64_bits, ecma_pow, has_static_ty, to_int32, to_uint32};

/// Lattice value for SCCP.
#[derive(Clone, Debug, PartialEq, Eq)]
enum LatticeVal {
    Top,                // Unknown / not yet reached
    Constant(ConstVal), // Known constant
    Bottom,             // Overdefined (multiple values possible)
}

/// Constant value representation. `Number` stores raw IEEE-754 `u64` bits so
/// lattice `meet()` compares bit-exactly (`meet(+0.0, -0.0) == Bottom`,
/// `R3-H5` / `N37`), while newly folded arithmetic canonicalizes `NaN` to
/// [`crate::CANONICAL_NAN_BITS`] (`#60`).
#[derive(Clone, Debug, PartialEq, Eq)]
enum ConstVal {
    Number(u64),
    Bool(bool),
    Null,
    Undefined,
    String(Sym),
    BigInt(Sym),
}

impl ConstVal {
    #[inline]
    fn number(n: f64) -> Self {
        Self::Number(canonicalize_f64_bits(n))
    }
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
        let exc_handlers = crate::analysis::exception_handlers_by_block(func_data);

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
                inst.op.for_each_operand(|val| {
                    use_list.entry(val).or_default().push(inst_id);
                });
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
        for edge in crate::analysis::augmented_succs_indexed(module, &exc_handlers, entry) {
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
                        add_cfg_edges(module, &exc_handlers, inst_id, &lattice, &mut cfg_worklist);
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
                            add_cfg_edges(
                                module,
                                &exc_handlers,
                                inst_id,
                                &lattice,
                                &mut cfg_worklist,
                            );
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

            let mut folded_phis: Vec<InstId> = Vec::new();
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
                    let cid = module.consts.intern(const_to_const(&c));
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

            // Fold CondBranch with known condition (`R3-M6`: query `get_lattice`
            // so `ValueDef::Const` conditions also rewrite `CondBranch -> Branch`).
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
                if let LatticeVal::Constant(c) = get_lattice(module, &lattice, cond)
                    && let Some(is_true) = const_is_truthy(&c)
                {
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
                            if let Some(inst) = module.inst_mut(phi_id)
                                && let Op::Phi { entries } = &mut inst.op
                            {
                                entries.retain(|(edge, _)| *edge != dead_edge);
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
    inst.result?;

    match &inst.op {
        Op::LoadConst(cid) => match module.consts.get(*cid) {
            // Scalar and string/bigint constants enter the lattice; literal
            // buffers, typed integer/float literal tags, and the hole evaluate
            // to Bottom.
            Some(Const::Undefined) => Some(LatticeVal::Constant(ConstVal::Undefined)),
            Some(Const::Null) => Some(LatticeVal::Constant(ConstVal::Null)),
            Some(Const::Bool(b)) => Some(LatticeVal::Constant(ConstVal::Bool(*b))),
            Some(Const::Number(bits)) => Some(LatticeVal::Constant(ConstVal::Number(*bits))),
            Some(Const::String(sym)) => Some(LatticeVal::Constant(ConstVal::String(*sym))),
            Some(Const::BigInt(sym)) => Some(LatticeVal::Constant(ConstVal::BigInt(*sym))),
            Some(_) | None => Some(LatticeVal::Bottom),
        },

        Op::BinaryOp { op, left, right } => {
            if has_static_ty(module, inst_id) {
                return Some(LatticeVal::Bottom);
            }
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
            if has_static_ty(module, inst_id) {
                return Some(LatticeVal::Bottom);
            }
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
            if has_static_ty(module, inst_id) {
                return Some(LatticeVal::Bottom);
            }
            let v = get_lattice(module, lattice, *operand);
            match &v {
                LatticeVal::Bottom => Some(LatticeVal::Bottom),
                LatticeVal::Top => None,
                LatticeVal::Constant(c) => eval_unop_lattice(*op, c),
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
    exc_handlers: &HashMap<BlockId, Vec<BlockId>>,
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
                LatticeVal::Constant(c) => match const_is_truthy(&c) {
                    Some(true) => dests.push((block, *true_dest, EdgeKind::Normal)),
                    Some(false) => dests.push((block, *false_dest, EdgeKind::Normal)),
                    None => {
                        dests.push((block, *true_dest, EdgeKind::Normal));
                        dests.push((block, *false_dest, EdgeKind::Normal));
                    }
                },
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
    // Exception edges: pre-indexed handlers of the try regions protecting
    // this block (#29).
    if let Some(handlers) = exc_handlers.get(&block) {
        for &handler in handlers {
            let edge = (block, handler, EdgeKind::Exceptional);
            if !dests.contains(&edge) {
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
/// (non-scalars are Bottom), exception parameters are Bottom (the
/// exception object is unknown).
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
            Some(Const::Number(bits)) => LatticeVal::Constant(ConstVal::Number(*bits)),
            Some(Const::String(sym)) => LatticeVal::Constant(ConstVal::String(*sym)),
            Some(Const::BigInt(sym)) => LatticeVal::Constant(ConstVal::BigInt(*sym)),
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
        (Some(Const::Number(bits)), ConstVal::Number(n_bits)) => *bits == *n_bits,
        (Some(Const::Bool(x)), ConstVal::Bool(y)) => x == y,
        (Some(Const::Null), ConstVal::Null) => true,
        (Some(Const::Undefined), ConstVal::Undefined) => true,
        (Some(Const::String(x)), ConstVal::String(y)) => x == y,
        (Some(Const::BigInt(x)), ConstVal::BigInt(y)) => x == y,
        _ => false,
    }
}

fn const_to_const(c: &ConstVal) -> Const {
    match c {
        ConstVal::Number(bits) => Const::Number(*bits), // bit-exact (N37)
        ConstVal::Bool(b) => Const::Bool(*b),
        ConstVal::Null => Const::Null,
        ConstVal::Undefined => Const::Undefined,
        ConstVal::String(sym) => Const::String(*sym),
        ConstVal::BigInt(sym) => Const::BigInt(*sym),
    }
}

fn const_is_truthy(c: &ConstVal) -> Option<bool> {
    match c {
        ConstVal::Bool(b) => Some(*b),
        ConstVal::Number(bits) => {
            let n = f64::from_bits(*bits);
            Some(n != 0.0 && !n.is_nan())
        }
        ConstVal::Null | ConstVal::Undefined => Some(false),
        ConstVal::String(_) | ConstVal::BigInt(_) => None,
    }
}

fn const_to_number(c: &ConstVal) -> Option<f64> {
    match c {
        ConstVal::Number(bits) => Some(f64::from_bits(*bits)),
        ConstVal::Bool(true) => Some(1.0),
        ConstVal::Bool(false) => Some(0.0),
        ConstVal::Null => Some(0.0),
        ConstVal::Undefined => Some(f64::NAN),
        ConstVal::String(_) | ConstVal::BigInt(_) => None,
    }
}

fn eval_binop_lattice(op: BinOp, a: &ConstVal, b: &ConstVal) -> Option<LatticeVal> {
    let (Some(an), Some(bn)) = (const_to_number(a), const_to_number(b)) else {
        return Some(LatticeVal::Bottom);
    };
    // Bitwise/shift operands convert with ECMA-262 ToInt32/ToUint32
    // (N42): WRAP mod 2^32 with NaN/±Infinity → 0, NOT Rust's saturating
    // `as` casts — matches vendored DoubleToInt (number_helper.cpp:1137).
    // The shift count is masked `& 0x1f` AFTER the wrap, so -1 → 31.
    let res = match op {
        BinOp::Add => an + bn,
        BinOp::Sub => an - bn,
        BinOp::Mul => an * bn,
        BinOp::Div => an / bn,
        BinOp::Mod => an % bn,
        BinOp::Exp => ecma_pow(an, bn),
        BinOp::Shl => (to_int32(an) << (to_uint32(bn) & 0x1f)) as f64,
        // JS `>>>`: vendored shr2 is the LOGICAL (unsigned) shift —
        // (uint32)ToInt32(v) >> shift, so the unsigned reinterpret
        // goes through i32 (a direct `as u32` saturates negatives).
        BinOp::Shr => ((to_int32(an) as u32) >> (to_uint32(bn) & 0x1f)) as f64,
        // JS `>>`: vendored ashr2 is the ARITHMETIC (signed) shift.
        BinOp::Ashr => (to_int32(an) >> (to_uint32(bn) & 0x1f)) as f64,
        BinOp::BitAnd => (to_int32(an) & to_int32(bn)) as f64,
        BinOp::BitOr => (to_int32(an) | to_int32(bn)) as f64,
        BinOp::BitXor => (to_int32(an) ^ to_int32(bn)) as f64,
    };
    Some(LatticeVal::Constant(ConstVal::number(res)))
}

/// Evaluate a [`CmpOp`] comparison over constant lattice inputs.
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
    let (Some(an), Some(bn)) = (const_to_number(a), const_to_number(b)) else {
        return Some(LatticeVal::Bottom);
    };
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
            let Some(n) = const_to_number(c) else {
                return Some(LatticeVal::Bottom);
            };
            Some(LatticeVal::Constant(ConstVal::number(-n)))
        }
        UnOp::BitNot => {
            let Some(n) = const_to_number(c) else {
                return Some(LatticeVal::Bottom);
            };
            // ECMA-262 ToInt32 (wrap, NaN/±Inf → 0), not saturating (N42).
            Some(LatticeVal::Constant(ConstVal::number(!to_int32(n) as f64)))
        }
        UnOp::LogicalNot => Some(const_is_truthy(c).map_or(LatticeVal::Bottom, |b| {
            LatticeVal::Constant(ConstVal::Bool(!b))
        })),
        UnOp::IsTrue => Some(const_is_truthy(c).map_or(LatticeVal::Bottom, |b| {
            LatticeVal::Constant(ConstVal::Bool(b))
        })),
        UnOp::IsFalse => Some(const_is_truthy(c).map_or(LatticeVal::Bottom, |b| {
            LatticeVal::Constant(ConstVal::Bool(!b))
        })),
        UnOp::ToNumber | UnOp::ToNumeric => {
            let Some(n) = const_to_number(c) else {
                return Some(LatticeVal::Bottom);
            };
            Some(LatticeVal::Constant(ConstVal::number(n)))
        }
        UnOp::ToPropertyKey => match c {
            ConstVal::String(sym) => Some(LatticeVal::Constant(ConstVal::String(*sym))),
            _ => Some(LatticeVal::Bottom),
        },
        UnOp::Void => Some(LatticeVal::Constant(ConstVal::Undefined)),
        UnOp::JumpEqz => {
            let b = match c {
                ConstVal::Bool(b) => !*b,
                ConstVal::Number(bits) => f64::from_bits(*bits) == 0.0,
                ConstVal::Null
                | ConstVal::Undefined
                | ConstVal::String(_)
                | ConstVal::BigInt(_) => false,
            };
            Some(LatticeVal::Constant(ConstVal::Bool(b)))
        }
        UnOp::JumpNez => {
            let b = match c {
                ConstVal::Bool(b) => *b,
                ConstVal::Number(bits) => f64::from_bits(*bits) != 0.0,
                ConstVal::Null
                | ConstVal::Undefined
                | ConstVal::String(_)
                | ConstVal::BigInt(_) => false,
            };
            Some(LatticeVal::Constant(ConstVal::Bool(b)))
        }
        _ => Some(LatticeVal::Bottom),
    }
}
