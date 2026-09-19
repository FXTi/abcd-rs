//! Sparse Conditional Constant Propagation (Wegman-Zadeck 1991).
//!
//! Lattice: Top → Constant(val) → Bottom.
//! Dual worklist: CFG edges (reachability) + SSA edges (value changes).
//! After convergence: replace constants, fold dead branches.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::analysis::{augmented_succs, inst_operands};
use crate::entity::{Block, FuncId, Inst, Value};
use crate::inst::{BinOp, InstData, UnOp};
use crate::module::Module;

use super::{FuncPass, to_int32, to_uint32};

/// Lattice value for SCCP.
#[derive(Clone, Debug, PartialEq)]
enum LatticeVal {
    Top,                // Unknown / not yet reached
    Constant(ConstVal), // Known constant
    Bottom,             // Overdefined (multiple values possible)
}

/// Constant value representation.
#[derive(Clone, Debug, PartialEq)]
enum ConstVal {
    Number(f64),
    Bool(bool),
    Null,
    Undefined,
}

pub struct Sccp;

impl FuncPass for Sccp {
    fn run(&self, module: &mut Module, func: FuncId) -> bool {
        let entry = module.func(func).entry_block;
        let blocks: Vec<Block> = module.func(func).blocks.clone();

        // N38(ii): catch-handler blocks. Exception dispatch transfers
        // control from ANY protected instruction to the handler
        // mid-block, so a handler phi entry keyed by a protected pred
        // carries that pred's BLOCK-END value, which is not the value
        // live at the point of exception — folding handler phis is
        // unsound. They are forced to lattice Bottom in evaluate_phi.
        let handler_blocks: HashSet<Block> = module
            .func(func)
            .try_regions
            .iter()
            .flat_map(|region| region.catches.iter().map(|c| c.handler_block))
            .collect();

        // Initialize lattice: all values start at Top.
        let mut lattice: HashMap<Value, LatticeVal> = HashMap::new();

        // Function params are Bottom (unknown input). `param_values` is the
        // authoritative parameter identity; an arena-index convention would
        // mark values of OTHER functions in a multi-function module and —
        // worse — leave this function's real parameters at Top, letting a
        // phi(param, const) fold to the constant.
        for &val in &module.func(func).param_values {
            lattice.insert(val, LatticeVal::Bottom);
        }

        // Build use-list: Value → Vec<Inst> that use it.
        let mut use_list: HashMap<Value, Vec<Inst>> = HashMap::new();
        for &bb in &blocks {
            let block = module.block(bb);
            for &inst_id in block.phis.iter().chain(block.insts.iter()) {
                for val in inst_operands(&module.inst(inst_id).data) {
                    use_list.entry(val).or_default().push(inst_id);
                }
            }
        }

        // Worklists.
        let mut cfg_worklist: VecDeque<(Block, Block)> = VecDeque::new(); // (from, to) edges
        let mut ssa_worklist: VecDeque<Value> = VecDeque::new();
        let mut reachable_edges: HashSet<(Block, Block)> = HashSet::new();
        let mut reachable_blocks: HashSet<Block> = HashSet::new();

        // Seed: entry block is reachable.
        reachable_blocks.insert(entry);
        // Process entry block's instructions.
        let entry_phis: Vec<Inst> = module.block(entry).phis.clone();
        let entry_insts: Vec<Inst> = module.block(entry).insts.clone();
        for &inst_id in entry_phis.iter().chain(entry_insts.iter()) {
            if let Some(new_val) = evaluate_inst(module, inst_id, &lattice) {
                if let Some(result) = module.inst(inst_id).result {
                    let old = lattice.get(&result).cloned().unwrap_or(LatticeVal::Top);
                    let met = meet(&old, &new_val);
                    if met != old {
                        lattice.insert(result, met);
                        ssa_worklist.push_back(result);
                    }
                }
            }
        }
        // Seed CFG edges from entry — AUGMENTED successors (N38(i)):
        // exception edges included, so catch handlers are reachable.
        for succ in augmented_succs(module, func, entry) {
            cfg_worklist.push_back((entry, succ));
        }

        // Main loop.
        loop {
            let has_cfg = !cfg_worklist.is_empty();
            let has_ssa = !ssa_worklist.is_empty();
            if !has_cfg && !has_ssa {
                break;
            }

            // Process CFG edges.
            while let Some((from, to)) = cfg_worklist.pop_front() {
                if !reachable_edges.insert((from, to)) {
                    continue;
                }
                let first_time = reachable_blocks.insert(to);

                // Re-evaluate phis in `to` (new edge may change phi values).
                let phis: Vec<Inst> = module.block(to).phis.clone();
                for &phi_id in &phis {
                    if let Some(new_val) =
                        evaluate_phi(module, phi_id, &lattice, &reachable_edges, &handler_blocks)
                    {
                        if let Some(result) = module.inst(phi_id).result {
                            let old = lattice.get(&result).cloned().unwrap_or(LatticeVal::Top);
                            let met = meet(&old, &new_val);
                            if met != old {
                                lattice.insert(result, met);
                                ssa_worklist.push_back(result);
                            }
                        }
                    }
                }

                if first_time {
                    // Evaluate all non-phi instructions.
                    let insts: Vec<Inst> = module.block(to).insts.clone();
                    for &inst_id in &insts {
                        if let Some(new_val) = evaluate_inst(module, inst_id, &lattice) {
                            if let Some(result) = module.inst(inst_id).result {
                                let old = lattice.get(&result).cloned().unwrap_or(LatticeVal::Top);
                                let met = meet(&old, &new_val);
                                if met != old {
                                    lattice.insert(result, met);
                                    ssa_worklist.push_back(result);
                                }
                            }
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
                        let inst_block = module.inst(inst_id).block;
                        if !reachable_blocks.contains(&inst_block) {
                            continue;
                        }

                        if module.inst(inst_id).data.is_phi() {
                            if let Some(new_val) = evaluate_phi(
                                module,
                                inst_id,
                                &lattice,
                                &reachable_edges,
                                &handler_blocks,
                            ) {
                                if let Some(result) = module.inst(inst_id).result {
                                    let old =
                                        lattice.get(&result).cloned().unwrap_or(LatticeVal::Top);
                                    let met = meet(&old, &new_val);
                                    if met != old {
                                        lattice.insert(result, met);
                                        ssa_worklist.push_back(result);
                                    }
                                }
                            }
                        } else {
                            if let Some(new_val) = evaluate_inst(module, inst_id, &lattice) {
                                if let Some(result) = module.inst(inst_id).result {
                                    let old =
                                        lattice.get(&result).cloned().unwrap_or(LatticeVal::Top);
                                    let met = meet(&old, &new_val);
                                    if met != old {
                                        lattice.insert(result, met);
                                        ssa_worklist.push_back(result);
                                    }
                                }
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
            let block = module.block(bb);
            let all_insts: Vec<Inst> = block
                .phis
                .iter()
                .chain(block.insts.iter())
                .copied()
                .collect();

            for inst_id in all_insts {
                if let Some(result) = module.inst(inst_id).result {
                    if let Some(LatticeVal::Constant(c)) = lattice.get(&result) {
                        let new_data = const_to_inst(c);
                        if !matches_inst_data(&module.inst(inst_id).data, &new_data) {
                            let was_phi = module.inst(inst_id).data.is_phi();
                            module.inst_mut(inst_id).data = new_data;
                            if was_phi {
                                module.block_mut(bb).phis.retain(|&id| id != inst_id);
                                module.block_mut(bb).insts.insert(0, inst_id);
                            }
                            changed = true;
                        }
                    }
                }
            }

            // Fold CondBranch with known condition.
            let insts = module.block(bb).insts.clone();
            if let Some(&last) = insts.last() {
                if let InstData::CondBranch {
                    cond,
                    true_dest,
                    false_dest,
                } = &module.inst(last).data
                {
                    let cond = *cond;
                    let true_dest = *true_dest;
                    let false_dest = *false_dest;
                    if let Some(LatticeVal::Constant(c)) = lattice.get(&cond) {
                        let is_true = const_is_truthy(c);
                        let target = if is_true { true_dest } else { false_dest };
                        let dead = if is_true { false_dest } else { true_dest };
                        module.inst_mut(last).data = InstData::Branch { dest: target };
                        // Remove bb from dead target's preds AND from its
                        // phi entries (N23/N27): a stale entry keyed by bb
                        // survives on the IMPOSSIBLE path, and a later
                        // merge/dedup can resurrect its value over the
                        // value from the only live path. When both dests
                        // name the same block the edge is still live (the
                        // branch still targets it), so nothing is removed.
                        if dead != target {
                            module.block_mut(dead).preds.retain(|p| *p != bb);
                            let dead_phis = module.block(dead).phis.clone();
                            for phi_id in dead_phis {
                                if let InstData::Phi { entries } = &mut module.inst_mut(phi_id).data
                                {
                                    entries.retain(|(pred, _)| *pred != bb);
                                }
                            }
                        }
                        changed = true;
                    }
                }
            }
        }

        changed
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
    inst_id: Inst,
    lattice: &HashMap<Value, LatticeVal>,
) -> Option<LatticeVal> {
    let data = &module.inst(inst_id).data;
    // If the instruction doesn't produce a result, nothing to evaluate.
    if module.inst(inst_id).result.is_none() {
        return None;
    }

    match data {
        InstData::LiteralNumber(n) => Some(LatticeVal::Constant(ConstVal::Number(*n))),
        InstData::LiteralBool(b) => Some(LatticeVal::Constant(ConstVal::Bool(*b))),
        InstData::LiteralNull => Some(LatticeVal::Constant(ConstVal::Null)),
        InstData::LiteralUndefined => Some(LatticeVal::Constant(ConstVal::Undefined)),
        InstData::LiteralNaN => Some(LatticeVal::Constant(ConstVal::Number(f64::NAN))),
        InstData::LiteralInfinity => Some(LatticeVal::Constant(ConstVal::Number(f64::INFINITY))),

        InstData::BinaryOp { op, left, right } => {
            let lv = get_lattice(lattice, *left);
            let rv = get_lattice(lattice, *right);
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

        InstData::UnaryOp { op, operand } => {
            let v = get_lattice(lattice, *operand);
            match &v {
                LatticeVal::Bottom => Some(LatticeVal::Bottom),
                LatticeVal::Top => None,
                LatticeVal::Constant(c) => eval_unop_lattice(*op, c),
            }
        }

        InstData::IsTrue { operand } => {
            let v = get_lattice(lattice, *operand);
            match &v {
                LatticeVal::Bottom => Some(LatticeVal::Bottom),
                LatticeVal::Top => None,
                LatticeVal::Constant(c) => {
                    Some(LatticeVal::Constant(ConstVal::Bool(const_is_truthy(c))))
                }
            }
        }

        InstData::IsFalse { operand } => {
            let v = get_lattice(lattice, *operand);
            match &v {
                LatticeVal::Bottom => Some(LatticeVal::Bottom),
                LatticeVal::Top => None,
                LatticeVal::Constant(c) => {
                    Some(LatticeVal::Constant(ConstVal::Bool(!const_is_truthy(c))))
                }
            }
        }

        // Everything else: if any operand is Bottom → Bottom, else Top.
        _ => {
            let ops = inst_operands(data);
            if ops.is_empty() {
                // No operands but produces a value (e.g. LoadThis) → Bottom.
                Some(LatticeVal::Bottom)
            } else {
                let mut has_top = false;
                for val in ops {
                    match get_lattice(lattice, val) {
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
    phi_id: Inst,
    lattice: &HashMap<Value, LatticeVal>,
    reachable_edges: &HashSet<(Block, Block)>,
    handler_blocks: &HashSet<Block>,
) -> Option<LatticeVal> {
    let phi_block = module.inst(phi_id).block;
    if handler_blocks.contains(&phi_block) {
        return Some(LatticeVal::Bottom);
    }
    if let InstData::Phi { entries } = &module.inst(phi_id).data {
        let mut result = LatticeVal::Top;
        for &(pred, val) in entries {
            if !reachable_edges.contains(&(pred, phi_block)) {
                continue;
            }
            let v = get_lattice(lattice, val);
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
    inst_id: Inst,
    lattice: &HashMap<Value, LatticeVal>,
    cfg_worklist: &mut VecDeque<(Block, Block)>,
) {
    let block = module.inst(inst_id).block;
    let mut dests: Vec<Block> = Vec::new();
    match &module.inst(inst_id).data {
        InstData::Branch { dest } => {
            dests.push(*dest);
        }
        InstData::CondBranch {
            cond,
            true_dest,
            false_dest,
        } => {
            match get_lattice(lattice, *cond) {
                LatticeVal::Constant(c) => {
                    if const_is_truthy(&c) {
                        dests.push(*true_dest);
                    } else {
                        dests.push(*false_dest);
                    }
                }
                _ => {
                    // Unknown or Bottom: both edges are possible.
                    dests.push(*true_dest);
                    dests.push(*false_dest);
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
        _ if module.inst(inst_id).data.is_terminator() => {}
        // Non-terminator: no edges (the exception edge is added once, at
        // the block's terminator — enough for reachability).
        _ => return,
    }
    // Exception edges: handlers of the try regions protecting this
    // block (the exception half of `analysis::augmented_succs`; the
    // terminator half is computed above so lattice-pruned CondBranch
    // edges stay pruned).
    let func_data = module.func(func);
    for region in &func_data.try_regions {
        if !region.try_blocks.contains(&block) {
            continue;
        }
        for catch in &region.catches {
            let handler = catch.handler_block;
            if func_data.blocks.contains(&handler) && !dests.contains(&handler) {
                dests.push(handler);
            }
        }
    }
    for dest in dests {
        cfg_worklist.push_back((block, dest));
    }
}

fn get_lattice(lattice: &HashMap<Value, LatticeVal>, val: Value) -> LatticeVal {
    lattice.get(&val).cloned().unwrap_or(LatticeVal::Top)
}

fn const_to_inst(c: &ConstVal) -> InstData {
    match c {
        ConstVal::Number(n) => InstData::LiteralNumber(*n),
        ConstVal::Bool(b) => InstData::LiteralBool(*b),
        ConstVal::Null => InstData::LiteralNull,
        ConstVal::Undefined => InstData::LiteralUndefined,
    }
}

fn matches_inst_data(a: &InstData, b: &InstData) -> bool {
    match (a, b) {
        (InstData::LiteralNumber(x), InstData::LiteralNumber(y)) => x.to_bits() == y.to_bits(),
        (InstData::LiteralBool(x), InstData::LiteralBool(y)) => x == y,
        (InstData::LiteralNull, InstData::LiteralNull) => true,
        (InstData::LiteralUndefined, InstData::LiteralUndefined) => true,
        _ => false,
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
    // N38(iii): JS loose equality does NOT ToNumber-coerce nullish
    // operands — `undefined == undefined` and `null == undefined` are
    // true, `null == 0` is false. The ToNumber path below maps
    // Undefined → NaN (so undefined == undefined folded to FALSE,
    // rewiring es2abc's finally guards) and Null → 0.0 (so null == 0
    // folded to TRUE). Never fold Eq/NotEq when either operand is a
    // Null/Undefined constant.
    if matches!(op, BinOp::Eq | BinOp::NotEq)
        && matches!(
            (a, b),
            (ConstVal::Null | ConstVal::Undefined, _) | (_, ConstVal::Null | ConstVal::Undefined)
        )
    {
        return Some(LatticeVal::Bottom);
    }
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
        BinOp::Eq => Some(LatticeVal::Constant(ConstVal::Bool(an == bn))),
        BinOp::NotEq => Some(LatticeVal::Constant(ConstVal::Bool(an != bn))),
        BinOp::Less => Some(LatticeVal::Constant(ConstVal::Bool(an < bn))),
        BinOp::LessEq => Some(LatticeVal::Constant(ConstVal::Bool(an <= bn))),
        BinOp::Greater => Some(LatticeVal::Constant(ConstVal::Bool(an > bn))),
        BinOp::GreaterEq => Some(LatticeVal::Constant(ConstVal::Bool(an >= bn))),
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
        UnOp::ToNumber | UnOp::ToNumeric => {
            let n = const_to_number(c)?;
            Some(LatticeVal::Constant(ConstVal::Number(n)))
        }
        UnOp::Void => Some(LatticeVal::Constant(ConstVal::Undefined)),
        _ => Some(LatticeVal::Bottom),
    }
}
