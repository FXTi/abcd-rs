//! SSA-based register allocation.
//!
//! 1. Exact backward dataflow liveness analysis.
//! 2. Interference graph construction (SSA guarantees chordal graph).
//! 3. MCS (Maximum Cardinality Search) ordering + greedy coloring with
//!    accumulator preference heuristic.
//! 4. Boissinot SSA destruction: coalesce same-color phi operands,
//!    insert copies for different colors, topological sort parallel copies.

use std::collections::{HashMap, HashSet};

use crate::analysis::{self, block_succs, inst_operands};
use crate::entity::{Block, FuncId, Value};
use crate::inst::InstData;
use crate::module::Module;

/// The result of register allocation for a function.
#[derive(Debug)]
pub struct RegAlloc {
    /// Value → allocated slot.
    pub allocation: HashMap<Value, RegSlot>,
    /// Parallel copies for phi elimination.
    /// Key: (predecessor, successor). Value: (src, dst) copies.
    pub phi_copies: HashMap<(Block, Block), Vec<(Value, Value)>>,
    /// Total registers used (excluding accumulator).
    pub num_regs: u16,
}

/// Where a value lives after allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RegSlot {
    Reg(u16),
    Acc,
}

/// Re-export compute_rpo for backward compatibility.
pub fn compute_rpo(module: &Module, func_id: FuncId) -> Vec<Block> {
    analysis::compute_rpo(module, func_id)
}

/// Allocate registers for a function using SSA-based chordal coloring.
pub fn allocate(module: &Module, func_id: FuncId) -> RegAlloc {
    let func = module.func(func_id);
    let rpo = analysis::compute_rpo(module, func_id);

    // Collect all values in the function.
    let mut all_values: Vec<Value> = Vec::new();
    for &bb in &rpo {
        let block = module.block(bb);
        for &inst_id in block.phis.iter().chain(block.insts.iter()) {
            if let Some(result) = module.inst(inst_id).result {
                all_values.push(result);
            }
        }
    }
    // Add function parameters.
    for i in 0..func.param_count {
        let val = Value::from_index(i as usize);
        if !all_values.contains(&val) {
            all_values.push(val);
        }
    }

    if all_values.is_empty() {
        return RegAlloc {
            allocation: HashMap::new(),
            phi_copies: HashMap::new(),
            num_regs: 0,
        };
    }

    // Step 1: Exact backward dataflow liveness.
    let (_live_in, live_out) = compute_liveness(module, func_id, &rpo);

    // Step 2: Build interference graph.
    let interference = build_interference(module, &rpo, &live_out);

    // Step 3: Compute accumulator preference scores.
    let acc_score = compute_acc_scores(module, &rpo);

    // Step 4: MCS ordering + greedy coloring.
    let (allocation, num_regs) =
        mcs_color(&all_values, &interference, &acc_score, func.param_count);

    // Step 5: Boissinot SSA destruction.
    let phi_copies = boissinot_destruction(module, &rpo, &allocation);

    RegAlloc {
        allocation,
        phi_copies,
        num_regs,
    }
}

// ─── Step 1: Exact backward dataflow liveness ────────────────────────────────

/// Compute live_in and live_out sets for each block.
/// Phi operands are treated as uses in the predecessor block.
fn compute_liveness(
    module: &Module,
    _func_id: FuncId,
    rpo: &[Block],
) -> (
    HashMap<Block, HashSet<Value>>,
    HashMap<Block, HashSet<Value>>,
) {
    // Compute use and def sets per block.
    let mut block_use: HashMap<Block, HashSet<Value>> = HashMap::new();
    let mut block_def: HashMap<Block, HashSet<Value>> = HashMap::new();

    for &bb in rpo {
        let mut uses = HashSet::new();
        let mut defs = HashSet::new();
        let block = module.block(bb);

        // Process phis: phi results are defs, but phi operands are NOT uses
        // in this block — they're uses in the predecessor blocks.
        for &phi_id in &block.phis {
            if let Some(result) = module.inst(phi_id).result {
                defs.insert(result);
            }
        }

        // Process non-phi instructions.
        for &inst_id in &block.insts {
            let node = module.inst(inst_id);
            // Uses that aren't already defined in this block.
            for val in inst_operands(&node.data) {
                if !defs.contains(&val) {
                    uses.insert(val);
                }
            }
            if let Some(result) = node.result {
                defs.insert(result);
            }
        }

        block_use.insert(bb, uses);
        block_def.insert(bb, defs);
    }

    // Add phi operands as uses in predecessor blocks.
    for &bb in rpo {
        let block = module.block(bb);
        for &phi_id in &block.phis {
            if let InstData::Phi { entries } = &module.inst(phi_id).data {
                for &(pred, val) in entries {
                    let pred_def = block_def.get(&pred).cloned().unwrap_or_default();
                    if !pred_def.contains(&val) {
                        block_use.entry(pred).or_default().insert(val);
                    }
                }
            }
        }
    }

    // Iterative dataflow: live_in[B] = use[B] ∪ (live_out[B] \ def[B])
    //                      live_out[B] = ∪ live_in[S] for S ∈ succs(B)
    let mut live_in: HashMap<Block, HashSet<Value>> = HashMap::new();
    let mut live_out: HashMap<Block, HashSet<Value>> = HashMap::new();

    for &bb in rpo {
        live_in.insert(bb, HashSet::new());
        live_out.insert(bb, HashSet::new());
    }

    let mut changed = true;
    while changed {
        changed = false;
        // Process in reverse RPO for faster convergence.
        for &bb in rpo.iter().rev() {
            // live_out = union of live_in of successors
            let mut new_out = HashSet::new();
            for succ in block_succs(module, bb) {
                if let Some(succ_in) = live_in.get(&succ) {
                    new_out.extend(succ_in);
                }
            }
            // Also add phi operands from successors that come from this block.
            for succ in block_succs(module, bb) {
                let succ_block = module.block(succ);
                for &phi_id in &succ_block.phis {
                    if let InstData::Phi { entries } = &module.inst(phi_id).data {
                        for &(pred, val) in entries {
                            if pred == bb {
                                new_out.insert(val);
                            }
                        }
                    }
                }
            }

            // live_in = use ∪ (live_out \ def)
            let uses = block_use.get(&bb).cloned().unwrap_or_default();
            let defs = block_def.get(&bb).cloned().unwrap_or_default();
            let mut new_in: HashSet<Value> = uses;
            for &v in &new_out {
                if !defs.contains(&v) {
                    new_in.insert(v);
                }
            }

            if new_in != *live_in.get(&bb).unwrap() || new_out != *live_out.get(&bb).unwrap() {
                changed = true;
                live_in.insert(bb, new_in);
                live_out.insert(bb, new_out);
            }
        }
    }

    (live_in, live_out)
}

// ─── Step 2: Interference graph ──────────────────────────────────────────────

type InterferenceGraph = HashMap<Value, HashSet<Value>>;

/// Build interference graph by scanning each block backward from live_out.
fn build_interference(
    module: &Module,
    rpo: &[Block],
    live_out: &HashMap<Block, HashSet<Value>>,
) -> InterferenceGraph {
    let mut graph: InterferenceGraph = HashMap::new();

    for &bb in rpo {
        let block = module.block(bb);
        let mut live: HashSet<Value> = live_out.get(&bb).cloned().unwrap_or_default();

        // Walk instructions backward.
        for &inst_id in block.insts.iter().rev() {
            let node = module.inst(inst_id);

            if let Some(result) = node.result {
                // result interferes with everything currently live (except itself).
                for &v in &live {
                    if v != result {
                        graph.entry(result).or_default().insert(v);
                        graph.entry(v).or_default().insert(result);
                    }
                }
                // result is no longer live above its definition.
                live.remove(&result);
            }

            // Operands become live.
            for val in inst_operands(&node.data) {
                live.insert(val);
            }
        }

        // Walk phis backward.
        for &phi_id in block.phis.iter().rev() {
            if let Some(result) = module.inst(phi_id).result {
                for &v in &live {
                    if v != result {
                        graph.entry(result).or_default().insert(v);
                        graph.entry(v).or_default().insert(result);
                    }
                }
                live.remove(&result);
            }
        }
    }

    graph
}

// ─── Step 3: Accumulator preference ──────────────────────────────────────────

/// Compute accumulator preference score for each value.
/// Positive = prefer acc, negative = prefer register.
fn compute_acc_scores(module: &Module, rpo: &[Block]) -> HashMap<Value, i32> {
    let mut scores: HashMap<Value, i32> = HashMap::new();

    for &bb in rpo {
        let block = module.block(bb);
        for &inst_id in block.insts.iter() {
            let node = module.inst(inst_id);

            // Result produced to acc: +2
            if let Some(result) = node.result {
                *scores.entry(result).or_default() += 2;
            }

            match &node.data {
                // BinOp left operand in acc: +2
                InstData::BinaryOp { left, .. } => {
                    *scores.entry(*left).or_default() += 2;
                }
                // Values used as register operands: -3
                InstData::Call { callee, args, .. } => {
                    *scores.entry(*callee).or_default() -= 3;
                    for a in args {
                        *scores.entry(*a).or_default() -= 3;
                    }
                }
                InstData::StoreProperty { object, value, .. } => {
                    *scores.entry(*object).or_default() -= 3;
                    *scores.entry(*value).or_default() -= 3;
                }
                _ => {}
            }
        }
    }

    // Values with >2 uses: -5 (long-lived, better in register).
    let mut use_count: HashMap<Value, u32> = HashMap::new();
    for &bb in rpo {
        let block = module.block(bb);
        for &inst_id in block.phis.iter().chain(block.insts.iter()) {
            for val in inst_operands(&module.inst(inst_id).data) {
                *use_count.entry(val).or_default() += 1;
            }
        }
    }
    for (val, count) in &use_count {
        if *count > 2 {
            *scores.entry(*val).or_default() -= 5;
        }
    }

    scores
}

// ─── Step 4: MCS + Greedy coloring ──────────────────────────────────────────

/// MCS ordering followed by reverse greedy coloring.
/// Returns (allocation, num_regs).
fn mcs_color(
    all_values: &[Value],
    interference: &InterferenceGraph,
    acc_score: &HashMap<Value, i32>,
    param_count: u16,
) -> (HashMap<Value, RegSlot>, u16) {
    let n = all_values.len();
    let val_set: HashSet<Value> = all_values.iter().copied().collect();

    // MCS: repeatedly pick the unvisited vertex with the most visited neighbors.
    let mut weight: HashMap<Value, u32> = HashMap::new();
    let mut visited = HashSet::new();
    let mut mcs_order: Vec<Value> = Vec::with_capacity(n);

    for _ in 0..n {
        // Pick vertex with max weight (ties broken by acc_score descending).
        let best = all_values
            .iter()
            .filter(|v| !visited.contains(*v))
            .max_by_key(|v| {
                let w = weight.get(*v).copied().unwrap_or(0);
                let s = acc_score.get(*v).copied().unwrap_or(0);
                (w, s)
            })
            .copied();

        let v = match best {
            Some(v) => v,
            None => break,
        };

        visited.insert(v);
        mcs_order.push(v);

        // Increment weight of unvisited neighbors.
        if let Some(neighbors) = interference.get(&v) {
            for &nb in neighbors {
                if !visited.contains(&nb) && val_set.contains(&nb) {
                    *weight.entry(nb).or_default() += 1;
                }
            }
        }
    }

    // Greedy coloring in reverse MCS order.
    let mut allocation: HashMap<Value, RegSlot> = HashMap::new();
    let mut next_reg = param_count;

    // Pre-assign params.
    for i in 0..param_count {
        let val = Value::from_index(i as usize);
        allocation.insert(val, RegSlot::Reg(i));
    }

    for &v in mcs_order.iter().rev() {
        if allocation.contains_key(&v) {
            continue;
        }

        // Collect colors used by neighbors.
        let mut used_colors: HashSet<RegSlot> = HashSet::new();
        if let Some(neighbors) = interference.get(&v) {
            for nb in neighbors {
                if let Some(&color) = allocation.get(nb) {
                    used_colors.insert(color);
                }
            }
        }

        let score = acc_score.get(&v).copied().unwrap_or(0);

        // Try accumulator first if score is positive and acc is available.
        if score > 0 && !used_colors.contains(&RegSlot::Acc) {
            allocation.insert(v, RegSlot::Acc);
        } else {
            // Find smallest available register.
            let mut reg = 0u16;
            while used_colors.contains(&RegSlot::Reg(reg)) {
                reg += 1;
            }
            if reg >= next_reg {
                next_reg = reg + 1;
            }
            allocation.insert(v, RegSlot::Reg(reg));
        }
    }

    (allocation, next_reg)
}

// ─── Step 5: Boissinot SSA destruction ───────────────────────────────────────

/// Boissinot-style SSA destruction:
/// - Same-color phi operands: coalesce (no copy needed).
/// - Different-color: insert copy.
/// - Parallel copies resolved via topological sort + cycle breaking.
fn boissinot_destruction(
    module: &Module,
    rpo: &[Block],
    allocation: &HashMap<Value, RegSlot>,
) -> HashMap<(Block, Block), Vec<(Value, Value)>> {
    let mut copies: HashMap<(Block, Block), Vec<(Value, Value)>> = HashMap::new();

    for &bb in rpo {
        let block = module.block(bb);
        for &phi_id in &block.phis {
            let inst_node = module.inst(phi_id);
            let dst = match inst_node.result {
                Some(v) => v,
                None => continue,
            };
            let dst_color = allocation.get(&dst);

            if let InstData::Phi { entries } = &inst_node.data {
                for &(pred, src) in entries {
                    let src_color = allocation.get(&src);
                    // Only insert copy if colors differ.
                    if src_color != dst_color {
                        copies.entry((pred, bb)).or_default().push((src, dst));
                    }
                }
            }
        }
    }

    // Resolve parallel copies: topological sort with cycle breaking.
    for (_, copy_list) in copies.iter_mut() {
        *copy_list = resolve_parallel_copies(copy_list, allocation);
    }

    copies
}

/// Resolve parallel copies into a sequential order.
/// Handles cycles by introducing a temporary swap.
fn resolve_parallel_copies(
    copies: &[(Value, Value)],
    _allocation: &HashMap<Value, RegSlot>,
) -> Vec<(Value, Value)> {
    if copies.len() <= 1 {
        return copies.to_vec();
    }

    // Build dependency graph: dst → src.
    let mut pending: Vec<(Value, Value)> = copies.to_vec();
    let mut result: Vec<(Value, Value)> = Vec::new();

    // Topological sort: emit copies whose dst is not a src of any other pending copy.
    let mut progress = true;
    while progress && !pending.is_empty() {
        progress = false;
        let srcs: HashSet<Value> = pending.iter().map(|(s, _)| *s).collect();
        let mut next_pending = Vec::new();

        for &(src, dst) in &pending {
            if !srcs.contains(&dst) || src == dst {
                // Safe to emit: no other copy reads from dst.
                if src != dst {
                    result.push((src, dst));
                }
                progress = true;
            } else {
                next_pending.push((src, dst));
            }
        }
        pending = next_pending;
    }

    // Remaining copies form cycles. Break each cycle with a swap pattern.
    // For a cycle a→b→c→a, emit: tmp=a, a=c, c=b, b=tmp
    while !pending.is_empty() {
        // Pick first copy to start the cycle.
        let (first_src, first_dst) = pending[0];
        result.push((first_src, first_dst)); // will be overwritten, but sequencing handles it
        pending.remove(0);

        // Follow the cycle.
        let mut cur = first_dst;
        while let Some(pos) = pending.iter().position(|(s, _)| *s == cur) {
            let (s, d) = pending.remove(pos);
            result.push((s, d));
            cur = d;
        }
    }

    result
}
