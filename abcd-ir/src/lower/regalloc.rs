//! SSA-based register allocation.
//!
//! 1. Exact backward dataflow liveness analysis.
//! 2. Interference graph construction (SSA guarantees chordal graph).
//! 3. MCS (Maximum Cardinality Search) ordering + greedy coloring with
//!    accumulator preference heuristic.
//! 4. Boissinot SSA destruction: coalesce same-color phi operands, collect
//!    the per-edge parallel copy sets for different colors. The copies are
//!    resolved (sequentialized) at slot level at the emission point in
//!    `layout`, because coalescing can make distinct values share a slot.

use std::collections::{BinaryHeap, HashMap, HashSet};

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
    /// Total registers used (excluding accumulator), including the reserved
    /// `copy_temp` and `spill_slot` registers when present.
    pub num_regs: u16,
    /// Reserved real register for breaking slot-level copy cycles in layout.
    /// `Some` iff the function has any phi copies; never assigned to a value.
    pub copy_temp: Option<RegSlot>,
    /// Reserved real register for isel's intra-instruction accumulator spills
    /// (an Acc-colored value needed as a register operand). `Some` iff any
    /// allocated value is `RegSlot::Acc`; always a `RegSlot::Reg`; never
    /// assigned to a value.
    pub spill_slot: Option<RegSlot>,
}

#[derive(Debug, thiserror::Error)]
pub enum RegAllocError {
    #[error("function requires more than 65535 registers")]
    RegisterOverflow,
}

/// Where a value lives after allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RegSlot {
    Reg(u16),
    Acc,
}

/// Ceiling for allocated (and reserved) registers. Slots at or above this
/// base are outside the declared frame; nothing may be assigned there.
pub const TEMP_REG_BASE: u16 = 0xfff0;

/// Re-export compute_rpo for backward compatibility.
pub fn compute_rpo(module: &Module, func_id: FuncId) -> Vec<Block> {
    analysis::compute_rpo(module, func_id)
}

/// Allocate registers for a function using SSA-based chordal coloring.
pub fn allocate(module: &Module, func_id: FuncId) -> Result<RegAlloc, RegAllocError> {
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
    // Add function parameters. `param_values` is the authoritative
    // parameter identity (lift entry seeding / IRBuilder::create_func_param);
    // an arena-index convention (`Value::from_index(i)`) would name values
    // of OTHER functions in a multi-function module.
    for &val in &func.param_values {
        if !all_values.contains(&val) {
            all_values.push(val);
        }
    }

    if all_values.is_empty() {
        return Ok(RegAlloc {
            allocation: HashMap::new(),
            phi_copies: HashMap::new(),
            num_regs: 0,
            copy_temp: None,
            spill_slot: None,
        });
    }
    // Step 1: Exact backward dataflow liveness (exception edges included).
    let (live_in, live_out) = compute_liveness(module, func_id, &rpo);

    // Values live into a catch handler must not be Acc-colored: exception
    // dispatch physically delivers the thrown object in the accumulator,
    // so the acc content of any value live across an exception edge is
    // dead at handler entry. They must keep a real register home.
    let handler_live_in: HashSet<Value> = func
        .try_regions
        .iter()
        .flat_map(|region| region.catches.iter())
        .filter_map(|catch| live_in.get(&catch.handler_block))
        .flatten()
        .copied()
        .collect();

    // Step 2: Build interference graph.
    let interference = build_interference(module, &rpo, &live_out);

    // Step 3: Compute accumulator preference scores.
    let acc_score = compute_acc_scores(module, &rpo);

    // Step 4: MCS ordering + greedy coloring.
    let (allocation, mut num_regs) = mcs_color(
        &all_values,
        &interference,
        &acc_score,
        func.param_count,
        &func.param_values,
        &handler_live_in,
    )?;

    // Step 5: Boissinot SSA destruction — collect the per-edge value-level
    // copy sets. Slot-level resolution happens at the emission point in
    // `layout`, so no value-level cycle breaking (or pseudo-temp) is done here.
    let phi_copies = boissinot_destruction(module, &rpo, &allocation);

    // Step 6: When any edge carries phi copies, reserve exactly one real temp
    // register for slot-level cycle breaking. Overflow is a hard error, not
    // a silent saturation.
    let copy_temp = if phi_copies.values().any(|copies| !copies.is_empty()) {
        let temp = num_regs;
        if temp >= TEMP_REG_BASE {
            return Err(RegAllocError::RegisterOverflow);
        }
        num_regs += 1;
        Some(RegSlot::Reg(temp))
    } else {
        None
    };

    // Step 7: When any value lives in the accumulator, reserve exactly one
    // real register as isel's intra-instruction spill slot. The reservation
    // order is deterministic: `copy_temp` (step 6) first, then `spill_slot`,
    // each taking the current `num_regs` and incrementing it. Both registers
    // are therefore distinct, in-frame, and disjoint from every colored slot.
    let spill_slot = if allocation.values().any(|&slot| slot == RegSlot::Acc) {
        let spill = num_regs;
        if spill >= TEMP_REG_BASE {
            return Err(RegAllocError::RegisterOverflow);
        }
        num_regs += 1;
        Some(RegSlot::Reg(spill))
    } else {
        None
    };

    Ok(RegAlloc {
        allocation,
        phi_copies,
        num_regs,
        copy_temp,
        spill_slot,
    })
}

// ─── Step 1: Exact backward dataflow liveness ────────────────────────────────

/// Compute live_in and live_out sets for each block.
/// Phi operands are treated as uses in the predecessor block.
///
/// Exception edges participate: a catch handler is a control-flow
/// successor of every block in its try region — an exception can transfer
/// control from any protected instruction to the handler, so values the
/// handler uses are live out of every try block. Terminator-only
/// successors (`block_succs`) miss this: a try body may end in
/// `Throw`/`Unreachable` while the handler still reads values defined
/// there (S6 — without these edges such values look dead past their
/// definition, never interfere, and can all be colored Acc).
fn compute_liveness(
    module: &Module,
    func_id: FuncId,
    rpo: &[Block],
) -> (
    HashMap<Block, HashSet<Value>>,
    HashMap<Block, HashSet<Value>>,
) {
    let func = module.func(func_id);

    // Augmented successor map: terminator successors plus, for every try
    // region, an edge from each protected block to each of its handlers.
    let mut succs: HashMap<Block, Vec<Block>> = rpo
        .iter()
        .map(|&bb| (bb, block_succs(module, bb)))
        .collect();
    for region in &func.try_regions {
        for &try_block in &region.try_blocks {
            if let Some(edges) = succs.get_mut(&try_block) {
                for catch in &region.catches {
                    if !edges.contains(&catch.handler_block) {
                        edges.push(catch.handler_block);
                    }
                }
            }
        }
    }

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
            let empty: Vec<Block> = Vec::new();
            let bb_succs = succs.get(&bb).unwrap_or(&empty);
            // live_out = union of live_in of successors
            let mut new_out = HashSet::new();
            for &succ in bb_succs {
                if let Some(succ_in) = live_in.get(&succ) {
                    new_out.extend(succ_in);
                }
            }
            // Also add phi operands from successors that come from this block.
            for &succ in bb_succs {
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
                // copydataproperties: dst is a register operand (-3), src
                // rides the accumulator (+2) — vendor
                // `copydataproperties v:in:top, acc: inout:top`.
                InstData::CopyDataProperties { dst, src } => {
                    *scores.entry(*dst).or_default() -= 3;
                    *scores.entry(*src).or_default() += 2;
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
///
/// Parameters are pre-assigned to their vreg homes: `params[i]` (the
/// function's own `param_values`, NOT an arena index) gets `Reg(i)`, the
/// bottom of the frame. isel's copy-in prologue moves the ABI top slots
/// into these homes. `param_count` still seeds `next_reg` so a hand-built
/// function that declares more args than it created values for keeps the
/// bottom slots reserved, preserving the historical frame size.
///
/// `acc_forbidden` values (live into a catch handler) are never colored
/// Acc: exception dispatch physically clobbers the accumulator.
fn mcs_color(
    all_values: &[Value],
    interference: &InterferenceGraph,
    acc_score: &HashMap<Value, i32>,
    param_count: u16,
    params: &[Value],
    acc_forbidden: &HashSet<Value>,
) -> Result<(HashMap<Value, RegSlot>, u16), RegAllocError> {
    let n = all_values.len();
    let val_set: HashSet<Value> = all_values.iter().copied().collect();

    // MCS: repeatedly pick the unvisited vertex with the most visited
    // neighbors. A heap avoids rescanning the complete value set for every
    // vertex on high-register-pressure methods.
    let mut weight: HashMap<Value, u32> = HashMap::new();
    let mut visited = HashSet::new();
    let mut mcs_order: Vec<Value> = Vec::with_capacity(n);
    let mut heap: BinaryHeap<(u32, i32, Value)> = BinaryHeap::new();
    for &value in all_values {
        heap.push((0, acc_score.get(&value).copied().unwrap_or(0), value));
    }

    for _ in 0..n {
        let v = loop {
            let Some((w, _score, value)) = heap.pop() else {
                return Err(RegAllocError::RegisterOverflow);
            };
            if visited.contains(&value) || weight.get(&value).copied().unwrap_or(0) != w {
                continue;
            }
            break value;
        };

        visited.insert(v);
        mcs_order.push(v);

        // Increment weight of unvisited neighbors.
        if let Some(neighbors) = interference.get(&v) {
            for &nb in neighbors {
                if !visited.contains(&nb) && val_set.contains(&nb) {
                    let new_weight = weight.entry(nb).or_default();
                    *new_weight += 1;
                    heap.push((*new_weight, acc_score.get(&nb).copied().unwrap_or(0), nb));
                }
            }
        }
    }

    // Greedy coloring in reverse MCS order.
    let mut allocation: HashMap<Value, RegSlot> = HashMap::new();
    let mut next_reg = param_count;

    // Pre-assign params to their vreg homes at the bottom of the frame.
    for (i, &val) in params.iter().enumerate() {
        allocation.insert(val, RegSlot::Reg(i as u16));
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

        // Try accumulator first if score is positive, acc is available, and
        // the value is not live into a catch handler (exception dispatch
        // clobbers the physical acc).
        if score > 0 && !acc_forbidden.contains(&v) && !used_colors.contains(&RegSlot::Acc) {
            allocation.insert(v, RegSlot::Acc);
        } else {
            // Find smallest available register.
            let mut reg = 0u16;
            while used_colors.contains(&RegSlot::Reg(reg)) {
                if reg == u16::MAX {
                    return Err(RegAllocError::RegisterOverflow);
                }
                reg += 1;
            }
            if reg >= TEMP_REG_BASE {
                return Err(RegAllocError::RegisterOverflow);
            }
            if reg >= next_reg {
                next_reg = reg + 1;
            }
            allocation.insert(v, RegSlot::Reg(reg));
        }
    }

    Ok((allocation, next_reg))
}

// ─── Step 5: Boissinot SSA destruction ───────────────────────────────────────

/// Boissinot-style SSA destruction:
/// - Same-color phi operands: coalesce (no copy needed).
/// - Different-color: record a copy on the (pred, block) edge.
///
/// The returned per-edge lists are parallel copy *sets* in value space.
/// They are NOT sequentialized here: coalescing lets distinct values share
/// a slot, so the safe emission order (and any cycle breaking through the
/// reserved `copy_temp` register) is computed at slot level in `layout`.
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

    copies
}
