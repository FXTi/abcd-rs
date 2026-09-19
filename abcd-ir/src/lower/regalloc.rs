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

use crate::analysis::{self, augmented_succs, inst_operands};
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
    /// allocated value is `RegSlot::Acc` AND the frame is low-only (see
    /// `low_scratch_base`); always a `RegSlot::Reg`; never assigned to a
    /// value. In high-register mode acc spills route through the low scratch
    /// block instead, because this top-of-frame slot would itself be
    /// unencodable for the `op_v_8`-only `sta`/`lda`.
    pub spill_slot: Option<RegSlot>,
    /// Base of the reserved consecutive range-call argument window. `Some`
    /// iff the function contains a range-form call (isel's
    /// Callrange/Callthisrange/Supercallthisrange/Supercallarrowrange arms,
    /// narrow or wide). Every vendored range-call form encodes only a u8
    /// START register and reads argc consecutive slots, while the args'
    /// colored slots are not guaranteed consecutive (N4) — isel copies the
    /// args into `base .. base + argc` with auto-widening `mov`s and encodes
    /// `base` as the start. The window is reserved ONCE per function (sized
    /// to the largest range call); windows of different call sites overlap
    /// because each site's fill+call sequence completes before the next
    /// instruction is emitted — the window registers are dead outside the
    /// fill sequence. Coloring never assigns these slots to a value.
    /// Guaranteed ≤ 255 (checked at reservation; isel re-checks).
    pub call_window_base: Option<u16>,
    /// Base of the [`LOW_SCRATCH_COUNT`] consecutive reserved low (≤ 255)
    /// scratch registers, present iff the frame may exceed the u8 register
    /// operand encodings ("high-register mode"): indices `base .. base+3`
    /// route high register OPERANDS (one per operand position, so a
    /// 4-register-operand instruction never aliases two operands), index
    /// `base + 4` routes acc traffic (`sta scratch; mov high, scratch` for
    /// stores, `mov scratch, high; lda scratch` for loads, likewise for
    /// phi-copy emission in layout). `sta`/`lda` are `op_v_8`-only in the
    /// vendored ISA, so high registers are reachable only via `mov` (the
    /// sole auto-widening mnemonic, op_v1_16_v2_16). Never assigned to a
    /// value.
    pub low_scratch_base: Option<u16>,
}

/// Number of low scratch registers reserved in high-register mode for
/// routing register OPERANDS of one instruction: the maximum simultaneous
/// register operands of any instruction isel emits is 4
/// (`definegettersetterbyvalue`, `callthis3`).
pub const LOW_OPERAND_SCRATCHES: u16 = 4;
/// Total size of the reserved low scratch block: the operand scratches plus
/// one acc-routing scratch at index [`LOW_OPERAND_SCRATCHES`]. The acc
/// scratch must be distinct from the operand scratches: operand registers
/// stay live in their scratches across the acc operand's `lda`.
pub const LOW_SCRATCH_COUNT: u16 = LOW_OPERAND_SCRATCHES + 1;

#[derive(Debug, thiserror::Error)]
pub enum RegAllocError {
    #[error("function requires more than 65535 registers")]
    RegisterOverflow,
    #[error(
        "range-call argument window needs a start register <= 255 (u8 in every vendored \
         callrange form, narrow and wide), but the parameter/scratch area already extends past it"
    )]
    WindowBaseOverflow,
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
            call_window_base: None,
            low_scratch_base: None,
        });
    }

    // Range-call argument window + low scratch block reservation (S2/N4).
    //
    // The vendored range-call forms encode only a u8 START register and read
    // argc consecutive slots, and `sta`/`lda` are op_v_8-only, so:
    //
    // 1. `window` = the largest range-call argc in the function. When > 0, a
    //    consecutive window of that many slots is reserved right after the
    //    parameter homes (plus the scratch block in high-register mode) and
    //    coloring never assigns it; isel copies each call's args into it in
    //    call order (auto-widening `mov`, encodable for any slot). The
    //    window start must be ≤ 255 even for the wide forms.
    // 2. High-register mode: when even the most compact packing (values +
    //    params + window + the two top reservations) cannot keep every slot
    //    ≤ 255, some value may be colored to a register ≥ 256, which
    //    `sta`/`lda` cannot encode. LOW_SCRATCH_COUNT low scratch registers
    //    are then reserved between the parameter homes and the window, and
    //    isel/layout route all high-register acc traffic through them.
    //    Coloring skips the reserved slots, so the reservation is honest:
    //    the scratches are never live across any instruction.
    //
    // Both reservations are computed BEFORE liveness/interference: the
    // overflow checks are cheap hard errors even for pathological inputs
    // (e.g. a > u16::MAX-arg call would otherwise build a quadratic
    // interference graph before failing).
    let window = range_call_window_size(module, &rpo) as u64;
    let param_count = func.param_count as u64;
    let n_values = all_values.len() as u64;
    // Low mode must also fit the copy_temp/spill_slot top reservations (+ 2).
    let low_mode_fits = param_count + window + n_values + 2 <= 256;
    let low_scratches = if low_mode_fits {
        0
    } else {
        LOW_SCRATCH_COUNT as u64
    };
    let window_base = param_count + low_scratches;
    if window > 0 {
        if window_base > 255 {
            return Err(RegAllocError::WindowBaseOverflow);
        }
        if window_base + window > u16::MAX as u64 {
            // The frame cannot hold the window (this also rejects
            // argc > u16::MAX, which no vendored form can encode).
            return Err(RegAllocError::RegisterOverflow);
        }
    }
    if low_scratches > 0 && param_count + low_scratches > 256 {
        // The scratch block itself would not be low-addressable.
        return Err(RegAllocError::RegisterOverflow);
    }
    let reserved_start = param_count as u16;
    let reserved_len = (low_scratches + window) as u16;

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

    // Step 4: MCS ordering + greedy coloring. The reserved parameter homes
    // are pre-assigned; the reserved window/scratch range is skipped by the
    // smallest-slot scan.
    let (allocation, colored_regs) = mcs_color(
        &all_values,
        &interference,
        &acc_score,
        func.param_count,
        &func.param_values,
        &handler_live_in,
        reserved_start,
        reserved_len,
    )?;

    // The frame must cover the reserved window/scratch range even when
    // coloring stayed below it.
    let mut num_regs = colored_regs.max(reserved_start + reserved_len);

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
    //
    // High-register mode skips this reservation: a top-of-frame slot would
    // be ≥ 256 and unencodable for the op_v_8-only `sta`, and isel routes
    // acc spills through the low scratch block (`low_scratch_base`) instead.
    let spill_slot = if low_scratches == 0 && allocation.values().any(|&slot| slot == RegSlot::Acc)
    {
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
        call_window_base: if window > 0 {
            Some(window_base as u16)
        } else {
            None
        },
        low_scratch_base: if low_scratches > 0 {
            Some(param_count as u16)
        } else {
            None
        },
    })
}

/// Largest argument count among the function's range-form calls — the arms
/// where isel encodes a start register and the VM reads argc consecutive
/// slots: `Call` with > 3 args, `CallThis` with > 4 args (args[0] is `this`),
/// the always-range `SuperCall`/`SuperCallArrow`, and every `Construct`
/// (the window holds [callee, args...] — the constructor counts, so the
/// window is args.len() + 1 slots). Fixed-arity forms and spread/apply
/// calls pass individual register operands and need no window.
fn range_call_window_size(module: &Module, rpo: &[Block]) -> usize {
    use crate::inst::CallKind;
    let mut window = 0usize;
    for &bb in rpo {
        for &inst_id in &module.block(bb).insts {
            if let InstData::Call { kind, args, .. } = &module.inst(inst_id).data {
                let range_argc = match kind {
                    CallKind::Call if args.len() > 3 => Some(args.len()),
                    CallKind::CallThis if args.len() > 4 => Some(args.len()),
                    CallKind::SuperCall | CallKind::SuperCallArrow => Some(args.len()),
                    CallKind::Construct => Some(args.len() + 1),
                    _ => None,
                };
                if let Some(argc) = range_argc {
                    window = window.max(argc);
                }
            }
        }
    }
    window
}

// ─── Step 1: Exact backward dataflow liveness ────────────────────────────────

/// Compute live_in and live_out sets for each block.
/// Phi operands are treated as uses in the predecessor block.
///
/// Exception edges participate (`analysis::augmented_succs`): a catch
/// handler is a control-flow successor of every block in its try region —
/// an exception can transfer control from any protected instruction to
/// the handler, so values the handler uses are live out of every try
/// block. Terminator-only successors (`block_succs`) miss this: a try
/// body may end in `Throw`/`Unreachable` while the handler still reads
/// values defined there (S6 — without these edges such values look dead
/// past their definition, never interfere, and can all be colored Acc).
fn compute_liveness(
    module: &Module,
    func_id: FuncId,
    rpo: &[Block],
) -> (
    HashMap<Block, HashSet<Value>>,
    HashMap<Block, HashSet<Value>>,
) {
    // Augmented successor map: terminator successors plus, for every try
    // region, an edge from each protected block to each of its handlers.
    let succs: HashMap<Block, Vec<Block>> = rpo
        .iter()
        .map(|&bb| (bb, augmented_succs(module, func_id, bb)))
        .collect();

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
///
/// `reserved_start .. reserved_start + reserved_len` is the reserved
/// low-slot range (low scratch block + range-call argument window, starting
/// right after the parameter homes): the smallest-slot scan never hands
/// those slots to a value, so isel can use them as dead scratch at any
/// emission point.
#[allow(clippy::too_many_arguments)]
fn mcs_color(
    all_values: &[Value],
    interference: &InterferenceGraph,
    acc_score: &HashMap<Value, i32>,
    param_count: u16,
    params: &[Value],
    acc_forbidden: &HashSet<Value>,
    reserved_start: u16,
    reserved_len: u16,
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
            // Find smallest available register, skipping the reserved
            // scratch/window range: those slots must stay dead for isel.
            let mut reg = 0u16;
            loop {
                if reg >= reserved_start && reg < reserved_start + reserved_len {
                    reg = reserved_start + reserved_len;
                    continue;
                }
                if !used_colors.contains(&RegSlot::Reg(reg)) {
                    break;
                }
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
