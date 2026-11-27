//! Hack–Grund–Goos dominance-tree SSA register allocation with Boissinot CSSA
//! isolation and biased coalescing (`design/ir.md` §5, `design/decisions.md`
//! `ADR-03`, `ADR-04`, `D7 = B`).
//!
//! 1. **Exception-augmented `[u64]` bitset backward liveness**:
//!    `O(iter * B * ceil(V / 64))` dataflow over `abcd_ir::cfg` (`compute_rpo`,
//!    `normal_succs_inline`, `ExceptionHandlerMap`), killing
//!    [`ValueDef::ExceptionParam`] at handler entry along every
//!    [`EdgeKind::Exceptional`] incoming edge while preserving loop-carried
//!    exception parameters across normal handler loop back-edges.
//! 2. **CSSA Isolation & Zero-Exception-Copy Handler Phi Lowering**
//!    (Boissinot et al., *CGO* 2009 + `N21`):
//!    - Pure-normal `Phi`s keep CSSA non-interfering operand/result webs; any
//!      uncoalesced normal edge lowers via [`RegAlloc::phi_copies`] and
//!      `copy_resolve`.
//!    - Handler `Phi`s with valid non-self `Exceptional` predecessors receive a
//!      dedicated pinned home register `slot(p)` in `O(total_phi_inputs)`:
//!      `Exceptional` predecessors write-through to `slot(p)` at definition /
//!      block-entry sites (`handler_phi_stores`), while `Normal` incoming edges
//!      into the same catch handler emit standard `Normal`-edge `phi_copies`
//!      (`slot(p) <- reg(v_norm)`), never clobbering `slot(p)` inside a live
//!      protected `try` block!
//! 3. **Hack–Grund–Goos Dominance-Tree Preorder Coloring** (*CC* 2006):
//!    Iterative preorder walk of `DomTree::compute_augmented` using an explicit
//!    heap stack (`DomStep::Enter` / `DomStep::Exit`) and an `in_use` color
//!    bitset with undo restoration — `O(1)` call stack, `O(V + E)` memory,
//!    **zero** `O(V^2)` interference graph, and biased coalescing hints across
//!    `Phi`s, `Mov`s, and `AllocClosure`s.

use std::collections::{HashMap, HashSet};

use abcd_ir::cfg::{
    DomTree, ExceptionHandlerMap, compute_rpo as ir_compute_rpo, normal_succs_inline,
};
use abcd_ir::{BlockId, EdgeKind, FuncId, InstId, Module, Op, UnOp, ValueDef, ValueId};

use crate::fusion::Suppression;

/// The result of register allocation for a function.
#[derive(Debug)]
pub struct RegAlloc {
    /// Value → allocated register home. Every value lives in a register;
    /// the accumulator is a physical emission-time resource tracked by
    /// isel (acc-as-cache, B4), never a coloring class.
    pub allocation: HashMap<ValueId, RegSlot>,
    /// Parallel copies for phi elimination on `EdgeKind::Normal` edges.
    /// Key: `(predecessor, successor)`. Value: `(src, dst)` copies.
    /// Never carries exception-edge copies (`N21`).
    pub phi_copies: HashMap<(BlockId, BlockId), Vec<(ValueId, ValueId)>>,
    /// `N21` write-through stores for handler-block phis along
    /// `EdgeKind::Exceptional` edges, as `(pred, incoming value, phi result)`
    /// triples sorted deterministically.
    pub handler_phi_stores: Vec<(BlockId, ValueId, ValueId)>,
    /// Total registers used, including the reserved `copy_temp` register
    /// when present.
    pub num_regs: u16,
    /// Reserved real register for breaking slot-level copy cycles in layout
    /// and same-block handler-phi store cycles in isel.
    pub copy_temp: Option<RegSlot>,
    /// Base of the reserved consecutive range-call argument window (`<= 255`).
    pub call_window_base: Option<u16>,
    /// Base of the [`LOW_SCRATCH_COUNT`] consecutive reserved low (`<= 255`)
    /// scratch registers in high-register mode.
    pub low_scratch_base: Option<u16>,
}

/// Number of low scratch registers reserved in high-register mode for
/// routing register OPERANDS of one instruction (`definegettersetterbyvalue`,
/// `callthis3`).
pub const LOW_OPERAND_SCRATCHES: u16 = 4;

/// Total size of the reserved low scratch block: operand scratches plus one
/// acc-routing scratch at index [`LOW_OPERAND_SCRATCHES`].
pub const LOW_SCRATCH_COUNT: u16 = LOW_OPERAND_SCRATCHES + 1;

/// Register allocation failure modes.
#[derive(Debug, thiserror::Error)]
pub enum RegAllocError {
    /// The function requires more registers than the frame can hold.
    #[error("function requires more than 65535 registers")]
    RegisterOverflow,
    /// The range-call window cannot start low enough.
    #[error(
        "range-call argument window needs a start register <= 255 (u8 in every vendored \
         callrange form, narrow and wide), but the parameter/scratch area already extends past it"
    )]
    WindowBaseOverflow,
    /// A same-slot result/incoming handler-phi pair interferes.
    #[error(
        "a catch-handler phi has a same-slot result/incoming pair that interferes — SSA \
         coloring never assigns one slot to an interfering pair, so this is inconsistent \
         (hand-crafted) input"
    )]
    HandlerPhiSlotConflict,
    /// A handler-phi result or incoming value was never colored.
    #[error("a catch-handler phi result or one of its incoming values was never colored")]
    HandlerPhiUncoalesced,
}

/// Where a value lives after allocation (`ADR-03` / `B4`: virtual register home).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RegSlot {
    /// A virtual register home.
    Reg(u16),
}

/// Ceiling for allocated (and reserved) registers. Slots at or above this
/// base are outside the declared frame; nothing may be assigned there.
pub const TEMP_REG_BASE: u16 = 0xfff0;

/// Compute reachable-first reverse post-order block sequence via `abcd_ir::cfg`.
pub fn compute_rpo(module: &Module, func_id: FuncId) -> Vec<BlockId> {
    ir_compute_rpo(module, func_id)
}

/// Iterate a block's phi instructions (the leading [`Op::Phi`] prefix).
fn for_each_phi(module: &Module, block: BlockId, mut f: impl FnMut(&abcd_ir::Inst)) {
    let Some(bb) = module.block(block) else {
        return;
    };
    for &iid in &bb.insts {
        let Some(inst) = module.inst(iid) else { break };
        if !inst.op.is_phi() {
            break;
        }
        f(inst);
    }
}

/// Visit effective non-suppressed SSA uses of `inst_id`, unwrapping fused
/// single-use `JumpEqz` / `JumpNez` conditions at their consuming `CondBranch`
/// so operand liveness extends to the exact emission point in `isel`.
fn for_each_effective_use(
    module: &Module,
    suppression: &Suppression,
    inst_id: InstId,
    mut f: impl FnMut(ValueId),
) {
    if suppression.insts.contains(&inst_id) {
        return;
    }
    let Some(inst) = module.inst(inst_id) else {
        return;
    };
    inst.op.for_each_operand(|v| {
        if suppression.values.contains(&v) {
            if let Some(ValueDef::Inst(def_iid)) = module.value(v).map(|val| val.def)
                && let Some(Op::UnaryOp {
                    op: UnOp::JumpEqz | UnOp::JumpNez,
                    operand,
                }) = module.inst(def_iid).map(|i| &i.op)
                && !suppression.values.contains(operand)
            {
                f(*operand);
            }
        } else {
            f(v);
        }
    });
}

/// Per-function frame-initial constant values (`ValueDef::Const`, #30).
pub fn frame_init_consts(module: &Module, func_id: FuncId) -> Vec<ValueId> {
    let Some(func) = module.func(func_id) else {
        return Vec::new();
    };
    let mut out: Vec<ValueId> = Vec::with_capacity(func.frame_init_consts.len());
    let mut seen: HashSet<ValueId> = HashSet::with_capacity(func.frame_init_consts.len());
    for &vid in &func.frame_init_consts {
        if module
            .value(vid)
            .is_some_and(|v| matches!(v.def, ValueDef::Const(_)))
            && seen.insert(vid)
        {
            out.push(vid);
        }
    }
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &iid in &block.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            inst.op.for_each_operand(|operand| {
                if !seen.contains(&operand)
                    && module
                        .value(operand)
                        .is_some_and(|v| matches!(v.def, ValueDef::Const(_)))
                {
                    seen.insert(operand);
                    out.push(operand);
                }
            });
        }
    }
    out
}

/// Explicit heap workstack step for iterative `DomTree` preorder coloring.
#[derive(Clone, Copy, Debug)]
enum DomStep {
    Enter(BlockId),
    Exit(BlockId),
}

/// Allocate registers for a function using Hack–Grund–Goos dominance-tree SSA
/// coloring and Boissinot CSSA isolation.
pub fn allocate(
    module: &Module,
    func_id: FuncId,
    suppression: &Suppression,
) -> Result<RegAlloc, RegAllocError> {
    allocate_with_options(module, func_id, suppression, crate::LowerOptions::default())
}

/// [`allocate`] with explicit [`crate::LowerOptions`].
pub fn allocate_with_options(
    module: &Module,
    func_id: FuncId,
    suppression: &Suppression,
    _options: crate::LowerOptions,
) -> Result<RegAlloc, RegAllocError> {
    let Some(func) = module.func(func_id) else {
        return Ok(empty_regalloc());
    };
    let rpo = compute_rpo(module, func_id);
    let num_blocks = rpo.len();
    if num_blocks == 0 {
        return Ok(empty_regalloc());
    }

    let mut bb_to_idx: HashMap<BlockId, usize> = HashMap::with_capacity(num_blocks);
    for (idx, &bb) in rpo.iter().enumerate() {
        bb_to_idx.entry(bb).or_insert(idx);
    }

    let mut is_handler_idx = vec![false; num_blocks];
    let mut handler_exc_by_block: Vec<Vec<ValueId>> = vec![Vec::new(); num_blocks];
    let mut handler_exc_ordered: Vec<(BlockId, ValueId)> = Vec::new();
    for region in &func.try_regions {
        for catch in &region.catches {
            if let Some(&h_idx) = bb_to_idx.get(&catch.handler) {
                is_handler_idx[h_idx] = true;
                let list = &mut handler_exc_by_block[h_idx];
                if !list.contains(&catch.exception) {
                    list.push(catch.exception);
                }
            }
            let pair = (catch.handler, catch.exception);
            if !handler_exc_ordered.contains(&pair) {
                handler_exc_ordered.push(pair);
            }
        }
    }

    // Collect all allocatable SSA values in deterministic RPO order.
    let const_values = frame_init_consts(module, func_id);
    let mut entry_consts = const_values.clone();
    entry_consts.sort_unstable_by(|a, b| b.cmp(a));

    let entry = rpo[0];
    let mut all_values: Vec<ValueId> = Vec::new();
    let mut in_all: HashSet<ValueId> = HashSet::new();
    for &c in const_values.iter().rev() {
        if in_all.insert(c) {
            all_values.push(c);
        }
    }
    for &bb in &rpo {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &inst_id in &block.insts {
            if suppression.insts.contains(&inst_id) {
                continue;
            }
            if let Some(result) = module.inst(inst_id).and_then(|i| i.result)
                && in_all.insert(result)
            {
                all_values.push(result);
            }
        }
    }

    // Collect values with >= 1 effective non-suppressed use.
    let mut used: HashSet<ValueId> = HashSet::new();
    for &bb in &rpo {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &inst_id in &block.insts {
            for_each_effective_use(module, suppression, inst_id, |v| {
                used.insert(v);
            });
        }
    }

    for &val in &func.params {
        if in_all.insert(val) {
            all_values.push(val);
        }
    }
    for &(_, exc) in &handler_exc_ordered {
        if used.contains(&exc) && in_all.insert(exc) {
            all_values.push(exc);
        }
    }

    if all_values.is_empty() {
        return Ok(empty_regalloc());
    }

    // S2 / N4 / R3-M7: Reserve call window and low scratch registers up front.
    let window = range_call_window_size(module, &rpo) as u64;
    let param_count = func.params.len() as u64;
    let n_values = all_values.len() as u64;
    let low_mode_fits = param_count + window + n_values < 256;
    let low_scratches = if low_mode_fits {
        0
    } else {
        LOW_SCRATCH_COUNT as u64
    };

    let params_at_bottom =
        param_count + low_scratches <= 256 && (window == 0 || param_count + low_scratches <= 255);

    let (param_base, reserved_start, reserved_len, window_base, low_scratch_base) =
        if params_at_bottom {
            let wb = param_count + low_scratches;
            if window > 0 && wb + window > u64::from(u16::MAX) {
                return Err(RegAllocError::RegisterOverflow);
            }
            (
                0u16,
                param_count as u16,
                (low_scratches + window) as u16,
                wb as u16,
                (low_scratches > 0).then_some(param_count as u16),
            )
        } else {
            let wb = low_scratches;
            if window > 0 && wb + window > u64::from(u16::MAX) {
                return Err(RegAllocError::RegisterOverflow);
            }
            let res_len = low_scratches + window;
            if res_len + param_count > u64::from(TEMP_REG_BASE) {
                return Err(RegAllocError::RegisterOverflow);
            }
            (
                res_len as u16,
                0u16,
                res_len as u16,
                wb as u16,
                (low_scratches > 0).then_some(0u16),
            )
        };

    // Dense bit index `0..num_vals` strictly for `all_values`.
    let num_vals = all_values.len();
    let mut val_to_bit: HashMap<ValueId, usize> = HashMap::with_capacity(num_vals);
    for (bit, &v) in all_values.iter().enumerate() {
        val_to_bit.insert(v, bit);
    }
    let val_words = num_vals.div_ceil(64).max(1);

    // Precompute normal and exceptional successor indices per RPO block.
    let exc_map = ExceptionHandlerMap::build(module, func_id);
    let mut normal_succ_indices: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];
    let mut exc_succ_indices: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];
    let mut has_normal_pred = vec![false; num_blocks];

    for (b_idx, &bb) in rpo.iter().enumerate() {
        if let Some(block) = module.block(bb) {
            if block.preds.iter().any(|e| e.kind == EdgeKind::Normal) {
                has_normal_pred[b_idx] = true;
            }
            if let Some(term_op) = block
                .insts
                .last()
                .and_then(|&iid| module.inst(iid))
                .map(|i| &i.op)
            {
                let (ns, nlen) = normal_succs_inline(term_op);
                let out = &mut normal_succ_indices[b_idx];
                for &succ_bb in &ns[..nlen] {
                    if let Some(&si) = bb_to_idx.get(&succ_bb) {
                        has_normal_pred[si] = true;
                        if !out.contains(&si) {
                            out.push(si);
                        }
                    }
                }
            }
        }
        if let Some(ref em) = exc_map {
            let out = &mut exc_succ_indices[b_idx];
            for &h_bb in em.handlers_of(bb) {
                if let Some(&hi) = bb_to_idx.get(&h_bb)
                    && !out.contains(&hi)
                {
                    out.push(hi);
                }
            }
        }
    }

    // Classify whether an incoming `(edge, src)` to `b_idx` dispatches along
    // an `Exceptional` edge (`handler_phi_stores`) vs a `Normal` edge (`phi_copies`).
    let is_exc_phi_entry = |pred_bb: BlockId, b_idx: usize, kind: EdgeKind| -> bool {
        if !is_handler_idx[b_idx] {
            return false;
        }
        if kind == EdgeKind::Exceptional {
            return true;
        }
        if let Some(&pred_idx) = bb_to_idx.get(&pred_bb) {
            !normal_succ_indices[pred_idx].contains(&b_idx)
                && exc_succ_indices[pred_idx].contains(&b_idx)
        } else {
            false
        }
    };

    // Track defining block index per value bit for dominance & store-placement checks.
    let mut def_b_idx: Vec<Option<usize>> = vec![None; num_vals];
    let mut def_is_non_phi_in_block: Vec<Option<usize>> = vec![None; num_vals];
    for &p in &func.params {
        if let Some(&bit) = val_to_bit.get(&p) {
            def_b_idx[bit] = Some(0);
        }
    }
    for &c in &const_values {
        if let Some(&bit) = val_to_bit.get(&c) {
            def_b_idx[bit] = Some(0);
            def_is_non_phi_in_block[bit] = Some(0);
        }
    }
    for (b_idx, &bb) in rpo.iter().enumerate() {
        for &exc in &handler_exc_by_block[b_idx] {
            if let Some(&bit) = val_to_bit.get(&exc) {
                def_b_idx[bit] = Some(b_idx);
            }
        }
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &iid in &block.insts {
            if suppression.insts.contains(&iid) {
                continue;
            }
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            if let Some(res) = inst.result
                && let Some(&bit) = val_to_bit.get(&res)
            {
                def_b_idx[bit] = Some(b_idx);
                if !inst.op.is_phi() {
                    def_is_non_phi_in_block[bit] = Some(b_idx);
                }
            }
        }
    }

    // CSSA Handler-Phi Isolation (`O(total_phi_inputs)`, zero quadratic scans):
    // Pin a dedicated home register `slot(p)` for each used handler `Phi` `p`
    // that has >= 1 valid non-self `Exceptional` predecessor in `bb_to_idx`.
    let mut is_pinned_handler_phi = vec![false; num_vals];
    let mut handler_phi_stores: Vec<(BlockId, ValueId, ValueId)> = Vec::new();
    let mut block_start_store_srcs: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];

    for (b_idx, &bb) in rpo.iter().enumerate() {
        if !is_handler_idx[b_idx] {
            continue;
        }
        for_each_phi(module, bb, |inst| {
            let Some(res) = inst.result else { return };
            if !used.contains(&res) {
                return;
            }
            let Some(&res_bit) = val_to_bit.get(&res) else {
                return;
            };
            let Op::Phi { entries } = &inst.op else {
                return;
            };
            let has_valid_exc = entries.iter().any(|&(edge, src)| {
                src != res
                    && is_exc_phi_entry(edge.from, b_idx, edge.kind)
                    && bb_to_idx.contains_key(&edge.from)
                    && val_to_bit.contains_key(&src)
            });
            if !has_valid_exc {
                return;
            }
            is_pinned_handler_phi[res_bit] = true;
            for &(edge, src) in entries {
                if src == res || !is_exc_phi_entry(edge.from, b_idx, edge.kind) {
                    continue;
                }
                let Some(&pred_idx) = bb_to_idx.get(&edge.from) else {
                    continue;
                };
                let Some(&src_bit) = val_to_bit.get(&src) else {
                    continue;
                };
                handler_phi_stores.push((edge.from, src, res));
                if def_is_non_phi_in_block[src_bit] != Some(pred_idx)
                    && !block_start_store_srcs[pred_idx].contains(&src_bit)
                {
                    block_start_store_srcs[pred_idx].push(src_bit);
                }
            }
        });
    }
    handler_phi_stores.sort_unstable();
    handler_phi_stores.dedup();

    // Backward Bitset Liveness (`O(iter * B * ceil(V / 64))`).
    let mut handler_exc_bits: Vec<Vec<u64>> = vec![vec![0u64; val_words]; num_blocks];
    let mut block_use: Vec<Vec<u64>> = vec![vec![0u64; val_words]; num_blocks];
    let mut block_def: Vec<Vec<u64>> = vec![vec![0u64; val_words]; num_blocks];
    let mut phi_out_bits: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];

    for (b_idx, &bb) in rpo.iter().enumerate() {
        for &exc in &handler_exc_by_block[b_idx] {
            if let Some(&bit) = val_to_bit.get(&exc) {
                bit_set(&mut handler_exc_bits[b_idx], bit);
                if !has_normal_pred[b_idx] {
                    // Kill `ExceptionParam` at handler entry when `bb` has no
                    // normal predecessors (loop-header handlers mask `handler_exc_bits`
                    // on `Exceptional` edges below while keeping `exc` live across
                    // normal loop back-edges).
                    bit_set(&mut block_def[b_idx], bit);
                }
            }
        }
        for &src_bit in &block_start_store_srcs[b_idx] {
            bit_set(&mut block_use[b_idx], src_bit);
        }
        if b_idx == 0 {
            for &c in &const_values {
                if let Some(&bit) = val_to_bit.get(&c) {
                    bit_set(&mut block_def[0], bit);
                }
            }
        }
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &iid in &block.insts {
            let Some(node) = module.inst(iid) else {
                continue;
            };
            if let Op::Phi { entries } = &node.op {
                if let Some(res) = node.result
                    && let Some(&r_bit) = val_to_bit.get(&res)
                {
                    bit_set(&mut block_def[b_idx], r_bit);
                }
                if node.result.is_some_and(|r| used.contains(&r)) {
                    for &(edge, val) in entries {
                        if is_exc_phi_entry(edge.from, b_idx, edge.kind) {
                            continue;
                        }
                        if let (Some(&pred_idx), Some(&v_bit)) =
                            (bb_to_idx.get(&edge.from), val_to_bit.get(&val))
                            && normal_succ_indices[pred_idx].contains(&b_idx)
                        {
                            phi_out_bits[pred_idx].push(v_bit);
                        }
                    }
                }
                continue;
            }
            for_each_effective_use(module, suppression, iid, |val| {
                if let Some(&bit) = val_to_bit.get(&val)
                    && !bit_test(&block_def[b_idx], bit)
                {
                    bit_set(&mut block_use[b_idx], bit);
                }
            });
            if !suppression.insts.contains(&iid)
                && let Some(res) = node.result
                && let Some(&r_bit) = val_to_bit.get(&res)
            {
                bit_set(&mut block_def[b_idx], r_bit);
            }
        }
    }

    for pred_idx in 0..num_blocks {
        phi_out_bits[pred_idx].sort_unstable();
        phi_out_bits[pred_idx].dedup();
        for &bit in &phi_out_bits[pred_idx] {
            if !bit_test(&block_def[pred_idx], bit) {
                bit_set(&mut block_use[pred_idx], bit);
            }
        }
    }

    let mut live_in_bits: Vec<Vec<u64>> = vec![vec![0u64; val_words]; num_blocks];
    let mut live_out_bits: Vec<Vec<u64>> = vec![vec![0u64; val_words]; num_blocks];
    let mut scratch_out = vec![0u64; val_words];
    let mut scratch_in = vec![0u64; val_words];

    let mut changed = true;
    while changed {
        changed = false;
        for b_idx in (0..num_blocks).rev() {
            scratch_out.fill(0);
            for &si in &normal_succ_indices[b_idx] {
                for (dst_w, &src_w) in scratch_out.iter_mut().zip(&live_in_bits[si]) {
                    *dst_w |= src_w;
                }
            }
            for &hi in &exc_succ_indices[b_idx] {
                for (dst_w, (&in_w, &exc_w)) in scratch_out
                    .iter_mut()
                    .zip(live_in_bits[hi].iter().zip(&handler_exc_bits[hi]))
                {
                    *dst_w |= in_w & !exc_w;
                }
            }
            for &bit in &phi_out_bits[b_idx] {
                bit_set(&mut scratch_out, bit);
            }
            for w in 0..val_words {
                scratch_in[w] = block_use[b_idx][w] | (scratch_out[w] & !block_def[b_idx][w]);
            }
            if scratch_in != live_in_bits[b_idx] || scratch_out != live_out_bits[b_idx] {
                live_in_bits[b_idx].copy_from_slice(&scratch_in);
                live_out_bits[b_idx].copy_from_slice(&scratch_out);
                changed = true;
            }
        }
    }

    // Collect biased coalescing mate hints (`Phi` normal operands, `Mov`, `AllocClosure`).
    let mut copy_mate_hints: Vec<Vec<usize>> = vec![Vec::new(); num_vals];
    let mut add_mate_hint = |a_bit: usize, b_bit: usize| {
        if a_bit != b_bit && !is_pinned_handler_phi[a_bit] && !is_pinned_handler_phi[b_bit] {
            if !copy_mate_hints[a_bit].contains(&b_bit) {
                copy_mate_hints[a_bit].push(b_bit);
            }
            if !copy_mate_hints[b_bit].contains(&a_bit) {
                copy_mate_hints[b_bit].push(a_bit);
            }
        }
    };
    for (b_idx, &bb) in rpo.iter().enumerate() {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &iid in &block.insts {
            if suppression.insts.contains(&iid) {
                continue;
            }
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            let Some(res) = inst.result else {
                continue;
            };
            if !used.contains(&res) {
                continue;
            }
            let Some(&res_bit) = val_to_bit.get(&res) else {
                continue;
            };
            match &inst.op {
                Op::Phi { entries } => {
                    for &(edge, src) in entries {
                        if is_pinned_handler_phi[res_bit]
                            && is_exc_phi_entry(edge.from, b_idx, edge.kind)
                        {
                            continue;
                        }
                        if let Some(&src_bit) = val_to_bit.get(&src) {
                            add_mate_hint(res_bit, src_bit);
                        }
                    }
                }
                Op::Mov { src } => {
                    if let Some(&src_bit) = val_to_bit.get(src) {
                        add_mate_hint(res_bit, src_bit);
                    }
                }
                Op::AllocClosure { func: src } if !suppression.values.contains(src) => {
                    if let Some(&src_bit) = val_to_bit.get(src) {
                        add_mate_hint(res_bit, src_bit);
                    }
                }
                _ => {}
            }
        }
    }

    // Color bitsets (`0..TEMP_REG_BASE` valid; `TEMP_REG_BASE..65536` permanently forbidden).
    let color_words = 65_536usize.div_ceil(64);
    let mut base_forbidden_colors = vec![0u64; color_words];
    for c in usize::from(TEMP_REG_BASE)..(color_words * 64) {
        bit_set(&mut base_forbidden_colors, c);
    }
    for c in usize::from(reserved_start)..usize::from(reserved_start.saturating_add(reserved_len)) {
        if c < color_words * 64 {
            bit_set(&mut base_forbidden_colors, c);
        }
    }

    let mut val_color: Vec<Option<u16>> = vec![None; num_vals];
    let mut max_reg_plus_one: u16 = if func.params.is_empty() {
        0
    } else {
        param_base.saturating_add(func.params.len() as u16)
    };

    // Pre-assign function parameters (`param_base .. param_base + param_count`).
    let mut pin_forbidden = base_forbidden_colors.clone();
    for (i, &val) in func.params.iter().enumerate() {
        let r_u32 = u32::from(param_base) + i as u32;
        if r_u32 >= u32::from(TEMP_REG_BASE) {
            return Err(RegAllocError::RegisterOverflow);
        }
        let r = r_u32 as u16;
        if let Some(&bit) = val_to_bit.get(&val)
            && val_color[bit].is_none()
        {
            val_color[bit] = Some(r);
            bit_set(&mut pin_forbidden, usize::from(r));
        }
    }

    // Pre-assign dedicated pinned slots `slot(p)` for handler `Phi`s (`N21`).
    for bit in 0..num_vals {
        if !is_pinned_handler_phi[bit] || val_color[bit].is_some() {
            continue;
        }
        let slot = find_lowest_free_color(&pin_forbidden, 0)?;
        val_color[bit] = Some(slot);
        bit_set(&mut pin_forbidden, usize::from(slot));
        bit_set(&mut base_forbidden_colors, usize::from(slot));
        max_reg_plus_one = max_reg_plus_one.max(slot + 1);
    }

    // Build augmented dominance tree (`DomTree::compute_augmented`).
    let dom = DomTree::compute_augmented(module, func_id);

    // Defensive guard for hand-crafted unverified IR: any value live-in at a
    // reachable block not dominated by its definition (or live-in to its own
    // defining block without a `Phi`) gets a dedicated non-reusable slot so
    // `DomTree` preorder never sees an uncolored live-in or false reuse.
    if let Some(ref dt) = dom {
        for (b_idx, &bb) in rpo.iter().enumerate() {
            if !dt.is_reachable(bb) {
                continue;
            }
            for (w_idx, &word) in live_in_bits[b_idx].iter().enumerate() {
                let mut w = word;
                while w != 0 {
                    let tz = w.trailing_zeros() as usize;
                    let bit = (w_idx << 6) + tz;
                    w &= w - 1;
                    if val_color[bit].is_some() {
                        continue;
                    }
                    let dominates_use = match def_b_idx[bit] {
                        Some(def_idx) => {
                            let def_bb = rpo[def_idx];
                            def_idx != b_idx && dt.is_reachable(def_bb) && dt.dominates(def_bb, bb)
                        }
                        None => false,
                    };
                    if !dominates_use {
                        let slot = find_lowest_free_color(&pin_forbidden, 0)?;
                        val_color[bit] = Some(slot);
                        bit_set(&mut pin_forbidden, usize::from(slot));
                        bit_set(&mut base_forbidden_colors, usize::from(slot));
                        max_reg_plus_one = max_reg_plus_one.max(slot + 1);
                    }
                }
            }
        }
    }

    // Hack–Grund–Goos iterative `DomTree` preorder coloring (`O(1)` call stack).
    let mut colorer = DomColorer {
        module,
        suppression,
        entry_consts: &entry_consts,
        func_params: &func.params,
        handler_exc_by_block: &handler_exc_by_block,
        block_start_store_srcs: &block_start_store_srcs,
        used: &used,
        val_to_bit: &val_to_bit,
        live_in_bits: &live_in_bits,
        live_out_bits: &live_out_bits,
        copy_mate_hints: &copy_mate_hints,
        def_b_idx: &def_b_idx,
        in_use: base_forbidden_colors.clone(),
        undo_log: Vec::with_capacity(64),
        last_use_in_block: vec![0u32; num_vals],
        is_active_val: vec![false; num_vals],
        touched_vals: Vec::with_capacity(64),
        step_zero_bits: Vec::with_capacity(16),
        hint_candidates: Vec::with_capacity(8),
        val_color: &mut val_color,
        max_reg_plus_one: &mut max_reg_plus_one,
    };

    let mut visited_blocks = vec![false; num_blocks];
    if let Some(ref dt) = dom
        && dt.is_reachable(entry)
    {
        let mut dom_stack: Vec<DomStep> = vec![DomStep::Enter(entry)];
        let mut children_buf: Vec<(usize, BlockId)> = Vec::new();
        while let Some(step) = dom_stack.pop() {
            match step {
                DomStep::Enter(bb) => {
                    let Some(&b_idx) = bb_to_idx.get(&bb) else {
                        continue;
                    };
                    if visited_blocks[b_idx] {
                        continue;
                    }
                    visited_blocks[b_idx] = true;
                    let undo_mark = colorer.undo_log.len();
                    colorer.color_block(b_idx, bb)?;
                    // Restore `in_use` to `base_forbidden_colors` via the undo log
                    // before visiting dominated children (`in_use := colors(LiveIn(C))`).
                    colorer.unwind_to(undo_mark);

                    dom_stack.push(DomStep::Exit(bb));
                    children_buf.clear();
                    for &child in dt.dom_children(bb) {
                        if let Some(&c_idx) = bb_to_idx.get(&child) {
                            children_buf.push((c_idx, child));
                        }
                    }
                    children_buf.sort_unstable_by_key(|&(c_idx, _)| c_idx);
                    for &(_, child) in children_buf.iter().rev() {
                        dom_stack.push(DomStep::Enter(child));
                    }
                }
                DomStep::Exit(_bb) => {}
            }
        }
    }

    // Color any remaining values in unreachable dead blocks in deterministic RPO order.
    for (b_idx, &bb) in rpo.iter().enumerate() {
        if !visited_blocks[b_idx] {
            visited_blocks[b_idx] = true;
            let undo_mark = colorer.undo_log.len();
            colorer.color_block(b_idx, bb)?;
            colorer.unwind_to(undo_mark);
        }
    }

    // Fallback for any orphaned value in `all_values` not encountered in a block.
    for slot in &mut val_color {
        if slot.is_none() {
            let reg = find_lowest_free_color(&base_forbidden_colors, 0)?;
            *slot = Some(reg);
            max_reg_plus_one = max_reg_plus_one.max(reg + 1);
        }
    }

    let mut allocation: HashMap<ValueId, RegSlot> = HashMap::with_capacity(num_vals);
    for (bit, &val) in all_values.iter().enumerate() {
        let reg = val_color[bit].ok_or(RegAllocError::RegisterOverflow)?;
        allocation.insert(val, RegSlot::Reg(reg));
    }

    #[cfg(debug_assertions)]
    debug_verify_allocation(
        module,
        suppression,
        &rpo,
        &entry_consts,
        &func.params,
        &handler_exc_by_block,
        &block_start_store_srcs,
        &used,
        &val_to_bit,
        &live_in_bits,
        &live_out_bits,
        &val_color,
        reserved_start,
        reserved_len,
    );

    let min_param_end = if func.params.is_empty() {
        0
    } else {
        param_base + func.params.len() as u16
    };
    let mut num_regs = max_reg_plus_one
        .max(reserved_start + reserved_len)
        .max(min_param_end);

    // Boissinot out-of-SSA parallel copy collection on `EdgeKind::Normal` edges.
    let phi_copies = boissinot_destruction(module, &rpo, &allocation, &used, is_exc_phi_entry);

    // Reserve `copy_temp` whenever normal edge copies exist or same-block
    // handler-phi stores could form a swap/WAR chain (`R3-X3`).
    let handler_store_cycle_possible =
        handler_phi_stores
            .iter()
            .enumerate()
            .any(|(i, &(p1, s1, d1))| {
                let s1_slot = allocation.get(&s1);
                let d1_slot = allocation.get(&d1);
                handler_phi_stores[i + 1..].iter().any(|&(p2, s2, d2)| {
                    p1 == p2 && (allocation.get(&s2) == d1_slot || allocation.get(&d2) == s1_slot)
                })
            });
    let need_copy_temp =
        phi_copies.values().any(|copies| !copies.is_empty()) || handler_store_cycle_possible;
    let copy_temp = if need_copy_temp {
        let temp = num_regs;
        if temp >= TEMP_REG_BASE {
            return Err(RegAllocError::RegisterOverflow);
        }
        num_regs += 1;
        Some(RegSlot::Reg(temp))
    } else {
        None
    };

    Ok(RegAlloc {
        allocation,
        phi_copies,
        handler_phi_stores,
        num_regs,
        copy_temp,
        call_window_base: (window > 0).then_some(window_base),
        low_scratch_base,
    })
}

fn empty_regalloc() -> RegAlloc {
    RegAlloc {
        allocation: HashMap::new(),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 0,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    }
}

struct DomColorer<'a> {
    module: &'a Module,
    suppression: &'a Suppression,
    entry_consts: &'a [ValueId],
    func_params: &'a [ValueId],
    handler_exc_by_block: &'a [Vec<ValueId>],
    block_start_store_srcs: &'a [Vec<usize>],
    used: &'a HashSet<ValueId>,
    val_to_bit: &'a HashMap<ValueId, usize>,
    live_in_bits: &'a [Vec<u64>],
    live_out_bits: &'a [Vec<u64>],
    copy_mate_hints: &'a [Vec<usize>],
    def_b_idx: &'a [Option<usize>],
    in_use: Vec<u64>,
    undo_log: Vec<(usize, bool)>,
    last_use_in_block: Vec<u32>,
    is_active_val: Vec<bool>,
    touched_vals: Vec<usize>,
    step_zero_bits: Vec<usize>,
    hint_candidates: Vec<u16>,
    val_color: &'a mut [Option<u16>],
    max_reg_plus_one: &'a mut u16,
}

impl DomColorer<'_> {
    #[inline]
    fn set_color_in_use(&mut self, color: u16) {
        let idx = usize::from(color);
        let prev = bit_test(&self.in_use, idx);
        if !prev {
            self.undo_log.push((idx, false));
            bit_set(&mut self.in_use, idx);
        }
    }

    #[inline]
    fn clear_color_in_use(&mut self, color: u16) {
        let idx = usize::from(color);
        let prev = bit_test(&self.in_use, idx);
        if prev {
            self.undo_log.push((idx, true));
            bit_clear(&mut self.in_use, idx);
        }
    }

    fn unwind_to(&mut self, mark: usize) {
        while self.undo_log.len() > mark {
            if let Some((idx, prev)) = self.undo_log.pop() {
                if prev {
                    bit_set(&mut self.in_use, idx);
                } else {
                    bit_clear(&mut self.in_use, idx);
                }
            }
        }
    }

    #[inline]
    fn record_local_use(&mut self, bit: usize, step: u32) {
        if self.last_use_in_block[bit] == 0 {
            self.touched_vals.push(bit);
        }
        if step > self.last_use_in_block[bit] {
            self.last_use_in_block[bit] = step;
        }
    }

    #[inline]
    fn mark_active_val(&mut self, bit: usize, color: u16) {
        if !self.is_active_val[bit] {
            if self.last_use_in_block[bit] == 0 {
                self.touched_vals.push(bit);
            }
            self.is_active_val[bit] = true;
            self.set_color_in_use(color);
        }
    }

    #[inline]
    fn release_active_val(&mut self, bit: usize) {
        if self.is_active_val[bit] {
            self.is_active_val[bit] = false;
            if let Some(c) = self.val_color[bit] {
                self.clear_color_in_use(c);
            }
        }
    }

    #[inline]
    fn stays_live_past(&self, b_idx: usize, bit: usize, step: u32) -> bool {
        bit_test(&self.live_out_bits[b_idx], bit) || self.last_use_in_block[bit] > step
    }

    fn pick_color_for(&mut self, d_bit: usize) -> Result<u16, RegAllocError> {
        if let Some(existing) = self.val_color[d_bit] {
            return Ok(existing);
        }
        self.hint_candidates.clear();
        for &mate_bit in &self.copy_mate_hints[d_bit] {
            if let Some(c) = self.val_color[mate_bit]
                && !bit_test(&self.in_use, usize::from(c))
            {
                // Reject loop-header mate hints if unverified IR has `d_bit`
                // live-in at `mate_bit`'s defining block.
                let safe = match self.def_b_idx[mate_bit] {
                    Some(m_blk) => !bit_test(&self.live_in_bits[m_blk], d_bit),
                    None => true,
                };
                if safe && !self.hint_candidates.contains(&c) {
                    self.hint_candidates.push(c);
                }
            }
        }
        let chosen = if let Some(&hint_c) = self.hint_candidates.first() {
            hint_c
        } else {
            find_lowest_free_color(&self.in_use, 0)?
        };
        self.val_color[d_bit] = Some(chosen);
        if chosen >= *self.max_reg_plus_one {
            *self.max_reg_plus_one = chosen + 1;
        }
        Ok(chosen)
    }

    fn color_block(&mut self, b_idx: usize, bb: BlockId) -> Result<(), RegAllocError> {
        let Some(block) = self.module.block(bb) else {
            return Ok(());
        };

        // 1. Pre-scan local last-use step indices (`1` = `block_start_stores`,
        //    `2..` = `entry_consts` + non-phi, non-suppressed `block.insts`).
        for &src_bit in &self.block_start_store_srcs[b_idx] {
            self.record_local_use(src_bit, 1);
        }
        let mut step: u32 = 2;
        if b_idx == 0 {
            step += self.entry_consts.len() as u32;
        }
        for &iid in &block.insts {
            if self.suppression.insts.contains(&iid) {
                continue;
            }
            let Some(inst) = self.module.inst(iid) else {
                continue;
            };
            if inst.op.is_phi() {
                continue;
            }
            let cur_step = step;
            step += 1;
            if let Some(inst_ref) = self.module.inst(iid) {
                inst_ref.op.for_each_operand(|v| {
                    if self.suppression.values.contains(&v) {
                        if let Some(ValueDef::Inst(def_iid)) =
                            self.module.value(v).map(|val| val.def)
                            && let Some(Op::UnaryOp {
                                op: UnOp::JumpEqz | UnOp::JumpNez,
                                operand,
                            }) = self.module.inst(def_iid).map(|i| &i.op)
                            && !self.suppression.values.contains(operand)
                            && let Some(&u_bit) = self.val_to_bit.get(operand)
                        {
                            self.record_local_use(u_bit, cur_step);
                        }
                    } else if let Some(&u_bit) = self.val_to_bit.get(&v) {
                        self.record_local_use(u_bit, cur_step);
                    }
                });
            }
        }

        // 2. Seed `in_use` with colors of `live_in_bits[b_idx]`.
        for (w_idx, &word) in self.live_in_bits[b_idx].iter().enumerate() {
            let mut w = word;
            while w != 0 {
                let tz = w.trailing_zeros() as usize;
                let bit = (w_idx << 6) + tz;
                w &= w - 1;
                if let Some(c) = self.val_color[bit] {
                    self.mark_active_val(bit, c);
                }
            }
        }

        // 3. Step 0: Simultaneous entry definitions (`params` at entry,
        //    `ExceptionParam`s at handlers, and `Op::Phi`s).
        self.step_zero_bits.clear();
        if b_idx == 0 {
            for &pval in self.func_params {
                if let Some(&p_bit) = self.val_to_bit.get(&pval) {
                    let c = self.pick_color_for(p_bit)?;
                    self.mark_active_val(p_bit, c);
                    self.step_zero_bits.push(p_bit);
                }
            }
        }
        for &exc in &self.handler_exc_by_block[b_idx] {
            if let Some(&e_bit) = self.val_to_bit.get(&exc) {
                let c = self.pick_color_for(e_bit)?;
                self.mark_active_val(e_bit, c);
                self.step_zero_bits.push(e_bit);
            }
        }
        for &iid in &block.insts {
            let Some(inst) = self.module.inst(iid) else {
                break;
            };
            if !inst.op.is_phi() {
                break;
            }
            let Some(res) = inst.result else {
                continue;
            };
            let Some(&r_bit) = self.val_to_bit.get(&res) else {
                continue;
            };
            if self.used.contains(&res) {
                let c = self.pick_color_for(r_bit)?;
                self.mark_active_val(r_bit, c);
                self.step_zero_bits.push(r_bit);
            } else {
                let _ = self.pick_color_for(r_bit)?;
            }
        }
        for idx in 0..self.step_zero_bits.len() {
            let bit = self.step_zero_bits[idx];
            if !self.stays_live_past(b_idx, bit, 0) {
                self.release_active_val(bit);
            }
        }

        // 4. Step 1: Release `block_start_stores` sources whose last use is step 1.
        for &src_bit in &self.block_start_store_srcs[b_idx] {
            if self.last_use_in_block[src_bit] == 1
                && !bit_test(&self.live_out_bits[b_idx], src_bit)
            {
                self.release_active_val(src_bit);
            }
        }

        // 5. Step 2..: Materialize `entry_consts` (if entry), then walk instructions.
        let mut cur_step: u32 = 2;
        if b_idx == 0 {
            for &cval in self.entry_consts {
                let s = cur_step;
                cur_step += 1;
                if let Some(&c_bit) = self.val_to_bit.get(&cval) {
                    let c = self.pick_color_for(c_bit)?;
                    if self.stays_live_past(b_idx, c_bit, s) {
                        self.mark_active_val(c_bit, c);
                    }
                }
            }
        }

        for &iid in &block.insts {
            if self.suppression.insts.contains(&iid) {
                continue;
            }
            let Some(inst) = self.module.inst(iid) else {
                continue;
            };
            if inst.op.is_phi() {
                continue;
            }
            let s = cur_step;
            cur_step += 1;

            // Release dead effective operands BEFORE coloring `inst.result`
            // so `result` can reuse a dying operand's register!
            inst.op.for_each_operand(|v| {
                let eff_opt = if self.suppression.values.contains(&v) {
                    if let Some(ValueDef::Inst(def_iid)) = self.module.value(v).map(|val| val.def)
                        && let Some(Op::UnaryOp {
                            op: UnOp::JumpEqz | UnOp::JumpNez,
                            operand,
                        }) = self.module.inst(def_iid).map(|i| &i.op)
                        && !self.suppression.values.contains(operand)
                    {
                        Some(*operand)
                    } else {
                        None
                    }
                } else {
                    Some(v)
                };
                if let Some(eff_v) = eff_opt
                    && let Some(&u_bit) = self.val_to_bit.get(&eff_v)
                    && self.last_use_in_block[u_bit] == s
                    && !bit_test(&self.live_out_bits[b_idx], u_bit)
                {
                    self.release_active_val(u_bit);
                }
            });

            if let Some(res) = inst.result
                && let Some(&d_bit) = self.val_to_bit.get(&res)
            {
                let c = self.pick_color_for(d_bit)?;
                if self.used.contains(&res) && self.stays_live_past(b_idx, d_bit, s) {
                    self.mark_active_val(d_bit, c);
                }
            }
        }

        // Clean per-block sparse scratch arrays in `O(|touched|)`.
        for bit in self.touched_vals.drain(..) {
            self.last_use_in_block[bit] = 0;
            self.is_active_val[bit] = false;
        }
        Ok(())
    }
}

#[inline]
fn find_lowest_free_color(in_use: &[u64], start_word: usize) -> Result<u16, RegAllocError> {
    for (offset, &word) in in_use[start_word..].iter().enumerate() {
        if word != u64::MAX {
            let tz = (!word).trailing_zeros() as usize;
            let color = ((start_word + offset) << 6) + tz;
            if color >= usize::from(TEMP_REG_BASE) {
                return Err(RegAllocError::RegisterOverflow);
            }
            return Ok(color as u16);
        }
    }
    Err(RegAllocError::RegisterOverflow)
}

/// Largest operand count among the function's range-form instructions (`S2` / `N4`).
fn range_call_window_size(module: &Module, rpo: &[BlockId]) -> usize {
    use abcd_ir::CallKind;
    let mut window = 0usize;
    for &bb in rpo {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &inst_id in &block.insts {
            let Some(inst) = module.inst(inst_id) else {
                continue;
            };
            match &inst.op {
                Op::Call {
                    kind, this, args, ..
                } => {
                    let range_argc = match kind {
                        CallKind::Dynamic | CallKind::Direct if this.is_none() => {
                            (args.len() > 3).then_some(args.len())
                        }
                        CallKind::Dynamic | CallKind::Direct => {
                            (args.len() + 1 > 4).then_some(args.len() + 1)
                        }
                        CallKind::Super | CallKind::SuperArrow => Some(args.len()),
                        CallKind::New => Some(args.len() + 1),
                        CallKind::Apply
                        | CallKind::SuperSpread
                        | CallKind::SuperForwardAllArgs
                        | CallKind::NewSpread
                        | CallKind::ClassInit => None,
                    };
                    if let Some(argc) = range_argc {
                        window = window.max(argc);
                    }
                }
                Op::CreateObjectWithExcludedKeys { keys, .. } => {
                    window = window.max(keys.len().max(1));
                }
                _ => {}
            }
        }
    }
    window
}

#[inline]
fn bit_set(bits: &mut [u64], idx: usize) {
    bits[idx >> 6] |= 1u64 << (idx & 63);
}

#[inline]
fn bit_clear(bits: &mut [u64], idx: usize) {
    bits[idx >> 6] &= !(1u64 << (idx & 63));
}

#[inline]
fn bit_test(bits: &[u64], idx: usize) -> bool {
    (bits[idx >> 6] & (1u64 << (idx & 63))) != 0
}

/// Boissinot out-of-SSA parallel copy collection along `EdgeKind::Normal` edges.
///
/// `Exceptional` handler-phi edges are lowered via `handler_phi_stores` (`N21`);
/// `Normal` incoming edges into BOTH normal blocks and mixed `Normal + Exceptional`
/// catch handlers emit standard parallel copies here!
fn boissinot_destruction(
    module: &Module,
    rpo: &[BlockId],
    allocation: &HashMap<ValueId, RegSlot>,
    used: &HashSet<ValueId>,
    is_exc_phi_entry: impl Fn(BlockId, usize, EdgeKind) -> bool,
) -> HashMap<(BlockId, BlockId), Vec<(ValueId, ValueId)>> {
    let mut copies: HashMap<(BlockId, BlockId), Vec<(ValueId, ValueId)>> = HashMap::new();

    for (b_idx, &bb) in rpo.iter().enumerate() {
        for_each_phi(module, bb, |inst_node| {
            let Some(dst) = inst_node.result else {
                return;
            };
            if !used.contains(&dst) {
                return;
            }
            let dst_color = allocation.get(&dst);

            if let Op::Phi { entries } = &inst_node.op {
                for &(edge, src) in entries {
                    if is_exc_phi_entry(edge.from, b_idx, edge.kind) {
                        continue;
                    }
                    let src_color = allocation.get(&src);
                    if src_color != dst_color {
                        copies.entry((edge.from, bb)).or_default().push((src, dst));
                    }
                }
            }
        });
    }

    copies
}

/// Linear-time debug invariant verifier: checks that every value has a valid
/// non-reserved register home and NO two simultaneously live `used` values
/// share a register at any program point in any block.
#[cfg(debug_assertions)]
#[expect(
    clippy::too_many_arguments,
    reason = "debug verifier inspects precomputed regalloc tables without wrapper structs"
)]
fn debug_verify_allocation(
    module: &Module,
    suppression: &Suppression,
    rpo: &[BlockId],
    entry_consts: &[ValueId],
    func_params: &[ValueId],
    handler_exc_by_block: &[Vec<ValueId>],
    block_start_store_srcs: &[Vec<usize>],
    used: &HashSet<ValueId>,
    val_to_bit: &HashMap<ValueId, usize>,
    live_in_bits: &[Vec<u64>],
    live_out_bits: &[Vec<u64>],
    val_color: &[Option<u16>],
    reserved_start: u16,
    reserved_len: u16,
) {
    let num_vals = val_color.len();
    let val_words = num_vals.div_ceil(64).max(1);
    let mut is_used_bit = vec![false; num_vals];
    for (&v, &bit) in val_to_bit {
        if used.contains(&v) {
            is_used_bit[bit] = true;
        }
    }
    for (bit, &c_opt) in val_color.iter().enumerate() {
        let c = c_opt.expect("every value in all_values must receive a color");
        assert!(c < TEMP_REG_BASE, "allocated color {c} >= TEMP_REG_BASE");
        assert!(
            !(c >= reserved_start && c < reserved_start + reserved_len),
            "value bit {bit} assigned to reserved scratch/window register {c}"
        );
    }

    let mut color_owner: Vec<Option<usize>> = vec![None; usize::from(TEMP_REG_BASE)];
    let mut active_colors: Vec<usize> = Vec::with_capacity(64);
    let mut live = vec![0u64; val_words];

    let insert_live = |bit: usize,
                       live: &mut [u64],
                       color_owner: &mut [Option<usize>],
                       active_colors: &mut Vec<usize>,
                       ctx: &str| {
        if !is_used_bit[bit] || bit_test(live, bit) {
            return;
        }
        bit_set(live, bit);
        let c = usize::from(val_color[bit].expect("colored"));
        if let Some(other_bit) = color_owner[c]
            && other_bit != bit
        {
            panic!(
                "regalloc live-range collision ({ctx}): value bits {bit} and {other_bit} \
                 both occupy v{c} simultaneously"
            );
        }
        color_owner[c] = Some(bit);
        active_colors.push(c);
    };

    let remove_def =
        |bit: usize, live: &mut [u64], color_owner: &mut [Option<usize>], ctx: &str| {
            if !is_used_bit[bit] {
                return;
            }
            let c = usize::from(val_color[bit].expect("colored"));
            if let Some(other_bit) = color_owner[c]
                && other_bit != bit
            {
                panic!(
                    "regalloc def-clobber collision ({ctx}): defining bit {bit} in v{c} \
                 clobbers live value bit {other_bit}"
                );
            }
            if bit_test(live, bit) {
                bit_clear(live, bit);
                color_owner[c] = None;
            }
        };

    for (b_idx, &bb) in rpo.iter().enumerate() {
        let Some(block) = module.block(bb) else {
            continue;
        };
        live.fill(0);
        for &c in &active_colors {
            color_owner[c] = None;
        }
        active_colors.clear();

        for (w_idx, &word) in live_out_bits[b_idx].iter().enumerate() {
            let mut w = word;
            while w != 0 {
                let tz = w.trailing_zeros() as usize;
                let bit = (w_idx << 6) + tz;
                w &= w - 1;
                insert_live(
                    bit,
                    &mut live,
                    &mut color_owner,
                    &mut active_colors,
                    "live_out",
                );
            }
        }

        for &iid in block.insts.iter().rev() {
            if suppression.insts.contains(&iid) {
                continue;
            }
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            if inst.op.is_phi() {
                continue;
            }
            if let Some(res) = inst.result
                && let Some(&d_bit) = val_to_bit.get(&res)
            {
                remove_def(d_bit, &mut live, &mut color_owner, "inst_def");
            }
            for_each_effective_use(module, suppression, iid, |u| {
                if let Some(&u_bit) = val_to_bit.get(&u) {
                    insert_live(
                        u_bit,
                        &mut live,
                        &mut color_owner,
                        &mut active_colors,
                        "inst_use",
                    );
                }
            });
        }

        if b_idx == 0 {
            for &cval in entry_consts.iter().rev() {
                if let Some(&c_bit) = val_to_bit.get(&cval) {
                    remove_def(c_bit, &mut live, &mut color_owner, "entry_const");
                }
            }
        }

        for &src_bit in &block_start_store_srcs[b_idx] {
            insert_live(
                src_bit,
                &mut live,
                &mut color_owner,
                &mut active_colors,
                "block_start_store",
            );
        }

        // Verify simultaneous Step 0 definitions (`Phi`s, `handler_exc`, `params`)
        // neither collide with each other nor clobber `live_in_bits[b_idx]`.
        for &iid in &block.insts {
            let Some(inst) = module.inst(iid) else { break };
            if !inst.op.is_phi() {
                break;
            }
            if let Some(res) = inst.result
                && let Some(&r_bit) = val_to_bit.get(&res)
            {
                remove_def(r_bit, &mut live, &mut color_owner, "phi_def");
            }
        }
        for &exc in &handler_exc_by_block[b_idx] {
            if let Some(&e_bit) = val_to_bit.get(&exc) {
                remove_def(e_bit, &mut live, &mut color_owner, "exc_param");
            }
        }
        if b_idx == 0 {
            for &pval in func_params {
                if let Some(&p_bit) = val_to_bit.get(&pval) {
                    remove_def(p_bit, &mut live, &mut color_owner, "func_param");
                }
            }
        }
        let _ = &live_in_bits[b_idx];
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower_function;
    use abcd_ir::{
        BinOp, Block, Catch, ClassData, ClassId, Const, Edge, FunctionData, FunctionKind, Inst,
        TryRegion, Ty, Value,
    };
    use abcd_isa::Bytecode;

    fn mk_module_and_func() -> (Module, FuncId) {
        let mut m = Module::new();
        let desc = m.sym.intern("Ltest;");
        m.classes.push(ClassData::new(desc, desc));
        let fname = m.sym.intern("f");
        let fid = FuncId::new(0);
        m.functions.push(FunctionData::new(
            ClassId::new(0),
            fname,
            FunctionKind::Function,
        ));
        (m, fid)
    }

    fn push_block(m: &mut Module, fid: FuncId) -> BlockId {
        let bb = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.functions[fid.index()].blocks.push(bb);
        bb
    }

    fn emit_val(m: &mut Module, bb: BlockId, op: Op) -> ValueId {
        let vid = ValueId::new(m.values.len() as u32);
        let iid = InstId::new(m.insts.len() as u32);
        m.values.push(Value {
            def: ValueDef::Inst(iid),
            ty: Ty::Any,
        });
        m.insts.push(Inst {
            op,
            result: Some(vid),
            block: bb,
            loc: None,
        });
        m.blocks[bb.index()].insts.push(iid);
        vid
    }

    fn emit_void(m: &mut Module, bb: BlockId, op: Op) {
        let iid = InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op,
            result: None,
            block: bb,
            loc: None,
        });
        m.blocks[bb.index()].insts.push(iid);
    }

    /// Mixed `Normal + Exceptional` catch-handler `Phi` regression:
    /// When a protected block `try_bb` has BOTH an `EdgeKind::Exceptional` edge
    /// to `handler` (`v_exc = 10` before throwing op, then `v_norm = 20` on the
    /// normal path) AND an `EdgeKind::Normal` edge (`CondBranch` -> `handler` or `exit`),
    /// the `Normal` edge MUST copy `v_norm` on the `Normal -> handler` trampoline
    /// without overwriting `slot(p)` inside `try_bb`, while the `Exceptional` edge
    /// has ZERO copies and observes `v_exc = 10` if `try_bb` throws!
    #[test]
    fn mixed_normal_and_exceptional_handler_phi_preserves_both_paths() {
        let (mut m, fid) = mk_module_and_func();
        let entry = push_block(&mut m, fid);
        let exit = push_block(&mut m, fid);
        let handler = push_block(&mut m, fid);

        let p_cond = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Param(0),
            ty: Ty::Any,
        });
        m.functions[0].params.push(p_cond);

        let exc_val = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::ExceptionParam(handler),
            ty: Ty::Any,
        });

        let c10 = m.consts.intern(Const::number(10.0));
        let c20 = m.consts.intern(Const::number(20.0));
        let v_exc = emit_val(&mut m, entry, Op::LoadConst(c10));
        let v_norm = emit_val(&mut m, entry, Op::LoadConst(c20));
        // Potentially throwing call/add between v_exc/v_norm and normal branch!
        let _sum = emit_val(
            &mut m,
            entry,
            Op::BinaryOp {
                op: BinOp::Add,
                left: v_exc,
                right: v_norm,
            },
        );
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond: p_cond,
                true_dest: handler,
                false_dest: exit,
            },
        );

        m.blocks[exit.index()].preds.push(Edge {
            from: entry,
            kind: EdgeKind::Normal,
        });
        emit_void(&mut m, exit, Op::Return { value: Some(v_exc) });

        m.blocks[handler.index()].preds.push(Edge {
            from: entry,
            kind: EdgeKind::Exceptional,
        });
        m.blocks[handler.index()].preds.push(Edge {
            from: entry,
            kind: EdgeKind::Normal,
        });
        let phi = emit_val(
            &mut m,
            handler,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: entry,
                            kind: EdgeKind::Exceptional,
                        },
                        v_exc,
                    ),
                    (
                        Edge {
                            from: entry,
                            kind: EdgeKind::Normal,
                        },
                        v_norm,
                    ),
                ],
            },
        );
        let res = emit_val(
            &mut m,
            handler,
            Op::BinaryOp {
                op: BinOp::Add,
                left: phi,
                right: exc_val,
            },
        );
        emit_void(&mut m, handler, Op::Return { value: Some(res) });

        m.functions[0].try_regions.push(TryRegion {
            protected: vec![entry],
            catches: vec![Catch {
                handler,
                exception: exc_val,
                type_class: None,
            }],
        });

        let sup = crate::fusion::analyze(&m, &m.functions[0].blocks);
        let alloc = allocate(&m, fid, &sup).expect("mixed handler phi must allocate");

        // `Exceptional` input `v_exc` writes through via `handler_phi_stores`;
        // `Normal` input `v_norm` does NOT appear in `handler_phi_stores`, and
        // instead lowers via `phi_copies` on `(entry, handler)`!
        assert_eq!(alloc.handler_phi_stores, vec![(entry, v_exc, phi)]);
        assert_eq!(
            alloc.phi_copies.get(&(entry, handler)).cloned(),
            Some(vec![(v_norm, phi)])
        );

        let lowered = lower_function(&m, fid).expect("mixed handler phi must lower cleanly");
        assert_eq!(lowered.try_blocks.len(), 1);
        let tb = &lowered.try_blocks[0];
        let RegSlot::Reg(phi_slot) = alloc.allocation[&phi];
        let RegSlot::Reg(v_norm_slot) = alloc.allocation[&v_norm];
        assert_ne!(phi_slot, v_norm_slot);

        // Verify that NO instruction inside the protected `try` span writes `v_norm` into `phi_slot`!
        let try_slice = &lowered.bytecodes[tb.start as usize..(tb.start + tb.len) as usize];
        assert!(
            !try_slice.iter().any(
                |bc| matches!(bc, Bytecode::Mov(d, s) if d.0 == phi_slot && s.0 == v_norm_slot)
            ),
            "protected try body must never clobber handler phi slot with normal-edge value: {try_slice:?}"
        );
    }

    /// `ValueDef::ExceptionParam` liveness kill: an exception parameter is
    /// defined at handler entry and must NOT inflate register pressure inside
    /// the protected `try` block!
    #[test]
    fn exception_param_killed_at_handler_entry_not_live_in_try() {
        let (mut m, fid) = mk_module_and_func();
        let entry = push_block(&mut m, fid);
        let handler = push_block(&mut m, fid);

        let exc = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::ExceptionParam(handler),
            ty: Ty::Any,
        });

        let c1 = m.consts.intern(Const::number(1.0));
        let v1 = emit_val(&mut m, entry, Op::LoadConst(c1));
        emit_void(&mut m, entry, Op::Return { value: Some(v1) });

        m.blocks[handler.index()].preds.push(Edge {
            from: entry,
            kind: EdgeKind::Exceptional,
        });
        emit_void(&mut m, handler, Op::Return { value: Some(exc) });

        m.functions[0].try_regions.push(TryRegion {
            protected: vec![entry],
            catches: vec![Catch {
                handler,
                exception: exc,
                type_class: None,
            }],
        });

        let sup = crate::fusion::analyze(&m, &m.functions[0].blocks);
        let alloc = allocate(&m, fid, &sup).expect("allocation must succeed");
        // Since `exc` is killed at handler entry (never live across `entry`),
        // `v1` and `exc` have disjoint live ranges and share `v0` (`num_regs == 1`)!
        assert_eq!(alloc.allocation[&v1], RegSlot::Reg(0));
        assert_eq!(alloc.allocation[&exc], RegSlot::Reg(0));
        assert_eq!(alloc.num_regs, 1);
    }

    /// Biased coalescing eliminates `Mov` and normal `Phi` copies when live
    /// ranges do not overlap.
    #[test]
    fn biased_coalescing_coalesces_mov_and_diamond_phi() {
        let (mut m, fid) = mk_module_and_func();
        let entry = push_block(&mut m, fid);
        let left = push_block(&mut m, fid);
        let right = push_block(&mut m, fid);
        let join = push_block(&mut m, fid);

        let c_true = m.consts.intern(Const::Bool(true));
        let cond = emit_val(&mut m, entry, Op::LoadConst(c_true));
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond,
                true_dest: left,
                false_dest: right,
            },
        );

        m.blocks[left.index()].preds.push(Edge {
            from: entry,
            kind: EdgeKind::Normal,
        });
        let c1 = m.consts.intern(Const::number(1.0));
        let a0 = emit_val(&mut m, left, Op::LoadConst(c1));
        let a1 = emit_val(&mut m, left, Op::Mov { src: a0 });
        emit_void(&mut m, left, Op::Branch { dest: join });

        m.blocks[right.index()].preds.push(Edge {
            from: entry,
            kind: EdgeKind::Normal,
        });
        let c2 = m.consts.intern(Const::number(2.0));
        let b0 = emit_val(&mut m, right, Op::LoadConst(c2));
        emit_void(&mut m, right, Op::Branch { dest: join });

        m.blocks[join.index()].preds.push(Edge {
            from: left,
            kind: EdgeKind::Normal,
        });
        m.blocks[join.index()].preds.push(Edge {
            from: right,
            kind: EdgeKind::Normal,
        });
        let phi = emit_val(
            &mut m,
            join,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: left,
                            kind: EdgeKind::Normal,
                        },
                        a1,
                    ),
                    (
                        Edge {
                            from: right,
                            kind: EdgeKind::Normal,
                        },
                        b0,
                    ),
                ],
            },
        );
        emit_void(&mut m, join, Op::Return { value: Some(phi) });

        let sup = crate::fusion::analyze(&m, &m.functions[0].blocks);
        let alloc = allocate(&m, fid, &sup).expect("allocation must succeed");
        assert_eq!(alloc.allocation[&a0], alloc.allocation[&a1]);
        assert_eq!(alloc.allocation[&a1], alloc.allocation[&phi]);
        assert_eq!(alloc.allocation[&b0], alloc.allocation[&phi]);
        assert!(alloc.phi_copies.is_empty(), "all phi inputs coalesced");
    }

    /// Zero-recursion `256 KiB`-stack regression test on a deep 2,000-block
    /// dominance chain with carried `Phi`s!
    #[test]
    fn regalloc_2000_block_deep_cfg_succeeds_on_256kib_stack() {
        let handle = std::thread::Builder::new()
            .name("regalloc-256k".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let (mut m, fid) = mk_module_and_func();
                let count = 2_000usize;
                let mut blocks = Vec::with_capacity(count);
                for _ in 0..count {
                    blocks.push(push_block(&mut m, fid));
                }
                let c1 = m.consts.intern(Const::number(1.0));
                let mut prev_val = emit_val(&mut m, blocks[0], Op::LoadConst(c1));
                emit_void(&mut m, blocks[0], Op::Branch { dest: blocks[1] });

                for i in 1..count {
                    let bb = blocks[i];
                    let pred = blocks[i - 1];
                    m.blocks[bb.index()].preds.push(Edge {
                        from: pred,
                        kind: EdgeKind::Normal,
                    });
                    let p = emit_val(
                        &mut m,
                        bb,
                        Op::Phi {
                            entries: vec![(
                                Edge {
                                    from: pred,
                                    kind: EdgeKind::Normal,
                                },
                                prev_val,
                            )],
                        },
                    );
                    let one = emit_val(&mut m, bb, Op::LoadConst(c1));
                    let sum = emit_val(
                        &mut m,
                        bb,
                        Op::BinaryOp {
                            op: BinOp::Add,
                            left: p,
                            right: one,
                        },
                    );
                    prev_val = sum;
                    if i + 1 < count {
                        emit_void(
                            &mut m,
                            bb,
                            Op::Branch {
                                dest: blocks[i + 1],
                            },
                        );
                    } else {
                        emit_void(&mut m, bb, Op::Return { value: Some(sum) });
                    }
                }

                let sup = crate::fusion::analyze(&m, &m.functions[0].blocks);
                let alloc = allocate(&m, fid, &sup).expect("2,000-block allocation must succeed");
                // 6,000 SSA values >= 256 reserves `LOW_SCRATCH_COUNT` (5) low scratches
                // plus O(1) registers (2 SSA slots + 1 copy_temp at most) across 2,000 blocks.
                assert!(
                    alloc.num_regs <= LOW_SCRATCH_COUNT + 4,
                    "linear 2,000-block chain must use O(1) registers, got {}",
                    alloc.num_regs
                );
            })
            .expect("spawn 256 KiB thread");
        handle
            .join()
            .expect("256 KiB regalloc thread must not overflow stack");
    }
}
