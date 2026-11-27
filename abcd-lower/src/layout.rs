//! Block layout and jump target resolution (`design/ir.md` §5,
//! `design/decisions.md` `ADR-04`).
//!
//! Arranges basic blocks in reverse post-order, flattens them into a linear
//! bytecode sequence, and resolves Block references in jump instructions
//! to concrete instruction indices (Labels).
//!
//! Phi copies execute ONLY on their own CFG edge: copies for an
//! unconditional predecessor are inserted before its terminator; for a
//! `CondBranch` predecessor a trampoline per successor edge (copy sequence +
//! `Jmp succ`) is appended after all regular blocks and the corresponding
//! branch target is rewritten to it. Trampolines belong to no IR block and
//! sort after every real block offset, so `reconstruct_try_blocks` never
//! extends a try/handler range over them.
//!
//! Exception edges (try block → catch handler) NEVER carry copies: the VM
//! dispatches directly to the handler's flat offset, so no copy code could
//! run there (trampolines cannot serve them). Regalloc eliminates them via
//! pinned write-through stores (N21); any residual handler-edge copy set
//! is inconsistent input and a hard [`LowerError::HandlerEdgeCopies`], and
//! copies keyed to a block that is neither a terminator successor nor a
//! catch handler of the predecessor are [`LowerError::InconsistentEdgeCopies`].
//! The exception-edge set comes from the function's structured
//! [`TryRegion`](abcd_ir::TryRegion)s (mirrored by
//! [`EdgeKind::Exceptional`](abcd_ir::EdgeKind) block predecessors).

use std::collections::{BTreeMap, HashMap, HashSet};

use abcd_ir::cfg::block_succs;
use abcd_ir::{BlockId, ClassId, FuncId, InstId, Module, Op};
use abcd_isa::{Bytecode, EntityKind, Label};

use crate::LowerError;
use crate::copy_resolve::{emit_copy, resolve_slot_copies};
use crate::isel::{EntityTrace, IselResult};
use crate::regalloc::{RegAlloc, RegSlot};

/// Format-independent catch handler range on [`LayoutResult`] (`#50` `R3-D2`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LoweredCatchBlock {
    /// Caught exception class in [`Module::classes`], or `None` for catch-all.
    pub type_class: Option<ClassId>,
    /// Instruction index where the catch handler starts.
    pub handler: u32,
    /// Number of instructions in the catch handler.
    pub len: u32,
}

/// Format-independent try range on [`LayoutResult`] (`#50` `R3-D2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoweredTryBlock {
    /// Instruction index where the try region starts.
    pub start: u32,
    /// Number of instructions covered by the try region.
    pub len: u32,
    /// Catch handlers in dispatch priority order.
    pub catches: Vec<LoweredCatchBlock>,
}

/// Result of layout: a flat bytecode sequence + try blocks + frame size.
#[derive(Debug)]
pub struct LayoutResult {
    /// The flattened bytecodes.
    pub bytecodes: Vec<Bytecode>,
    /// The reconstructed IR-typed try blocks.
    pub try_blocks: Vec<LoweredTryBlock>,
    /// Post-layout instruction index per IR [`InstId`] (`#57` `R3-H8`).
    pub inst_pcs: HashMap<InstId, u32>,
    /// Final register count for the function frame, including the reserved
    /// phi-copy temporary register (if any).
    pub num_regs: u16,
    /// Entity operand traceability inherited from instruction selection,
    /// keyed by (entity kind, raw operand value).
    pub entity_traces: HashMap<(EntityKind, u32), EntityTrace>,
    /// Total IC-slot consumption of the flattened sequence (after the
    /// N71 rearrangement, when it fired).
    pub ic_size: u32,
}

/// Lay out blocks and resolve jump targets.
pub fn layout(
    module: &Module,
    func_id: FuncId,
    isel: &IselResult,
    alloc: &RegAlloc,
    rpo: &[BlockId],
) -> Result<LayoutResult, LowerError> {
    // Step 1: Resolve each edge's phi copies at SLOT level. Coalescing lets
    // distinct values share a slot, so the value-level list must be re-mapped
    // and re-ordered here, at the emission point.
    //
    // BTreeMap (N20): the legacy/unconditional placement loops below iterate
    // this map, and that iteration order is byte-observable in the flattened
    // output — a HashMap would permute copy-sequence order (and thereby the
    // encoded bytes) between runs. Block/edge keys are arena indices, so the
    // sorted order is stable and total.
    let mut edge_codes: BTreeMap<(BlockId, BlockId), Vec<Bytecode>> = BTreeMap::new();
    for (&edge, copies) in &alloc.phi_copies {
        if copies.is_empty() {
            continue;
        }
        // Values without an allocation are skipped, preserving the previous
        // (both endpoints known) filtering behavior.
        let slot_pairs: Vec<(RegSlot, RegSlot)> = copies
            .iter()
            .filter_map(|&(src, dst)| {
                let s = alloc.allocation.get(&src).copied()?;
                let d = alloc.allocation.get(&dst).copied()?;
                Some((s, d))
            })
            .collect();
        let resolved = resolve_slot_copies(&slot_pairs, alloc.copy_temp)
            .map_err(|_| LowerError::MissingCopyTemp(func_id))?;
        // Every resolved copy is Reg→Reg (B4: there is no accumulator
        // coloring, so acc never appears in copy slots): the auto-widening
        // `Mov` encodes at any register height without scratch routing.
        let codes: Vec<Bytecode> = resolved.into_iter().map(|(s, d)| emit_copy(s, d)).collect();
        if !codes.is_empty() {
            edge_codes.insert(edge, codes);
        }
    }

    // N21: validate every edge that carries copies BEFORE placement.
    //
    // - Exception edges (try block → catch handler) must never carry
    //   copies: the VM dispatches directly to the handler's flat offset, so
    //   no copy code can run there. Regalloc's write-through stores make
    //   them unnecessary; a residual copy set is inconsistent input and
    //   fails loudly.
    // - Any other edge whose successor is not a terminator successor of the
    //   predecessor is inconsistent input (verification enforces
    //   preds↔terminator agreement with a try-region exemption); it
    //   previously fell into the legacy in-block placement that ran the
    //   copies on the predecessor's NORMAL path (the N21 wart — iterator-close
    //   `func_main_0` clobbered the iterator object in v0 before a `jnez`).
    let mut exception_edges: HashSet<(BlockId, BlockId)> = HashSet::new();
    let func = module
        .func(func_id)
        .ok_or(LowerError::EmptyFunction(func_id))?;
    for region in &func.try_regions {
        for &try_block in &region.protected {
            for catch in &region.catches {
                exception_edges.insert((try_block, catch.handler));
            }
        }
    }
    for &(pred, succ) in edge_codes.keys() {
        if !block_succs(module, pred).contains(&succ) {
            if exception_edges.contains(&(pred, succ)) {
                return Err(LowerError::HandlerEdgeCopies {
                    func: func_id,
                    pred,
                    handler: succ,
                });
            }
            return Err(LowerError::InconsistentEdgeCopies {
                func: func_id,
                pred,
                succ,
            });
        }
    }

    // Step 2: Place copies on their edges, invert boolean CondBranch when
    // `true_dest` falls through (`R3-X1`), and elide fallthrough `Jmp`s (`R3-A7`).
    let mut block_codes: HashMap<BlockId, Vec<Bytecode>> =
        HashMap::with_capacity(isel.block_codes.len());
    for (bb, codes) in &isel.block_codes {
        block_codes.insert(*bb, codes.clone());
    }
    let mut copy_shift: HashMap<BlockId, (usize, usize)> = HashMap::new();

    // Synthetic trampoline blocks (copy sequence + `Jmp succ`), appended
    // after all real blocks. Keys count down from `u32::MAX - 1`.
    let mut trampolines: Vec<(BlockId, Vec<Bytecode>)> = Vec::new();

    for (i, &bb) in rpo.iter().enumerate() {
        let next_bb = rpo.get(i + 1).copied();
        let Some(block_data) = module.block(bb) else {
            continue;
        };
        let term = block_data
            .insts
            .last()
            .and_then(|&inst| module.inst(inst).map(|n| &n.op));

        let can_fallthrough_to = |dest: BlockId| -> bool {
            next_bb == Some(dest) && isel.handler_prologue_len.get(&dest).copied().unwrap_or(0) == 0
        };

        if let Some(Op::CondBranch {
            true_dest,
            false_dest,
            ..
        }) = term
        {
            let (true_dest, false_dest) = (*true_dest, *false_dest);
            let true_copies = edge_codes.get(&(bb, true_dest));
            let false_copies = edge_codes.get(&(bb, false_dest));

            let Some(codes) = block_codes.get_mut(&bb) else {
                continue;
            };

            // R3-X1 Case 3/4: When `acc` is guaranteed boolean (`bool_cond_blocks`)
            // and `true_dest` immediately follows in RPO with no edge copies or
            // handler prologue, invert `Jnez` -> `Jeqz` targeting `false_target`
            // and fall straight through into `true_dest` with zero trailing `Jmp`.
            if isel.bool_cond_blocks.contains(&bb)
                && true_copies.is_none()
                && true_dest != false_dest
                && can_fallthrough_to(true_dest)
            {
                let false_target = match false_copies {
                    Some(copies) => add_trampoline(&mut trampolines, copies, false_dest),
                    None => false_dest,
                };
                if let Some(last) = codes.last_mut() {
                    invert_bool_branch(last, false_target);
                }
                continue;
            }

            let true_target = match true_copies {
                Some(copies) => add_trampoline(&mut trampolines, copies, true_dest),
                None => true_dest,
            };
            let false_target =
                false_copies.map(|copies| add_trampoline(&mut trampolines, copies, false_dest));

            if let Some(last) = codes.last_mut() {
                rewrite_branch_target(last, true_target);
            }
            if let Some(tramp) = false_target {
                codes.push(Bytecode::Jmp(Label(tramp.0)));
            } else if !can_fallthrough_to(false_dest) {
                codes.push(Bytecode::Jmp(Label(false_dest.0)));
            }
        } else {
            // R3-A3: Query outgoing copies of `bb` in O(log E + out_degree) via
            // BTreeMap::range instead of rescanning all edges per block.
            let mut copy_codes: Vec<Bytecode> = Vec::new();
            for (_, codes) in edge_codes.range((bb, BlockId::new(0))..=(bb, BlockId::new(u32::MAX)))
            {
                copy_codes.extend(codes.iter().cloned());
            }
            let Some(codes) = block_codes.get_mut(&bb) else {
                continue;
            };
            if !copy_codes.is_empty() {
                let insert_pos = codes.len().saturating_sub(1);
                let copy_len = copy_codes.len();
                codes.splice(insert_pos..insert_pos, copy_codes);
                copy_shift.insert(bb, (insert_pos, copy_len));
            }
            // R3-A7: Elide trailing unconditional `Jmp(dest)` when `dest` is next
            // in RPO (with no handler prologue) and `bb` retains >= 1 bytecode (N49).
            if let Some(Op::Branch { dest }) = term
                && can_fallthrough_to(*dest)
                && codes.len() >= 2
                && matches!(codes.last(), Some(Bytecode::Jmp(l)) if l.0 == dest.0)
            {
                codes.pop();
            }
        }
    }

    // Step 3: Flatten blocks in RPO order, then trampolines, recording spans & inst PCs.
    let mut flat: Vec<Bytecode> = Vec::new();
    let mut block_spans: HashMap<BlockId, (usize, usize)> = HashMap::with_capacity(rpo.len());
    let mut jump_targets: HashMap<u32, usize> =
        HashMap::with_capacity(rpo.len() + trampolines.len() + isel.internal_labels.len());
    let mut inst_pcs: HashMap<InstId, u32> = HashMap::new();

    for &bb in rpo {
        let start = flat.len();
        if let Some(codes) = block_codes.get(&bb) {
            flat.extend(codes.iter().cloned());
        }
        let end = flat.len();
        if end == start {
            return Err(LowerError::ZeroExtentBlock {
                func: func_id,
                block: bb,
            });
        }
        block_spans.insert(bb, (start, end));
        let prol_len = isel.handler_prologue_len.get(&bb).copied().unwrap_or(0);
        jump_targets.insert(bb.0, (start + prol_len).min(end - 1));

        if let Some(local_pcs) = isel.block_inst_pcs.get(&bb) {
            let shift = copy_shift.get(&bb).copied();
            for &(iid, local_pc) in local_pcs {
                let adjusted = match shift {
                    Some((insert_pos, copy_len)) if local_pc >= insert_pos => local_pc + copy_len,
                    _ => local_pc,
                };
                inst_pcs.insert(iid, (start + adjusted) as u32);
            }
        }
    }
    for &(lbl, bb, local_pc) in &isel.internal_labels {
        if let Some(&(start, _)) = block_spans.get(&bb) {
            let adjusted = match copy_shift.get(&bb).copied() {
                Some((insert_pos, copy_len)) if local_pc >= insert_pos => local_pc + copy_len,
                _ => local_pc,
            };
            jump_targets.insert(lbl, start + adjusted);
        }
    }
    for (key, codes) in &trampolines {
        jump_targets.insert(key.0, flat.len());
        flat.extend(codes.iter().cloned());
    }

    // Step 4: Resolve jump targets; unresolved labels fail loudly (R3-M3).
    for bc in &mut flat {
        resolve_labels(func_id, bc, &jump_targets)?;
    }

    // Step 5: Reconstruct IR-typed try blocks in O(R * P log P) (R3-A3).
    let try_blocks = reconstruct_try_blocks(module, func_id, &block_spans);

    Ok(LayoutResult {
        bytecodes: flat,
        try_blocks,
        inst_pcs,
        num_regs: alloc.num_regs,
        entity_traces: isel.entity_traces.clone(),
        ic_size: isel.ic_size,
    })
}

/// Append a trampoline (copy sequence + `Jmp succ`) and return its synthetic
/// Block key.
fn add_trampoline(
    trampolines: &mut Vec<(BlockId, Vec<Bytecode>)>,
    copies: &[Bytecode],
    succ: BlockId,
) -> BlockId {
    let key = BlockId::new(u32::MAX - 1 - trampolines.len() as u32);
    let mut codes = copies.to_vec();
    codes.push(Bytecode::Jmp(Label(succ.0)));
    trampolines.push((key, codes));
    key
}

/// Rewrite the target of a (conditional or unconditional) branch bytecode.
/// No-op for non-branch bytecodes.
fn rewrite_branch_target(bc: &mut Bytecode, target: BlockId) {
    // Only `Jmp`, `Jeqz`, and `Jnez` are legal ArkCompiler branch instructions
    // (ruling 2026-10-04: the 24 fused compare-and-branch variants FATAL/NOP-skip
    // in vendor interpreters and are never emitted by `abcd-lower`).
    let label = match bc {
        Bytecode::Jmp(l) | Bytecode::Jeqz(l) | Bytecode::Jnez(l) => l,
        _ => return,
    };
    *label = Label(target.0);
}

/// Invert a boolean `Jnez` / `Jeqz` branch and point it at `target`.
fn invert_bool_branch(bc: &mut Bytecode, target: BlockId) {
    match bc {
        Bytecode::Jnez(_) => *bc = Bytecode::Jeqz(Label(target.0)),
        Bytecode::Jeqz(_) => *bc = Bytecode::Jnez(Label(target.0)),
        _ => rewrite_branch_target(bc, target),
    }
}

/// Reconstruct [`LoweredTryBlock`] entries from `func.try_regions` using exact
/// O(1) per-block `(start, end)` spans (`R3-A3`, `N43`).
fn reconstruct_try_blocks(
    module: &Module,
    func_id: FuncId,
    block_spans: &HashMap<BlockId, (usize, usize)>,
) -> Vec<LoweredTryBlock> {
    let mut try_blocks = Vec::new();
    let Some(func) = module.func(func_id) else {
        return try_blocks;
    };

    for region in &func.try_regions {
        if region.protected.is_empty() || region.catches.is_empty() {
            continue;
        }

        let mut extents: Vec<(usize, usize)> = region
            .protected
            .iter()
            .filter_map(|bb| block_spans.get(bb).copied())
            .collect();
        if extents.is_empty() {
            continue;
        }
        extents.sort_unstable();
        let mut runs: Vec<(usize, usize)> = Vec::with_capacity(extents.len());
        for (start, end) in extents {
            match runs.last_mut() {
                Some((_, cur_end)) if start <= *cur_end => *cur_end = (*cur_end).max(end),
                _ => runs.push((start, end)),
            }
        }

        let catches: Vec<LoweredCatchBlock> = region
            .catches
            .iter()
            .filter_map(|ch| {
                let &(handler_start, handler_end) = block_spans.get(&ch.handler)?;
                Some(LoweredCatchBlock {
                    type_class: ch.type_class,
                    handler: handler_start as u32,
                    len: (handler_end - handler_start) as u32,
                })
            })
            .collect();

        if catches.is_empty() {
            continue;
        }

        for (start, end) in runs {
            try_blocks.push(LoweredTryBlock {
                start: start as u32,
                len: (end - start) as u32,
                catches: catches.clone(),
            });
        }
    }

    try_blocks
}

/// Resolve Block/internal labels in jump instructions to flat instruction indices (`R3-M3`).
fn resolve_labels(
    func_id: FuncId,
    bc: &mut Bytecode,
    jump_targets: &HashMap<u32, usize>,
) -> Result<(), LowerError> {
    match bc {
        Bytecode::Jmp(label) | Bytecode::Jeqz(label) | Bytecode::Jnez(label) => {
            let target = label.0;
            let &off = jump_targets
                .get(&target)
                .ok_or(LowerError::UnresolvedLabel {
                    func: func_id,
                    target,
                })?;
            *label = Label(off as u32);
        }
        _ => {}
    }
    Ok(())
}
