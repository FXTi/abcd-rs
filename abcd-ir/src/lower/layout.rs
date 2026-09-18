//! Block layout and jump target resolution.
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

use std::collections::HashMap;

use abcd_file::TryBlock;
use abcd_isa::{Bytecode, Label};

use crate::entity::{Block, FuncId};
use crate::inst::InstData;
use crate::module::Module;

use super::LowerError;
use super::copy_resolve::{emit_copy, resolve_slot_copies};
use super::isel::IselResult;
use super::regalloc::{RegAlloc, RegSlot};

/// Result of layout: a flat bytecode sequence + try blocks + frame size.
#[derive(Debug)]
pub struct LayoutResult {
    pub bytecodes: Vec<Bytecode>,
    pub try_blocks: Vec<TryBlock>,
    /// Final register count for the function frame, including the reserved
    /// phi-copy temporary register (if any).
    pub num_regs: u16,
}

/// Lay out blocks and resolve jump targets.
pub fn layout(
    module: &Module,
    func_id: FuncId,
    isel: &IselResult,
    alloc: &RegAlloc,
    rpo: &[Block],
) -> Result<LayoutResult, LowerError> {
    // Step 1: Resolve each edge's phi copies at SLOT level. Coalescing lets
    // distinct values share a slot, so the value-level list must be re-mapped
    // and re-ordered here, at the emission point.
    let mut edge_codes: HashMap<(Block, Block), Vec<Bytecode>> = HashMap::new();
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
        let codes: Vec<Bytecode> = resolved
            .into_iter()
            .filter_map(|(s, d)| emit_copy(s, d))
            .collect();
        if !codes.is_empty() {
            edge_codes.insert(edge, codes);
        }
    }

    // Step 2: Place copies on their edges.
    let mut block_codes: HashMap<Block, Vec<Bytecode>> = HashMap::new();
    for (bb, codes) in &isel.block_codes {
        block_codes.insert(*bb, codes.clone());
    }

    // Synthetic trampoline blocks (copy sequence + `Jmp succ`), appended
    // after all real blocks. Keys are synthetic Block ids counting down from
    // `u32::MAX - 1`; real Block ids are module block-vector indices and
    // cannot reach that range (`Block(u32::MAX)` itself is `Block::INVALID`).
    let mut trampolines: Vec<(Block, Vec<Bytecode>)> = Vec::new();

    for (i, &bb) in rpo.iter().enumerate() {
        let next_bb = rpo.get(i + 1).copied();
        let block_data = module.block(bb);
        let term = block_data.insts.last().map(|&inst| &module.inst(inst).data);

        if let Some(InstData::CondBranch {
            true_dest,
            false_dest,
            ..
        }) = term
        {
            let (true_dest, false_dest) = (*true_dest, *false_dest);

            // Copies keyed to a successor that is neither branch target are
            // inconsistent input; keep the legacy in-block placement rather
            // than dropping them.
            let legacy: Vec<Bytecode> = edge_codes
                .iter()
                .filter(|&(&(pred, succ), _)| pred == bb && succ != true_dest && succ != false_dest)
                .flat_map(|(_, c)| c.iter().cloned())
                .collect();

            // True edge: redirect the conditional branch (always the last
            // bytecode of the block) to the trampoline when the edge has copies.
            let true_target = match edge_codes.get(&(bb, true_dest)) {
                Some(copies) => add_trampoline(&mut trampolines, copies, true_dest),
                None => true_dest,
            };
            // False edge: route to its trampoline when it has copies;
            // otherwise keep the fall-through / explicit-Jmp behavior.
            let false_target = match edge_codes.get(&(bb, false_dest)) {
                Some(copies) => Some(add_trampoline(&mut trampolines, copies, false_dest)),
                None => None,
            };

            let Some(codes) = block_codes.get_mut(&bb) else {
                continue;
            };
            if !legacy.is_empty() {
                let insert_pos = codes.len().saturating_sub(1);
                for (j, bc) in legacy.into_iter().enumerate() {
                    codes.insert(insert_pos + j, bc);
                }
            }
            if let Some(last) = codes.last_mut() {
                rewrite_branch_target(last, true_target);
            }
            match false_target {
                Some(tramp) => codes.push(Bytecode::Jmp(Label(tramp.0))),
                None => {
                    if next_bb != Some(false_dest) {
                        codes.push(Bytecode::Jmp(Label(false_dest.0)));
                    }
                }
            }
        } else {
            // Unconditional (or no) terminator: copies inserted before the
            // terminator run on exactly the outgoing edge(s).
            let mut copy_codes: Vec<Bytecode> = Vec::new();
            for (&(pred, _), codes) in &edge_codes {
                if pred == bb {
                    copy_codes.extend(codes.iter().cloned());
                }
            }
            if copy_codes.is_empty() {
                continue;
            }
            let Some(codes) = block_codes.get_mut(&bb) else {
                continue;
            };
            let insert_pos = codes.len().saturating_sub(1);
            for (j, bc) in copy_codes.into_iter().enumerate() {
                codes.insert(insert_pos + j, bc);
            }
        }
    }

    // Step 3: Flatten blocks in RPO order, then trampolines, recording offsets.
    let mut flat: Vec<Bytecode> = Vec::new();
    let mut final_offsets: HashMap<Block, usize> = HashMap::new();

    for &bb in rpo {
        final_offsets.insert(bb, flat.len());
        if let Some(codes) = block_codes.get(&bb) {
            flat.extend(codes.iter().cloned());
        }
    }
    for (key, codes) in &trampolines {
        final_offsets.insert(*key, flat.len());
        flat.extend(codes.iter().cloned());
    }

    // Step 4: Resolve jump targets (Block references → instruction indices).
    // Synthetic trampoline keys resolve through the same map.
    for bc in &mut flat {
        resolve_labels(bc, &final_offsets);
    }

    // Step 5: Reconstruct try blocks from IR try_regions. Trampoline offsets
    // sort after every real block, so try/handler ranges computed as
    // "distance to the next greater offset" exclude them.
    let try_blocks = reconstruct_try_blocks(module, func_id, &final_offsets, flat.len());

    Ok(LayoutResult {
        bytecodes: flat,
        try_blocks,
        num_regs: alloc.num_regs,
    })
}

/// Append a trampoline (copy sequence + `Jmp succ`) and return its synthetic
/// Block key.
fn add_trampoline(
    trampolines: &mut Vec<(Block, Vec<Bytecode>)>,
    copies: &[Bytecode],
    succ: Block,
) -> Block {
    let key = Block(u32::MAX - 1 - trampolines.len() as u32);
    let mut codes = copies.to_vec();
    codes.push(Bytecode::Jmp(Label(succ.0)));
    trampolines.push((key, codes));
    key
}

/// Rewrite the target of a (conditional or unconditional) branch bytecode.
/// No-op for non-branch bytecodes.
fn rewrite_branch_target(bc: &mut Bytecode, target: Block) {
    let label = match bc {
        Bytecode::Jmp(l)
        | Bytecode::Jeqz(l)
        | Bytecode::Jnez(l)
        | Bytecode::Jstricteqz(l)
        | Bytecode::Jnstricteqz(l)
        | Bytecode::Jeqnull(l)
        | Bytecode::Jnenull(l)
        | Bytecode::Jstricteqnull(l)
        | Bytecode::Jnstricteqnull(l)
        | Bytecode::Jequndefined(l)
        | Bytecode::Jneundefined(l)
        | Bytecode::Jstrictequndefined(l)
        | Bytecode::Jnstrictequndefined(l) => l,
        Bytecode::Jeq(_, l)
        | Bytecode::Jne(_, l)
        | Bytecode::Jstricteq(_, l)
        | Bytecode::Jnstricteq(_, l) => l,
        _ => return,
    };
    *label = Label(target.0);
}

/// Reconstruct TryBlock entries from the function's try_regions using final block offsets.
fn reconstruct_try_blocks(
    module: &Module,
    func_id: FuncId,
    block_offsets: &HashMap<Block, usize>,
    total_len: usize,
) -> Vec<TryBlock> {
    use abcd_file::CatchBlock;

    let func = module.func(func_id);
    let mut try_blocks = Vec::new();

    for region in &func.try_regions {
        if region.try_blocks.is_empty() || region.catches.is_empty() {
            continue;
        }

        // Find the min start and max end of all try blocks in this region.
        let mut min_start = usize::MAX;
        let mut max_end = 0usize;
        for &bb in &region.try_blocks {
            if let Some(&offset) = block_offsets.get(&bb) {
                min_start = min_start.min(offset);
                // Compute block end: find the next block's offset or use total_len.
                let block_end = block_offsets
                    .values()
                    .filter(|&&o| o > offset)
                    .min()
                    .copied()
                    .unwrap_or(total_len);
                max_end = max_end.max(block_end);
            }
        }

        if min_start == usize::MAX {
            continue;
        }

        let try_len = max_end - min_start;

        // Build catch entries.
        let catches: Vec<CatchBlock> = region
            .catches
            .iter()
            .filter_map(|ch| {
                let handler_offset = block_offsets.get(&ch.handler_block)?;
                // Compute handler length: distance to next block or end.
                let handler_end = block_offsets
                    .values()
                    .filter(|&&o| o > *handler_offset)
                    .min()
                    .copied()
                    .unwrap_or(total_len);
                Some(CatchBlock {
                    type_idx: ch.type_idx,
                    handler: *handler_offset as u32,
                    len: (handler_end - handler_offset) as u32,
                })
            })
            .collect();

        if !catches.is_empty() {
            try_blocks.push(TryBlock {
                start: min_start as u32,
                len: try_len as u32,
                catches,
            });
        }
    }

    try_blocks
}

/// Resolve Block-encoded labels in jump instructions to instruction indices.
fn resolve_labels(bc: &mut Bytecode, offsets: &HashMap<Block, usize>) {
    match bc {
        Bytecode::Jmp(label) => {
            if let Some(&off) = offsets.get(&Block(label.0 as u32)) {
                *label = Label(off as u32);
            }
        }
        Bytecode::Jeqz(label)
        | Bytecode::Jnez(label)
        | Bytecode::Jstricteqz(label)
        | Bytecode::Jnstricteqz(label)
        | Bytecode::Jeqnull(label)
        | Bytecode::Jnenull(label)
        | Bytecode::Jstricteqnull(label)
        | Bytecode::Jnstricteqnull(label)
        | Bytecode::Jequndefined(label)
        | Bytecode::Jneundefined(label)
        | Bytecode::Jstrictequndefined(label)
        | Bytecode::Jnstrictequndefined(label) => {
            if let Some(&off) = offsets.get(&Block(label.0 as u32)) {
                *label = Label(off as u32);
            }
        }
        Bytecode::Jeq(_, label)
        | Bytecode::Jne(_, label)
        | Bytecode::Jstricteq(_, label)
        | Bytecode::Jnstricteq(_, label) => {
            if let Some(&off) = offsets.get(&Block(label.0 as u32)) {
                *label = Label(off as u32);
            }
        }
        _ => {}
    }
}
