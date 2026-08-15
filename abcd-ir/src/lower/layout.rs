//! Block layout and jump target resolution.
//!
//! Arranges basic blocks in reverse post-order, flattens them into a linear
//! bytecode sequence, and resolves Block references in jump instructions
//! to concrete instruction indices (Labels).

use std::collections::HashMap;

use abcd_file::TryBlock;
use abcd_isa::{Bytecode, Label, Reg};

use crate::entity::{Block, FuncId};
use crate::inst::InstData;
use crate::module::Module;

use super::isel::IselResult;
use super::regalloc::RegAlloc;

/// Result of layout: a flat bytecode sequence + try blocks.
#[derive(Debug)]
pub struct LayoutResult {
    pub bytecodes: Vec<Bytecode>,
    pub try_blocks: Vec<TryBlock>,
}

/// Lay out blocks and resolve jump targets.
pub fn layout(
    module: &Module,
    func_id: FuncId,
    isel: &IselResult,
    alloc: &RegAlloc,
    rpo: &[Block],
) -> LayoutResult {
    // Step 1: Insert phi copies before terminators.
    let mut block_codes: HashMap<Block, Vec<Bytecode>> = HashMap::new();
    for (bb, codes) in &isel.block_codes {
        block_codes.insert(*bb, codes.clone());
    }

    // Insert parallel copies for phi elimination.
    for (&(pred, succ), copies) in &alloc.phi_copies {
        if let Some(codes) = block_codes.get_mut(&pred) {
            // Insert copies before the last instruction (terminator).
            let insert_pos = if codes.is_empty() { 0 } else { codes.len() - 1 };
            let mut copy_codes = Vec::new();
            for &(src, dst) in copies {
                let src_slot = alloc.allocation.get(&src).copied();
                let dst_slot = alloc.allocation.get(&dst).copied();
                match (src_slot, dst_slot) {
                    (
                        Some(super::regalloc::RegSlot::Reg(sr)),
                        Some(super::regalloc::RegSlot::Reg(dr)),
                    ) => {
                        if sr != dr {
                            copy_codes.push(Bytecode::Mov(Reg(dr), Reg(sr)));
                        }
                    }
                    (
                        Some(super::regalloc::RegSlot::Acc),
                        Some(super::regalloc::RegSlot::Reg(dr)),
                    ) => {
                        copy_codes.push(Bytecode::Sta(Reg(dr)));
                    }
                    (
                        Some(super::regalloc::RegSlot::Reg(sr)),
                        Some(super::regalloc::RegSlot::Acc),
                    ) => {
                        copy_codes.push(Bytecode::Lda(Reg(sr)));
                    }
                    _ => {
                        // acc→acc or unknown — skip
                    }
                }
            }
            for (i, bc) in copy_codes.into_iter().enumerate() {
                codes.insert(insert_pos + i, bc);
            }
            let _ = succ; // used only as key
        }
    }

    // Step 2: Flatten blocks in RPO order, recording block start offsets.
    let mut flat: Vec<Bytecode> = Vec::new();
    let mut block_offsets: HashMap<Block, usize> = HashMap::new();

    for &bb in rpo {
        block_offsets.insert(bb, flat.len());
        if let Some(codes) = block_codes.get(&bb) {
            flat.extend(codes.iter().cloned());
        }
    }

    // Check if fall-through is needed: if a block's last instruction is a
    // conditional branch and the false_dest is NOT the next block, insert Jmp.
    let mut insertions: Vec<(usize, Bytecode)> = Vec::new();
    for (i, &bb) in rpo.iter().enumerate() {
        let next_bb = rpo.get(i + 1).copied();
        let block_data = module.block(bb);
        if let Some(&last_inst) = block_data.insts.last() {
            if let InstData::CondBranch { false_dest, .. } = &module.inst(last_inst).data {
                if next_bb != Some(*false_dest) {
                    // Need explicit jump to false_dest.
                    let offset = block_offsets[&bb] + block_codes.get(&bb).map_or(0, |c| c.len());
                    insertions.push((offset, Bytecode::Jmp(Label(false_dest.0))));
                }
            }
        }
    }

    // Apply insertions (in reverse to preserve offsets).
    for (offset, bc) in insertions.into_iter().rev() {
        flat.insert(offset, bc);
    }

    // Recompute block offsets after insertions.
    let mut final_offsets: HashMap<Block, usize> = HashMap::new();
    let mut pos = 0;
    for &bb in rpo {
        final_offsets.insert(bb, pos);
        if let Some(codes) = block_codes.get(&bb) {
            pos += codes.len();
        }
        // Account for any inserted Jmp
        let block_data = module.block(bb);
        if let Some(&last_inst) = block_data.insts.last() {
            if let InstData::CondBranch { false_dest, .. } = &module.inst(last_inst).data {
                let next_idx = rpo
                    .iter()
                    .position(|&b| b == bb)
                    .map(|i| rpo.get(i + 1).copied());
                if next_idx != Some(Some(*false_dest)) {
                    pos += 1;
                }
            }
        }
    }

    // Step 3: Resolve jump targets (Block references → instruction indices).
    for bc in &mut flat {
        resolve_labels(bc, &final_offsets);
    }

    // Step 4: Reconstruct try blocks from IR try_regions.
    let try_blocks = reconstruct_try_blocks(module, func_id, &final_offsets, flat.len());

    LayoutResult {
        bytecodes: flat,
        try_blocks,
    }
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
