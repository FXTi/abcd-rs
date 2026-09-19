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
//!
//! Exception edges (try block → catch handler) NEVER carry copies: the VM
//! dispatches directly to the handler's flat offset, so no copy code could
//! run there (trampolines cannot serve them). Regalloc eliminates them via
//! pinned write-through stores (N21); any residual handler-edge copy set
//! is inconsistent input and a hard [`LowerError::HandlerEdgeCopies`], and
//! copies keyed to a block that is neither a terminator successor nor a
//! catch handler of the predecessor are [`LowerError::InconsistentEdgeCopies`].
//! (The legacy fallback that inlined such copies before the predecessor's
//! terminator — executing them on the NORMAL path, clobbering coalesced
//! slots — is deleted.)

use std::collections::{BTreeMap, HashMap, HashSet};

use abcd_file::TryBlock;
use abcd_isa::{Bytecode, EntityKind, Label};

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
    /// Entity operand traceability inherited from instruction selection,
    /// keyed by (entity kind, raw operand value).
    /// Layout only inserts `Mov` copies and `Jmp` trampolines — none of
    /// which carry entity operands — so the selection-time records
    /// stay valid for the flattened sequence.
    pub entity_traces: HashMap<(EntityKind, u32), super::isel::EntityTrace>,
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
    //
    // BTreeMap (N20): the legacy/unconditional placement loops below iterate
    // this map, and that iteration order is byte-observable in the flattened
    // output — a HashMap would permute copy-sequence order (and thereby the
    // encoded bytes) between runs. Block/edge keys are arena indices, so the
    // sorted order is stable and total.
    let mut edge_codes: BTreeMap<(Block, Block), Vec<Bytecode>> = BTreeMap::new();
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
    let mut exception_edges: HashSet<(Block, Block)> = HashSet::new();
    for region in &module.func(func_id).try_regions {
        for &try_block in &region.try_blocks {
            for catch in &region.catches {
                exception_edges.insert((try_block, catch.handler_block));
            }
        }
    }
    for &(pred, succ) in edge_codes.keys() {
        if exception_edges.contains(&(pred, succ)) {
            return Err(LowerError::HandlerEdgeCopies {
                func: func_id,
                pred,
                handler: succ,
            });
        }
        if !crate::analysis::block_succs(module, pred).contains(&succ) {
            return Err(LowerError::InconsistentEdgeCopies {
                func: func_id,
                pred,
                succ,
            });
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

            // The edge validation above guarantees that every copy-bearing
            // edge out of a CondBranch predecessor targets one of the two
            // branch destinations: copies keyed to any other block are an
            // exception edge (hard error) or inconsistent input (hard
            // error) — there is no in-block placement for them (that legacy
            // fallback executed copies on the NORMAL path and clobbered
            // coalesced slots; deleted, N21).

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
        entity_traces: isel.entity_traces.clone(),
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
///
/// N43: ONE TryBlock PER CONTIGUOUS RUN of protected blocks — no contiguity
/// assumption. `compute_rpo` may interleave an unprotected block between two
/// protected blocks of the same region (shape: `try { if (c) return 1; }
/// catch {…}; o.p` — the after-try block sorts between the protected entry
/// and the protected return block in RPO). The old single
/// `[min_start, max_end)` span then covered the unprotected block, and the
/// VM's linear first-match scan (vendored
/// arkcompiler_ets_runtime-master/ecmascript/method.cpp:86-107,
/// `Method::FindCatchBlock`) would misdispatch an exception raised in the
/// AFTER-try code to the region's handler.
///
/// Multiple try blocks per code item are native to the format: the vendored
/// writer stores a `std::vector<TryBlock>` per CodeItem
/// (abcd-file-sys/vendor/libpandafile/file_items.h:1370-1373,1426), our
/// encode path emits one file entry per model TryBlock
/// (abcd-file/src/encode.rs:1313-1348), and decode enumerates every try
/// block independently (abcd-file/src/decode.rs:1790-1839), so several
/// ranges sharing the same catch entries round-trip. Region order in the
/// output vector follows `func.try_regions` order, preserving the
/// first-match-wins dispatch priority for nested regions (the inner region
/// must precede the outer one — the same ordering the old overlapping spans
/// relied on).
///
/// Ranges of the SAME region that are adjacent in the flat stream coalesce:
/// a region whose blocks are contiguous yields exactly one
/// `[min_start, max_end)` TryBlock — byte-identical to the pre-N43 output.
///
/// Phi-copy placement vs ranges: copies for an unconditional predecessor are
/// inserted before its terminator, INSIDE the block's extent, and are pure
/// `Mov` sequences that cannot throw — covering them is harmless. Copies on
/// `CondBranch` edges live in trampolines, which sort after every real block
/// offset and therefore stay outside every try/handler range. Handler-edge
/// copies cannot exist (hard `LowerError::HandlerEdgeCopies`, N21).
fn reconstruct_try_blocks(
    module: &Module,
    func_id: FuncId,
    block_offsets: &HashMap<Block, usize>,
    total_len: usize,
) -> Vec<TryBlock> {
    use abcd_file::CatchBlock;

    let func = module.func(func_id);
    let mut try_blocks = Vec::new();

    // Extent of a block in the flat stream: [offset, next greater offset).
    // Trampoline offsets sort after every real block, so a range end never
    // extends over a trampoline.
    let extent_of = |bb: Block| -> Option<(usize, usize)> {
        let &start = block_offsets.get(&bb)?;
        let end = block_offsets
            .values()
            .filter(|&&o| o > start)
            .min()
            .copied()
            .unwrap_or(total_len);
        Some((start, end))
    };

    for region in &func.try_regions {
        if region.try_blocks.is_empty() || region.catches.is_empty() {
            continue;
        }

        // Per-block extents, coalesced into contiguous runs (N43).
        let mut extents: Vec<(usize, usize)> = region
            .try_blocks
            .iter()
            .filter_map(|&bb| extent_of(bb))
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

        // Build catch entries (shared by every run of this region).
        let catches: Vec<CatchBlock> = region
            .catches
            .iter()
            .filter_map(|ch| {
                let (handler_start, handler_end) = extent_of(ch.handler_block)?;
                Some(CatchBlock {
                    type_idx: ch.type_idx,
                    handler: handler_start as u32,
                    len: (handler_end - handler_start) as u32,
                })
            })
            .collect();

        if catches.is_empty() {
            continue;
        }

        for (start, end) in runs {
            try_blocks.push(TryBlock {
                start: start as u32,
                len: (end - start) as u32,
                catches: catches.clone(),
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
