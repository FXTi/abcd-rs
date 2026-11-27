//! Aggressive Dead Code Elimination (ADCE) + CFG simplification (`design/ir.md`).
//!
//! ADCE: mark essential roots (side-effecting instructions + terminators),
//! propagate liveness backward along use-def chains, sweep dead instructions,
//! unused `frame_init_consts`, and stale `DebugData` instruction references
//! (`line_table`, `column_table`, `local_names` scope extents).
//!
//! ## Essentiality is DERIVED, not listed (`N48`/`N50`, `design/decisions.md`)
//!
//! Observable load forms (`GetIterator`, `GetAsyncIterator`, `LoadProp`,
//! `LoadPrivate`, `TestPrivate`, `AllocRegExp`, `TryGetGlobal`, `LoadSuper`)
//! invoke user getters, check private brands, or raise `SyntaxError` /
//! `ReferenceError` / `TypeError` even when their result is dead. Rather than
//! maintaining a separate list in the optimizer, that runtime evidence lives in
//! ONE place — the `T3` effects model ([`abcd_ir::Op::effects_in`] and
//! [`abcd_ir::Effects::is_removable_if_unused`], `design/ir.md`).
//!
//! CFG simplify: merge single-pred/single-succ block pairs, eliminate empty
//! jump-only blocks, remove unreachable blocks — all exception-neutral (`N11`:
//! reachability and predecessor rebuilds use [`abcd_ir::ExceptionHandlerMap`] +
//! [`abcd_ir::normal_succs_inline`]; merges/eliminations refuse to disturb
//! try-region semantics or handler-phi edge values).

use std::collections::{HashMap, HashSet, VecDeque};

use abcd_ir::{
    BlockId, Edge, EdgeKind, ExceptionHandlerMap, FuncId, InstId, Module, Op, ValueDef, ValueId,
    normal_succs_inline,
};

use crate::FuncPass;
use crate::const_eval::{block_phis, prune_func_debug_data, replace_uses_map_in_func};

// ─── ADCE ────────────────────────────────────────────────────────────────────

/// The ADCE pass.
pub struct Adce;

impl FuncPass for Adce {
    fn run(&self, module: &mut Module, func: FuncId) -> bool {
        let Some(func_data) = module.func(func) else {
            return false;
        };
        let blocks: Vec<BlockId> = func_data.blocks.clone();

        // Collect all instructions.
        let mut all_insts: Vec<(BlockId, InstId)> = Vec::new();
        for &bb in &blocks {
            let Some(block) = module.block(bb) else {
                continue;
            };
            for &i in &block.insts {
                all_insts.push((bb, i));
            }
        }

        // Mark essential (side-effecting) instructions.
        let mut live: HashSet<InstId> = HashSet::new();
        let mut worklist: VecDeque<InstId> = VecDeque::new();

        for &(_bb, inst_id) in &all_insts {
            let Some(inst) = module.inst(inst_id) else {
                continue;
            };
            if is_essential(module, &inst.op) {
                live.insert(inst_id);
                worklist.push_back(inst_id);
            }
        }

        // Build Value → defining Inst map.
        let mut def_inst: HashMap<ValueId, InstId> = HashMap::new();
        for &(_bb, inst_id) in &all_insts {
            let Some(inst) = module.inst(inst_id) else {
                continue;
            };
            if let Some(result) = inst.result
                && matches!(module.value(result).map(|v| v.def), Some(ValueDef::Inst(_)))
            {
                def_inst.insert(result, inst_id);
            }
        }

        // Propagate: if inst is live, its operands' defining insts are live (`R3-A5`).
        while let Some(inst_id) = worklist.pop_front() {
            let Some(inst) = module.inst(inst_id) else {
                continue;
            };
            inst.op.for_each_operand(|val| {
                if let Some(&def) = def_inst.get(&val)
                    && live.insert(def)
                {
                    worklist.push_back(def);
                }
            });
        }

        // Sweep: remove dead instructions.
        let mut changed = false;
        let mut live_const_uses: HashSet<ValueId> = HashSet::new();
        for &bb in &blocks {
            let Some(block) = module.block(bb) else {
                continue;
            };
            let old_len = block.insts.len();
            let mut new_insts: Vec<InstId> = Vec::with_capacity(old_len);
            for &iid in &block.insts {
                if live.contains(&iid) {
                    new_insts.push(iid);
                    if let Some(inst) = module.inst(iid) {
                        inst.op.for_each_operand(|val| {
                            live_const_uses.insert(val);
                        });
                    }
                }
            }
            if new_insts.len() != old_len {
                changed = true;
                if let Some(block) = module.block_mut(bb) {
                    block.insts = new_insts;
                }
            }
        }

        // Sweep unused frame-initial constants owned by this function (#30).
        if let Some(func_data) = module.func_mut(func) {
            let old_consts = func_data.frame_init_consts.len();
            func_data
                .frame_init_consts
                .retain(|v| live_const_uses.contains(v));
            if func_data.frame_init_consts.len() != old_consts {
                changed = true;
            }
        }

        // Sweep dead or foreign InstIds from DebugData (`DebugInstNotInFunc`).
        changed |= prune_func_debug_data(module, func);

        changed
    }
}

/// An instruction is essential if it is a terminator or its context-refined
/// effects forbid dead-result removal (`R2-D2`, `N48`/`N50`, `design/ir.md`).
fn is_essential(module: &Module, op: &Op) -> bool {
    op.is_terminator() || !op.effects_in(module).is_removable_if_unused()
}

// ─── CFG Simplify ────────────────────────────────────────────────────────────

/// The CFG simplification pass: block merging, empty-jump elimination,
/// unreachable-block removal.
pub struct CfgSimplify;

impl FuncPass for CfgSimplify {
    fn run(&self, module: &mut Module, func: FuncId) -> bool {
        let mut changed = false;
        changed |= merge_single_succ_pred(module, func);
        changed |= eliminate_empty_jumps(module, func);
        changed |= remove_unreachable_blocks(module, func);
        if changed {
            let _ = prune_func_debug_data(module, func);
        }
        changed
    }
}

/// Contract all maximal mergeable single-pred/single-succ block chains
/// (`A -> B -> C -> ...`) in `O(B + I)` time per pass (`R3-A1`).
fn merge_single_succ_pred(module: &mut Module, func: FuncId) -> bool {
    let mut changed = false;
    while contract_chains_once(module, func) {
        changed = true;
    }
    changed
}

fn contract_chains_once(module: &mut Module, func: FuncId) -> bool {
    let Some(func_data) = module.func(func) else {
        return false;
    };
    let blocks: Vec<BlockId> = func_data.blocks.clone();
    let n = blocks.len();
    if n <= 1 {
        return false;
    }
    let entry = blocks[0];

    let mut block_to_idx: HashMap<BlockId, usize> = HashMap::with_capacity(n);
    for (idx, &bb) in blocks.iter().enumerate() {
        block_to_idx.entry(bb).or_insert(idx);
    }

    let mut is_handler = vec![false; n];
    let mut regions_of: Vec<Vec<u32>> = vec![Vec::new(); n];
    for (r_idx, region) in func_data.try_regions.iter().enumerate() {
        for catch in &region.catches {
            if let Some(&hi) = block_to_idx.get(&catch.handler) {
                is_handler[hi] = true;
            }
        }
        let r_tag = r_idx as u32;
        for &p in &region.protected {
            if let Some(&pi) = block_to_idx.get(&p)
                && regions_of[pi].last() != Some(&r_tag)
            {
                regions_of[pi].push(r_tag);
            }
        }
    }

    let Some(exc_map) = ExceptionHandlerMap::build(module, func) else {
        return false;
    };

    // Pre-index handler leading phis and their per-pred incoming values once.
    let mut handler_phis: HashMap<BlockId, Vec<InstId>> = HashMap::new();
    let mut handler_phi_vals: HashMap<(InstId, BlockId), ValueId> = HashMap::new();
    for (idx, &bb) in blocks.iter().enumerate() {
        if !is_handler[idx] {
            continue;
        }
        let phis = block_phis(module, bb);
        if phis.is_empty() {
            continue;
        }
        for &phi_id in &phis {
            if let Some(Op::Phi { entries }) = module.inst(phi_id).map(|i| &i.op) {
                for &(edge, val) in entries {
                    handler_phi_vals.insert((phi_id, edge.from), val);
                }
            }
        }
        handler_phis.insert(bb, phis);
    }

    // Identify all valid single-pred/single-succ merge edges in `O(B)`.
    let mut merge_next: Vec<Option<usize>> = vec![None; n];
    let mut merge_prev: Vec<Option<usize>> = vec![None; n];
    for (ui, &bb) in blocks.iter().enumerate() {
        if is_handler[ui] {
            continue;
        }
        let Some(&last_iid) = module.block(bb).and_then(|b| b.insts.last()) else {
            continue;
        };
        let Some(Op::Branch { dest: succ }) = module.inst(last_iid).map(|i| &i.op) else {
            continue;
        };
        let succ = *succ;
        if succ == bb || succ == entry {
            continue;
        }
        let Some(&vi) = block_to_idx.get(&succ) else {
            continue;
        };
        if is_handler[vi] || regions_of[ui] != regions_of[vi] {
            continue;
        }
        let Some(succ_block) = module.block(succ) else {
            continue;
        };
        if succ_block.preds.len() != 1 || succ_block.preds[0].from != bb {
            continue;
        }
        if !regions_of[ui].is_empty() {
            let phis_agree = exc_map.handlers_of_index(ui).iter().all(|h| {
                handler_phis.get(h).is_none_or(|phis| {
                    phis.iter().all(|&phi_id| {
                        handler_phi_vals.get(&(phi_id, bb)) == handler_phi_vals.get(&(phi_id, succ))
                    })
                })
            });
            if !phis_agree {
                continue;
            }
        }
        let succ_phis = block_phis(module, succ);
        let phi_inputs_match = succ_phis.iter().all(|&phi_id| {
            matches!(
                module.inst(phi_id).map(|i| &i.op),
                Some(Op::Phi { entries }) if entries.len() == 1 && entries[0].0.from == bb
            )
        });
        if !phi_inputs_match {
            continue;
        }
        merge_next[ui] = Some(vi);
        merge_prev[vi] = Some(ui);
    }

    // Decompose into maximal chains iteratively with explicit `visited` cycle guard.
    let mut visited = vec![false; n];
    let mut chains: Vec<(usize, Vec<usize>)> = Vec::new();
    for start in 0..n {
        if merge_next[start].is_some() && merge_prev[start].is_none() && !visited[start] {
            visited[start] = true;
            let mut cur = start;
            let mut absorbed = Vec::new();
            while let Some(nxt) = merge_next[cur] {
                if visited[nxt] {
                    break;
                }
                visited[nxt] = true;
                absorbed.push(nxt);
                cur = nxt;
            }
            if !absorbed.is_empty() {
                chains.push((start, absorbed));
            }
        }
    }
    for start in 0..n {
        if merge_next[start].is_some() && !visited[start] {
            visited[start] = true;
            let mut cur = start;
            let mut absorbed = Vec::new();
            while let Some(nxt) = merge_next[cur] {
                if visited[nxt] {
                    break;
                }
                visited[nxt] = true;
                absorbed.push(nxt);
                cur = nxt;
            }
            if !absorbed.is_empty() {
                chains.push((start, absorbed));
            }
        }
    }

    if chains.is_empty() {
        return false;
    }

    let mut is_absorbed = vec![false; n];
    let mut redirect_to_head: HashMap<BlockId, BlockId> = HashMap::new();
    let mut phi_subst: HashMap<ValueId, ValueId> = HashMap::new();

    for &(head_idx, ref absorbed) in &chains {
        let head_bb = blocks[head_idx];
        let mut prev_bb = head_bb;
        for &abs_idx in absorbed {
            is_absorbed[abs_idx] = true;
            let abs_bb = blocks[abs_idx];
            redirect_to_head.insert(abs_bb, head_bb);
            for phi_id in block_phis(module, abs_bb) {
                if let Some(inst) = module.inst(phi_id)
                    && let Op::Phi { entries } = &inst.op
                    && let Some(result) = inst.result
                    && let Some(&(_, incoming)) = entries.iter().find(|(e, _)| e.from == prev_bb)
                    && incoming != result
                {
                    phi_subst.insert(result, incoming);
                }
            }
            prev_bb = abs_bb;
        }
    }

    if !phi_subst.is_empty() {
        replace_uses_map_in_func(module, func, &phi_subst);
    }

    for &(head_idx, ref absorbed) in &chains {
        let head_bb = blocks[head_idx];
        let last_abs_pos = absorbed.len() - 1;
        let mut appended: Vec<InstId> = Vec::new();
        for (pos, &abs_idx) in absorbed.iter().enumerate() {
            let abs_bb = blocks[abs_idx];
            let Some(abs_block) = module.block(abs_bb) else {
                continue;
            };
            let phi_len = abs_block
                .insts
                .iter()
                .take_while(|&&id| module.inst(id).is_some_and(|i| i.op.is_phi()))
                .count();
            let end = if pos < last_abs_pos {
                abs_block.insts.len().saturating_sub(1)
            } else {
                abs_block.insts.len()
            };
            if phi_len < end {
                appended.extend_from_slice(&abs_block.insts[phi_len..end]);
            }
        }
        for &iid in &appended {
            if let Some(inst) = module.inst_mut(iid) {
                inst.block = head_bb;
            }
        }
        if let Some(head_block) = module.block_mut(head_bb) {
            head_block.insts.pop();
            head_block.insts.extend(appended);
        }

        let tail_bb = blocks[absorbed[last_abs_pos]];
        let succs: Vec<BlockId> = module
            .block(head_bb)
            .and_then(|b| b.insts.last().copied())
            .and_then(|iid| module.inst(iid))
            .map(|inst| {
                let (targets, count) = normal_succs_inline(&inst.op);
                targets[..count].to_vec()
            })
            .unwrap_or_default();
        for s in succs {
            for phi_id in block_phis(module, s) {
                if let Some(inst) = module.inst_mut(phi_id)
                    && let Op::Phi { entries } = &mut inst.op
                {
                    for (edge, _) in entries.iter_mut() {
                        if edge.kind == EdgeKind::Normal && edge.from == tail_bb {
                            edge.from = head_bb;
                        }
                    }
                }
            }
        }
    }

    for (idx, &bb) in blocks.iter().enumerate() {
        if !is_absorbed[idx] {
            redirect_terminator_map(module, bb, &redirect_to_head);
        }
    }
    if let Some(func_data) = module.func_mut(func) {
        func_data
            .blocks
            .retain(|b| block_to_idx.get(b).is_none_or(|&i| !is_absorbed[i]));
        for region in &mut func_data.try_regions {
            region
                .protected
                .retain(|b| block_to_idx.get(b).is_none_or(|&i| !is_absorbed[i]));
            region.protected.sort_by_key(|b| b.index());
            region.protected.dedup();
        }
    }
    rebuild_predecessors(module, func);
    true
}

/// Eliminate empty blocks that only contain an unconditional branch (`R3-A1`).
fn eliminate_empty_jumps(module: &mut Module, func: FuncId) -> bool {
    let Some(entry) = module.func(func).and_then(|f| f.entry()) else {
        return false;
    };
    let Some(func_data) = module.func(func) else {
        return false;
    };
    let blocks: Vec<BlockId> = func_data.blocks.clone();
    let handler_set: HashSet<BlockId> = func_data
        .try_regions
        .iter()
        .flat_map(|r| r.catches.iter().map(|c| c.handler))
        .collect();
    let mut region_vecs: Vec<Vec<BlockId>> = func_data
        .try_regions
        .iter()
        .map(|r| r.protected.clone())
        .collect();
    let mut region_sets: Vec<HashSet<BlockId>> = region_vecs
        .iter()
        .map(|v| v.iter().copied().collect())
        .collect();
    let mut removed_jumps: HashSet<BlockId> = HashSet::new();
    let mut redirect_map: HashMap<BlockId, BlockId> = HashMap::new();

    for &bb in &blocks {
        if bb == entry {
            continue;
        }
        let Some(block) = module.block(bb) else {
            continue;
        };
        if block.insts.len() != 1 {
            continue;
        }
        let inst_id = block.insts[0];
        let Some(inst) = module.inst(inst_id) else {
            continue;
        };
        if inst.op.is_phi() {
            continue;
        }
        let Op::Branch { dest: raw_target } = inst.op else {
            continue;
        };
        let target = resolve_block_redirect(&redirect_map, raw_target);
        if target == bb {
            continue;
        }

        let preds: Vec<BlockId> = block.preds.iter().map(|e| e.from).collect();

        if handler_set.contains(&bb) || handler_set.contains(&target) {
            continue;
        }
        if region_sets
            .iter()
            .any(|rset| rset.contains(&bb) && !preds.iter().all(|p| rset.contains(p)))
        {
            continue;
        }

        if elimination_loses_converging_phi_value(module, bb, target, &preds) {
            continue;
        }

        for &pred in &preds {
            redirect_terminator(module, pred, bb, target);
            let pred_edge = Edge {
                from: pred,
                kind: EdgeKind::Normal,
            };
            if let Some(target_block) = module.block_mut(target)
                && !target_block.preds.contains(&pred_edge)
            {
                for p in target_block.preds.iter_mut() {
                    if p.from == bb {
                        *p = pred_edge;
                        break;
                    }
                }
                if !target_block.preds.contains(&pred_edge) {
                    target_block.preds.push(pred_edge);
                }
            }
        }
        if let Some(target_block) = module.block_mut(target) {
            target_block.preds.retain(|p| p.from != bb);
        }

        for phi_id in block_phis(module, target) {
            let Some(inst) = module.inst_mut(phi_id) else {
                continue;
            };
            if let Op::Phi { entries } = &mut inst.op {
                let incoming = entries.iter().find(|(e, _)| e.from == bb).map(|(_, v)| *v);
                entries.retain(|(e, _)| e.from != bb);
                if let Some(value) = incoming {
                    for &pred in &preds {
                        if !entries.iter().any(|(e, _)| e.from == pred) {
                            entries.push((
                                Edge {
                                    from: pred,
                                    kind: EdgeKind::Normal,
                                },
                                value,
                            ));
                        }
                    }
                }
            }
        }

        for (rvec, rset) in region_vecs.iter_mut().zip(region_sets.iter_mut()) {
            if rset.remove(&bb) {
                rvec.retain(|&b| b != bb);
                for &p in &preds {
                    if rset.insert(p) {
                        rvec.push(p);
                    }
                }
            }
        }
        removed_jumps.insert(bb);
        redirect_map.insert(bb, target);
    }

    if removed_jumps.is_empty() {
        return false;
    }

    for &bb in &blocks {
        if !removed_jumps.contains(&bb) {
            redirect_terminator_map(module, bb, &redirect_map);
        }
    }
    if let Some(func_data) = module.func_mut(func) {
        func_data.blocks.retain(|b| !removed_jumps.contains(b));
        for (region, mut protected) in func_data.try_regions.iter_mut().zip(region_vecs) {
            protected.sort_by_key(|b| b.index());
            protected.dedup();
            region.protected = protected;
        }
    }
    rebuild_predecessors(module, func);
    true
}

/// Redirect a block's terminator from `old_target` to `new_target`.
fn redirect_terminator(
    module: &mut Module,
    block: BlockId,
    old_target: BlockId,
    new_target: BlockId,
) {
    let Some(&last) = module.block(block).and_then(|b| b.insts.last()) else {
        return;
    };
    if let Some(inst) = module.inst_mut(last)
        && inst.op.is_terminator()
    {
        inst.op.for_each_block_id_mut(|dest| {
            if *dest == old_target {
                *dest = new_target;
            }
        });
    }
}

#[inline]
fn resolve_block_redirect(redirects: &HashMap<BlockId, BlockId>, mut b: BlockId) -> BlockId {
    for _ in 0..=redirects.len() {
        match redirects.get(&b) {
            Some(&next) if next != b => b = next,
            _ => break,
        }
    }
    b
}

fn redirect_terminator_map(
    module: &mut Module,
    block: BlockId,
    redirects: &HashMap<BlockId, BlockId>,
) {
    if redirects.is_empty() {
        return;
    }
    let Some(&last) = module.block(block).and_then(|b| b.insts.last()) else {
        return;
    };
    if let Some(inst) = module.inst_mut(last)
        && inst.op.is_terminator()
    {
        inst.op.for_each_block_id_mut(|dest| {
            *dest = resolve_block_redirect(redirects, *dest);
        });
    }
}

fn rebuild_predecessors(module: &mut Module, func: FuncId) {
    let Some(func_data) = module.func(func) else {
        return;
    };
    let blocks: Vec<BlockId> = func_data.blocks.clone();
    let Some(exc_map) = ExceptionHandlerMap::build(module, func) else {
        return;
    };
    for &block in &blocks {
        if let Some(b) = module.block_mut(block) {
            b.preds.clear();
        }
    }
    let mut seen_preds: HashMap<BlockId, HashSet<Edge>> = HashMap::new();
    for (bi, &block) in blocks.iter().enumerate() {
        let (targets, count) = module
            .block(block)
            .and_then(|b| b.insts.last().copied())
            .and_then(|iid| module.inst(iid))
            .map_or(([BlockId::new(0); 2], 0), |inst| {
                normal_succs_inline(&inst.op)
            });
        for &succ in &targets[..count] {
            push_pred_unique(
                module,
                &mut seen_preds,
                succ,
                Edge {
                    from: block,
                    kind: EdgeKind::Normal,
                },
            );
        }
        for &handler in exc_map.handlers_of_index(bi) {
            push_pred_unique(
                module,
                &mut seen_preds,
                handler,
                Edge {
                    from: block,
                    kind: EdgeKind::Exceptional,
                },
            );
        }
    }
    for &block in &blocks {
        let phis = block_phis(module, block);
        if phis.is_empty() {
            continue;
        }
        let Some(preds) = module.block(block).map(|b| b.preds.clone()) else {
            continue;
        };
        let pred_set: Option<HashSet<Edge>> = if preds.len() > 8 {
            Some(preds.iter().copied().collect())
        } else {
            None
        };
        for phi_id in phis {
            let Some(inst) = module.inst_mut(phi_id) else {
                continue;
            };
            if let Op::Phi { entries } = &mut inst.op {
                let mut seen = HashSet::with_capacity(entries.len());
                entries.retain(|(edge, _)| {
                    let valid = match &pred_set {
                        Some(pset) => pset.contains(edge),
                        None => preds.contains(edge),
                    };
                    valid && seen.insert(*edge)
                });
            }
        }
    }
}

#[inline]
fn push_pred_unique(
    module: &mut Module,
    seen_preds: &mut HashMap<BlockId, HashSet<Edge>>,
    succ: BlockId,
    edge: Edge,
) {
    let Some(succ_block) = module.block_mut(succ) else {
        return;
    };
    if succ_block.preds.len() < 8 && !seen_preds.contains_key(&succ) {
        if !succ_block.preds.contains(&edge) {
            succ_block.preds.push(edge);
        }
        return;
    }
    let set = seen_preds
        .entry(succ)
        .or_insert_with(|| succ_block.preds.iter().copied().collect());
    if set.insert(edge) {
        succ_block.preds.push(edge);
    }
}

/// Converging-edge phi value guard (`V4`).
fn elimination_loses_converging_phi_value(
    module: &Module,
    bb: BlockId,
    target: BlockId,
    preds: &[BlockId],
) -> bool {
    let Some(target_block) = module.block(target) else {
        return false;
    };
    let target_preds: Vec<BlockId> = target_block.preds.iter().map(|e| e.from).collect();
    let converging: Vec<BlockId> = preds
        .iter()
        .copied()
        .filter(|p| target_preds.contains(p))
        .collect();
    if converging.is_empty() {
        return false;
    }
    block_phis(module, target).iter().any(|&phi_id| {
        let Some(inst) = module.inst(phi_id) else {
            return false;
        };
        let Op::Phi { entries } = &inst.op else {
            return false;
        };
        let via_bb = entries.iter().find(|(e, _)| e.from == bb).map(|(_, v)| *v);
        converging.iter().any(|&pred| {
            let direct = entries
                .iter()
                .find(|(e, _)| e.from == pred)
                .map(|(_, v)| *v);
            via_bb != direct
        })
    })
}

/// Remove blocks not reachable from entry (`R3-A1`: `ExceptionHandlerMap` +
/// `normal_succs_inline` BFS, `N11`).
fn remove_unreachable_blocks(module: &mut Module, func: FuncId) -> bool {
    let Some(entry) = module.func(func).and_then(|f| f.entry()) else {
        return false;
    };
    let Some(func_data) = module.func(func) else {
        return false;
    };
    let blocks: Vec<BlockId> = func_data.blocks.clone();
    let Some(exc_map) = ExceptionHandlerMap::build(module, func) else {
        return false;
    };

    let mut reachable: HashSet<BlockId> = HashSet::with_capacity(blocks.len());
    let mut queue = VecDeque::new();
    reachable.insert(entry);
    queue.push_back(entry);
    while let Some(bb) = queue.pop_front() {
        let (targets, count) = module
            .block(bb)
            .and_then(|b| b.insts.last().copied())
            .and_then(|iid| module.inst(iid))
            .map_or(([BlockId::new(0); 2], 0), |inst| {
                normal_succs_inline(&inst.op)
            });
        for &succ in &targets[..count] {
            if reachable.insert(succ) {
                queue.push_back(succ);
            }
        }
        for &handler in exc_map.handlers_of(bb) {
            if reachable.insert(handler) {
                queue.push_back(handler);
            }
        }
    }

    if blocks.iter().all(|b| reachable.contains(b)) {
        return false;
    }

    if let Some(func_data) = module.func_mut(func) {
        func_data.blocks.retain(|b| reachable.contains(b));
        for region in &mut func_data.try_regions {
            region.protected.retain(|b| reachable.contains(b));
            region.catches.retain(|c| reachable.contains(&c.handler));
        }
    }
    rebuild_predecessors(module, func);
    true
}
