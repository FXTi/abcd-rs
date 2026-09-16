//! Aggressive Dead Code Elimination (ADCE) + CFG simplification.
//!
//! ADCE: mark essential roots (side-effecting instructions + terminators),
//! propagate liveness backward along use-def chains, sweep dead instructions.
//! Dead CondBranch → Branch when the condition is dead.
//!
//! CFG simplify: merge single-pred/single-succ block pairs, eliminate empty
//! jump-only blocks, remove unreachable blocks.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::analysis::{block_succs, inst_operands};
use crate::entity::{Block, FuncId, Inst, Value};
use crate::inst::InstData;
use crate::module::Module;

use super::FuncPass;

// ─── ADCE ────────────────────────────────────────────────────────────────────

pub struct Adce;

impl FuncPass for Adce {
    fn run(&self, module: &mut Module, func: FuncId) -> bool {
        let blocks: Vec<Block> = module.func(func).blocks.clone();

        // Collect all instructions.
        let mut all_insts: Vec<(Block, Inst)> = Vec::new();
        for &bb in &blocks {
            let block = module.block(bb);
            for &i in block.phis.iter().chain(block.insts.iter()) {
                all_insts.push((bb, i));
            }
        }

        // Mark essential (side-effecting) instructions.
        let mut live: HashSet<Inst> = HashSet::new();
        let mut worklist: VecDeque<Inst> = VecDeque::new();

        for &(_bb, inst_id) in &all_insts {
            if is_essential(&module.inst(inst_id).data) {
                live.insert(inst_id);
                worklist.push_back(inst_id);
            }
        }

        // Build Value → defining Inst map.
        let mut def_inst: HashMap<Value, Inst> = HashMap::new();
        for &(_bb, inst_id) in &all_insts {
            if let Some(result) = module.inst(inst_id).result {
                def_inst.insert(result, inst_id);
            }
        }

        // Propagate: if inst is live, its operands' defining insts are live.
        while let Some(inst_id) = worklist.pop_front() {
            for val in inst_operands(&module.inst(inst_id).data) {
                if let Some(&def) = def_inst.get(&val) {
                    if live.insert(def) {
                        worklist.push_back(def);
                    }
                }
            }
        }

        // Sweep: remove dead instructions.
        let mut changed = false;
        for &bb in &blocks {
            let block = module.block(bb);
            let old_phis = block.phis.clone();
            let old_insts = block.insts.clone();

            let new_phis: Vec<Inst> = old_phis.into_iter().filter(|i| live.contains(i)).collect();
            let new_insts: Vec<Inst> = old_insts.into_iter().filter(|i| live.contains(i)).collect();

            if new_phis.len() != module.block(bb).phis.len()
                || new_insts.len() != module.block(bb).insts.len()
            {
                changed = true;
                module.block_mut(bb).phis = new_phis;
                module.block_mut(bb).insts = new_insts;
            }
        }

        changed
    }
}

/// An instruction is essential if it has side effects or is a terminator.
fn is_essential(data: &InstData) -> bool {
    use InstData::*;
    match data {
        // Terminators are always essential.
        Branch { .. } | CondBranch { .. } | Return { .. } | Unreachable => true,

        // Side-effecting: stores, calls, throws, scope ops, etc.
        StoreProperty { .. }
        | StoreOwnProperty { .. }
        | StoreSuperProperty { .. }
        | StoreGlobalVar { .. }
        | TryStoreGlobalByName { .. }
        | StoreLexVar { .. }
        | StoreModuleVar { .. }
        | DeleteProperty { .. }
        | Call { .. }
        | Throw { .. }
        | ThrowIfNotObject { .. }
        | ThrowConstAssignment { .. }
        | ThrowUndefinedIfHole { .. }
        | ThrowIfSuperNotCorrectCall { .. }
        | ThrowNotExists
        | ThrowPatternNonCoercible
        | ThrowDeleteSuperProperty
        | NewLexEnv { .. }
        | NewLexEnvWithName { .. }
        | PopLexEnv
        | DynamicImport { .. }
        | SuspendGenerator { .. }
        | AsyncFunctionAwaitUncaught { .. }
        | AsyncFunctionResolve { .. }
        | AsyncFunctionReject { .. }
        | CloseIterator { .. }
        | DefineFunc { .. }
        | DefineMethod { .. }
        | DefineClassWithBuffer { .. }
        | DefineGetterSetterByValue { .. }
        | Debugger => true,

        // Pure computations — dead unless used.
        _ => false,
    }
}

// ─── CFG Simplify ────────────────────────────────────────────────────────────

pub struct CfgSimplify;

impl FuncPass for CfgSimplify {
    fn run(&self, module: &mut Module, func: FuncId) -> bool {
        let mut changed = false;
        changed |= merge_single_succ_pred(module, func);
        changed |= eliminate_empty_jumps(module, func);
        changed |= remove_unreachable_blocks(module, func);
        changed
    }
}

/// Merge block pairs where `a` has single successor `b` and `b` has single predecessor `a`.
fn merge_single_succ_pred(module: &mut Module, func: FuncId) -> bool {
    let mut changed = false;
    let entry = module.func(func).entry_block;

    loop {
        let blocks: Vec<Block> = module.func(func).blocks.clone();
        let mut merged_any = false;

        for &bb in &blocks {
            let succs = block_succs(module, bb);
            if succs.len() != 1 {
                continue;
            }
            let succ = succs[0];
            if succ == bb {
                continue;
            } // self-loop
            if succ == entry {
                continue;
            } // don't merge into entry

            let succ_preds = module.block(succ).preds.clone();
            if succ_preds.len() != 1 || succ_preds[0] != bb {
                continue;
            }

            // Merge: remove bb's terminator, append succ's insts to bb.
            // succ must have no phis (single pred).
            let succ_phis = module.block(succ).phis.clone();
            let succ_insts = module.block(succ).insts.clone();
            let bb_preds = module.block(bb).preds.clone();
            for &phi_id in &succ_phis {
                if let InstData::Phi { entries } = &mut module.inst_mut(phi_id).data {
                    let incoming = entries
                        .iter()
                        .find(|(pred, _)| *pred == bb)
                        .map(|(_, v)| *v);
                    if let Some(value) = incoming {
                        entries.clear();
                        entries.extend(bb_preds.iter().copied().map(|pred| (pred, value)));
                    }
                }
            }

            // Remove the terminator from bb.
            module.block_mut(bb).insts.pop();

            // Move succ's phis (should be empty for single-pred) and insts.
            module.block_mut(bb).phis.extend(succ_phis.iter().copied());
            module
                .block_mut(bb)
                .insts
                .extend(succ_insts.iter().copied());
            for &inst_id in succ_phis.iter().chain(succ_insts.iter()) {
                module.inst_mut(inst_id).block = bb;
            }

            // Update block references in successors of succ.
            let new_succs = block_succs(module, bb);
            for s in new_succs {
                let preds = &mut module.block_mut(s).preds;
                for p in preds.iter_mut() {
                    if *p == succ {
                        *p = bb;
                    }
                }
                let phi_ids = module.block(s).phis.clone();
                for phi_id in phi_ids {
                    if let InstData::Phi { entries } = &mut module.inst_mut(phi_id).data {
                        for (pred, _) in entries.iter_mut() {
                            if *pred == succ {
                                *pred = bb;
                            }
                        }
                    }
                }
            }

            // Remove succ from function's block list.
            rewrite_all_terminators(module, func, succ, bb);
            module.func_mut(func).blocks.retain(|b| *b != succ);
            rewrite_try_regions(module, func, succ, &[bb]);
            rebuild_predecessors(module, func);

            merged_any = true;
            changed = true;
            break; // restart since block list changed
        }

        if !merged_any {
            break;
        }
    }

    changed
}

/// Eliminate empty blocks that only contain an unconditional branch.
fn eliminate_empty_jumps(module: &mut Module, func: FuncId) -> bool {
    let mut changed = false;
    let entry = module.func(func).entry_block;
    let blocks: Vec<Block> = module.func(func).blocks.clone();

    for &bb in &blocks {
        if bb == entry {
            continue;
        }
        let block = module.block(bb);
        if !block.phis.is_empty() {
            continue;
        }
        if block.insts.len() != 1 {
            continue;
        }

        let inst_id = block.insts[0];
        let target = match &module.inst(inst_id).data {
            InstData::Branch { dest } => *dest,
            _ => continue,
        };

        if target == bb {
            continue;
        } // self-loop

        // Redirect all predecessors of bb to target.
        let preds = block.preds.clone();
        for &pred in &preds {
            redirect_terminator(module, pred, bb, target);
            // Update target's preds.
            let target_preds = &mut module.block_mut(target).preds;
            if !target_preds.contains(&pred) {
                // Replace bb with pred in target's preds.
                for p in target_preds.iter_mut() {
                    if *p == bb {
                        *p = pred;
                    }
                }
                if !target_preds.contains(&pred) {
                    target_preds.push(pred);
                }
            }
        }

        // Remove bb from target's preds (it's been replaced by bb's preds).
        module.block_mut(target).preds.retain(|p| *p != bb);

        // Preserve phi semantics when the removed block had predecessors:
        // every predecessor now reaches `target` with the value that used to
        // arrive through `bb`.
        let phi_ids = module.block(target).phis.clone();
        for phi_id in phi_ids {
            if let InstData::Phi { entries } = &mut module.inst_mut(phi_id).data {
                let incoming = entries.iter().find(|(p, _)| *p == bb).map(|(_, v)| *v);
                entries.retain(|(p, _)| *p != bb);
                if let Some(value) = incoming {
                    for &pred in &preds {
                        if !entries.iter().any(|(p, _)| *p == pred) {
                            entries.push((pred, value));
                        }
                    }
                }
            }
        }

        // Remove bb from function.
        rewrite_all_terminators(module, func, bb, target);
        module.func_mut(func).blocks.retain(|b| *b != bb);
        rewrite_try_regions(module, func, bb, &preds);
        rebuild_predecessors(module, func);
        changed = true;
    }

    changed
}

/// Redirect a block's terminator from `old_target` to `new_target`.
fn redirect_terminator(module: &mut Module, block: Block, old_target: Block, new_target: Block) {
    let insts = module.block(block).insts.clone();
    if let Some(&last) = insts.last() {
        match &mut module.inst_mut(last).data {
            InstData::Branch { dest } => {
                if *dest == old_target {
                    *dest = new_target;
                }
            }
            InstData::CondBranch {
                true_dest,
                false_dest,
                ..
            } => {
                if *true_dest == old_target {
                    *true_dest = new_target;
                }
                if *false_dest == old_target {
                    *false_dest = new_target;
                }
            }
            _ => {}
        }
    }
}

fn rewrite_all_terminators(module: &mut Module, func: FuncId, old: Block, new: Block) {
    let blocks = module.func(func).blocks.clone();
    for block in blocks {
        redirect_terminator(module, block, old, new);
    }
}

fn rebuild_predecessors(module: &mut Module, func: FuncId) {
    let blocks = module.func(func).blocks.clone();
    for &block in &blocks {
        module.block_mut(block).preds.clear();
    }
    for &block in &blocks {
        for succ in block_succs(module, block) {
            if !module.block(succ).preds.contains(&block) {
                module.block_mut(succ).preds.push(block);
            }
        }
    }
    let regions = module.func(func).try_regions.clone();
    for region in regions {
        for &protected in &region.try_blocks {
            for catch in &region.catches {
                if module.func(func).blocks.contains(&catch.handler_block)
                    && !module.block(catch.handler_block).preds.contains(&protected)
                {
                    module.block_mut(catch.handler_block).preds.push(protected);
                }
            }
        }
    }
}

/// Rewrite exception metadata when a CFG block is replaced by other blocks.
fn rewrite_try_regions(module: &mut Module, func: FuncId, removed: Block, replacements: &[Block]) {
    for region in &mut module.func_mut(func).try_regions {
        let mut protected = Vec::new();
        for block in region.try_blocks.drain(..) {
            if block == removed {
                protected.extend_from_slice(replacements);
            } else {
                protected.push(block);
            }
        }
        protected.sort_by_key(|b| b.0);
        protected.dedup();
        region.try_blocks = protected;
        for catch in &mut region.catches {
            if catch.handler_block == removed {
                if let Some(&replacement) = replacements.first() {
                    catch.handler_block = replacement;
                }
            }
        }
    }
}

/// Remove blocks not reachable from entry.
fn remove_unreachable_blocks(module: &mut Module, func: FuncId) -> bool {
    let entry = module.func(func).entry_block;
    let blocks: Vec<Block> = module.func(func).blocks.clone();

    // BFS from entry.
    let mut reachable = HashSet::new();
    let mut queue = VecDeque::new();
    reachable.insert(entry);
    queue.push_back(entry);
    while let Some(bb) = queue.pop_front() {
        for succ in block_succs(module, bb) {
            if reachable.insert(succ) {
                queue.push_back(succ);
            }
        }
    }

    let unreachable: Vec<Block> = blocks
        .iter()
        .filter(|b| !reachable.contains(b))
        .copied()
        .collect();
    if unreachable.is_empty() {
        return false;
    }

    // Remove unreachable blocks from predecessor lists.
    for &bb in &unreachable {
        let succs = block_succs(module, bb);
        for s in succs {
            if reachable.contains(&s) {
                module.block_mut(s).preds.retain(|p| *p != bb);
            }
        }
    }

    module
        .func_mut(func)
        .blocks
        .retain(|b| reachable.contains(b));
    for region in &mut module.func_mut(func).try_regions {
        region.try_blocks.retain(|b| reachable.contains(b));
        region
            .catches
            .retain(|c| reachable.contains(&c.handler_block));
    }
    true
}
