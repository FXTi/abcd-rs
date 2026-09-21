//! Aggressive Dead Code Elimination (ADCE) + CFG simplification — the
//! v0.2 port of v0.1 `opt::dce`.
//!
//! ADCE: mark essential roots (side-effecting instructions + terminators),
//! propagate liveness backward along use-def chains, sweep dead
//! instructions.
//!
//! ## Essentiality is DERIVED, not listed (N48/N50)
//!
//! v0.1 kept a hand-maintained `is_essential` list whose observable-load
//! entries (GetIterator/GetAsyncIterator/LoadProperty/LoadPrivateProperty/
//! TestPrivateProperty/CreateRegExp/LoadGlobalVar/TryLoadGlobalByName/
//! LoadSuperProperty) each rest on vendored runtime evidence (getter
//! calls, brand checks, ReferenceErrors). In v0.2 that evidence lives in
//! ONE place — the T3 effects table
//! ([`abcd_ir::Op::effects`], design/ir-v0.2.md §4.4): an instruction is
//! essential iff it is a terminator or its effects record shows a write,
//! a possible throw, or a possible call. Pure reads (lexical/global/module
//! loads that cannot throw or call) and pure allocations stay
//! dead-deletable, exactly as in v0.1.
//!
//! CFG simplify: merge single-pred/single-succ block pairs, eliminate
//! empty jump-only blocks, remove unreachable blocks — all
//! exception-neutral (N11: reachability and predecessor rebuilds use the
//! AUGMENTED successor relation; merges/eliminations refuse to disturb
//! try-region semantics or handler-phi edge values).

use std::collections::{HashMap, HashSet, VecDeque};

use abcd_ir::{BlockId, Edge, EdgeKind, FuncId, InstId, Module, Op, ValueDef, ValueId};

use crate::FuncPass;
use crate::analysis::{augmented_succs, normal_succs, replace_uses_in_func};

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
            if is_essential(&inst.op) {
                live.insert(inst_id);
                worklist.push_back(inst_id);
            }
        }

        // Build Value → defining Inst map (only instruction-defined
        // values have a defining instruction to keep alive; params,
        // const-defined values, and exception params have none).
        let mut def_inst: HashMap<ValueId, InstId> = HashMap::new();
        for &(_bb, inst_id) in &all_insts {
            let Some(inst) = module.inst(inst_id) else {
                continue;
            };
            if let Some(result) = inst.result {
                if matches!(module.value(result).map(|v| v.def), Some(ValueDef::Inst(_))) {
                    def_inst.insert(result, inst_id);
                }
            }
        }

        // Propagate: if inst is live, its operands' defining insts are live.
        while let Some(inst_id) = worklist.pop_front() {
            let Some(inst) = module.inst(inst_id) else {
                continue;
            };
            for val in inst.op.operands() {
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
            let Some(block) = module.block(bb) else {
                continue;
            };
            let old_len = block.insts.len();
            let new_insts: Vec<InstId> = block
                .insts
                .iter()
                .copied()
                .filter(|i| live.contains(i))
                .collect();
            if new_insts.len() != old_len {
                changed = true;
                if let Some(block) = module.block_mut(bb) {
                    block.insts = new_insts;
                }
            }
        }

        changed
    }
}

/// An instruction is essential if it has side effects or is a terminator.
///
/// Derived from the T3 effects table (N48/N50): a write to any memory
/// class, a possible throw, or a possible call makes the instruction
/// observable even when its result is dead. Pure reads (e.g.
/// `GetLexVar`, `LoadModuleVar`, `GetResumeMode`) and pure allocations
/// (e.g. `AllocObject`, `AllocArray`, `AllocClosure`) are dead-deletable
/// when their result is unused — v0.1 parity.
fn is_essential(op: &Op) -> bool {
    if op.is_terminator() {
        return true;
    }
    let effects = op.effects();
    !effects.writes.is_empty() || effects.may_throw || effects.may_call != abcd_ir::CallEffect::None
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
        changed
    }
}

/// The phi instructions of a block (the leading phi prefix).
fn block_phis(module: &Module, bb: BlockId) -> Vec<InstId> {
    module
        .block(bb)
        .map(|b| {
            b.insts
                .iter()
                .copied()
                .take_while(|&id| module.inst(id).is_some_and(|i| i.op.is_phi()))
                .collect()
        })
        .unwrap_or_default()
}

/// Merge block pairs where `a` has single successor `b` and `b` has single predecessor `a`.
fn merge_single_succ_pred(module: &mut Module, func: FuncId) -> bool {
    let mut changed = false;
    let Some(entry) = module.func(func).and_then(|f| f.entry()) else {
        return false;
    };

    loop {
        let Some(func_data) = module.func(func) else {
            break;
        };
        let blocks: Vec<BlockId> = func_data.blocks.clone();
        let mut merged_any = false;

        for &bb in &blocks {
            let succs = normal_succs(module, bb);
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
            // Exception-neutrality: merging bb+succ must not disturb
            // try-region semantics. The merged block keeps bb's identity,
            // so this is sound iff (a) both blocks have IDENTICAL region
            // membership (the protected byte range is unchanged), (b)
            // neither is a catch handler (handler entry identity), and (c)
            // every handler phi carries the SAME incoming value for both
            // blocks — handler phi entries are keyed by the individual
            // protected block (the value live at the point of exception)
            // and the absorbed block's entry is dropped by
            // rebuild_predecessors, so the survivor's entry must hold an
            // equal value.
            if !merge_is_exception_neutral(module, func, bb, succ) {
                continue;
            }

            let succ_preds = module
                .block(succ)
                .map(|b| b.preds.clone())
                .unwrap_or_default();
            if succ_preds.len() != 1 || succ_preds[0].from != bb {
                continue;
            }

            // Merge: remove bb's terminator, append succ's insts to bb.
            // succ must have no phis (single pred).
            let succ_phis = block_phis(module, succ);
            let succ_insts: Vec<InstId> = module
                .block(succ)
                .map(|b| {
                    b.insts
                        .iter()
                        .copied()
                        .skip_while(|&id| module.inst(id).is_some_and(|i| i.op.is_phi()))
                        .collect()
                })
                .unwrap_or_default();
            let phi_inputs_match = succ_phis.iter().all(|&phi_id| {
                matches!(&module.inst(phi_id).map(|i| &i.op), Some(Op::Phi { entries })
                    if entries.len() == 1 && entries[0].0.from == bb)
            });
            if !phi_inputs_match {
                continue;
            }
            // A single-pred phi is definitionally equal to its one
            // incoming value: SUBSTITUTE the value for every use of the
            // phi result and drop the phi. Re-keying the entry to bb's
            // preds instead would (a) manufacture a trivial phi for
            // copyprop to clean up, and (b) — when bb is the entry block
            // and has no preds — produce `Phi { entries: [] }` whose
            // result may stay live: no edge ever writes its home
            // register at lowering, so uses read frame garbage (N27).
            for &phi_id in &succ_phis {
                let (result, incoming) = {
                    let Some(inst) = module.inst(phi_id) else {
                        continue;
                    };
                    let incoming = match &inst.op {
                        Op::Phi { entries } => entries
                            .iter()
                            .find(|(edge, _)| edge.from == bb)
                            .map(|(_, v)| *v),
                        _ => None,
                    };
                    (inst.result, incoming)
                };
                if let (Some(result), Some(value)) = (result, incoming) {
                    if value != result {
                        replace_uses_in_func(module, func, result, value);
                    }
                    // Self-referential single-entry phis (dead cycles)
                    // need no rewrite: uses already name the phi result,
                    // and ADCE sweeps them when the result is unused.
                }
            }

            // Remove the terminator from bb.
            if let Some(block) = module.block_mut(bb) {
                block.insts.pop();
            }

            // Move succ's insts. Its phis are eliminated above, so they
            // are NOT moved into bb (a moved phi would sit at a join it
            // does not belong to — or, for entry bb, become empty).
            if let Some(block) = module.block_mut(bb) {
                block.insts.extend(succ_insts.iter().copied());
            }
            for &inst_id in succ_insts.iter() {
                if let Some(inst) = module.inst_mut(inst_id) {
                    inst.block = bb;
                }
            }

            // Update block references in successors of succ.
            let new_succs = normal_succs(module, bb);
            for s in new_succs {
                if let Some(s_block) = module.block_mut(s) {
                    for p in s_block.preds.iter_mut() {
                        if p.from == succ {
                            p.from = bb;
                        }
                    }
                }
                let phi_ids = block_phis(module, s);
                for phi_id in phi_ids {
                    if let Some(inst) = module.inst_mut(phi_id) {
                        if let Op::Phi { entries } = &mut inst.op {
                            for (edge, _) in entries.iter_mut() {
                                if edge.from == succ {
                                    edge.from = bb;
                                }
                            }
                        }
                    }
                }
            }

            // Remove succ from function's block list.
            rewrite_all_terminators(module, func, succ, bb);
            if let Some(func_data) = module.func_mut(func) {
                func_data.blocks.retain(|b| *b != succ);
            }
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
    let Some(entry) = module.func(func).and_then(|f| f.entry()) else {
        return false;
    };
    let Some(func_data) = module.func(func) else {
        return false;
    };
    let blocks: Vec<BlockId> = func_data.blocks.clone();

    for &bb in &blocks {
        if bb == entry {
            continue;
        }
        let Some(block) = module.block(bb) else {
            continue;
        };
        if block
            .insts
            .iter()
            .any(|&id| module.inst(id).is_some_and(|i| i.op.is_phi()))
        {
            continue;
        }
        if block.insts.len() != 1 {
            continue;
        }

        let inst_id = block.insts[0];
        let target = match module.inst(inst_id).map(|i| &i.op) {
            Some(Op::Branch { dest }) => *dest,
            _ => continue,
        };

        if target == bb {
            continue;
        } // self-loop

        // Redirect all predecessors of bb to target.
        let preds: Vec<BlockId> = block.preds.iter().map(|e| e.from).collect();

        // Exception-neutrality: eliminating a jump-only block is sound
        // for try regions iff (a) bb is not a catch handler and target is
        // not one either (handler entry identity; a terminator edge into
        // a handler would give it preds its phis are not keyed by), and
        // (b) every region protecting bb also protects ALL of bb's
        // predecessors — a bare `jmp` cannot throw, so removing bb loses
        // no throwing code, while extending a region over an unprotected
        // predecessor would misdispatch that predecessor's exceptions.
        if !elimination_is_exception_neutral(module, func, bb, target, &preds) {
            continue;
        }

        // Converging-edge phi guard (V4): if a predecessor `pred` of bb
        // ALSO has a direct edge to `target`, eliminating bb threads a
        // second pred→target edge that claims the same per-pred phi
        // entry. Phi entries are keyed by edge SOURCE block, so the
        // per-pred model cannot represent two converging edges from one
        // pred carrying DIFFERENT values — elimination is sound only
        // when, for every phi in `target`, the value arriving via bb
        // equals the value arriving via pred directly. Otherwise the
        // rewrite below would skip pred's existing entry
        // (`any(|(p,_)| p.from == pred)`) and silently drop the
        // bb-mediated value (optional-chain corpus family).
        if elimination_loses_converging_phi_value(module, bb, target, &preds) {
            continue;
        }

        for &pred in &preds {
            redirect_terminator(module, pred, bb, target);
            // Update target's preds.
            let pred_edge = Edge {
                from: pred,
                kind: EdgeKind::Normal,
            };
            if let Some(target_block) = module.block_mut(target) {
                if !target_block.preds.contains(&pred_edge) {
                    // Replace bb with pred in target's preds.
                    for p in target_block.preds.iter_mut() {
                        if p.from == bb {
                            *p = pred_edge;
                        }
                    }
                    if !target_block.preds.contains(&pred_edge) {
                        target_block.preds.push(pred_edge);
                    }
                }
            }
        }

        // Remove bb from target's preds (it's been replaced by bb's preds).
        if let Some(target_block) = module.block_mut(target) {
            target_block.preds.retain(|p| p.from != bb);
        }

        // Preserve phi semantics when the removed block had predecessors:
        // every predecessor now reaches `target` with the value that used to
        // arrive through `bb`.
        let phi_ids = block_phis(module, target);
        for phi_id in phi_ids {
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

        // Remove bb from function.
        rewrite_all_terminators(module, func, bb, target);
        if let Some(func_data) = module.func_mut(func) {
            func_data.blocks.retain(|b| *b != bb);
        }
        rewrite_try_regions(module, func, bb, &preds);
        rebuild_predecessors(module, func);
        changed = true;
    }

    changed
}

/// Redirect a block's terminator from `old_target` to `new_target`.
fn redirect_terminator(
    module: &mut Module,
    block: BlockId,
    old_target: BlockId,
    new_target: BlockId,
) {
    let Some(b) = module.block(block) else {
        return;
    };
    let Some(&last) = b.insts.last() else {
        return;
    };
    if let Some(inst) = module.inst_mut(last) {
        match &mut inst.op {
            Op::Branch { dest } => {
                if *dest == old_target {
                    *dest = new_target;
                }
            }
            Op::CondBranch {
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

fn rewrite_all_terminators(module: &mut Module, func: FuncId, old: BlockId, new: BlockId) {
    let Some(func_data) = module.func(func) else {
        return;
    };
    let blocks = func_data.blocks.clone();
    for block in blocks {
        redirect_terminator(module, block, old, new);
    }
}

fn rebuild_predecessors(module: &mut Module, func: FuncId) {
    let Some(func_data) = module.func(func) else {
        return;
    };
    let blocks: Vec<BlockId> = func_data.blocks.clone();
    for &block in &blocks {
        if let Some(b) = module.block_mut(block) {
            b.preds.clear();
        }
    }
    // Predecessors derive from the augmented successor relation:
    // terminator edges (Normal) plus try→handler exception edges
    // (Exceptional; handlers still owned by this function only). This
    // keeps handler preds consistent with the pruned try_regions.
    for &block in &blocks {
        for (succ, kind) in augmented_succs(module, func, block) {
            let edge = Edge { from: block, kind };
            if let Some(succ_block) = module.block_mut(succ) {
                if !succ_block.preds.contains(&edge) {
                    succ_block.preds.push(edge);
                }
            }
        }
    }
    for &block in &blocks {
        let Some(b) = module.block(block) else {
            continue;
        };
        let preds = b.preds.clone();
        let phis = block_phis(module, block);
        for phi_id in phis {
            let Some(inst) = module.inst_mut(phi_id) else {
                continue;
            };
            if let Op::Phi { entries } = &mut inst.op {
                entries.retain(|(edge, _)| preds.contains(edge));
                let mut seen = HashSet::new();
                entries.retain(|(edge, _)| seen.insert(*edge));
            }
        }
    }
}

/// Is `block` a catch handler of any of `func`'s try regions?
fn is_handler_block(module: &Module, func: FuncId, block: BlockId) -> bool {
    module.func(func).is_some_and(|f| {
        f.try_regions
            .iter()
            .any(|region| region.catches.iter().any(|c| c.handler == block))
    })
}

/// May `bb` (single terminator successor `succ`) absorb `succ` without
/// disturbing try-region semantics? Requires: identical region membership
/// for both blocks (protected byte range unchanged), no handler
/// involvement (handler entry identity), and — for every handler of every
/// region covering both — phi incoming values that agree on `bb` and
/// `succ`. The absorbed block's handler-phi entries are dropped by
/// `rebuild_predecessors` (only the survivor `bb` stays a handler pred),
/// so the two entries must carry equal values for the merge to preserve
/// the value live at the point of exception.
fn merge_is_exception_neutral(module: &Module, func: FuncId, bb: BlockId, succ: BlockId) -> bool {
    let Some(func_data) = module.func(func) else {
        return false;
    };
    if is_handler_block(module, func, bb) || is_handler_block(module, func, succ) {
        return false;
    }
    for region in &func_data.try_regions {
        let bb_in = region.protected.contains(&bb);
        let succ_in = region.protected.contains(&succ);
        if bb_in != succ_in {
            return false;
        }
        if !bb_in {
            continue;
        }
        for catch in &region.catches {
            let handler = catch.handler;
            if !func_data.blocks.contains(&handler) {
                continue;
            }
            for &phi_id in &block_phis(module, handler) {
                let Some(inst) = module.inst(phi_id) else {
                    continue;
                };
                if let Op::Phi { entries } = &inst.op {
                    let vb = entries.iter().find(|(e, _)| e.from == bb).map(|(_, v)| *v);
                    let vs = entries
                        .iter()
                        .find(|(e, _)| e.from == succ)
                        .map(|(_, v)| *v);
                    if vb != vs {
                        return false;
                    }
                }
            }
        }
    }
    true
}

/// May the jump-only block `bb` (predecessors `preds`, branch target
/// `target`) be eliminated without disturbing try-region semantics?
/// Handlers keep their identity on both sides of the rewrite, and any
/// region protecting `bb` must already protect every predecessor — a bare
/// `jmp` cannot throw, so dropping `bb` loses no throwing code, while
/// extending the region over an unprotected predecessor would
/// misdispatch that predecessor's exceptions.
fn elimination_is_exception_neutral(
    module: &Module,
    func: FuncId,
    bb: BlockId,
    target: BlockId,
    preds: &[BlockId],
) -> bool {
    if is_handler_block(module, func, bb) || is_handler_block(module, func, target) {
        return false;
    }
    module.func(func).is_some_and(|f| {
        f.try_regions.iter().all(|region| {
            !region.protected.contains(&bb) || preds.iter().all(|p| region.protected.contains(p))
        })
    })
}

/// Would eliminating the jump-only block `bb` (predecessors `preds`,
/// branch target `target`) drop a phi value? For every predecessor that
/// ALSO has a direct edge to `target` (i.e. is already one of target's
/// preds), threading bb's edge onto `target` merges two converging
/// edges into one per-pred phi entry. The merge is value-preserving
/// only when every phi in `target` carries the SAME incoming value for
/// the bb-mediated path (entry keyed `bb`) as for the direct path
/// (entry keyed `pred`); any difference means one value would be lost.
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

/// Rewrite exception metadata when a CFG block is replaced by other blocks.
///
/// Never fires on a catch handler: merges and empty-jump eliminations
/// refuse handler involvement (handler entry identity), so
/// `catch.handler == removed` — and with it the [`Catch`]'s
/// `ExceptionParam(removed)` exception value — cannot occur here.
fn rewrite_try_regions(
    module: &mut Module,
    func: FuncId,
    removed: BlockId,
    replacements: &[BlockId],
) {
    let Some(func_data) = module.func_mut(func) else {
        return;
    };
    for region in &mut func_data.try_regions {
        let mut protected = Vec::new();
        for block in region.protected.drain(..) {
            if block == removed {
                protected.extend_from_slice(replacements);
            } else {
                protected.push(block);
            }
        }
        protected.sort_by_key(|b| b.index());
        protected.dedup();
        region.protected = protected;
        for catch in &mut region.catches {
            if catch.handler == removed {
                if let Some(&replacement) = replacements.first() {
                    catch.handler = replacement;
                }
            }
        }
    }
}

/// Remove blocks not reachable from entry.
///
/// Reachability uses the AUGMENTED successor relation
/// (`analysis::augmented_succs`): terminator successors plus try→handler
/// exception edges. Catch handlers have no terminator-level incoming
/// edges — exception dispatch is implicit — so a terminator-only BFS
/// deletes every catch handler and prunes its try-region entry, silently
/// dropping the exceptional control-flow path (N11).
fn remove_unreachable_blocks(module: &mut Module, func: FuncId) -> bool {
    let Some(entry) = module.func(func).and_then(|f| f.entry()) else {
        return false;
    };
    let Some(func_data) = module.func(func) else {
        return false;
    };
    let blocks: Vec<BlockId> = func_data.blocks.clone();

    // BFS from entry over terminator successors + exception edges.
    let mut reachable = HashSet::new();
    let mut queue = VecDeque::new();
    reachable.insert(entry);
    queue.push_back(entry);
    while let Some(bb) = queue.pop_front() {
        for (succ, _kind) in augmented_succs(module, func, bb) {
            if reachable.insert(succ) {
                queue.push_back(succ);
            }
        }
    }

    let unreachable: Vec<BlockId> = blocks
        .iter()
        .filter(|b| !reachable.contains(b))
        .copied()
        .collect();
    if unreachable.is_empty() {
        return false;
    }

    // Remove unreachable blocks from predecessor lists.
    for &bb in &unreachable {
        let succs = normal_succs(module, bb);
        for s in succs {
            if reachable.contains(&s) {
                if let Some(s_block) = module.block_mut(s) {
                    s_block.preds.retain(|p| p.from != bb);
                }
            }
        }
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
