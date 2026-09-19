//! IR well-formedness verification.
//!
//! Checks structural invariants that must hold for valid IR:
//! - Every block ends with a terminator
//! - Phi nodes only appear at the beginning of blocks
//! - Phi entry count matches predecessor count
//! - Entry block has no predecessors
//! - Values used by instructions are defined (exist in the module)
//! - Every use is dominated by its definition (terminator-CFG
//!   dominance, with documented exception-model exemptions — N45)

use std::collections::HashSet;
use std::fmt;

use crate::analysis;
use crate::entity::{Block, FuncId, Inst, Value};
use crate::inst::InstData;
use crate::module::{Module, ValueDef};

/// A verification error with location context.
#[derive(Debug)]
pub struct VerifyError {
    pub func: FuncId,
    pub block: Option<Block>,
    pub inst: Option<Inst>,
    pub message: String,
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "verify error in {}", self.func)?;
        if let Some(bb) = self.block {
            write!(f, " {bb}")?;
        }
        if let Some(i) = self.inst {
            write!(f, " {i}")?;
        }
        write!(f, ": {}", self.message)
    }
}

impl std::error::Error for VerifyError {}

/// Verify a single function's IR.
pub fn verify_func(module: &Module, func_id: FuncId) -> Vec<VerifyError> {
    let mut errors = Vec::new();
    let func = module.func(func_id);
    let func_blocks: HashSet<Block> = func.blocks.iter().copied().collect();
    let err = |block: Option<Block>, inst: Option<Inst>, msg: String| VerifyError {
        func: func_id,
        block,
        inst,
        message: msg,
    };

    if func.blocks.first().copied() != Some(func.entry_block) {
        errors.push(err(
            None,
            None,
            "entry block must be the first block in the function".into(),
        ));
    }
    if func_blocks.len() != func.blocks.len() {
        errors.push(err(
            None,
            None,
            "function block list contains duplicates".into(),
        ));
    }

    // Collect values defined in this function and validate their ownership.
    let mut defined_values: HashSet<Value> = HashSet::new();
    for &bb in &func.blocks {
        let block = module.block(bb);
        for &inst_id in block.phis.iter().chain(block.insts.iter()) {
            if module.inst(inst_id).block != bb {
                errors.push(err(
                    Some(bb),
                    Some(inst_id),
                    "instruction is stored in a different block".into(),
                ));
            }
            if let Some(val) = module.inst(inst_id).result {
                defined_values.insert(val);
            }
        }
    }
    // Function parameters are also defined values, but only parameters of
    // this function. `param_values` records per-function ownership; a
    // global scan of FuncParam defs would incorrectly permit cross-function
    // value references (two functions can both have a FuncParam(0)).
    for &val in &func.param_values {
        defined_values.insert(val);
    }
    // Exception values delivered at catch-handler entries (N13) are defined
    // values of this function — recorded per function in `exception_values`
    // for the same ownership reason as `param_values`.
    for &(_, val) in &func.exception_values {
        defined_values.insert(val);
    }

    // Entry normally has no predecessors. A loop may legally branch back to
    // itself, so only predecessors from a different block are invalid.
    let entry = func.entry_block;
    if module.block(entry).preds.iter().any(|pred| *pred != entry) {
        errors.push(err(
            Some(entry),
            None,
            "entry block has a predecessor from another block".into(),
        ));
    }

    // N27: a phi on a REACHABLE block with no predecessors can never
    // receive a value — no incoming edge carries a phi copy at lowering,
    // so any use reads a never-written frame register. Reachability uses
    // the augmented successor relation (terminator edges + try→handler
    // exception edges), matching the optimizer's own liveness model.
    // Dead pred-less blocks (N18) legitimately carry junk and are exempt:
    // CfgSimplify removes them, and this rule must not fire on them.
    // (The entry block with a self-loop back-edge has itself as a pred
    // and is unaffected; handlers have their try blocks as preds.)
    {
        let mut reachable: HashSet<Block> = HashSet::new();
        let mut queue: std::collections::VecDeque<Block> = std::collections::VecDeque::new();
        reachable.insert(entry);
        queue.push_back(entry);
        while let Some(bb) = queue.pop_front() {
            for succ in analysis::augmented_succs(module, func_id, bb) {
                if func_blocks.contains(&succ) && reachable.insert(succ) {
                    queue.push_back(succ);
                }
            }
        }
        for &bb in &func.blocks {
            if !reachable.contains(&bb) || !module.block(bb).preds.is_empty() {
                continue;
            }
            for &inst_id in &module.block(bb).phis {
                errors.push(err(
                    Some(bb),
                    Some(inst_id),
                    "phi on a reachable block with no predecessors".into(),
                ));
            }
        }
    }

    for &bb in &func.blocks {
        let block = module.block(bb);

        // Predecessor lists are sets and must agree with terminator edges.
        let pred_set: HashSet<Block> = block.preds.iter().copied().collect();
        if pred_set.len() != block.preds.len() {
            errors.push(err(
                Some(bb),
                None,
                "block has duplicate predecessors".into(),
            ));
        }
        for &pred in &block.preds {
            if !func_blocks.contains(&pred) {
                errors.push(err(
                    Some(bb),
                    None,
                    format!("predecessor {pred} is not in this function"),
                ));
            } else if !analysis::block_succs(module, pred).contains(&bb)
                && !func.try_regions.iter().any(|region| {
                    region.try_blocks.contains(&pred)
                        && region.catches.iter().any(|catch| catch.handler_block == bb)
                })
            {
                errors.push(err(
                    Some(bb),
                    None,
                    format!("predecessor {pred} does not target block"),
                ));
            }
        }

        // Block must have at least one instruction (the terminator).
        if block.insts.is_empty() {
            errors.push(err(
                Some(bb),
                None,
                "block has no instructions (missing terminator)".into(),
            ));
            continue;
        }

        // Last instruction must be a terminator.
        let last = *block.insts.last().unwrap();
        if !module.inst(last).data.is_terminator() {
            errors.push(err(
                Some(bb),
                Some(last),
                "block does not end with a terminator".into(),
            ));
        }

        // No terminator before the last instruction.
        for &inst_id in &block.insts[..block.insts.len() - 1] {
            if module.inst(inst_id).data.is_terminator() {
                errors.push(err(
                    Some(bb),
                    Some(inst_id),
                    "terminator in the middle of a block".into(),
                ));
            }
        }

        // No phi in the regular instruction list.
        for &inst_id in &block.insts {
            if module.inst(inst_id).data.is_phi() {
                errors.push(err(
                    Some(bb),
                    Some(inst_id),
                    "phi node in regular instruction list (should be in phis)".into(),
                ));
            }
        }

        // All phis are actually phi instructions.
        for &inst_id in &block.phis {
            if !module.inst(inst_id).data.is_phi() {
                errors.push(err(
                    Some(bb),
                    Some(inst_id),
                    "non-phi instruction in phi list".into(),
                ));
            }
        }

        // Phi entry count matches predecessor count.
        for &inst_id in &block.phis {
            if let InstData::Phi { entries } = &module.inst(inst_id).data {
                if entries.len() != block.preds.len() {
                    errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        format!(
                            "phi has {} entries but block has {} predecessors",
                            entries.len(),
                            block.preds.len()
                        ),
                    ));
                }
                let pred_set: HashSet<Block> = block.preds.iter().copied().collect();
                let mut entry_preds = HashSet::new();
                for (entry_bb, _) in entries {
                    if !pred_set.contains(entry_bb) {
                        errors.push(err(
                            Some(bb),
                            Some(inst_id),
                            format!("phi references {entry_bb} which is not a predecessor"),
                        ));
                    }
                    if !entry_preds.insert(*entry_bb) {
                        errors.push(err(
                            Some(bb),
                            Some(inst_id),
                            format!("phi contains duplicate predecessor {entry_bb}"),
                        ));
                    }
                }
            }
        }

        // Terminator successors reference blocks in this function.
        let last_data = &module.inst(last).data;
        let succs: Vec<Block> = match last_data {
            InstData::Branch { dest } => vec![*dest],
            InstData::CondBranch {
                true_dest,
                false_dest,
                ..
            } => {
                vec![*true_dest, *false_dest]
            }
            _ => vec![],
        };
        for succ in succs {
            if !func_blocks.contains(&succ) {
                errors.push(err(
                    Some(bb),
                    Some(last),
                    format!("successor {succ} is not in this function"),
                ));
            } else if !module.block(succ).preds.contains(&bb) {
                errors.push(err(
                    Some(bb),
                    Some(last),
                    format!("successor {succ} is missing this block from predecessors"),
                ));
            }
        }

        // Value operands are defined.
        for &inst_id in block.phis.iter().chain(block.insts.iter()) {
            for val in analysis::inst_operands(&module.inst(inst_id).data) {
                if !defined_values.contains(&val) {
                    errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        format!("uses undefined value {val}"),
                    ));
                }
            }
        }

        // Every value definition must belong to this function and point back
        // to the instruction that defines it.
        for &inst_id in block.phis.iter().chain(block.insts.iter()) {
            if let Some(result) = module.inst(inst_id).result {
                match module.values.get(result.index()).map(|v| v.def) {
                    Some(ValueDef::Inst(def)) if def == inst_id => {}
                    Some(_) => errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        format!("result {result} has mismatched definition"),
                    )),
                    None => errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        format!("result {result} is outside value arena"),
                    )),
                }
            }
        }
    }

    verify_dominance(module, func_id, &mut errors);

    // Try/catch metadata must only reference blocks owned by this function.
    // Keep the region lists consistent with the CFG so lowering cannot emit
    // handlers or protected ranges from another function.
    for (ri, region) in func.try_regions.iter().enumerate() {
        let mut seen = HashSet::new();
        for &try_block in &region.try_blocks {
            if !func_blocks.contains(&try_block) {
                errors.push(err(
                    None,
                    None,
                    format!("try region {ri} references foreign block {try_block}"),
                ));
            }
            if !seen.insert(try_block) {
                errors.push(err(
                    Some(try_block),
                    None,
                    format!("try region {ri} contains duplicate protected block"),
                ));
            }
        }
        for catch in &region.catches {
            if !func_blocks.contains(&catch.handler_block) {
                errors.push(err(
                    None,
                    None,
                    format!(
                        "try region {ri} references foreign handler {}",
                        catch.handler_block
                    ),
                ));
            }
        }
    }

    errors
}

/// N45 use-def dominance: every use of a value must be dominated by its
/// definition, over the TERMINATOR CFG (`analysis::domtree::DomTree`).
///
/// The terminator-successor model gives catch handlers no incoming CFG
/// edges — exception dispatch is implicit — so handlers (and blocks only
/// reachable through them, plus genuinely dead blocks, N18) have no
/// dominator-tree entry. The documented exemptions, all forced by that
/// model:
///
/// 1. USES IN CFG-UNREACHABLE BLOCKS are exempt. A handler reads values
///    defined in its protected try blocks (live there at the point of
///    exception — N13/N21), which terminator-CFG dominance can never
///    justify; that flow is governed by the augmented liveness model
///    (`analysis::augmented_succs`). Dead pred-less blocks legitimately
///    carry junk (same standing as the N27 zero-pred phi rule's
///    exemption).
/// 2. PHI ENTRIES are uses on the incoming EDGE: the value must be
///    available at the END of the keyed predecessor — defined in the
///    pred itself, or in a block dominating the pred. Entries keyed by a
///    CFG-unreachable pred (handler → merge edges, dead preds) are
///    exempt per (1).
/// 3. ENTRY-DEFINED values — function parameters (`ValueDef::FuncParam`,
///    bound to the frame's argument slots at function entry) and
///    instruction results defined in the entry block (including the
///    shared frame-initial LiteralUndefined/LiteralHole seeds, P3-T7) —
///    dominate everything, handlers included: control can only reach any
///    block after executing the entry block. (Within the entry block
///    itself the usual def-before-use ordering still applies.)
/// 4. EXCEPTION PARAMS (`ValueDef::ExceptionParam`, N13) are defined by
///    the exception dispatch itself, at the owning handler's entry:
///    valid in the owning handler block, in CFG-unreachable blocks
///    downstream of it, and on phi edges keyed by that handler.
fn verify_dominance(module: &Module, func_id: FuncId, errors: &mut Vec<VerifyError>) {
    let func = module.func(func_id);
    let entry = func.entry_block;
    let dom = crate::analysis::domtree::DomTree::build(module, func_id);
    let cfg_reachable = |b: Block| dom.dominates(entry, b);
    let exception_owner: std::collections::HashMap<Value, Block> = func
        .exception_values
        .iter()
        .map(|&(handler, val)| (val, handler))
        .collect();
    let err = |block: Option<Block>, inst: Option<Inst>, msg: String| VerifyError {
        func: func_id,
        block,
        inst,
        message: msg,
    };

    for &bb in &func.blocks {
        let block = module.block(bb);
        // Instruction positions (phis first, then insts) for the
        // same-block def-before-use ordering check.
        let mut position: std::collections::HashMap<Inst, usize> = std::collections::HashMap::new();
        for (i, &inst_id) in block.phis.iter().chain(block.insts.iter()).enumerate() {
            position.insert(inst_id, i);
        }

        for (i, &inst_id) in block.phis.iter().chain(block.insts.iter()).enumerate() {
            let data = &module.inst(inst_id).data;

            if let InstData::Phi { entries } = data {
                // Phi entries: uses on the incoming edge (exemption 2).
                for &(pred, val) in entries {
                    match module.values.get(val.index()).map(|v| v.def) {
                        // Params are entry-defined (exemption 3).
                        Some(ValueDef::FuncParam(_)) => {}
                        // Exception params: edge must leave the owning
                        // handler (exemption 4); unreachable preds are
                        // exempt per (1).
                        Some(ValueDef::ExceptionParam) => {
                            let owner = exception_owner.get(&val).copied();
                            if owner.is_some() && owner != Some(pred) && cfg_reachable(pred) {
                                errors.push(err(
                                    Some(bb),
                                    Some(inst_id),
                                    format!(
                                        "phi entry from {pred} uses exception value {val} \
                                         delivered at {:?} — not available at the end of {pred}",
                                        owner.unwrap()
                                    ),
                                ));
                            }
                        }
                        Some(ValueDef::Inst(def_inst)) => {
                            let def_block = module.inst(def_inst).block;
                            if def_block == pred || def_block == entry || !cfg_reachable(pred) {
                                continue;
                            }
                            if !dom.dominates(def_block, pred) {
                                errors.push(err(
                                    Some(bb),
                                    Some(inst_id),
                                    format!(
                                        "phi entry from {pred} uses {val} whose definition in \
                                         {def_block} does not dominate the predecessor"
                                    ),
                                ));
                            }
                        }
                        // Undefined values are reported by the existence check.
                        None => {}
                    }
                }
                continue;
            }

            for val in analysis::inst_operands(data) {
                match module.values.get(val.index()).map(|v| v.def) {
                    Some(ValueDef::FuncParam(_)) => {}
                    Some(ValueDef::ExceptionParam) => {
                        let owner = exception_owner.get(&val).copied();
                        if owner.is_some() && owner != Some(bb) && cfg_reachable(bb) {
                            errors.push(err(
                                Some(bb),
                                Some(inst_id),
                                format!(
                                    "uses exception value {val} delivered at handler {:?} — \
                                     not available in this block",
                                    owner.unwrap()
                                ),
                            ));
                        }
                    }
                    Some(ValueDef::Inst(def_inst)) => {
                        let def_block = module.inst(def_inst).block;
                        if def_block == bb {
                            // Same block: the definition must precede the
                            // use (phis precede all regular insts).
                            let def_pos = position.get(&def_inst).copied().unwrap_or(usize::MAX);
                            if def_pos >= i {
                                errors.push(err(
                                    Some(bb),
                                    Some(inst_id),
                                    format!(
                                        "uses {val} before its definition — the definition does \
                                         not dominate this use"
                                    ),
                                ));
                            }
                            continue;
                        }
                        // Entry-defined values dominate everything,
                        // handlers included (exemption 3).
                        if def_block == entry || !cfg_reachable(bb) {
                            continue;
                        }
                        if !dom.dominates(def_block, bb) {
                            errors.push(err(
                                Some(bb),
                                Some(inst_id),
                                format!(
                                    "uses {val} whose definition in {def_block} does not \
                                     dominate this block"
                                ),
                            ));
                        }
                    }
                    None => {}
                }
            }
        }
    }
}

/// Verify all functions in the module.
pub fn verify_module(module: &Module) -> Vec<VerifyError> {
    let mut errors = Vec::new();
    for i in 0..module.functions.len() {
        errors.extend(verify_func(module, FuncId::from_index(i)));
    }
    errors
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builder::IRBuilder;
    use crate::inst::{BinOp, InstData};
    use crate::module::{CatchHandler, Module, TryRegion};
    use crate::types::IrType;
    use abcd_file::{FileType, FunctionKind, Version};

    fn make_module() -> Module {
        Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic)
    }

    #[test]
    fn valid_simple_function() {
        let mut m = make_module();
        let func = IRBuilder::create_function(&mut m, "f", FunctionKind::Function, 2);
        let mut b = IRBuilder::new(&mut m, func);
        let p0 = b.create_func_param(0, IrType::default());
        let p1 = b.create_func_param(1, IrType::default());
        let sum = b.emit_val(
            InstData::BinaryOp {
                op: BinOp::Add,
                left: p0,
                right: p1,
            },
            IrType::default(),
        );
        b.emit_void(InstData::Return { value: Some(sum) });

        let errs = verify_func(&m, func);
        assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
    }

    #[test]
    fn missing_terminator() {
        let mut m = make_module();
        let func = IRBuilder::create_function(&mut m, "f", FunctionKind::Function, 0);
        let mut b = IRBuilder::new(&mut m, func);
        // Emit a non-terminator only
        b.emit_val(InstData::LiteralNull, IrType::default());

        let errs = verify_func(&m, func);
        assert!(errs.iter().any(|e| e.message.contains("terminator")));
    }

    #[test]
    fn phi_entry_mismatch() {
        let mut m = make_module();
        let func = IRBuilder::create_function(&mut m, "f", FunctionKind::Function, 0);
        let mut b = IRBuilder::new(&mut m, func);

        let bb1 = b.create_block();
        let entry = b.current_block();
        b.add_predecessor(bb1, entry);
        b.emit_void(InstData::Branch { dest: bb1 });

        b.set_insert_block(bb1);
        let v = b.emit_val(InstData::LiteralNumber(1.0), IrType::default());
        // Phi with 2 entries but only 1 predecessor
        b.emit_val(
            InstData::Phi {
                entries: vec![(entry, v), (bb1, v)],
            },
            IrType::default(),
        );
        b.emit_void(InstData::Return { value: None });

        let errs = verify_func(&m, func);
        assert!(
            errs.iter()
                .any(|e| e.message.contains("phi has 2 entries but block has 1"))
        );
    }

    #[test]
    fn rejects_foreign_try_region_blocks() {
        let mut m = make_module();
        let func = IRBuilder::create_function(&mut m, "f", FunctionKind::Function, 0);
        let foreign = Block::from_index(m.blocks.len());
        m.blocks.push(crate::module::BasicBlockData::new());
        m.func_mut(func).try_regions.push(TryRegion {
            try_blocks: vec![foreign],
            catches: vec![CatchHandler {
                type_idx: u32::MAX,
                handler_block: foreign,
            }],
        });
        let errs = verify_func(&m, func);
        assert!(errs.iter().any(|e| e.message.contains("foreign block")));
        assert!(errs.iter().any(|e| e.message.contains("foreign handler")));
    }

    #[test]
    fn rejects_duplicate_function_blocks() {
        let mut m = make_module();
        let func = IRBuilder::create_function(&mut m, "f", FunctionKind::Function, 0);
        let entry = m.func(func).entry_block;
        m.func_mut(func).blocks.push(entry);
        let errs = verify_func(&m, func);
        assert!(
            errs.iter()
                .any(|e| e.message.contains("block list contains duplicates"))
        );
    }

    #[test]
    fn rejects_duplicate_phi_predecessors() {
        let mut m = make_module();
        let func = IRBuilder::create_function(&mut m, "f", FunctionKind::Function, 0);
        let mut b = IRBuilder::new(&mut m, func);
        let entry = b.current_block();
        let target = b.create_block();
        b.emit_void(InstData::Branch { dest: target });
        b.set_insert_block(target);
        b.emit_val(
            InstData::Phi {
                entries: vec![(entry, Value::from_index(0)), (entry, Value::from_index(0))],
            },
            IrType::default(),
        );
        b.emit_void(InstData::Return { value: None });
        let errs = verify_func(&m, func);
        assert!(
            errs.iter()
                .any(|e| e.message.contains("duplicate predecessor"))
        );
    }

    /// N27: a phi on a REACHABLE block with no predecessors can never
    /// receive a value — no edge carries a phi copy at lowering, so any
    /// use reads a never-written frame register. This must be an error.
    #[test]
    fn phi_on_reachable_zero_pred_block_is_error() {
        let mut m = make_module();
        let func = IRBuilder::create_function(&mut m, "f", FunctionKind::Function, 0);
        let mut b = IRBuilder::new(&mut m, func);
        // Entry block (reachable, zero preds) carrying an EMPTY phi — the
        // exact N27 end state the optimizer once produced.
        b.emit_val(InstData::Phi { entries: vec![] }, IrType::default());
        b.emit_void(InstData::Return { value: None });

        let errs = verify_func(&m, func);
        assert!(
            errs.iter()
                .any(|e| e.message.contains("reachable block with no predecessors")),
            "expected the zero-pred reachable phi rule to fire, got: {errs:?}"
        );
    }

    /// N18 twin: a phi on an UNREACHABLE zero-pred block is tolerated —
    /// dead pred-less blocks legitimately carry junk and CfgSimplify
    /// removes them; the rule must not fire on them.
    #[test]
    fn phi_on_unreachable_zero_pred_block_is_tolerated() {
        let mut m = make_module();
        let func = IRBuilder::create_function(&mut m, "f", FunctionKind::Function, 0);
        let mut b = IRBuilder::new(&mut m, func);
        let dead = b.create_block();
        b.emit_void(InstData::Return { value: None });
        b.set_insert_block(dead);
        b.emit_val(InstData::Phi { entries: vec![] }, IrType::default());
        b.emit_void(InstData::Return { value: None });

        let errs = verify_func(&m, func);
        assert!(
            errs.is_empty(),
            "dead pred-less blocks must not trip the rule: {errs:?}"
        );
    }

    /// N45 red pin: a use whose definition does NOT dominate it (over
    /// the terminator CFG) must be an error. Existence-only
    /// verification accepts this today.
    ///
    /// ```text
    /// entry: CondBranch(p0, b1, b2)
    /// b1: v = 1.0; Return          — v defined in b1
    /// b2: Return(v)                — b1 does not dominate b2
    /// ```
    #[test]
    fn use_not_dominated_by_def_is_error() {
        let mut m = make_module();
        let func = IRBuilder::create_function(&mut m, "f", FunctionKind::Function, 1);
        let mut b = IRBuilder::new(&mut m, func);
        let p0 = b.create_func_param(0, IrType::default());
        let b1 = b.create_block();
        let b2 = b.create_block();
        let entry = b.current_block();
        b.add_predecessor(b1, entry);
        b.add_predecessor(b2, entry);
        b.emit_void(InstData::CondBranch {
            cond: p0,
            true_dest: b1,
            false_dest: b2,
        });
        b.set_insert_block(b1);
        let v = b.emit_val(InstData::LiteralNumber(1.0), IrType::default());
        b.emit_void(InstData::Return { value: None });
        b.set_insert_block(b2);
        b.emit_void(InstData::Return { value: Some(v) });

        let errs = verify_func(&m, func);
        assert!(
            errs.iter().any(|e| e.message.contains("dominat")),
            "expected a use-def dominance error, got: {errs:?}"
        );
    }

    /// N45 red pin: within one block a use must come AFTER its
    /// definition (dominance is not just block-granular).
    #[test]
    fn use_before_def_in_same_block_is_error() {
        let mut m = make_module();
        let func = IRBuilder::create_function(&mut m, "f", FunctionKind::Function, 0);
        let entry;
        let use_inst;
        {
            let mut b = IRBuilder::new(&mut m, func);
            entry = b.current_block();
            let v = b.emit_val(InstData::LiteralNumber(1.0), IrType::default());
            let (ui, _) = b.emit(
                InstData::BinaryOp {
                    op: crate::inst::BinOp::Add,
                    left: v,
                    right: v,
                },
                IrType::default(),
            );
            use_inst = ui;
            b.emit_void(InstData::Return { value: None });
        }
        // Move the use BEFORE its definition within the same block.
        let insts = &mut m.block_mut(entry).insts;
        insts.swap(0, 1);

        let errs = verify_func(&m, func);
        assert!(
            errs.iter()
                .any(|e| e.inst == Some(use_inst) && e.message.contains("dominat")),
            "expected a same-block def-after-use dominance error, got: {errs:?}"
        );
    }

    /// N45 exemptions pin: exception-dispatch value flow is NOT
    /// terminator-CFG dominance, so the check must stay silent on:
    ///
    /// ```text
    /// entry: e0 = undefined; Branch(t)
    /// t (try-protected): v = 1.0; Branch(join)
    /// h (catch-all handler of t): w = v + e0; Branch(join)
    /// join: phi[(t, v), (h, w)]; Return(phi)
    /// ```
    ///
    /// - `w = v + e0` in h uses a try-PROTECTED def (v in t) and an
    ///   ENTRY-defined value (e0) from a block the terminator CFG cannot
    ///   reach — exempt (N13/N21 exception dispatch is implicit).
    /// - The phi entry `(h, w)` is keyed by a CFG-unreachable pred —
    ///   the edge use is exempt the same way.
    /// - The phi entry `(t, v)` is a normal dominated edge use.
    #[test]
    fn handler_uses_of_protected_and_entry_defs_are_exempt() {
        let mut m = make_module();
        let func = IRBuilder::create_function(&mut m, "f", FunctionKind::Function, 0);
        let mut b = IRBuilder::new(&mut m, func);
        let entry = b.current_block();
        let t = b.create_block();
        let h = b.create_block();
        let join = b.create_block();
        b.add_predecessor(t, entry);
        b.add_predecessor(h, t);
        b.add_predecessor(join, t);
        b.add_predecessor(join, h);

        let e0 = b.emit_val(InstData::LiteralUndefined, IrType::default());
        b.emit_void(InstData::Branch { dest: t });

        b.set_insert_block(t);
        let v = b.emit_val(InstData::LiteralNumber(1.0), IrType::default());
        b.emit_void(InstData::Branch { dest: join });

        b.set_insert_block(h);
        let w = b.emit_val(
            InstData::BinaryOp {
                op: crate::inst::BinOp::Add,
                left: v,
                right: e0,
            },
            IrType::default(),
        );
        b.emit_void(InstData::Branch { dest: join });

        b.set_insert_block(join);
        let (_, result) = b.emit(
            InstData::Phi {
                entries: vec![(t, v), (h, w)],
            },
            IrType::default(),
        );
        b.emit_void(InstData::Return { value: result });

        m.func_mut(func).try_regions.push(TryRegion {
            try_blocks: vec![t],
            catches: vec![CatchHandler {
                type_idx: u32::MAX,
                handler_block: h,
            }],
        });

        let errs = verify_func(&m, func);
        assert!(
            errs.is_empty(),
            "exception-dispatch value flow must be exempt from CFG dominance: {errs:?}"
        );
    }

    #[test]
    fn verify_module_all_funcs() {
        let mut m = make_module();
        let f1 = IRBuilder::create_function(&mut m, "a", FunctionKind::Function, 0);
        {
            let mut b = IRBuilder::new(&mut m, f1);
            b.emit_void(InstData::Return { value: None });
        }
        let f2 = IRBuilder::create_function(&mut m, "b", FunctionKind::Function, 0);
        {
            let mut b = IRBuilder::new(&mut m, f2);
            b.emit_void(InstData::Return { value: None });
        }

        let errs = verify_module(&m);
        assert!(errs.is_empty());
    }
}
