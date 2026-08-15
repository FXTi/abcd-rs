//! Function inlining pass.
//!
//! This pass is NOT enabled in the default optimization pipeline.
//! To use it, call `Inline::new(threshold).run(module, func)` manually.
//!
//! The inliner identifies call sites where the callee is a known function
//! defined in the same module, checks if it's small enough to inline,
//! and replaces the call with a copy of the callee's body.

use std::collections::HashMap;

use crate::entity::{Block, FuncId, Inst, Value};
use crate::inst::{CallKind, InstData};
use crate::module::{BasicBlockData, InstNode, Module, ValueData, ValueDef};
use crate::types::IrType;

use super::FuncPass;

/// Function inlining pass with configurable size threshold.
///
/// Not included in the default pipeline. Enable manually:
/// ```ignore
/// use abcd_ir::opt::inline::Inline;
/// use abcd_ir::opt::FuncPass;
/// Inline::new(50).run(&mut module, func_id);
/// ```
pub struct Inline {
    /// Maximum number of instructions in a callee to be eligible for inlining.
    max_inst_count: usize,
}

impl Inline {
    pub fn new(max_inst_count: usize) -> Self {
        Self { max_inst_count }
    }
}

impl FuncPass for Inline {
    fn run(&self, module: &mut Module, func: FuncId) -> bool {
        let mut changed = false;

        // Collect call sites: (caller_block, call_inst, callee_func_id).
        let call_sites = find_inline_candidates(module, func, self.max_inst_count);

        for site in call_sites {
            if inline_call_site(module, func, &site) {
                changed = true;
            }
        }

        changed
    }
}

/// A candidate call site for inlining.
#[allow(dead_code)]
struct InlineSite {
    /// The block containing the call instruction.
    caller_block: Block,
    /// The call instruction.
    call_inst: Inst,
    /// The callee function to inline.
    callee: FuncId,
    /// The call's result value (if any).
    result: Option<Value>,
    /// Arguments passed to the call (excluding callee).
    args: Vec<Value>,
}

/// Find call sites eligible for inlining.
fn find_inline_candidates(module: &Module, func: FuncId, max_inst_count: usize) -> Vec<InlineSite> {
    let mut sites = Vec::new();
    let blocks: Vec<Block> = module.func(func).blocks.clone();

    for bb in blocks {
        let insts: Vec<Inst> = module.block(bb).insts.clone();
        for inst_id in insts {
            let node = module.inst(inst_id);
            if let InstData::Call {
                kind: CallKind::Call,
                callee,
                args,
            } = &node.data
            {
                // Check if callee is a known DefineFunc in this module.
                if let Some(callee_func) = resolve_callee(module, *callee) {
                    // Check size threshold.
                    let callee_size = count_instructions(module, callee_func);
                    if callee_size <= max_inst_count && callee_func != func {
                        sites.push(InlineSite {
                            caller_block: bb,
                            call_inst: inst_id,
                            callee: callee_func,
                            result: node.result,
                            args: args.clone(),
                        });
                    }
                }
            }
        }
    }

    sites
}

/// Try to resolve a callee Value to a FuncId.
///
/// Looks for the pattern: callee is defined by DefineFunc { method_id, .. }
/// and method_id maps to a function in the module.
fn resolve_callee(module: &Module, callee: Value) -> Option<FuncId> {
    let vd = module.value(callee);
    let inst = match vd.def {
        ValueDef::Inst(i) => i,
        _ => return None,
    };

    if let InstData::DefineFunc { method_id, .. } = &module.inst(inst).data {
        let name = module.strings.get(*method_id);
        // Search for a function with this name.
        for (i, f) in module.functions.iter().enumerate() {
            if module.strings.get(f.name) == name {
                return Some(FuncId::from_index(i));
            }
        }
    }
    None
}

/// Count the total number of non-phi instructions in a function.
fn count_instructions(module: &Module, func: FuncId) -> usize {
    let f = module.func(func);
    f.blocks
        .iter()
        .map(|&bb| module.block(bb).insts.len())
        .sum()
}

/// Inline a single call site. Returns true if successful.
fn inline_call_site(module: &mut Module, caller: FuncId, site: &InlineSite) -> bool {
    let callee = module.func(site.callee);
    if callee.blocks.is_empty() {
        return false;
    }

    let callee_blocks: Vec<Block> = callee.blocks.clone();
    let callee_entry = callee.entry_block;

    // Step 1: Clone callee blocks into the module, building remap tables.
    let mut block_remap: HashMap<Block, Block> = HashMap::new();
    let mut value_remap: HashMap<Value, Value> = HashMap::new();
    let mut inst_remap: HashMap<Inst, Inst> = HashMap::new();

    // Map callee parameters to call arguments.
    // In our IR, parameters are represented as values defined by the callee.
    // We map them via the argument list.
    // Note: this is a simplified mapping — real parameter passing depends on
    // how the callee reads its parameters.

    // Create new blocks for the inlined copy.
    for &bb in &callee_blocks {
        let new_bb = Block::from_index(module.blocks.len());
        module.blocks.push(BasicBlockData::new());
        block_remap.insert(bb, new_bb);
        module.func_mut(caller).blocks.push(new_bb);
    }

    // Clone instructions, remapping values and blocks.
    for &bb in &callee_blocks {
        let new_bb = block_remap[&bb];
        let orig_block = module.block(bb);
        let phis: Vec<Inst> = orig_block.phis.clone();
        let insts: Vec<Inst> = orig_block.insts.clone();

        // Clone phis.
        for phi_id in phis {
            clone_inst(
                module,
                phi_id,
                new_bb,
                &mut block_remap,
                &mut value_remap,
                &mut inst_remap,
            );
        }

        // Clone non-phi instructions.
        for inst_id in insts {
            let data = &module.inst(inst_id).data;

            // Replace Return with a branch or value assignment.
            if let InstData::Return { value } = data {
                // If the call has a result, map the return value to it.
                if let (Some(call_result), Some(ret_val)) = (site.result, value) {
                    let remapped = remap_value(*ret_val, &value_remap);
                    value_remap.insert(call_result, remapped);
                }
                // Don't clone the return — it will be replaced by a branch
                // to the continuation block.
                continue;
            }

            clone_inst(
                module,
                inst_id,
                new_bb,
                &mut block_remap,
                &mut value_remap,
                &mut inst_remap,
            );
        }
    }

    // Step 2: Remap all value references in cloned instructions.
    let cloned_blocks: Vec<Block> = callee_blocks.iter().map(|bb| block_remap[bb]).collect();
    for &bb in &cloned_blocks {
        let block = module.block(bb);
        let all_insts: Vec<Inst> = block
            .phis
            .iter()
            .chain(block.insts.iter())
            .copied()
            .collect();
        for inst_id in all_insts {
            remap_inst_operands(module, inst_id, &value_remap, &block_remap);
        }
    }

    // Step 3: Split the caller block at the call site.
    // - caller_block: instructions before the call + branch to inlined entry
    // - continuation_block: instructions after the call
    let inlined_entry = block_remap[&callee_entry];

    // Find the call instruction position in the caller block.
    let caller_insts: Vec<Inst> = module.block(site.caller_block).insts.clone();
    let call_pos = caller_insts.iter().position(|&i| i == site.call_inst);

    if let Some(pos) = call_pos {
        // Create continuation block for instructions after the call.
        let cont_block = Block::from_index(module.blocks.len());
        module.blocks.push(BasicBlockData::new());
        module.func_mut(caller).blocks.push(cont_block);

        // Move instructions after the call to the continuation block.
        let after_call: Vec<Inst> = caller_insts[pos + 1..].to_vec();
        module.block_mut(cont_block).insts = after_call;
        module.block_mut(cont_block).preds.push(site.caller_block);

        // Truncate caller block at the call, replace call with branch to inlined entry.
        module.block_mut(site.caller_block).insts.truncate(pos);

        // Create a branch to the inlined entry.
        let branch_inst = Inst::from_index(module.insts.len());
        module.insts.push(InstNode {
            data: InstData::Branch {
                dest: inlined_entry,
            },
            result: None,
            result_type: IrType::default(),
            block: site.caller_block,
            loc: None,
        });
        module.block_mut(site.caller_block).insts.push(branch_inst);

        // Add branches from inlined return points to continuation block.
        for &bb in &cloned_blocks {
            let block_insts = module.block(bb).insts.clone();
            // If the block has no terminator (return was stripped), add branch to cont.
            let has_terminator = block_insts
                .last()
                .map(|&i| module.inst(i).data.is_terminator())
                .unwrap_or(false);
            if !has_terminator {
                let br = Inst::from_index(module.insts.len());
                module.insts.push(InstNode {
                    data: InstData::Branch { dest: cont_block },
                    result: None,
                    result_type: IrType::default(),
                    block: bb,
                    loc: None,
                });
                module.block_mut(bb).insts.push(br);
            }
        }

        // Set predecessor for inlined entry.
        module
            .block_mut(inlined_entry)
            .preds
            .push(site.caller_block);

        return true;
    }

    false
}

/// Clone a single instruction into a new block, updating remap tables.
fn clone_inst(
    module: &mut Module,
    orig_inst: Inst,
    new_block: Block,
    _block_remap: &mut HashMap<Block, Block>,
    value_remap: &mut HashMap<Value, Value>,
    inst_remap: &mut HashMap<Inst, Inst>,
) {
    let orig = module.inst(orig_inst);
    let data = orig.data.clone();
    let has_result = data.has_result();
    let is_phi = data.is_phi();
    let loc = orig.loc;
    let orig_result = orig.result;

    let new_inst = Inst::from_index(module.insts.len());
    let result = if has_result {
        let new_val = Value::from_index(module.values.len());
        module.values.push(ValueData {
            def: ValueDef::Inst(new_inst),
            ty: IrType::default(),
        });
        // Map original result to new result.
        if let Some(orig_res) = orig_result {
            value_remap.insert(orig_res, new_val);
        }
        Some(new_val)
    } else {
        None
    };

    module.insts.push(InstNode {
        data,
        result,
        result_type: IrType::default(),
        block: new_block,
        loc,
    });

    if is_phi {
        module.block_mut(new_block).phis.push(new_inst);
    } else {
        module.block_mut(new_block).insts.push(new_inst);
    }

    inst_remap.insert(orig_inst, new_inst);
}

/// Remap value and block references in an instruction's operands.
fn remap_inst_operands(
    module: &mut Module,
    inst_id: Inst,
    value_remap: &HashMap<Value, Value>,
    block_remap: &HashMap<Block, Block>,
) {
    // Remap value operands.
    let data = &mut module.insts[inst_id.index()].data;
    for v in data.operands_mut() {
        if let Some(&new_v) = value_remap.get(v) {
            *v = new_v;
        }
    }

    // Remap block references in terminators and phis.
    let data = &mut module.insts[inst_id.index()].data;
    match data {
        InstData::Branch { dest } => {
            if let Some(&new_bb) = block_remap.get(dest) {
                *dest = new_bb;
            }
        }
        InstData::CondBranch {
            true_dest,
            false_dest,
            ..
        } => {
            if let Some(&new_bb) = block_remap.get(true_dest) {
                *true_dest = new_bb;
            }
            if let Some(&new_bb) = block_remap.get(false_dest) {
                *false_dest = new_bb;
            }
        }
        InstData::Phi { entries } => {
            for (bb, _) in entries.iter_mut() {
                if let Some(&new_bb) = block_remap.get(bb) {
                    *bb = new_bb;
                }
            }
        }
        _ => {}
    }
}

/// Remap a value through the remap table, returning the original if not found.
fn remap_value(val: Value, remap: &HashMap<Value, Value>) -> Value {
    remap.get(&val).copied().unwrap_or(val)
}
