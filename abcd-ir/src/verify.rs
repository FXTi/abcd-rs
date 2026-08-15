//! IR well-formedness verification.
//!
//! Checks structural invariants that must hold for valid IR:
//! - Every block ends with a terminator
//! - Phi nodes only appear at the beginning of blocks
//! - Phi entry count matches predecessor count
//! - Entry block has no predecessors
//! - Values used by instructions are defined (exist in the module)

use std::collections::HashSet;
use std::fmt;

use crate::analysis;
use crate::entity::{Block, FuncId, Inst, Value};
use crate::inst::InstData;
use crate::module::Module;

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

    // Collect all values defined in this function.
    let mut defined_values: HashSet<Value> = HashSet::new();
    for &bb in &func.blocks {
        let block = module.block(bb);
        for &inst_id in block.phis.iter().chain(block.insts.iter()) {
            if let Some(val) = module.inst(inst_id).result {
                defined_values.insert(val);
            }
        }
    }
    // Function parameters are also defined values.
    for (vi, vd) in module.values.iter().enumerate() {
        if let crate::module::ValueDef::FuncParam(_) = vd.def {
            defined_values.insert(Value::from_index(vi));
        }
    }

    let err = |block: Option<Block>, inst: Option<Inst>, msg: String| VerifyError {
        func: func_id,
        block,
        inst,
        message: msg,
    };

    // Entry block has no predecessors.
    let entry = func.entry_block;
    if !module.block(entry).preds.is_empty() {
        errors.push(err(
            Some(entry),
            None,
            "entry block must have no predecessors".into(),
        ));
    }

    for &bb in &func.blocks {
        let block = module.block(bb);

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
                for (entry_bb, _) in entries {
                    if !pred_set.contains(entry_bb) {
                        errors.push(err(
                            Some(bb),
                            Some(inst_id),
                            format!("phi references {entry_bb} which is not a predecessor"),
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
    }

    errors
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
    use crate::module::Module;
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
