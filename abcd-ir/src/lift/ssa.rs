//! Braun SSA construction: register/accumulator → SSA values.
//!
//! Implements the algorithm from "Simple and Efficient Construction of SSA Form"
//! (Braun et al., 2013). As bytecodes are translated, register/accumulator reads
//! are resolved to SSA values on-the-fly, inserting phi nodes as needed.

use std::collections::HashMap;

use abcd_isa::Reg;

use crate::entity::{Block, Value};
use crate::inst::InstData;
use crate::module::Module;
use crate::types::IrType;

/// Identifies a virtual location: either the accumulator or a register.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RegOrAcc {
    Acc,
    Reg(u16),
}

impl From<Reg> for RegOrAcc {
    fn from(r: Reg) -> Self {
        RegOrAcc::Reg(r.0)
    }
}

/// Per-block SSA state: maps each virtual location to its current SSA value.
type BlockDefs = HashMap<RegOrAcc, Value>;

/// SSA construction context using the Braun algorithm.
///
/// Maintains per-block definition maps and handles recursive phi insertion
/// when a value is read that hasn't been defined in the current block.
pub struct SsaBuilder {
    /// Per-block definition maps.
    defs: HashMap<Block, BlockDefs>,
    /// Tracks which blocks are "sealed" (all predecessors known).
    sealed: HashMap<Block, bool>,
    /// Incomplete phis: block → [(location, phi_value)] for unsealed blocks.
    incomplete_phis: HashMap<Block, Vec<(RegOrAcc, Value)>>,
}

impl SsaBuilder {
    pub fn new() -> Self {
        Self {
            defs: HashMap::new(),
            sealed: HashMap::new(),
            incomplete_phis: HashMap::new(),
        }
    }

    /// Record a definition: `loc` is defined as `val` in `block`.
    pub fn write_variable(&mut self, loc: RegOrAcc, block: Block, val: Value) {
        self.defs.entry(block).or_default().insert(loc, val);
    }

    /// Read a variable in `block`. If not locally defined, recursively searches
    /// predecessors and inserts phi nodes as needed.
    pub fn read_variable(&mut self, loc: RegOrAcc, block: Block, module: &mut Module) -> Value {
        if let Some(val) = self.defs.get(&block).and_then(|m| m.get(&loc)).copied() {
            return val;
        }
        self.read_variable_recursive(loc, block, module)
    }

    fn read_variable_recursive(
        &mut self,
        loc: RegOrAcc,
        block: Block,
        module: &mut Module,
    ) -> Value {
        let preds = module.block(block).preds.clone();
        let val = if !self.is_sealed(block) {
            // Block not sealed yet — create an incomplete phi.
            let phi_val = self.emit_empty_phi(block, module);
            self.incomplete_phis
                .entry(block)
                .or_default()
                .push((loc, phi_val));
            phi_val
        } else if preds.len() == 1 {
            // Single predecessor — no phi needed, just recurse.
            self.read_variable(loc, preds[0], module)
        } else {
            // Multiple predecessors — insert a phi and fill it.
            let phi_val = self.emit_empty_phi(block, module);
            // Write before recursing to break cycles.
            self.write_variable(loc, block, phi_val);
            self.add_phi_operands(loc, block, phi_val, module)
        };
        self.write_variable(loc, block, val);
        val
    }

    /// Mark a block as sealed (all predecessors are known).
    /// Completes any incomplete phis.
    pub fn seal_block(&mut self, block: Block, module: &mut Module) {
        self.sealed.insert(block, true);
        if let Some(incomplete) = self.incomplete_phis.remove(&block) {
            for (loc, phi_val) in incomplete {
                self.add_phi_operands(loc, block, phi_val, module);
            }
        }
    }

    pub fn is_sealed(&self, block: Block) -> bool {
        self.sealed.get(&block).copied().unwrap_or(false)
    }

    /// Emit an empty phi node in `block` and return its result value.
    fn emit_empty_phi(&self, block: Block, module: &mut Module) -> Value {
        use crate::entity::Inst;
        use crate::module::{InstNode, ValueData, ValueDef};

        let inst_id = Inst::from_index(module.insts.len());
        let val = Value::from_index(module.values.len());
        module.values.push(ValueData {
            def: ValueDef::Inst(inst_id),
            ty: IrType::default(),
        });
        module.insts.push(InstNode {
            data: InstData::Phi { entries: vec![] },
            result: Some(val),
            result_type: IrType::default(),
            block,
            loc: None,
        });
        module.block_mut(block).phis.push(inst_id);
        val
    }

    /// Fill phi operands by reading the variable from each predecessor.
    fn add_phi_operands(
        &mut self,
        loc: RegOrAcc,
        block: Block,
        phi_val: Value,
        module: &mut Module,
    ) -> Value {
        let preds = module.block(block).preds.clone();
        let mut entries = Vec::with_capacity(preds.len());
        for pred in &preds {
            let val = self.read_variable(loc, *pred, module);
            entries.push((*pred, val));
        }

        // Find the phi instruction for this value and update its entries.
        let phi_inst = match module.value(phi_val).def {
            crate::module::ValueDef::Inst(inst) => inst,
            _ => unreachable!("phi_val must be an instruction result"),
        };
        module.inst_mut(phi_inst).data = InstData::Phi { entries };

        self.try_remove_trivial_phi(phi_val, phi_inst, module)
    }

    /// If a phi is trivial (all operands are the same value or the phi itself),
    /// remove it and replace uses with the single value.
    fn try_remove_trivial_phi(
        &mut self,
        phi_val: Value,
        phi_inst: crate::entity::Inst,
        module: &mut Module,
    ) -> Value {
        let entries = match &module.inst(phi_inst).data {
            InstData::Phi { entries } => entries.clone(),
            _ => return phi_val,
        };

        let mut same: Option<Value> = None;
        for (_, val) in &entries {
            if *val == phi_val {
                continue; // self-reference
            }
            if let Some(s) = same {
                if *val == s {
                    continue; // same as existing
                }
                return phi_val; // non-trivial: at least two distinct values
            }
            same = Some(*val);
        }

        // If same is None, all operands are self-references (unreachable in practice).
        let replacement = match same {
            Some(v) => v,
            None => return phi_val,
        };

        // Replace all uses of phi_val with replacement in the definition maps.
        for block_defs in self.defs.values_mut() {
            for val in block_defs.values_mut() {
                if *val == phi_val {
                    *val = replacement;
                }
            }
        }

        replacement
    }
}
