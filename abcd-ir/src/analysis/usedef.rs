//! Use-def chains: maps each Value to the set of instructions that use it.

use std::collections::HashMap;

use crate::entity::{FuncId, Inst, Value};
use crate::module::Module;

use super::inst_operands;

/// Use-def map: `Value → Vec<Inst>` (instructions that use the value).
pub struct UseDef {
    uses: HashMap<Value, Vec<Inst>>,
}

impl UseDef {
    /// Build use-def chains by scanning all instructions in `func`.
    pub fn build(module: &Module, func_id: FuncId) -> Self {
        let func = module.func(func_id);
        let mut uses: HashMap<Value, Vec<Inst>> = HashMap::new();

        for &bb in &func.blocks {
            let block = module.block(bb);
            for &inst_id in block.phis.iter().chain(block.insts.iter()) {
                let data = &module.inst(inst_id).data;
                for val in inst_operands(data) {
                    uses.entry(val).or_default().push(inst_id);
                }
            }
        }

        Self { uses }
    }

    /// All instructions that use `val`.
    pub fn uses_of(&self, val: Value) -> &[Inst] {
        self.uses.get(&val).map_or(&[], |v| v.as_slice())
    }

    /// Whether `val` has any uses.
    pub fn is_used(&self, val: Value) -> bool {
        self.uses.get(&val).map_or(false, |v| !v.is_empty())
    }

    /// Number of uses of `val`.
    pub fn use_count(&self, val: Value) -> usize {
        self.uses.get(&val).map_or(0, |v| v.len())
    }
}
