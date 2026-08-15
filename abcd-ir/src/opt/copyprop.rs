//! Copy Propagation: eliminate trivial phis and identity operations.
//!
//! - Trivial phi: all incoming values are the same → replace with that value.
//! - Identity ops: operations that just pass through a value unchanged.

use crate::analysis;
use crate::entity::{Block, FuncId, Inst, Value};
use crate::inst::InstData;
use crate::module::Module;

use super::FuncPass;

pub struct CopyProp;

impl FuncPass for CopyProp {
    fn run(&self, module: &mut Module, func: FuncId) -> bool {
        let mut changed = false;
        // Iterate until no more changes (trivial phi removal can expose more).
        loop {
            let mut round_changed = false;
            round_changed |= eliminate_trivial_phis(module, func);
            if !round_changed {
                break;
            }
            changed = true;
        }
        changed
    }
}

/// Find and eliminate trivial phis where all incoming values are the same
/// (or the phi itself). Replace all uses of the phi result with that value.
fn eliminate_trivial_phis(module: &mut Module, func: FuncId) -> bool {
    let mut changed = false;
    let blocks: Vec<Block> = module.func(func).blocks.clone();

    for bb in blocks {
        let phis: Vec<Inst> = module.block(bb).phis.clone();
        for phi_id in phis {
            let result = match module.inst(phi_id).result {
                Some(v) => v,
                None => continue,
            };

            if let InstData::Phi { entries } = &module.inst(phi_id).data {
                // Find the unique non-self value.
                let mut unique: Option<Value> = None;
                let mut is_trivial = true;

                for &(_pred, val) in entries {
                    if val == result {
                        continue;
                    } // self-reference
                    match unique {
                        None => unique = Some(val),
                        Some(u) if u == val => {} // same value
                        _ => {
                            is_trivial = false;
                            break;
                        }
                    }
                }

                if !is_trivial {
                    continue;
                }

                if let Some(replacement) = unique {
                    // Replace all uses of `result` with `replacement`.
                    analysis::replace_uses_in_func(module, func, result, replacement);
                    changed = true;
                }
                // If unique is None, all entries are self-references (dead phi).
                // ADCE will clean it up.
            }
        }
    }

    changed
}
