//! Copy Propagation: eliminate trivial phis and identity operations —
//! the v0.2 port of v0.1 `opt::copyprop`.
//!
//! - Trivial phi: all incoming values are the same → replace with that value.
//!
//! v0.2 port note: phi entries key on full [`abcd_ir::Edge`]s (kind-qualified);
//! triviality is decided on the VALUEs alone, exactly as in v0.1 (a phi
//! whose normal and exceptional in-edges carry the same value is trivial
//! — and folding it is sound even for handler phis, since the folded
//! value equals every incoming value regardless of dispatch timing).

use std::collections::{HashMap, HashSet};

use abcd_ir::{BlockId, FuncId, InstId, Module, Op, ValueId};

use crate::FuncPass;
use crate::analysis::{replace_uses_map_in_func, resolve_subst};

/// The copy-propagation pass.
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
/// (or the phi itself), applying all substitutions in a single pass per round
/// (#29).
fn eliminate_trivial_phis(module: &mut Module, func: FuncId) -> bool {
    let Some(func_data) = module.func(func) else {
        return false;
    };
    let blocks: Vec<BlockId> = func_data.blocks.clone();
    let mut subst: HashMap<ValueId, ValueId> = HashMap::new();

    for bb in blocks {
        let phis: Vec<InstId> = module
            .block(bb)
            .map(|b| {
                b.insts
                    .iter()
                    .copied()
                    .take_while(|&id| module.inst(id).is_some_and(|i| i.op.is_phi()))
                    .collect()
            })
            .unwrap_or_default();
        let mut dead_phis: HashSet<InstId> = HashSet::new();
        for phi_id in phis {
            let result = match module.inst(phi_id).and_then(|i| i.result) {
                Some(v) => v,
                None => continue,
            };

            let Some(inst) = module.inst(phi_id) else {
                continue;
            };
            if let Op::Phi { entries } = &inst.op {
                let mut unique: Option<ValueId> = None;
                let mut is_trivial = true;

                for (_edge, val) in entries {
                    let resolved = resolve_subst(&subst, *val);
                    if resolved == result {
                        continue;
                    } // self-reference
                    match unique {
                        None => unique = Some(resolved),
                        Some(u) if u == resolved => {} // same value
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
                    subst.insert(result, replacement);
                    dead_phis.insert(phi_id);
                }
                // If unique is None, all entries are self-references (dead phi).
                // ADCE will clean it up (N28: that holds because the dead
                // phi's RESULT is unused — a live-result phi never reaches
                // this arm).
            }
        }
        if !dead_phis.is_empty()
            && let Some(block) = module.block_mut(bb)
        {
            block.insts.retain(|id| !dead_phis.contains(id));
        }
    }

    if subst.is_empty() {
        return false;
    }
    replace_uses_map_in_func(module, func, &subst);
    true
}
