//! Copy Propagation: eliminate trivial phis and `Op::Mov` chains across SSA
//! blocks (`design/ir.md`, `#93`).
//!
//! - **Trivial phi**: all non-self incoming values resolve to the same
//!   [`ValueId`] → substitute that value across the function and drop the phi.
//!   Phi entries key on full kind-qualified [`abcd_ir::Edge`]s, while
//!   triviality is decided on the incoming values alone: a phi whose normal and
//!   exceptional in-edges carry the same value is trivial and sound to fold
//!   even in catch handlers.
//! - **Pure copy (`Op::Mov { src }`)**: resolves transitive `Mov` chains
//!   iteratively with an explicit cycle guard and substitutes `src` across all
//!   instruction operands (`Op::for_each_operand_mut`), skipping malformed
//!   dangling/foreign values or differing static ArkTS widths.

use std::collections::{HashMap, HashSet};

use abcd_ir::{BlockId, FuncId, InstId, Module, Op, Ty, ValueId};

use crate::FuncPass;
use crate::const_eval::{prune_func_debug_data, replace_uses_map_in_func, resolve_subst};

/// The copy-propagation pass.
pub struct CopyProp;

impl FuncPass for CopyProp {
    fn run(&self, module: &mut Module, func: FuncId) -> bool {
        let mut changed = false;
        loop {
            if !propagate_copies_and_phis(module, func) {
                break;
            }
            changed = true;
        }
        if changed {
            let _ = prune_func_debug_data(module, func);
        }
        changed
    }
}

/// Collect all valid `ValueId`s owned by `func` so `Op::Mov` copy propagation
/// never substitutes a dangling or foreign `ValueId` on unverified IR.
fn collect_owned_values(module: &Module, func: FuncId) -> HashSet<ValueId> {
    let Some(func_data) = module.func(func) else {
        return HashSet::new();
    };
    let mut owned = HashSet::new();
    for &v in func_data
        .params
        .iter()
        .chain(func_data.frame_init_consts.iter())
    {
        if module.value(v).is_some() {
            owned.insert(v);
        }
    }
    for region in &func_data.try_regions {
        for catch in &region.catches {
            if module.value(catch.exception).is_some() {
                owned.insert(catch.exception);
            }
        }
    }
    for &bb in &func_data.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &iid in &block.insts {
            if let Some(res) = module.inst(iid).and_then(|i| i.result)
                && module.value(res).is_some()
            {
                owned.insert(res);
            }
        }
    }
    owned
}

/// Find and eliminate trivial `Op::Phi`s and `Op::Mov` copies in one batched
/// substitution pass (`#29`, `#93`).
fn propagate_copies_and_phis(module: &mut Module, func: FuncId) -> bool {
    let Some(func_data) = module.func(func) else {
        return false;
    };
    let blocks: Vec<BlockId> = func_data.blocks.clone();
    let owned_values = collect_owned_values(module, func);
    let mut subst: HashMap<ValueId, ValueId> = HashMap::new();

    for bb in blocks {
        let insts: Vec<InstId> = module
            .block(bb)
            .map(|b| b.insts.clone())
            .unwrap_or_default();
        let mut dead_insts: HashSet<InstId> = HashSet::new();

        for inst_id in insts {
            let Some(inst) = module.inst(inst_id) else {
                continue;
            };
            let Some(result) = inst.result else {
                continue;
            };

            match &inst.op {
                Op::Phi { entries } => {
                    let mut unique: Option<ValueId> = None;
                    let mut is_trivial = true;
                    for (_edge, val) in entries {
                        let resolved = resolve_subst(&subst, *val);
                        if resolved == result {
                            continue;
                        }
                        match unique {
                            None => unique = Some(resolved),
                            Some(u) if u == resolved => {}
                            _ => {
                                is_trivial = false;
                                break;
                            }
                        }
                    }
                    if is_trivial
                        && let Some(replacement) = unique
                        && owned_values.contains(&replacement)
                    {
                        subst.insert(result, replacement);
                        dead_insts.insert(inst_id);
                    }
                }
                Op::Mov { src } => {
                    let resolved = resolve_subst(&subst, *src);
                    if resolved == result || !owned_values.contains(&resolved) {
                        continue;
                    }
                    let compatible_ty = match (
                        module.value(result).map(|v| &v.ty),
                        module.value(resolved).map(|v| &v.ty),
                    ) {
                        (Some(Ty::Static(a)), Some(Ty::Static(b))) => a == b,
                        (Some(_), Some(_)) => true,
                        _ => false,
                    };
                    if compatible_ty {
                        subst.insert(result, resolved);
                        dead_insts.insert(inst_id);
                    }
                }
                _ => {}
            }
        }

        if !dead_insts.is_empty()
            && let Some(block) = module.block_mut(bb)
        {
            block.insts.retain(|id| !dead_insts.contains(id));
        }
    }

    if subst.is_empty() {
        return false;
    }
    replace_uses_map_in_func(module, func, &subst);
    true
}
