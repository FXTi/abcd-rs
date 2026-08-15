//! Optimization pass infrastructure and pipeline.

pub mod copyprop;
pub mod dce;
pub mod inline;
pub mod peephole;
pub mod sccp;

use crate::entity::FuncId;
use crate::module::Module;

/// A function-level optimization pass.
pub trait FuncPass {
    /// Run the pass on `func` within `module`.
    /// Returns `true` if the IR was modified.
    fn run(&self, module: &mut Module, func: FuncId) -> bool;
}

/// Run the full optimization pipeline on a single function.
/// Pipeline: peephole → sccp → dce → copyprop → peephole → dce
/// Returns `true` if any pass modified the IR.
pub fn optimize_func(module: &mut Module, func: FuncId) -> bool {
    let mut changed = false;

    // Round 1: peephole → sccp → adce + cfg simplify → copyprop
    changed |= peephole::Peephole.run(module, func);
    changed |= sccp::Sccp.run(module, func);
    changed |= dce::Adce.run(module, func);
    changed |= dce::CfgSimplify.run(module, func);
    changed |= copyprop::CopyProp.run(module, func);

    // Round 2: peephole → adce + cfg simplify (cleanup)
    changed |= peephole::Peephole.run(module, func);
    changed |= dce::Adce.run(module, func);
    changed |= dce::CfgSimplify.run(module, func);

    changed
}

/// Run the optimization pipeline on all functions in the module.
pub fn optimize_module(module: &mut Module) -> bool {
    let func_count = module.functions.len();
    let mut changed = false;
    for i in 0..func_count {
        let func_id = FuncId::from_index(i);
        if module.func(func_id).blocks.is_empty() {
            continue;
        }
        changed |= optimize_func(module, func_id);
    }
    changed
}
