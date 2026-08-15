//! Lowering: IR → bytecode.
//!
//! Entry point: [`lower_function`] takes a Module + FuncId and produces
//! a flat bytecode sequence with try blocks.

pub mod isel;
pub mod layout;
pub mod regalloc;

use std::collections::HashMap;

use abcd_isa::EntityId;

use crate::entity::{FuncId, StringId};
use crate::module::Module;

pub use self::layout::LayoutResult;
pub use self::regalloc::RegAlloc;

/// Errors that can occur during lowering.
#[derive(Debug, thiserror::Error)]
pub enum LowerError {
    #[error("function {0:?} has no blocks")]
    EmptyFunction(FuncId),
}

/// Lower a single IR function back to bytecodes.
pub fn lower_function(module: &Module, func_id: FuncId) -> Result<LayoutResult, LowerError> {
    let func = module.func(func_id);
    if func.blocks.is_empty() {
        return Err(LowerError::EmptyFunction(func_id));
    }

    // Build string→EntityId reverse map.
    let string_map = build_string_map(module);

    // Step 1: Register allocation.
    let alloc = regalloc::allocate(module, func_id);

    // Step 2: Compute RPO (reuse from regalloc).
    let rpo = regalloc::compute_rpo(module, func_id);

    // Step 3: Instruction selection.
    let isel_result = isel::select(module, func_id, &alloc, &rpo, &string_map);

    // Step 4: Layout and jump resolution.
    let result = layout::layout(module, func_id, &isel_result, &alloc, &rpo);

    Ok(result)
}

/// Build a mapping from StringId → EntityId for the output file.
/// For now, StringId.0 == EntityId.0 (identity mapping).
fn build_string_map(module: &Module) -> HashMap<StringId, EntityId> {
    let mut map = HashMap::new();
    for i in 0..module.strings.len() {
        let sid = StringId::from_index(i);
        map.insert(sid, EntityId(sid.0));
    }
    map
}
