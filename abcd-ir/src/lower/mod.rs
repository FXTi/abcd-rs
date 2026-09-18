//! Lowering: IR → bytecode.
//!
//! Entry point: [`lower_function`] takes a Module + FuncId and produces
//! a flat bytecode sequence with try blocks.

pub mod copy_resolve;
pub mod isel;
pub mod layout;
pub mod method_body;
pub mod regalloc;

use std::collections::HashMap;

use abcd_isa::{EntityId, EntityKind};

use crate::entity::{FuncId, StringId, Value};
use crate::module::Module;

pub use self::isel::EntityTrace;
pub use self::layout::LayoutResult;
pub use self::method_body::to_method_body;
pub use self::regalloc::RegAlloc;

/// Errors that can occur during lowering.
#[derive(Debug, thiserror::Error)]
pub enum LowerError {
    #[error("function {0:?} has no blocks")]
    EmptyFunction(FuncId),
    #[error("register allocation overflow in function {0:?}")]
    RegisterOverflow(FuncId),
    #[error("unsupported instruction in function {func:?}: {message}")]
    UnsupportedInstruction { func: FuncId, message: String },
    #[error(
        "function {0:?} has a slot-level phi copy cycle but no reserved copy temporary register"
    )]
    MissingCopyTemp(FuncId),
    #[error("function {func:?} uses value {value:?} that register allocation never colored")]
    UnallocatedOperand { func: FuncId, value: Value },
    #[error(
        "function {func:?} has parameter {value:?} colored Acc; parameters need a register home \
         for the copy-in prologue"
    )]
    AccColoredParam { func: FuncId, value: Value },
    #[error(
        "function {0:?} has an accumulator-colored register operand but no reserved spill register"
    )]
    MissingSpillSlot(FuncId),
    #[error(
        "function {func:?} has an instruction with two distinct accumulator-colored operands \
         ({a:?} and {b:?}); the interference invariant guarantees at most one"
    )]
    MultipleAccOperands { func: FuncId, a: Value, b: Value },
    #[error(
        "function {func:?} has a {kind:?} entity operand with raw value {raw:#x} that cannot \
         be traced to a source-file offset recorded by lift"
    )]
    UntraceableEntity {
        func: FuncId,
        kind: EntityKind,
        raw: u32,
    },
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
    let alloc =
        regalloc::allocate(module, func_id).map_err(|_| LowerError::RegisterOverflow(func_id))?;

    // Step 2: Compute RPO (reuse from regalloc).
    let rpo = regalloc::compute_rpo(module, func_id);

    // Step 3: Instruction selection.
    let isel_result = isel::select(module, func_id, &alloc, &rpo, &string_map)?;
    if let Some(message) = isel_result.unsupported.clone() {
        return Err(LowerError::UnsupportedInstruction {
            func: func_id,
            message,
        });
    }

    // Step 4: Layout and jump resolution.
    let result = layout::layout(module, func_id, &isel_result, &alloc, &rpo)?;

    Ok(result)
}

/// Build a mapping from StringId → EntityId for the output file.
/// For now, StringId.0 == EntityId.0 (identity mapping).
fn build_string_map(module: &Module) -> HashMap<StringId, EntityId> {
    let mut map = HashMap::new();
    for i in 0..module.strings.len() {
        let sid = StringId::from_index(i);
        map.insert(
            sid,
            module
                .string_entities
                .get(&sid)
                .copied()
                .unwrap_or(EntityId(sid.0)),
        );
    }
    map
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builder::IRBuilder;
    use crate::inst::InstData;
    use crate::module::Module;
    use abcd_file::{FileType, FunctionKind, Version};

    #[test]
    fn rejects_dummy_register_lowering() {
        let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
        let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
        let mut builder = IRBuilder::new(&mut module, func);
        let name = builder.intern("constant");
        builder.emit_void(InstData::ThrowConstAssignment { name });
        builder.emit_void(InstData::Return { value: None });
        assert!(matches!(
            lower_function(&module, func),
            Err(LowerError::UnsupportedInstruction { .. })
        ));
    }
}
