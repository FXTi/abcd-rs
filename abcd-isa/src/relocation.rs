use abcd_isa_sys::{self as sys, EntityId};

/// Errors when rewriting an entity operand without changing instruction size.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum RelocationError {
    #[error("invalid or truncated instruction")]
    InvalidInstruction,
    #[error("instruction has no entity operand {0}")]
    MissingOperand(u32),
    #[error("entity id {0} does not fit the encoded operand")]
    IdOutOfRange(u32),
}

/// Rewrite an entity ID in the first instruction of `bytes` using the
/// upstream instruction updater. Operand ordinals count IDs, not registers
/// or immediates. An error leaves the buffer unchanged.
pub fn relocate_entity_id(
    bytes: &mut [u8],
    operand: u32,
    id: EntityId,
) -> Result<(), RelocationError> {
    // SAFETY: pure ISA query.
    let prefix_min = unsafe { sys::isa_min_prefix_opcode() };
    if bytes.is_empty() || (bytes[0] >= prefix_min && bytes.len() < 2) {
        return Err(RelocationError::InvalidInstruction);
    }
    // SAFETY: at least the entire opcode is readable (checked above).
    let opcode = unsafe { sys::isa_get_opcode(bytes.as_ptr()) };
    let size = unsafe { sys::isa_get_size_by_opcode(opcode) };
    if size == 0 || size > bytes.len() {
        return Err(RelocationError::InvalidInstruction);
    }
    // SAFETY: the opcode is valid and the instruction is wholly in bounds.
    let format = unsafe { sys::isa_get_format(opcode) };
    if unsafe { sys::isa_has_id(format, operand as usize) } == 0 {
        return Err(RelocationError::MissingOperand(operand));
    }
    let mut patched = bytes[..size].to_vec();
    // SAFETY: valid instruction, valid ID ordinal, and an owned writable
    // buffer. The upstream updater keeps the encoded format and size.
    unsafe { sys::isa_update_id(patched.as_mut_ptr(), id.0, operand) };
    if unsafe { sys::isa_get_id(patched.as_ptr(), operand as usize) } != id.0 {
        return Err(RelocationError::IdOutOfRange(id.0));
    }
    bytes[..size].copy_from_slice(&patched);
    Ok(())
}
