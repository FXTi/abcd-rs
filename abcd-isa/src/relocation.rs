use abcd_isa_sys::{EntityId, ModernEntitySlotFault, modern_entity_id_slot};

/// Errors when rewriting an entity operand without changing instruction size.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum RelocationError {
    /// The byte slice is empty, starts with an unassigned opcode, or is truncated.
    #[error("invalid or truncated instruction")]
    InvalidInstruction,
    /// The instruction format does not carry an entity-ID operand at ordinal `{0}`.
    #[error("instruction has no entity operand {0}")]
    MissingOperand(u32),
    /// The replacement entity ID `{0}` exceeds the encoded operand's bit width.
    #[error("entity id {0} does not fit the encoded operand")]
    IdOutOfRange(u32),
}

/// Rewrite an entity ID in the first instruction of `bytes` in place without
/// changing instruction size or allocating. Operand ordinals count IDs, not
/// registers or immediates. An error leaves `bytes` unchanged.
pub fn relocate_entity_id(
    bytes: &mut [u8],
    operand: u32,
    id: EntityId,
) -> Result<(), RelocationError> {
    let (byte_off, byte_width) =
        modern_entity_id_slot(bytes, operand).map_err(|fault| match fault {
            ModernEntitySlotFault::InvalidInstruction => RelocationError::InvalidInstruction,
            ModernEntitySlotFault::MissingOperand => RelocationError::MissingOperand(operand),
        })?;

    match byte_width {
        1 => {
            let Ok(v) = u8::try_from(id.0) else {
                return Err(RelocationError::IdOutOfRange(id.0));
            };
            bytes[byte_off] = v;
        }
        2 => {
            let Ok(v) = u16::try_from(id.0) else {
                return Err(RelocationError::IdOutOfRange(id.0));
            };
            bytes[byte_off..byte_off + 2].copy_from_slice(&v.to_le_bytes());
        }
        4 => {
            bytes[byte_off..byte_off + 4].copy_from_slice(&id.0.to_le_bytes());
        }
        _ => return Err(RelocationError::InvalidInstruction),
    }

    Ok(())
}
