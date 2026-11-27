use crate::generated::{Bytecode, Label, ModernDecodeFault};

/// Errors from [`decode`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum DecodeError {
    /// Invalid or unknown opcode at the given byte offset.
    #[error("invalid opcode at offset {0}")]
    InvalidOpcode(usize),
    /// Bytecode truncated at the given byte offset.
    #[error("truncated instruction at offset {0}")]
    Truncated(usize),
    /// A jump instruction at `offset` targets byte offset `target` which
    /// does not land on an instruction boundary (or is out of range).
    #[error("jump at offset {offset} targets invalid offset {target}")]
    InvalidJumpTarget { offset: usize, target: i64 },
    /// Too many instructions to represent jump targets as `u32` indices.
    #[error("instruction count {0} exceeds Label index capacity")]
    TooManyInstructions(usize),
}

/// Decode a modern (`9.0.0.0`..`24.0.0.0`) bytecode byte slice into a vector of
/// `(instruction, byte_offset)` pairs with resolved jump targets.
///
/// Jump operands are converted to [`Label`] values whose inner `u32` is the
/// index of the target instruction in the returned `Vec`.
///
/// Each tuple contains the decoded [`Bytecode`] and its byte offset within
/// the input slice. Instruction sizes can be derived from consecutive offsets
/// (or `bytes.len() - offset` for the last instruction).
pub fn decode(bytes: &[u8]) -> Result<Vec<(Bytecode, u32)>, DecodeError> {
    if bytes.is_empty() {
        return Ok(Vec::new());
    }

    let mut out: Vec<(Bytecode, u32)> = Vec::with_capacity(bytes.len() / 3);
    // (insn_index, insn_byte_offset, raw_jump_offset)
    let mut jumps: Vec<(usize, usize, i64)> = Vec::new();
    let mut offset: usize = 0;

    // Pass 1: pure-Rust linear scan of instructions and byte offsets.
    while offset < bytes.len() {
        let (bc, size, jump_offset) =
            Bytecode::decode_modern(&bytes[offset..]).map_err(|fault| match fault {
                ModernDecodeFault::InvalidOpcode => DecodeError::InvalidOpcode(offset),
                ModernDecodeFault::Truncated => DecodeError::Truncated(offset),
            })?;

        let off_u32 = u32::try_from(offset)
            .map_err(|_| DecodeError::TooManyInstructions(out.len().saturating_add(1)))?;

        if let Some(raw_imm) = jump_offset {
            jumps.push((out.len(), offset, raw_imm));
        }

        out.push((bc, off_u32));
        offset += size;
    }

    // Label uses u32 indices; guard against > u32::MAX 1-byte instructions on 64-bit platforms.
    if out.len() > u32::MAX as usize {
        return Err(DecodeError::TooManyInstructions(out.len()));
    }

    // Pass 2: resolve jump byte displacements to instruction indices via binary search.
    for (insn_idx, insn_offset, raw_imm) in jumps {
        let raw_target = insn_offset as i128 + raw_imm as i128;
        let target_offset =
            u32::try_from(raw_target).map_err(|_| DecodeError::InvalidJumpTarget {
                offset: insn_offset,
                target: raw_target.clamp(i64::MIN as i128, i64::MAX as i128) as i64,
            })?;
        let target_insn = out
            .binary_search_by_key(&target_offset, |&(_, off)| off)
            .map_err(|_| DecodeError::InvalidJumpTarget {
                offset: insn_offset,
                target: i64::from(target_offset),
            })?;
        out[insn_idx].0.set_label(Label(target_insn as u32));
    }

    Ok(out)
}
