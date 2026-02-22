use abcd_isa_sys::{Bytecode, Label};

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

/// Decode a bytecode byte slice into a vector of `(instruction, byte_offset)`
/// pairs with resolved jump targets.
///
/// Jump operands are converted to [`Label`] values whose inner `u32` is the
/// index of the target instruction in the returned `Vec`.
///
/// Each tuple contains the decoded [`Bytecode`] and its byte offset within
/// the input slice. Instruction sizes can be derived from consecutive offsets
/// (or `bytes.len() - offset` for the last instruction).
pub fn decode(bytes: &[u8]) -> Result<Vec<(Bytecode, u32)>, DecodeError> {
    let mut instructions: Vec<Bytecode> = Vec::new();
    let mut byte_offsets: Vec<usize> = Vec::new();
    // (insn_index, insn_byte_offset, raw_jump_offset)
    let mut jumps: Vec<(usize, usize, i64)> = Vec::new();
    let mut offset: usize = 0;

    // Pass 1: decode instructions, record byte offsets.
    // SAFETY: pure query, no preconditions.
    let prefix_min = unsafe { abcd_isa_sys::isa_min_prefix_opcode() };
    while offset < bytes.len() {
        // Prefixed opcodes occupy 2 bytes; ensure we don't read past the end.
        if bytes[offset] >= prefix_min && offset + 1 >= bytes.len() {
            return Err(DecodeError::Truncated(offset));
        }
        let ptr = bytes[offset..].as_ptr();
        // SAFETY: ptr points into `bytes[offset..]`; at least 1 byte is
        // readable (loop condition), and 2 bytes for prefixed opcodes
        // (checked above).
        let opcode = unsafe { abcd_isa_sys::isa_get_opcode(ptr) };
        // SAFETY: pure query, no preconditions.
        let size = unsafe { abcd_isa_sys::isa_get_size_by_opcode(opcode) };
        if size == 0 {
            return Err(DecodeError::InvalidOpcode(offset));
        }
        if offset + size > bytes.len() {
            return Err(DecodeError::Truncated(offset));
        }

        // SAFETY: ptr has at least `size` readable bytes (checked above);
        // opcode was obtained from `isa_get_opcode(ptr)`.
        let (bc, jump_offset) = unsafe { Bytecode::decode_one(ptr, opcode) }
            .ok_or(DecodeError::InvalidOpcode(offset))?;

        if let Some(raw_imm) = jump_offset {
            jumps.push((instructions.len(), offset, raw_imm));
        }

        byte_offsets.push(offset);
        instructions.push(bc);
        offset += size;
    }

    // Label uses u32 indices; guard against truncation on 64-bit platforms.
    if instructions.len() > u32::MAX as usize {
        return Err(DecodeError::TooManyInstructions(instructions.len()));
    }

    // Pass 2: resolve jump targets to instruction indices.
    for (insn_idx, insn_offset, raw_imm) in jumps {
        // Use i128 to avoid overflow when computing the target byte offset.
        let raw_target = insn_offset as i128 + raw_imm as i128;
        let target_offset =
            usize::try_from(raw_target).map_err(|_| DecodeError::InvalidJumpTarget {
                offset: insn_offset,
                target: raw_target.clamp(i64::MIN as i128, i64::MAX as i128) as i64,
            })?;
        let target_insn = byte_offsets.binary_search(&target_offset).map_err(|_| {
            DecodeError::InvalidJumpTarget {
                offset: insn_offset,
                target: target_offset as i64,
            }
        })?;
        instructions[insn_idx].set_label(Label(target_insn as u32));
    }

    Ok(instructions
        .into_iter()
        .zip(byte_offsets.iter().map(|&o| o as u32))
        .collect())
}
