//! Legacy (file format 0.0.0.2) bytecode decoding.
//!
//! Files written by the pre-2022-08-18 ArkCompiler toolchain (OpenHarmony
//! 3.0/3.1-era es2abc — still shipped by AppGallery-era demo apps on
//! OpenHarmony 3.2/4.0 devices) use the pre-refactoring ISA: a different
//! opcode numbering, a `0xff` prefix for all ecmascript instructions,
//! 32-bit string operands holding direct file offsets (the method index
//! header for strings/literal arrays did not exist yet), and no inline-cache
//! slot immediates.
//!
//! [`decode_legacy`] walks such a stream with the legacy table
//! (`legacy_table`, generated — see `tools/gen_legacy_table.py`) and
//! translates each instruction to the modern [`Bytecode`] IR:
//!
//! - Layout-identical instructions map to the same-named modern variant
//!   (including `deprecated.*` variants, which preserve the legacy operand
//!   lists — e.g. `DeprecatedCallarg1` keeps the explicit func register that
//!   modern `Callarg1` moved into the accumulator).
//! - Instructions whose modern encoding gained an IC-slot immediate get
//!   `Imm(0)` synthesized (the value a freshly loaded method would carry).
//! - The legacy `define*funcdyn` family maps to modern `Definefunc`; the
//!   function kind lives in the method header (decoded by abcd-file), and
//!   the legacy trailing lexenv register operand (modern `definefunc` reads
//!   the frame env) is dropped.
//!
//! Legacy opcodes with no modern counterpart (Java-era core ops, `debugger`,
//! `expdyn`, `iternext`, `copymodule`, `newobjspreaddyn`, `ldfunction`,
//! `newlexenvwithnamedyn`) are absent from the table and fail with
//! [`DecodeError::InvalidOpcode`], exactly like unknown bytes.
//!
//! This module is never entered for non-legacy files (the caller gates on
//! the file version), so it adds zero cost to the modern decode path.

use abcd_isa_sys::{Bytecode, Label};

use crate::decoder::DecodeError;
use crate::legacy_table::{LEGACY_CORE, LEGACY_ECMA};

/// Legacy ecmascript prefix byte.
const ECMA_PREFIX: u8 = 0xff;

/// Decode a legacy (format 0.0.0.2) bytecode byte slice into a vector of
/// `(instruction, byte_offset)` pairs with resolved jump targets.
///
/// Same contract as [`crate::decode`]: jump operands are returned as
/// [`Label`] instruction indices. Unknown legacy opcodes fail with
/// [`DecodeError::InvalidOpcode`]; truncated tails with
/// [`DecodeError::Truncated`].
pub fn decode_legacy(bytes: &[u8]) -> Result<Vec<(Bytecode, u32)>, DecodeError> {
    let mut instructions: Vec<Bytecode> = Vec::new();
    let mut byte_offsets: Vec<usize> = Vec::new();
    // (insn_index, insn_byte_offset, raw_jump_offset)
    let mut jumps: Vec<(usize, usize, i64)> = Vec::new();
    let mut offset: usize = 0;

    while offset < bytes.len() {
        let b0 = bytes[offset];
        let entry = if b0 == ECMA_PREFIX {
            if offset + 1 >= bytes.len() {
                return Err(DecodeError::Truncated(offset));
            }
            &LEGACY_ECMA[bytes[offset + 1] as usize]
        } else {
            &LEGACY_CORE[b0 as usize]
        };
        let Some(entry) = entry else {
            return Err(DecodeError::InvalidOpcode(offset));
        };
        let size = entry.size as usize;
        if offset + size > bytes.len() {
            return Err(DecodeError::Truncated(offset));
        }
        // `make` reads only bytes covered by the legacy format, all within
        // `size` (generator-enforced against the legacy ISA definition).
        let (bc, jump_offset) = (entry.make)(&bytes[offset..offset + size]);
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

    // Pass 2: resolve jump targets to instruction indices (identical to the
    // modern decoder: raw offset relative to the jump instruction start).
    for (insn_idx, insn_offset, raw_imm) in jumps {
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
