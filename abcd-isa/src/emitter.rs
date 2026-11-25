use abcd_isa_sys::{Bytecode, EncodeInsnKind, JMP_IMM32_OPCODE, JumpEncodeMeta, WideJumpKind};

/// Errors from [`encode`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum EncodeError {
    /// An internal invariant of the bytecode encoder was violated.
    #[error("internal emitter error")]
    Internal,
    /// The opcode is not recognized by the emitter.
    #[error("emit failed: unknown opcode")]
    UnknownOpcode,
    /// An operand does not fit the instruction's storage width; encoding it
    /// would silently truncate the value.
    #[error("operand out of range for the instruction encoding")]
    OperandOutOfRange,
    /// A jump instruction references instruction index `{0}` which is
    /// beyond the program length `{1}`.
    #[error("label index {0} is out of bounds (program length: {1})")]
    LabelOutOfBounds(u32, usize),
    /// The instruction slice is too large for [`Label`](abcd_isa_sys::Label)'s
    /// `u32` index space.
    #[error("instruction count {0} exceeds Label index capacity")]
    TooManyInstructions(usize),
}

/// Byte width of a jump instruction at relaxation `tier` (`0 = imm8`, `1 = imm16`, `2 = wide`).
#[inline]
const fn jump_tier_size(meta: &JumpEncodeMeta, tier: u8) -> u8 {
    match tier {
        0 => {
            if meta.reg.is_some() {
                3
            } else {
                2
            }
        }
        1 => {
            if meta.reg.is_some() {
                4
            } else {
                3
            }
        }
        _ => match meta.wide {
            WideJumpKind::NativeImm32(_) => 5,
            WideJumpKind::InvertImm8(_) => 7,
            WideJumpKind::InvertV8Imm8(_) => 8,
        },
    }
}

/// Prefix sum `sizes[0..k]` from a 1-indexed Fenwick tree (`k in 0..=n`).
#[inline]
fn fenwick_sum(bit: &[u64], k: usize) -> u64 {
    let mut sum = 0u64;
    let mut idx = k;
    while idx > 0 {
        sum += bit[idx];
        idx &= idx - 1;
    }
    sum
}

/// Point-add `delta` to `sizes[i]` in a 1-indexed Fenwick tree.
#[inline]
fn fenwick_add(bit: &mut [u64], i: usize, delta: u64) {
    let mut idx = i + 1;
    while idx < bit.len() {
        bit[idx] += delta;
        idx += idx & idx.wrapping_neg();
    }
}

/// Check one jump site against current Fenwick prefix offsets and widen its tier if needed.
#[inline]
fn relax_jump_site(
    site: &mut (usize, JumpEncodeMeta, u8),
    sizes: &mut [u8],
    bit: &mut [u64],
) -> bool {
    let (insn_idx, meta, ref mut tier) = *site;
    if *tier >= 2 {
        return false;
    }

    let insn_off = fenwick_sum(bit, insn_idx) as i64;
    let target_off = fenwick_sum(bit, meta.target.0 as usize) as i64;
    let disp = target_off - insn_off;

    if *tier == 0 {
        if (i8::MIN as i64..=i8::MAX as i64).contains(&disp) {
            return false;
        }
        *tier = 1;
        let old_sz = sizes[insn_idx];
        let new_sz = jump_tier_size(&meta, 1);
        sizes[insn_idx] = new_sz;
        fenwick_add(bit, insn_idx, u64::from(new_sz - old_sz));

        // Re-evaluate immediately under updated prefix sums in case displacement already exceeds i16.
        let insn_off = fenwick_sum(bit, insn_idx) as i64;
        let target_off = fenwick_sum(bit, meta.target.0 as usize) as i64;
        let disp = target_off - insn_off;
        if !(i16::MIN as i64..=i16::MAX as i64).contains(&disp) {
            *tier = 2;
            let old_sz = sizes[insn_idx];
            let new_sz = jump_tier_size(&meta, 2);
            sizes[insn_idx] = new_sz;
            fenwick_add(bit, insn_idx, u64::from(new_sz - old_sz));
        }
        return true;
    }

    // *tier == 1
    if (i16::MIN as i64..=i16::MAX as i64).contains(&disp) {
        return false;
    }
    *tier = 2;
    let old_sz = sizes[insn_idx];
    let new_sz = jump_tier_size(&meta, 2);
    sizes[insn_idx] = new_sz;
    fenwick_add(bit, insn_idx, u64::from(new_sz - old_sz));
    true
}

/// Encode a sequence of instructions into bytecode bytes in pure Safe Rust.
///
/// [`Label`](abcd_isa_sys::Label) operands in jump instructions are
/// interpreted as instruction indices into `instructions`.
///
/// Returns `(bytes, offsets)` where `offsets[i]` is the starting byte offset of
/// instruction `i` within `bytes` (`offsets.len() == instructions.len()` even
/// when a far `> 32 KiB` conditional jump expands into an inverted-branch +
/// `jmp.32` trampoline).
///
/// ```
/// use abcd_isa::{Bytecode, Label, encode, insn};
///
/// let program: &[Bytecode] = &[
///     insn::Jmp::new(Label(1)),
///     insn::Ldundefined::new(),
/// ];
/// let (bytes, offsets) = encode(program)?;
/// assert_eq!(offsets, vec![0, 2]);
/// assert_eq!(bytes.len(), 3);
/// # Ok::<(), abcd_isa::EncodeError>(())
/// ```
pub fn encode(instructions: &[Bytecode]) -> Result<(Vec<u8>, Vec<u32>), EncodeError> {
    let n = instructions.len();
    if n == 0 {
        return Ok((Vec::new(), Vec::new()));
    }
    if n > u32::MAX as usize {
        return Err(EncodeError::TooManyInstructions(n));
    }

    // 1. Pre-pack fixed instructions and collect jump sites at minimal (`imm8`) width.
    let mut kinds: Vec<EncodeInsnKind> = Vec::with_capacity(n);
    let mut sizes: Vec<u8> = Vec::with_capacity(n);
    let mut jumps: Vec<(usize, JumpEncodeMeta, u8)> = Vec::new();

    for (idx, bc) in instructions.iter().enumerate() {
        let kind = bc
            .classify_for_encode()
            .map_err(|()| EncodeError::OperandOutOfRange)?;
        match kind {
            EncodeInsnKind::Fixed { len, .. } => {
                sizes.push(len);
            }
            EncodeInsnKind::Jump(meta) => {
                if meta.target.0 as usize >= n {
                    return Err(EncodeError::LabelOutOfBounds(meta.target.0, n));
                }
                sizes.push(jump_tier_size(&meta, 0));
                jumps.push((idx, meta, 0));
            }
        }
        kinds.push(kind);
    }

    // 2. Deterministic O(N + J log N) Fenwick-tree branch relaxation.
    if !jumps.is_empty() {
        let mut bit = vec![0u64; n + 1];
        for (i, &sz) in sizes.iter().enumerate() {
            let idx1 = i + 1;
            bit[idx1] += u64::from(sz);
            let parent = idx1 + (idx1 & idx1.wrapping_neg());
            if parent <= n {
                bit[parent] += bit[idx1];
            }
        }

        loop {
            let mut changed = false;
            for site in jumps.iter_mut().rev() {
                if relax_jump_site(site, &mut sizes, &mut bit) {
                    changed = true;
                }
            }
            for site in &mut jumps {
                if relax_jump_site(site, &mut sizes, &mut bit) {
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    // 3. Materialize exact per-instruction starting offsets.
    let mut offsets: Vec<u32> = Vec::with_capacity(n);
    let mut cur_off = 0u64;
    for &sz in &sizes {
        let off32 = u32::try_from(cur_off).map_err(|_| EncodeError::OperandOutOfRange)?;
        offsets.push(off32);
        cur_off += u64::from(sz);
    }
    let total_bytes = usize::try_from(cur_off).map_err(|_| EncodeError::OperandOutOfRange)?;

    // 4. Single linear emission pass.
    let mut out: Vec<u8> = Vec::with_capacity(total_bytes);
    let mut jump_cursor = 0usize;
    for (i, kind) in kinds.iter().enumerate() {
        match *kind {
            EncodeInsnKind::Fixed { ref bytes, len } => {
                out.extend_from_slice(&bytes[..usize::from(len)]);
            }
            EncodeInsnKind::Jump(meta) => {
                let (j_idx, _, tier) = jumps[jump_cursor];
                debug_assert_eq!(j_idx, i);
                jump_cursor += 1;

                let insn_off = i64::from(offsets[i]);
                let target_off = i64::from(offsets[meta.target.0 as usize]);

                match tier {
                    0 => {
                        let disp = target_off - insn_off;
                        debug_assert!((i8::MIN as i64..=i8::MAX as i64).contains(&disp));
                        out.push(meta.op_imm8);
                        if let Some(r) = meta.reg {
                            out.push(r);
                        }
                        out.push((disp as i8) as u8);
                    }
                    1 => {
                        let disp = target_off - insn_off;
                        debug_assert!((i16::MIN as i64..=i16::MAX as i64).contains(&disp));
                        out.push(meta.op_imm16);
                        if let Some(r) = meta.reg {
                            out.push(r);
                        }
                        out.extend_from_slice(&(disp as i16).to_le_bytes());
                    }
                    _ => match meta.wide {
                        WideJumpKind::NativeImm32(op32) => {
                            let disp = target_off - insn_off;
                            let disp32 =
                                i32::try_from(disp).map_err(|_| EncodeError::OperandOutOfRange)?;
                            out.push(op32);
                            out.extend_from_slice(&disp32.to_le_bytes());
                        }
                        WideJumpKind::InvertImm8(inv_op8) => {
                            let jmp_pc = insn_off + 2;
                            let disp = target_off - jmp_pc;
                            let disp32 =
                                i32::try_from(disp).map_err(|_| EncodeError::OperandOutOfRange)?;
                            out.push(inv_op8);
                            out.push(7u8);
                            out.push(JMP_IMM32_OPCODE);
                            out.extend_from_slice(&disp32.to_le_bytes());
                        }
                        WideJumpKind::InvertV8Imm8(inv_op8) => {
                            let r = meta.reg.ok_or(EncodeError::Internal)?;
                            let jmp_pc = insn_off + 3;
                            let disp = target_off - jmp_pc;
                            let disp32 =
                                i32::try_from(disp).map_err(|_| EncodeError::OperandOutOfRange)?;
                            out.push(inv_op8);
                            out.push(r);
                            out.push(8u8);
                            out.push(JMP_IMM32_OPCODE);
                            out.extend_from_slice(&disp32.to_le_bytes());
                        }
                    },
                }
            }
        }
    }

    debug_assert_eq!(out.len(), total_bytes);
    Ok((out, offsets))
}
