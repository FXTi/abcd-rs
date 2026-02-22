use std::collections::HashMap;
use std::ptr;

use abcd_isa_sys::Bytecode;

// C bridge error codes (from isa_bridge.h).
const ISA_EMIT_UNKNOWN_OPCODE: i32 = -3;

/// Errors from [`encode`].
#[derive(Debug, thiserror::Error)]
pub enum EncodeError {
    /// The underlying C++ emitter returned a non-specific error.
    #[error("internal emitter error")]
    Internal,
    /// The opcode is not recognized by the emitter.
    #[error("emit failed: unknown opcode")]
    UnknownOpcode,
    /// A jump instruction references instruction index `{0}` which is
    /// beyond the program length `{1}`.
    #[error("label index {0} is out of bounds (program length: {1})")]
    LabelOutOfBounds(u32, usize),
    /// The instruction slice is too large for [`Label`](abcd_isa_sys::Label)'s
    /// `u32` index space.
    #[error("instruction count {0} exceeds Label index capacity")]
    TooManyInstructions(usize),
}

/// Encode a sequence of instructions into bytecode bytes.
///
/// [`Label`](abcd_isa_sys::Label) operands in jump instructions are
/// interpreted as instruction indices into `instructions`.
///
/// Returns `(bytes, offsets)` where `offsets[i]` is the byte offset of
/// instruction `i` within `bytes`. This is needed for try-block metadata
/// which references instructions by byte offset.
///
/// ```no_run
/// use abcd_isa::{encode, insn, Label, Bytecode};
///
/// let program: &[Bytecode] = &[
///     insn::Jmp::new(Label(1)).into(),
///     insn::Ldundefined::new().into(),
/// ];
/// let (bytes, offsets) = encode(program)?;
/// # Ok::<(), abcd_isa::EncodeError>(())
/// ```
pub fn encode(instructions: &[Bytecode]) -> Result<(Vec<u8>, Vec<u32>), EncodeError> {
    // Label uses u32 indices; guard against truncation on 64-bit platforms.
    if instructions.len() > u32::MAX as usize {
        return Err(EncodeError::TooManyInstructions(instructions.len()));
    }

    // 1. Collect jump targets and validate label bounds.
    let mut targets: HashMap<u32, u32> = HashMap::new(); // insn_index → cpp_label_id (filled in step 2)
    for bc in instructions {
        if let Some(idx) = bc.jump_label_arg_index() {
            let (_, args, _) = bc.emit_args();
            let target = args[idx] as u32;
            if target as usize >= instructions.len() {
                return Err(EncodeError::LabelOutOfBounds(target, instructions.len()));
            }
            targets.entry(target).or_insert(0);
        }
    }

    // 2. Create C++ emitter and allocate a label for each target.
    // SAFETY: no preconditions; returns null on allocation failure (checked below).
    let raw = unsafe { abcd_isa_sys::isa_emitter_create() };
    if raw.is_null() {
        return Err(EncodeError::Internal);
    }

    // Ensure cleanup on all exit paths.
    struct Guard(*mut abcd_isa_sys::IsaEmitter);
    impl Drop for Guard {
        fn drop(&mut self) {
            // SAFETY: self.0 is the sole owner, obtained from isa_emitter_create.
            unsafe { abcd_isa_sys::isa_emitter_destroy(self.0) };
        }
    }
    let _guard = Guard(raw);

    for cpp_id in targets.values_mut() {
        // SAFETY: raw is non-null (checked above) and exclusively owned.
        *cpp_id = unsafe { abcd_isa_sys::isa_emitter_create_label(raw) };
    }

    // 3. Emit instructions, binding labels at the right positions.
    for (i, bc) in instructions.iter().enumerate() {
        if let Some(&cpp_id) = targets.get(&(i as u32)) {
            // SAFETY: raw is non-null; cpp_id was returned by create_label.
            let rc = unsafe { abcd_isa_sys::isa_emitter_bind(raw, cpp_id) };
            debug_assert_eq!(rc, 0, "isa_emitter_bind failed for label {cpp_id}");
        }

        let (opcode, mut args, num_args) = bc.emit_args();

        // Replace instruction index with C++ label ID for jump operands.
        if let Some(label_idx) = bc.jump_label_arg_index() {
            let target_insn = args[label_idx] as u32;
            args[label_idx] = targets[&target_insn] as i64;
        }

        // SAFETY: raw is non-null; args points to a stack-allocated array
        // with at least num_args elements.
        let rc = unsafe { abcd_isa_sys::isa_emitter_emit(raw, opcode, args.as_ptr(), num_args) };
        match rc {
            0 => {}
            ISA_EMIT_UNKNOWN_OPCODE => return Err(EncodeError::UnknownOpcode),
            _ => return Err(EncodeError::Internal),
        }
    }

    // 4. Build final bytecode.
    let mut buf: *mut u8 = ptr::null_mut();
    let mut len: usize = 0;
    // SAFETY: raw is non-null; buf and len are valid mutable references.
    let rc = unsafe { abcd_isa_sys::isa_emitter_build(raw, &mut buf, &mut len) };
    match rc {
        0 if !buf.is_null() => {
            // SAFETY: buf is non-null (match guard) and points to `len` bytes
            // allocated by isa_emitter_build.
            let vec = unsafe { std::slice::from_raw_parts(buf, len) }.to_vec();
            // SAFETY: buf was allocated by isa_emitter_build.
            unsafe { abcd_isa_sys::isa_emitter_free_buf(buf) };

            // Compute per-instruction byte offsets by scanning the built bytes.
            // The C++ emitter may choose optimal formats, so we derive offsets
            // from the actual output rather than predicting them.
            let mut offsets = Vec::with_capacity(instructions.len());
            let mut pos = 0usize;
            while pos < vec.len() {
                offsets.push(pos as u32);
                // SAFETY: vec[pos..] has at least 1 byte; isa_get_size_from_bytes
                // reads the opcode and returns the instruction size.
                let size = unsafe { abcd_isa_sys::isa_get_size_from_bytes(vec[pos..].as_ptr()) };
                if size == 0 {
                    break;
                }
                pos += size;
            }

            Ok((vec, offsets))
        }
        _ => Err(EncodeError::Internal),
    }
}
