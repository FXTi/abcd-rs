//! Exhaustive differential oracle & branch-relaxation regression suite
//! (Decision D1, Issue #43 `R1-C2`, `N20`).

use std::collections::{BTreeSet, HashMap};
use std::ptr;

use abcd_isa::{
    Bytecode, BytecodeFlags, DecodeError, EntityId, ExceptionType, Imm, Label, Reg,
    RelocationError, decode, encode, insn, relocate_entity_id,
};
use abcd_isa_sys::{self as sys, MIN_PREFIX_OPCODE, ModernDecodeFault};

/// Encode `instructions` through the vendored C++ `BytecodeEmitter` FFI oracle.
fn cpp_oracle_encode(instructions: &[Bytecode]) -> Vec<u8> {
    if instructions.is_empty() {
        return Vec::new();
    }

    // SAFETY: stateless allocation in the C++ bridge; null is checked immediately.
    let raw = unsafe { sys::isa_emitter_create() };
    assert!(!raw.is_null(), "isa_emitter_create returned null");

    struct Guard(*mut sys::IsaEmitter);
    impl Drop for Guard {
        fn drop(&mut self) {
            // SAFETY: `self.0` was allocated by `isa_emitter_create` and is uniquely owned.
            unsafe { sys::isa_emitter_destroy(self.0) };
        }
    }
    let _guard = Guard(raw);

    let mut targets: HashMap<u32, u32> = HashMap::new();
    for bc in instructions {
        if let Some(lbl) = bc.jump_label() {
            targets.entry(lbl.0).or_insert_with(|| {
                // SAFETY: `raw` is non-null and exclusively owned.
                unsafe { sys::isa_emitter_create_label(raw) }
            });
        }
    }

    for (i, bc) in instructions.iter().enumerate() {
        if let Some(&cpp_lbl) = targets.get(&(i as u32)) {
            // SAFETY: `raw` is non-null and `cpp_lbl` came from `isa_emitter_create_label`.
            let rc = unsafe { sys::isa_emitter_bind(raw, cpp_lbl) };
            assert_eq!(rc, sys::ISA_EMIT_OK as i32);
        }
        let (opcode, mut args, num_args) = bc.emit_args();
        if let Some(label_idx) = bc.jump_label_arg_index() {
            let target_insn = args[label_idx] as u32;
            args[label_idx] = i64::from(targets[&target_insn]);
        }
        // SAFETY: `raw` is non-null and `args` holds `num_args` elements on the stack.
        let rc = unsafe { sys::isa_emitter_emit(raw, opcode, args.as_ptr(), num_args) };
        assert_eq!(
            rc,
            sys::ISA_EMIT_OK as i32,
            "C++ emitter rejected {bc:?}: rc={rc}"
        );
    }

    let mut buf: *mut u8 = ptr::null_mut();
    let mut len: usize = 0;
    // SAFETY: `raw` is non-null; `buf` and `len` are valid out-pointers.
    let rc = unsafe { sys::isa_emitter_build(raw, &mut buf, &mut len) };
    assert_eq!(rc, sys::ISA_BUILD_OK as i32, "C++ emitter build failed");
    assert!(!buf.is_null());
    // SAFETY: `buf` points to `len` initialized bytes from `isa_emitter_build`.
    let bytes = unsafe { std::slice::from_raw_parts(buf, len) }.to_vec();
    // SAFETY: `buf` was allocated by `isa_emitter_build` and is freed once here.
    unsafe { sys::isa_emitter_free_buf(buf) };
    bytes
}

/// Write a 1- or 2-byte modern opcode header into `buf`, returning `Some(header_len)`
/// if `op` can actually appear in a byte stream (`isa_get_opcode(buf) == op`).
fn write_opcode_header(op: u16, buf: &mut [u8; 16]) -> Option<usize> {
    let lo = (op & 0xFF) as u8;
    let hi = (op >> 8) as u8;
    if lo >= MIN_PREFIX_OPCODE {
        buf[0] = lo;
        buf[1] = hi;
        Some(2)
    } else if hi == 0 {
        buf[0] = lo;
        Some(1)
    } else {
        None
    }
}

/// 1. Exhaustive sweep over all 65,536 `u16` opcode values:
///    - Pure-Rust `decode_modern`, `decode`, and `relocate_entity_id` match C++
///      `isa_get_*` / `decode_one` / `isa_has_id` / `isa_update_id` 100%.
///    - Pure-Rust `const fn` classification (`is_jump`, `can_throw`,
///      `is_terminator`, `is_range`, `is_return_or_throw`, `is_suspend`,
///      `flags`, `exception_mask`) matches C++ `isa_*_opcode` 100%.
///    - Every non-jump instruction decoded across payload patterns re-encodes
///      byte-for-byte identically to C++ `BytecodeEmitter`.
#[test]
fn exhaustive_all_u16_opcodes_match_cpp_oracle() {
    let payload_patterns: [[u8; 16]; 5] = [
        [0x00; 16],
        [0xFF; 16],
        [0x7F; 16],
        [0x80; 16],
        [
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
            0x77, 0x88,
        ],
    ];
    let test_entity_ids: [u32; 10] = [
        0,
        1,
        0x7F,
        0xFF,
        0x0100,
        0x7FFF,
        0xFFFF,
        0x0001_0000,
        0xDEAD_BEEF,
        u32::MAX,
    ];

    let mut assigned_count = 0usize;
    let mut jump_mnemonics = BTreeSet::new();

    for op_u32 in 0u32..=0xFFFF {
        let op = op_u32 as u16;
        // SAFETY: stateless C++ lookup pre-validated in `isa_bridge.cpp`.
        let cpp_size = unsafe { sys::isa_get_size_by_opcode(op) };

        let mut base_buf = [0u8; 16];
        let Some(hdr_len) = write_opcode_header(op, &mut base_buf) else {
            assert_eq!(
                cpp_size, 0,
                "unrepresentable opcode {op:#06x} cannot have non-zero size"
            );
            continue;
        };

        if cpp_size == 0 {
            assert_eq!(
                Bytecode::decode_modern(&base_buf),
                Err(ModernDecodeFault::InvalidOpcode),
                "unassigned opcode {op:#06x} must report InvalidOpcode"
            );
            assert_eq!(
                decode(&base_buf[..hdr_len]),
                Err(DecodeError::InvalidOpcode(0)),
                "unassigned opcode {op:#06x} must fail decode at offset 0"
            );
            let mut probe = base_buf;
            assert_eq!(
                relocate_entity_id(&mut probe, 0, EntityId(1)),
                Err(RelocationError::InvalidInstruction),
                "unassigned opcode {op:#06x} must fail relocate_entity_id"
            );
            continue;
        }

        assigned_count += 1;
        assert!(cpp_size >= hdr_len && cpp_size <= 16);

        // Truncated lengths `1..cpp_size` must report `DecodeError::Truncated(0)`.
        for trunc_len in 1..cpp_size {
            assert_eq!(
                decode(&base_buf[..trunc_len]),
                Err(DecodeError::Truncated(0)),
                "opcode {op:#06x} truncated to {trunc_len}/{cpp_size} bytes"
            );
        }

        // Check decode, classification, entity relocation, and non-jump re-encoding across patterns.
        for (pat_idx, pat) in payload_patterns.iter().enumerate() {
            let mut buf = *pat;
            let _ = write_opcode_header(op, &mut buf);

            // SAFETY: `buf` has 16 readable bytes >= `cpp_size`.
            let cpp_opcode = unsafe { sys::isa_get_opcode(buf.as_ptr()) };
            assert_eq!(cpp_opcode, op);
            // SAFETY: `buf` has 16 readable bytes >= `cpp_size`.
            let cpp_sz_bytes = unsafe { sys::isa_get_size_from_bytes(buf.as_ptr()) };
            assert_eq!(cpp_sz_bytes, cpp_size);

            // SAFETY: `buf` has >= `cpp_size` readable bytes and `op` is assigned.
            let (cpp_bc, cpp_jmp) = unsafe { Bytecode::decode_one(buf.as_ptr(), op) }
                .expect("assigned opcode must decode in C++ oracle");
            let (rs_bc, rs_sz, rs_jmp) = Bytecode::decode_modern(&buf[..cpp_size])
                .expect("assigned opcode must decode in pure Rust");

            assert_eq!(rs_sz, cpp_size, "size mismatch on opcode {op:#06x}");
            assert_eq!(rs_bc, cpp_bc, "Bytecode mismatch on opcode {op:#06x}");
            assert_eq!(rs_jmp, cpp_jmp, "jump offset mismatch on opcode {op:#06x}");

            if rs_bc.is_jump() {
                jump_mnemonics.insert(rs_bc.mnemonic());
            }

            // Classification parity (checked once per assigned opcode on pattern 0).
            if pat_idx == 0 {
                // SAFETY: all `isa_*_opcode` functions are pure queries over `uint16_t`.
                unsafe {
                    assert_eq!(rs_bc.is_jump(), sys::isa_is_jump_opcode(op) != 0);
                    assert_eq!(rs_bc.can_throw(), sys::isa_can_throw_opcode(op) != 0);
                    assert_eq!(
                        rs_bc.is_terminator(),
                        sys::isa_is_terminator_opcode(op) != 0
                    );
                    assert_eq!(rs_bc.is_range(), sys::isa_is_range_opcode(op) != 0);
                    assert_eq!(
                        rs_bc.is_return_or_throw(),
                        sys::isa_is_return_or_throw_opcode(op) != 0
                    );
                    assert_eq!(rs_bc.is_suspend(), sys::isa_is_suspend_opcode(op) != 0);

                    for bit in 0..32 {
                        let mask = 1u32 << bit;
                        if let Some(flag) = BytecodeFlags::from_bits(mask) {
                            assert_eq!(
                                rs_bc.has_flag(flag),
                                sys::isa_has_flag_opcode(op, mask) != 0,
                                "flag {flag:?} mismatch on opcode {op:#06x} ({})",
                                rs_bc.mnemonic()
                            );
                        }
                        if let Some(ex) = ExceptionType::from_bits(mask) {
                            assert_eq!(
                                rs_bc.is_throw_ex(ex),
                                sys::isa_is_throw_ex_opcode(op, mask) != 0,
                                "exception {ex:?} mismatch on opcode {op:#06x} ({})",
                                rs_bc.mnemonic()
                            );
                        }
                    }
                }

                // Entity-ID slot & relocation parity across ordinals 0..4.
                // SAFETY: `isa_get_format` is pre-validated for all `u16` inputs.
                let fmt = unsafe { sys::isa_get_format(op) };
                for ord in 0u32..4 {
                    // SAFETY: `fmt` was returned by `isa_get_format` for assigned `op`.
                    let cpp_has = unsafe { sys::isa_has_id(fmt, ord as usize) != 0 };
                    if !cpp_has {
                        let mut rs_buf = buf[..cpp_size].to_vec();
                        assert_eq!(
                            relocate_entity_id(&mut rs_buf, ord, EntityId(1)),
                            Err(RelocationError::MissingOperand(ord))
                        );
                        assert_eq!(rs_buf, &buf[..cpp_size]);
                    } else {
                        for &test_id in &test_entity_ids {
                            let mut cpp_buf = buf[..cpp_size].to_vec();
                            let mut rs_buf = buf[..cpp_size].to_vec();
                            // SAFETY: valid instruction slice of length `cpp_size` and valid ID ordinal.
                            unsafe { sys::isa_update_id(cpp_buf.as_mut_ptr(), test_id, ord) };
                            // SAFETY: `cpp_buf` has `cpp_size` valid bytes and valid ID ordinal.
                            let roundtripped =
                                unsafe { sys::isa_get_id(cpp_buf.as_ptr(), ord as usize) };
                            let rs_res = relocate_entity_id(&mut rs_buf, ord, EntityId(test_id));
                            if roundtripped == test_id {
                                assert_eq!(
                                    rs_res,
                                    Ok(()),
                                    "relocate_entity_id rejected fitting id {test_id:#x} on {op:#06x} ord {ord}"
                                );
                                assert_eq!(
                                    rs_buf, cpp_buf,
                                    "relocate_entity_id bytes differ from C++ on {op:#06x} ord {ord}"
                                );
                            } else {
                                assert_eq!(
                                    rs_res,
                                    Err(RelocationError::IdOutOfRange(test_id)),
                                    "relocate_entity_id accepted overflowing id {test_id:#x} on {op:#06x} ord {ord}"
                                );
                                assert_eq!(
                                    rs_buf,
                                    &buf[..cpp_size],
                                    "failed relocation mutated caller slice"
                                );
                            }
                        }
                    }
                }
            }

            // Full `decode` + C++ byte-for-byte `encode` check for every decoded non-jump instruction.
            if !rs_bc.is_jump() {
                let full_dec = decode(&buf[..cpp_size]).unwrap();
                assert_eq!(full_dec, vec![(cpp_bc, 0)]);

                let (rs_enc, rs_offs) = encode(&[rs_bc]).unwrap();
                let cpp_enc = cpp_oracle_encode(&[rs_bc]);
                assert_eq!(rs_offs, vec![0]);
                assert_eq!(
                    rs_enc, cpp_enc,
                    "pure-Rust encode != C++ emitter for {rs_bc:?} (from opcode {op:#06x})"
                );
            }
        }
    }

    assert_eq!(
        assigned_count, 332,
        "expected 332 concrete assigned opcodes in 24.0.0.0"
    );
    assert_eq!(
        jump_mnemonics.len(),
        17,
        "expected exactly 17 jump mnemonics in isa.yaml: {jump_mnemonics:?}"
    );
}

/// 2. Boundary operand & jump encoding byte-for-byte parity against C++ `isa_emitter_build`.
#[test]
fn encode_boundary_operands_and_jumps_match_cpp_byte_for_byte() {
    let reg_edges: [u16; 9] = [0, 1, 7, 8, 15, 16, 127, 128, 255];
    let reg16_edges: [u16; 13] = [0, 1, 7, 8, 15, 16, 127, 128, 255, 256, 32767, 32768, 65535];
    let u8_edges: [i64; 9] = [0, 1, 7, 8, 15, 16, 127, 128, 255];
    let u16_edges: [i64; 13] = [0, 1, 7, 8, 15, 16, 127, 128, 255, 256, 32767, 32768, 65535];
    let i32_edges: [i64; 21] = [
        i64::from(i32::MIN),
        -32769,
        -32768,
        -129,
        -128,
        -9,
        -8,
        -1,
        0,
        1,
        7,
        8,
        15,
        16,
        127,
        128,
        255,
        256,
        32767,
        32768,
        i64::from(i32::MAX),
    ];
    let f64_specials: [i64; 7] = [
        0.0_f64.to_bits() as i64,
        (-0.0_f64).to_bits() as i64,
        1.5_f64.to_bits() as i64,
        f64::INFINITY.to_bits() as i64,
        f64::NEG_INFINITY.to_bits() as i64,
        0x7ff8_0000_0000_0001_u64 as i64, // quiet NaN with payload
        0x7ff0_0000_0000_0001_u64 as i64, // signaling NaN bit pattern
    ];

    let mut non_jump_batch: Vec<Bytecode> = Vec::new();
    for &r1 in &reg16_edges {
        for &r2 in &[0u16, 15, 16, 255, 256, 65535] {
            non_jump_batch.push(insn::Mov::new(Reg(r1), Reg(r2)));
        }
    }
    for &r in &reg_edges {
        non_jump_batch.push(insn::Lda::new(Reg(r)));
        non_jump_batch.push(insn::Sta::new(Reg(r)));
    }
    for &imm in &i32_edges {
        non_jump_batch.push(insn::Ldai::new(Imm(imm)));
    }
    for &bits in &f64_specials {
        non_jump_batch.push(insn::Fldai::new(Imm(bits)));
    }
    for &a in &u8_edges {
        for &b in &[0i64, 7, 8, 15, 16, 255] {
            non_jump_batch.push(insn::Ldlexvar::new(Imm(a), Imm(b)));
            non_jump_batch.push(insn::Stlexvar::new(Imm(a), Imm(b)));
        }
    }
    for &u in &u16_edges {
        non_jump_batch.push(insn::WideLdlexvar::new(Imm(u), Imm(65535 - u)));
        non_jump_batch.push(insn::Ldobjbyindex::new(Imm(0), Imm(u)));
        non_jump_batch.push(insn::LdaStr::new(EntityId(u as u32)));
    }
    for &r in &reg_edges {
        non_jump_batch.push(insn::Add2::new(Imm(r as i64), Reg(r)));
        non_jump_batch.push(insn::Callthisrange::new(Imm(0), Imm(3), Reg(r)));
        non_jump_batch.push(insn::CallruntimeDefinesendableclass::new(
            Imm(0),
            EntityId(1024),
            EntityId(2048),
            Imm(4),
            Reg(r),
        ));
    }

    let (rs_bytes, rs_offsets) = encode(&non_jump_batch).unwrap();
    let cpp_bytes = cpp_oracle_encode(&non_jump_batch);
    assert_eq!(rs_offsets.len(), non_jump_batch.len());
    assert_eq!(rs_bytes, cpp_bytes, "non-jump boundary batch differs");

    // Verify all 17 jump mnemonics match C++ byte-for-byte on imm8 and imm16 distances
    // (forward & backward), plus native imm32 (> 32 KiB) for jmp/jeqz/jnez.
    for filler in [0usize, 10, 80, 250, 4000] {
        for (idx, (mk, _)) in all_17_jump_builders().into_iter().enumerate() {
            // Forward jump
            let mut fwd = Vec::with_capacity(filler + 2);
            fwd.push(mk(Label((filler + 1) as u32)));
            fwd.resize(filler + 1, insn::Ldundefined::new());
            fwd.push(insn::Returnundefined::new());
            let (rs_fwd, _) = encode(&fwd).unwrap();
            let cpp_fwd = cpp_oracle_encode(&fwd);
            assert_eq!(
                rs_fwd, cpp_fwd,
                "forward jump mnemonic #{idx} filler={filler} differs from C++"
            );

            // Backward jump
            let mut bwd = Vec::with_capacity(filler + 3);
            bwd.push(insn::Nop::new());
            bwd.resize(filler + 1, insn::Ldundefined::new());
            bwd.push(mk(Label(0)));
            bwd.push(insn::Returnundefined::new());
            let (rs_bwd, _) = encode(&bwd).unwrap();
            let cpp_bwd = cpp_oracle_encode(&bwd);
            assert_eq!(
                rs_bwd, cpp_bwd,
                "backward jump mnemonic #{idx} filler={filler} differs from C++"
            );
        }
    }

    // Native imm32 jumps (`jmp`, `jeqz`, `jnez`) over 40,000 instructions match C++ byte-for-byte.
    let far_filler = 40_000usize;
    for mk in [
        insn::Jmp::new as fn(Label) -> Bytecode,
        insn::Jeqz::new,
        insn::Jnez::new,
    ] {
        let mut prog = Vec::with_capacity(far_filler + 2);
        prog.push(mk(Label((far_filler + 1) as u32)));
        prog.resize(far_filler + 1, insn::Ldundefined::new());
        prog.push(insn::Returnundefined::new());
        let (rs_far, _) = encode(&prog).unwrap();
        let cpp_far = cpp_oracle_encode(&prog);
        assert_eq!(rs_far, cpp_far, "native imm32 far jump differs from C++");
    }
}

type JumpSpec = (fn(Label) -> Bytecode, Option<&'static str>);

/// Returns `(jump_builder, expected_inverted_mnemonic_if_trampoline)` for all 17 jump mnemonics.
fn all_17_jump_builders() -> [JumpSpec; 17] {
    [
        (insn::Jmp::new, None),
        (insn::Jeqz::new, None),
        (insn::Jnez::new, None),
        (insn::Jstricteqz::new, Some("jnstricteqz")),
        (insn::Jnstricteqz::new, Some("jstricteqz")),
        (insn::Jeqnull::new, Some("jnenull")),
        (insn::Jnenull::new, Some("jeqnull")),
        (insn::Jstricteqnull::new, Some("jnstricteqnull")),
        (insn::Jnstricteqnull::new, Some("jstricteqnull")),
        (insn::Jequndefined::new, Some("jneundefined")),
        (insn::Jneundefined::new, Some("jequndefined")),
        (insn::Jstrictequndefined::new, Some("jnstrictequndefined")),
        (insn::Jnstrictequndefined::new, Some("jstrictequndefined")),
        (|l| insn::Jeq::new(Reg(5), l), Some("jne")),
        (|l| insn::Jne::new(Reg(5), l), Some("jeq")),
        (|l| insn::Jstricteq::new(Reg(5), l), Some("jnstricteq")),
        (|l| insn::Jnstricteq::new(Reg(5), l), Some("jstricteq")),
    ]
}

/// 3. Regression test for Issue #43 (`R1-C2`):
///    All 17 jump mnemonics succeed across BOTH forward and backward `> 40 KiB`
///    distances (`40,000` `ldundefined` instructions), return
///    `offsets.len() == instructions.len()`, and `decode` cleanly resolves both
///    the inverted skip branch and the `jmp.32` target instruction.
#[test]
fn issue_43_all_17_jump_mnemonics_over_40kib_forward_and_backward() {
    let filler = 40_000usize;
    let builders = all_17_jump_builders();
    assert_eq!(builders.len(), 17);

    for &(mk, expected_inv) in &builders {
        let probe = mk(Label(0));
        let mnem = probe.mnemonic();

        // --- Forward > 40 KiB ---
        let mut fwd = Vec::with_capacity(filler + 2);
        fwd.push(mk(Label((filler + 1) as u32)));
        fwd.resize(filler + 1, insn::Ldundefined::new());
        fwd.push(insn::Returnundefined::new());

        let (fwd_bytes, fwd_offsets) = encode(&fwd).expect("forward >40 KiB encode must succeed");
        assert_eq!(
            fwd_offsets.len(),
            fwd.len(),
            "{mnem} forward offsets length"
        );
        assert_eq!(fwd_offsets[0], 0);

        let fwd_dec = decode(&fwd_bytes).expect("forward >40 KiB decode must succeed");
        match expected_inv {
            None => {
                assert_eq!(fwd_dec.len(), fwd.len(), "{mnem} native imm32 insn count");
                assert_eq!(fwd_offsets[1], 5, "{mnem} native imm32 must be 5 bytes");
                assert_eq!(fwd_dec[0].0.jump_label(), Some(Label((filler + 1) as u32)));
                assert_eq!(
                    fwd_dec[filler + 1],
                    (Bytecode::Returnundefined, fwd_offsets[filler + 1])
                );
            }
            Some(inv_mnem) => {
                assert_eq!(fwd_dec.len(), fwd.len() + 1, "{mnem} trampoline insn count");
                assert_eq!(fwd_dec[0].0.mnemonic(), inv_mnem);
                // Inverted branch skips `jmp.32` (index 1) and lands on index 2 (`fwd_offsets[1]`).
                assert_eq!(fwd_dec[0].0.jump_label(), Some(Label(2)));
                assert_eq!(fwd_dec[2], (Bytecode::Ldundefined, fwd_offsets[1]));
                // `jmp.32` at index 1 lands on `Returnundefined` at `filler + 2`.
                assert_eq!(fwd_dec[1].0, Bytecode::Jmp(Label((filler + 2) as u32)));
                assert_eq!(
                    fwd_dec[filler + 2],
                    (Bytecode::Returnundefined, fwd_offsets[filler + 1])
                );
            }
        }

        // --- Backward > 40 KiB ---
        let mut bwd = Vec::with_capacity(filler + 3);
        bwd.push(insn::Nop::new()); // index 0: backward jump target
        bwd.resize(filler + 1, insn::Ldundefined::new());
        bwd.push(mk(Label(0))); // index filler + 1: >40 KiB backward jump
        bwd.push(insn::Returnundefined::new()); // index filler + 2: fallthrough target

        let (bwd_bytes, bwd_offsets) = encode(&bwd).expect("backward >40 KiB encode must succeed");
        assert_eq!(
            bwd_offsets.len(),
            bwd.len(),
            "{mnem} backward offsets length"
        );

        let bwd_dec = decode(&bwd_bytes).expect("backward >40 KiB decode must succeed");
        assert_eq!(bwd_dec[0], (Bytecode::Nop, 0));
        match expected_inv {
            None => {
                assert_eq!(bwd_dec.len(), bwd.len());
                assert_eq!(bwd_dec[filler + 1].0.jump_label(), Some(Label(0)));
                assert_eq!(
                    bwd_dec[filler + 2],
                    (Bytecode::Returnundefined, bwd_offsets[filler + 2])
                );
            }
            Some(inv_mnem) => {
                assert_eq!(bwd_dec.len(), bwd.len() + 1);
                assert_eq!(bwd_dec[filler + 1].1, bwd_offsets[filler + 1]);
                assert_eq!(bwd_dec[filler + 1].0.mnemonic(), inv_mnem);
                // Inverted branch skips `jmp.32` (at filler + 2) and lands on `Returnundefined` (at filler + 3).
                assert_eq!(
                    bwd_dec[filler + 1].0.jump_label(),
                    Some(Label((filler + 3) as u32))
                );
                assert_eq!(bwd_dec[filler + 2].0, Bytecode::Jmp(Label(0)));
                assert_eq!(
                    bwd_dec[filler + 3],
                    (Bytecode::Returnundefined, bwd_offsets[filler + 2])
                );
            }
        }
    }
}

/// 4. Domino-cascade relaxation tests right at the exact `imm8` (`-128..=127`) boundary.
#[test]
fn domino_cascade_forward_and_backward_at_imm8_boundary() {
    // --- Forward domino chain ---
    // Build J0 -> T0 (spanning J1), J1 -> T1 (spanning J2), J2 -> T2.
    // Layout indices:
    //   0: J0(target = 126)  [2B initially]
    //   1: J1(target = 127)  [2B initially]
    //   2: J2(target = 2 + 2 + extra + 123) [2B initially]
    // Let's construct exact 1-byte `Ldundefined` runs so at tier 0:
    //   J0 is at off=0, spans J0(2) + J1(2) + J2(2) + 121 * 1B = 127 bytes -> T0 at index 124 (off=127).
    //   J1 is at off=2, spans J1(2) + J2(2) + 121 * 1B + 2 * 1B = 127 bytes -> T1 at index 126 (off=129).
    //   J2 is at off=4, spans J2(2) + (125 + trigger) * 1B = 127 + trigger bytes!
    for trigger in [0usize, 1] {
        let mut prog = Vec::new();
        prog.push(insn::Jeqz::new(Label(124))); // idx 0: off 0 -> idx 124 (off 4 + 123 = 127 at tier 0)
        prog.push(insn::Jeqz::new(Label(126))); // idx 1: off 2 -> idx 126 (off 4 + 125 = 129, disp=127 at tier 0)
        prog.push(insn::Jeqz::new(Label((128 + trigger) as u32))); // idx 2: off 4 -> off 4 + 2 + 125 + trigger = 131 + trigger (disp = 127 + trigger)
        for _ in 0..(126 + trigger) {
            prog.push(insn::Ldundefined::new()); // indices 3 .. 129 + trigger
        }
        prog.push(insn::Returnundefined::new());

        let (bytes, offsets) = encode(&prog).unwrap();
        let dec = decode(&bytes).unwrap();
        assert_eq!(dec.len(), prog.len());
        for (orig, (d, _)) in prog.iter().zip(&dec) {
            assert_eq!(orig, d);
        }

        let j0_sz = offsets[1] - offsets[0];
        let j1_sz = offsets[2] - offsets[1];
        let j2_sz = offsets[3] - offsets[2];
        if trigger == 0 {
            // Exact 127-byte displacements: zero widening occurs!
            assert_eq!((j0_sz, j1_sz, j2_sz), (2, 2, 2));
        } else {
            // J2 = 128 -> widens to 3B -> pushes J1 to 128 -> widens to 3B -> pushes J0 to 128 -> widens to 3B!
            assert_eq!((j0_sz, j1_sz, j2_sz), (3, 3, 3));
        }
    }

    // --- Backward domino chain at `-128` (`i8::MIN`) ---
    // Target T2 at idx 0 (off 0), T1 at idx 2 (off 2), T0 at idx 4 (off 4).
    // Backward jumps:
    //   B0 at idx (4 + (128 + trigger)): at tier 0, off(B0) = 4 + 128 + trigger = 132 + trigger,
    //     target T0 at off 4 -> disp = 4 - (132 + trigger) = -128 - trigger.
    //   B1 right after B0 (off = off(B0) + sz(B0)): targets idx (2 + trigger) at off (2 + trigger):
    //     at tier 0, off(B1) = 134 + trigger, disp = (2 + trigger) - (134 + trigger) = -132? Wait:
    //     to make disp(B1) == -128 at tier 0, target B1 at idx (6 + trigger) (off = 6 + trigger):
    //     (6 + trigger) - (134 + trigger) = -128! When B0 widens 2->3, off(B1) becomes 135 + trigger,
    //     so disp(B1) becomes -129 -> widens B1 2->3!
    //   B2 right after B1: at tier 0, off(B2) = 136 + trigger; target idx (8 + trigger) (off = 8 + trigger):
    //     disp(B2) = -128 at tier 0, and becomes -129 when B1 widens!
    for trigger in [0usize, 1] {
        let b0_idx = 132 + trigger;
        let b1_idx = b0_idx + 1;
        let b2_idx = b0_idx + 2;
        let mut prog = vec![insn::Ldundefined::new(); b2_idx + 2];
        prog[b0_idx] = insn::Jnez::new(Label(4));
        prog[b1_idx] = insn::Jnez::new(Label((6 + trigger) as u32));
        prog[b2_idx] = insn::Jnez::new(Label((8 + trigger) as u32));
        prog[b2_idx + 1] = insn::Returnundefined::new();

        let (bytes, offsets) = encode(&prog).unwrap();
        let dec = decode(&bytes).unwrap();
        assert_eq!(dec.len(), prog.len());
        for (orig, (d, _)) in prog.iter().zip(&dec) {
            assert_eq!(orig, d);
        }

        let b0_sz = offsets[b0_idx + 1] - offsets[b0_idx];
        let b1_sz = offsets[b1_idx + 1] - offsets[b1_idx];
        let b2_sz = offsets[b2_idx + 1] - offsets[b2_idx];
        if trigger == 0 {
            assert_eq!((b0_sz, b1_sz, b2_sz), (2, 2, 2));
        } else {
            assert_eq!((b0_sz, b1_sz, b2_sz), (3, 3, 3));
        }
    }
}
