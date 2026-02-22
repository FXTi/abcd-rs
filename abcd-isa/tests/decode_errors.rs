use abcd_isa::*;

#[test]
fn decode_empty_is_ok() {
    let result = decode(&[]).unwrap();
    assert!(result.is_empty());
}

#[test]
fn decode_invalid_opcode() {
    // Encode a valid instruction, then corrupt the first byte.
    let (mut bytes, _) = encode(&[insn::Ldundefined::new()]).unwrap();
    // 0xFF is in the prefix range; with only 1 byte total, the decoder
    // sees a prefix byte with no second byte and reports Truncated.
    bytes[0] = 0xFF;
    let err = decode(&bytes).unwrap_err();
    assert_eq!(
        err,
        DecodeError::Truncated(0),
        "0xFF prefix byte with no second byte should be Truncated(0), got {err}"
    );
}

#[test]
fn decode_truncated_single() {
    // Encode a multi-byte instruction, then truncate.
    let (bytes, _) = encode(&[insn::Ldai::new(Imm(42))]).unwrap();
    assert!(bytes.len() > 1, "ldai should be multi-byte");
    let err = decode(&bytes[..1]).unwrap_err();
    assert!(
        matches!(err, DecodeError::Truncated(0)),
        "expected Truncated(0), got {err}"
    );
}

#[test]
fn decode_truncated_mid_stream() {
    // Two instructions, truncate the second.
    let (bytes, _) = encode(&[insn::Ldundefined::new(), insn::Ldai::new(Imm(42))]).unwrap();
    let ldundefined_size = encode(&[insn::Ldundefined::new()]).unwrap().0.len();
    // Remove last byte.
    let truncated = &bytes[..bytes.len() - 1];
    let err = decode(truncated).unwrap_err();
    match err {
        DecodeError::Truncated(offset) => assert_eq!(
            offset, ldundefined_size,
            "truncation should be reported at the start of the second instruction"
        ),
        other => panic!("expected Truncated, got {other}"),
    }
}

#[test]
fn decode_truncated_prefix_byte() {
    // A single prefix byte (>= min_prefix_opcode) with no second byte.
    let prefix_min = unsafe { abcd_isa_sys::isa_min_prefix_opcode() };
    let err = decode(&[prefix_min]).unwrap_err();
    assert!(
        matches!(err, DecodeError::Truncated(0)),
        "expected Truncated(0), got {err}"
    );
}

#[test]
fn decode_invalid_opcode_mid_stream() {
    // Encode two instructions, corrupt the second's opcode byte.
    let (mut bytes, _) = encode(&[insn::Ldundefined::new(), insn::Ldundefined::new()]).unwrap();
    let first_size = encode(&[insn::Ldundefined::new()]).unwrap().0.len();
    // Overwrite second instruction's opcode with 0xFF (a prefix byte).
    // Since 0xFF is a prefix and there's no room for a second byte,
    // the decoder reports Truncated at the corrupted offset.
    bytes[first_size] = 0xFF;
    let err = decode(&bytes).unwrap_err();
    assert_eq!(
        err,
        DecodeError::Truncated(first_size),
        "0xFF prefix at offset {first_size} with no second byte should be Truncated"
    );
}

#[test]
fn decode_invalid_jump_target_non_boundary() {
    // Encode a program with a jump, then patch the jump offset to point
    // to the middle of a multi-byte instruction.
    //
    // ldai(42) encodes to 5 bytes, jmp(0) backward uses imm8 (2 bytes).
    // Layout: [ldai:5 bytes][jmp_opcode:1][offset:1]
    // Patch the 1-byte offset so the jump lands at byte 1 (middle of ldai).
    let program = [insn::Ldai::new(Imm(42)), insn::Jmp::new(Label(0))];
    let mut patched = encode(&program).unwrap().0;
    let ldai_size = encode(&[insn::Ldai::new(Imm(42))]).unwrap().0.len();
    let jmp_size = patched.len() - ldai_size;

    // The jmp instruction is [opcode:1][offset:N]. Patch the offset field.
    let offset_start = ldai_size + 1;
    let offset_len = jmp_size - 1;
    assert!(offset_len > 0, "jmp should have an offset field");

    // Target byte 1 (middle of ldai). Jump is at byte ldai_size.
    // Relative offset = 1 - ldai_size.
    let target_offset = 1i64 - ldai_size as i64;
    match offset_len {
        1 => patched[offset_start] = target_offset as i8 as u8,
        2 => patched[offset_start..offset_start + 2]
            .copy_from_slice(&(target_offset as i16).to_le_bytes()),
        4 => patched[offset_start..offset_start + 4]
            .copy_from_slice(&(target_offset as i32).to_le_bytes()),
        _ => panic!("unexpected jmp offset field size: {offset_len}"),
    }

    let err = decode(&patched).unwrap_err();
    assert!(
        matches!(err, DecodeError::InvalidJumpTarget { .. }),
        "expected InvalidJumpTarget, got {err}"
    );
}

#[test]
fn decode_invalid_jump_target_negative_overflow() {
    // Encode a self-jump, then patch the offset to a large negative value.
    // jmp(0) self-loop uses imm8 encoding: [opcode:1][offset:1] = 2 bytes.
    let (mut bytes, _) = encode(&[insn::Jmp::new(Label(0))]).unwrap();
    let offset_len = bytes.len() - 1; // everything after the opcode byte
    assert!(offset_len > 0, "jmp should have an offset field");

    // Patch offset to the most negative value for this encoding width.
    match offset_len {
        1 => bytes[1] = i8::MIN as u8,
        2 => bytes[1..3].copy_from_slice(&i16::MIN.to_le_bytes()),
        4 => bytes[1..5].copy_from_slice(&i32::MIN.to_le_bytes()),
        _ => panic!("unexpected jmp offset field size: {offset_len}"),
    }
    let err = decode(&bytes).unwrap_err();
    assert!(
        matches!(err, DecodeError::InvalidJumpTarget { .. }),
        "expected InvalidJumpTarget, got {err}"
    );
}
