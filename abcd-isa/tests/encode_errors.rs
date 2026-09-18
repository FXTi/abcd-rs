use abcd_isa::*;

#[test]
fn encode_empty_is_ok() {
    let (bytes, _) = encode(&[]).unwrap();
    let decoded = decode(&bytes).unwrap();
    assert!(decoded.is_empty());
}

#[test]
fn encode_label_oob_forward() {
    let err = encode(&[insn::Jmp::new(Label(1))]).unwrap_err();
    assert!(
        matches!(err, EncodeError::LabelOutOfBounds(1, 1)),
        "expected LabelOutOfBounds(1, 1), got {err}"
    );
}

#[test]
fn encode_label_oob_large() {
    let err = encode(&[insn::Jmp::new(Label(100))]).unwrap_err();
    assert!(
        matches!(err, EncodeError::LabelOutOfBounds(100, 1)),
        "expected LabelOutOfBounds(100, 1), got {err}"
    );
}

#[test]
fn encode_label_oob_conditional() {
    let err = encode(&[insn::Jeqz::new(Label(5))]).unwrap_err();
    assert!(matches!(err, EncodeError::LabelOutOfBounds(5, 1)));
}

#[test]
fn encode_label_oob_reg_label() {
    let err = encode(&[insn::Jeq::new(Reg(0), Label(5))]).unwrap_err();
    assert!(matches!(err, EncodeError::LabelOutOfBounds(5, 1)));
}

#[test]
fn encode_label_at_boundary_ok() {
    let program = [insn::Jmp::new(Label(1)), insn::Ldundefined::new()];
    let (bytes, _) = encode(&program).unwrap();
    assert!(!bytes.is_empty(), "encoded bytes should not be empty");
    let decoded = decode(&bytes).unwrap();
    assert_eq!(decoded.len(), 2, "should decode back to 2 instructions");
}

#[test]
fn encode_multiple_jumps_one_invalid() {
    let program = [
        insn::Jmp::new(Label(2)),
        insn::Jeqz::new(Label(10)),
        insn::Ldundefined::new(),
    ];
    let err = encode(&program).unwrap_err();
    assert!(matches!(err, EncodeError::LabelOutOfBounds(10, 3)));
}

#[test]
fn encode_error_display() {
    // Verify error messages are well-formed for all variants we can construct.
    let err = encode(&[insn::Jmp::new(Label(1))]).unwrap_err();
    let msg = format!("{err}");
    assert!(
        msg.contains("out of bounds"),
        "LabelOutOfBounds message: {msg}"
    );
}

// --- Operand range validation (audit #2: used to silently truncate) ---

#[test]
fn encode_imm_out_of_range_is_an_error_not_truncation() {
    // Ldlexvar's widest immediate is u8; 300 does not fit.
    // Before the dispatch validated ranges, this encoded as Imm(44).
    let err = encode(&[insn::Ldlexvar::new(Imm(300), Imm(0))]).unwrap_err();
    assert!(
        matches!(err, EncodeError::OperandOutOfRange),
        "expected OperandOutOfRange, got {err}"
    );
}

#[test]
fn encode_negative_imm_for_unsigned_operand_is_an_error() {
    let err = encode(&[insn::Ldlexvar::new(Imm(-1), Imm(0))]).unwrap_err();
    assert!(
        matches!(err, EncodeError::OperandOutOfRange),
        "expected OperandOutOfRange, got {err}"
    );
}

#[test]
fn encode_reg_out_of_range_is_an_error() {
    // callarg1's register operand is 8-bit; 300 does not fit.
    let err = encode(&[insn::Callarg1::new(Imm(0), Reg(300))]).unwrap_err();
    assert!(
        matches!(err, EncodeError::OperandOutOfRange),
        "expected OperandOutOfRange, got {err}"
    );
}

#[test]
fn encode_imm32_boundaries_still_accepted() {
    // i32-range immediates must keep encoding (no false rejection).
    assert!(encode(&[insn::Ldai::new(Imm(i32::MAX as i64))]).is_ok());
    assert!(encode(&[insn::Ldai::new(Imm(i32::MIN as i64))]).is_ok());
    // Beyond i32 must be rejected.
    let err = encode(&[insn::Ldai::new(Imm(i32::MAX as i64 + 1))]).unwrap_err();
    assert!(matches!(err, EncodeError::OperandOutOfRange));
}

#[test]
fn encode_boundary_values_accepted_at_edges() {
    // Exact storage-width edges must pass.
    assert!(encode(&[insn::Ldlexvar::new(Imm(255), Imm(255))]).is_ok());
    assert!(encode(&[insn::Mov::new(Reg(65535), Reg(65535))]).is_ok());
}
