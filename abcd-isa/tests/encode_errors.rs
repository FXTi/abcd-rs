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
