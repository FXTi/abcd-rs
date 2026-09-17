use abcd_isa::{
    Bytecode, EntityId, EntityKind, Imm, Reg, RelocationError, decode, encode, relocate_entity_id,
};

#[test]
fn rewrites_the_selected_id_without_changing_other_operands() {
    let instruction =
        Bytecode::Defineclasswithbuffer(Imm(3), EntityId(4), EntityId(5), Imm(6), Reg(7));
    let (mut bytes, _) = encode(&[instruction, Bytecode::Returnundefined]).unwrap();
    let size = bytes.len();
    relocate_entity_id(&mut bytes, 1, EntityId(300)).unwrap();
    let decoded = decode(&bytes).unwrap();
    assert_eq!(
        decoded[0].0.entity_operands(),
        vec![
            (EntityKind::MethodId, EntityId(4)),
            (EntityKind::LiteralarrayId, EntityId(300))
        ]
    );
    assert!(matches!(
        decoded[0].0,
        Bytecode::Defineclasswithbuffer(Imm(3), _, _, Imm(6), Reg(7))
    ));
    assert!(matches!(decoded[1].0, Bytecode::Returnundefined));
    assert_eq!(bytes.len(), size);
}

#[test]
fn failed_relocations_leave_bytes_unchanged() {
    let (mut bytes, _) = encode(&[Bytecode::LdaStr(EntityId(2))]).unwrap();
    let original = bytes.clone();
    assert_eq!(
        relocate_entity_id(&mut bytes, 1, EntityId(0)),
        Err(RelocationError::MissingOperand(1))
    );
    assert_eq!(bytes, original);
    assert_eq!(
        relocate_entity_id(&mut bytes, 0, EntityId(u32::MAX)),
        Err(RelocationError::IdOutOfRange(u32::MAX))
    );
    assert_eq!(bytes, original);
    assert_eq!(
        relocate_entity_id(&mut bytes[..1], 0, EntityId(0)),
        Err(RelocationError::InvalidInstruction)
    );
    assert_eq!(bytes, original);
}
