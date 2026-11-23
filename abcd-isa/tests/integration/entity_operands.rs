use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Reg};

#[test]
fn reports_each_entity_role_in_signature_order() {
    assert_eq!(
        Bytecode::Defineclasswithbuffer(Imm(0), EntityId(2), EntityId(7), Imm(0), Reg(1))
            .entity_operands(),
        vec![
            (EntityKind::MethodId, EntityId(2)),
            (EntityKind::LiteralarrayId, EntityId(7))
        ]
    );
    assert_eq!(
        Bytecode::LdaStr(EntityId(0)).entity_operands(),
        vec![(EntityKind::StringId, EntityId(0))]
    );
    assert!(Bytecode::Mov(Reg(2), Reg(3)).entity_operands().is_empty());
}
