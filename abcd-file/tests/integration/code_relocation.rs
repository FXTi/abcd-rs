use abcd_file::{AccessFlags, Builder, CodeEntity, EntityRef, LiteralValue, Type, decode};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, encode};

#[test]
fn forward_and_same_named_references_relocate_after_layout() {
    let mut builder = Builder::new();
    builder.set_api(24, "");
    let class = builder.add_global_class();
    let other_class = builder.add_class("LOther;");
    let proto = builder.create_proto(Type::Void, &[]);
    // Invalid placeholder indices must be replaced, not used as handles.
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = encode(&[
        Bytecode::Definefunc(Imm(0), placeholder, Imm(0)),
        Bytecode::LdaStr(placeholder),
        Bytecode::Createarraywithbuffer(Imm(1), placeholder),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let owner = builder.class_add_method(class, "caller", proto, AccessFlags::STATIC, &code, 0, 0);
    let (ret, _) = encode(&[Bytecode::Returnundefined]).unwrap();
    builder.class_add_method(class, "same", proto, AccessFlags::STATIC, &ret, 0, 0);
    let target =
        builder.class_add_method(other_class, "same", proto, AccessFlags::STATIC, &ret, 0, 0);
    let name = builder.add_string("same");
    let array = builder.add_literal_array("payload");
    builder.literal_array_add_integer(array, 42);
    builder
        .relocate_code_id(owner, offsets[0], 0, CodeEntity::Method(target))
        .unwrap();
    builder
        .relocate_code_id(owner, offsets[1], 0, CodeEntity::String(name))
        .unwrap();
    builder
        .relocate_code_id(owner, offsets[2], 0, CodeEntity::LiteralArray(array))
        .unwrap();
    builder.deduplicate();
    let file = decode(&builder.finalize().unwrap()).unwrap();
    let caller = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("caller"))
        .unwrap()
        .1;
    let target_offset = file.class_by_str("LOther;").unwrap().methods[0].offset;
    let body = caller.body.as_ref().unwrap();
    let bcs = body.bytecodes();
    let method_id = bcs[0].entity_operands()[0].1;
    let EntityRef::Method(target_idx) = body.entities[&(EntityKind::MethodId, method_id.0)] else {
        panic!("expected EntityRef::Method");
    };
    let (_, _, resolved_target) = file.method_by_idx(target_idx).expect("target method");
    assert_eq!(resolved_target.offset, target_offset);

    let string_id = bcs[1].entity_operands()[0].1;
    let EntityRef::String {
        id: str_sid,
        source_offset: Some(string_offset),
    } = body.entities[&(EntityKind::StringId, string_id.0)]
    else {
        panic!("expected EntityRef::String with source_offset");
    };
    assert_ne!(
        string_offset, target_offset,
        "same text must not collapse method/string identity"
    );
    assert_eq!(file.strings.resolve(str_sid), Some("same"));

    let array_id = bcs[2].entity_operands()[0].1;
    let EntityRef::LiteralArray(la_idx) = body.entities[&(EntityKind::LiteralarrayId, array_id.0)]
    else {
        panic!("expected EntityRef::LiteralArray");
    };
    let values = &file.literal_arrays[la_idx.index()].values;
    assert!(matches!(values.as_slice(), [LiteralValue::Integer(42)]));
}

#[test]
fn invalid_id_ordinal_fails_before_output_is_returned() {
    let mut builder = Builder::new();
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let (code, _) = encode(&[Bytecode::Returnundefined]).unwrap();
    let owner = builder.class_add_method(class, "f", proto, AccessFlags::STATIC, &code, 0, 0);
    let text = builder.add_string("unused");
    builder
        .relocate_code_id(owner, 0, 0, CodeEntity::String(text))
        .unwrap();
    assert!(
        builder.finalize().is_err(),
        "return has no entity operand to patch"
    );
}
