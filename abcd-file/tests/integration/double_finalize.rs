//! Double-finalize contract. The Phase 0 audit (P2 list) claimed a second
//! `Builder::finalize` duplicates literal items and wrongly re-applies code
//! relocations because `literal_items_staging`/`code_id_relocations` are
//! never cleared. Investigated for the Phase 5 sweep: the claim is a false
//! positive — vendored `LiteralArrayItem::AddItems` is `items_.assign`
//! (replace, not append) and `BytecodeInst::UpdateId` overwrites the operand
//! field, so both re-applications are idempotent (and the retained staging
//! is load-bearing for items staged AFTER a first finalize). These tests
//! pin that contract so a future vendor change (e.g. AddItems switching to
//! append) fails loudly here instead of corrupting output.

use abcd_file::{AccessFlags, Builder, CodeEntity, LiteralValue, Type, decode};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, encode};

#[test]
fn second_finalize_produces_identical_bytes() {
    let mut builder = Builder::new();
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    // Placeholder operands, relocated after layout below. The literal array
    // must be referenced by an instruction, or the writer does not emit it.
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = encode(&[
        Bytecode::LdaStr(placeholder),
        Bytecode::Createarraywithbuffer(Imm(1), placeholder),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let owner = builder.class_add_method(class, "f", proto, AccessFlags::STATIC, &code, 0, 0);
    let text = builder.add_string("hello");
    let array = builder.add_literal_array("payload");
    builder.literal_array_add_integer(array, 42);
    builder.literal_array_add_string(array, text);
    builder
        .relocate_code_id(owner, offsets[0], 0, CodeEntity::String(text))
        .unwrap();
    builder
        .relocate_code_id(owner, offsets[1], 0, CodeEntity::LiteralArray(array))
        .unwrap();

    let first = builder.finalize().unwrap();
    let second = builder.finalize().unwrap();
    assert_eq!(
        first, second,
        "second finalize must be idempotent: staged literal items and code \
         relocations are consumed by the first finalize"
    );

    // The finalized file must contain exactly one copy of the staged items.
    let file = decode(&second).unwrap();
    let f = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("f"))
        .unwrap()
        .1;
    let body = f.body.as_ref().unwrap();
    let array_id = body.bytecodes[1].entity_operands()[0].1;
    let array_offset = body.entity_offsets[&(EntityKind::LiteralarrayId, array_id.0)];
    let values = &file.literal_arrays[file.literal_array_offsets[&array_offset] as usize].values;
    assert_eq!(
        values.len(),
        2,
        "staged items must not be duplicated by a second finalize: {values:?}"
    );
    assert!(matches!(values[0], LiteralValue::Integer(42)));
    assert!(
        matches!(values[1], LiteralValue::String(id) if file.strings.resolve(id) == Some("hello"))
    );
}

/// Items staged AFTER a first finalize must accumulate onto the earlier
/// ones (the bridge retains `literal_items_staging` and AddItems assigns),
/// and the re-applied relocation must track the shifted layout.
#[test]
fn staged_items_added_after_finalize_accumulate() {
    let mut builder = Builder::new();
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = encode(&[
        Bytecode::Createarraywithbuffer(Imm(1), placeholder),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let owner = builder.class_add_method(class, "f", proto, AccessFlags::STATIC, &code, 0, 0);
    let array = builder.add_literal_array("payload");
    builder.literal_array_add_integer(array, 1);
    builder
        .relocate_code_id(owner, offsets[0], 0, CodeEntity::LiteralArray(array))
        .unwrap();
    let first = builder.finalize().unwrap();

    // Stage one more item and finalize again: the array must hold both.
    builder.literal_array_add_integer(array, 2);
    let second = builder.finalize().unwrap();
    assert_ne!(
        first, second,
        "the second finalize must reflect the newly staged item"
    );

    let file = decode(&second).unwrap();
    let f = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("f"))
        .unwrap()
        .1;
    let body = f.body.as_ref().unwrap();
    let array_id = body.bytecodes[0].entity_operands()[0].1;
    let array_offset = body.entity_offsets[&(EntityKind::LiteralarrayId, array_id.0)];
    let values = &file.literal_arrays[file.literal_array_offsets[&array_offset] as usize].values;
    assert!(
        matches!(
            values.as_slice(),
            [LiteralValue::Integer(1), LiteralValue::Integer(2)]
        ),
        "items staged across two finalizes must accumulate: {values:?}"
    );
}
