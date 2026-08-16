//! Test group F — literal arrays: nested references and the full literal
//! tag matrix on the decode side (patched raw pairs), plus the typed
//! ARRAY_* segment semantics.

use abcd_file::{AccessFlags, Builder, LiteralValue, SourceLang, Type, decode};

/// Build a file whose literal array holds one string element, and return
/// (bytes, array_offset) so tests can rewrite the array body.
fn build_one_string_array() -> (Vec<u8>, usize) {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);

    let la = b.add_literal_array("s");
    let s = b.add_string("hello");
    b.literal_array_add_string(la, s);

    let data = b.finalize().expect("finalize");
    let literalarray_idx_off = u32::from_le_bytes(data[48..52].try_into().unwrap()) as usize;
    let array_off = u32::from_le_bytes(
        data[literalarray_idx_off..literalarray_idx_off + 4]
            .try_into()
            .unwrap(),
    ) as usize;
    (data, array_off)
}

#[test]
fn full_literal_tag_matrix_decodes() {
    let (mut data, array_off) = build_one_string_array();
    let orig_str_off: [u8; 4] = data[array_off + 5..array_off + 9].try_into().unwrap();

    // Rebuild the array: count = 2 * K pairs, first pair is the original
    // [STRING][offset], then patched pairs for every scalar tag.
    let mut body: Vec<u8> = Vec::new();
    body.extend_from_slice(&[0x05]); // STRING
    body.extend_from_slice(&orig_str_off);
    body.extend_from_slice(&[0x06, 0x00, 0x00, 0x00, 0x00]); // METHOD off 0
    body.extend_from_slice(&[0x01, 0x01]); // BOOL true
    body.extend_from_slice(&[0x02]); // INTEGER 42
    body.extend_from_slice(&42u32.to_le_bytes());
    body.extend_from_slice(&[0x03]); // FLOAT 1.5
    body.extend_from_slice(&1.5f32.to_bits().to_le_bytes());
    body.extend_from_slice(&[0x04]); // DOUBLE 2.5
    body.extend_from_slice(&2.5f64.to_bits().to_le_bytes());
    body.extend_from_slice(&[0x07, 0x00, 0x00, 0x00, 0x00]); // GENERATORMETHOD off 0
    body.extend_from_slice(&[0x08, 0x01]); // ACCESSOR 1
    body.extend_from_slice(&[0x09, 0x01, 0x00]); // METHODAFFILIATE 1
    body.extend_from_slice(&[0x16, 0x00, 0x00, 0x00, 0x00]); // ASYNCGENERATORMETHOD 0
    body.extend_from_slice(&[0x17]); // LITERALBUFFERINDEX 7
    body.extend_from_slice(&7u32.to_le_bytes());
    body.extend_from_slice(&[0x19, 0x03]); // BUILTINTYPEINDEX 3
    body.extend_from_slice(&[0x1a, 0x00, 0x00, 0x00, 0x00]); // GETTER 0
    body.extend_from_slice(&[0x1b, 0x00, 0x00, 0x00, 0x00]); // SETTER 0
    body.extend_from_slice(&[0xff, 0x00]); // NULLVALUE

    // Each logical literal is a [tag][value] pair = 2 items; 15 literals.
    let item_count = 15 * 2;
    let mut new_arr = Vec::new();
    new_arr.extend_from_slice(&(item_count as u32).to_le_bytes());
    new_arr.extend_from_slice(&body);

    // Write the new array over the old one (grow into the slack before the
    // next section; the file is ours, safe to append).
    let old_len = 4 + 5; // count + [tag][4B offset]
    let mut rebuilt: Vec<u8> = Vec::new();
    rebuilt.extend_from_slice(&data[..array_off]);
    rebuilt.extend_from_slice(&new_arr);
    rebuilt.extend_from_slice(&data[array_off + old_len..]);
    data = rebuilt;
    let file_size = data.len() as u32;
    data[16..20].copy_from_slice(&file_size.to_le_bytes());

    let file = decode(&data).expect("decode");
    let la = &file.literal_arrays[0];
    let vals = &la.values;
    assert_eq!(vals.len(), 15);
    assert!(matches!(vals[0], LiteralValue::String(_)));
    assert_eq!(vals[1], LiteralValue::Method(0));
    assert_eq!(vals[2], LiteralValue::Bool(true));
    assert_eq!(vals[3], LiteralValue::Integer(42));
    assert_eq!(vals[4], LiteralValue::Float(1.5));
    assert_eq!(vals[5], LiteralValue::Double(2.5));
    assert_eq!(vals[6], LiteralValue::GeneratorMethod(0));
    assert_eq!(vals[7], LiteralValue::Accessor(1));
    assert_eq!(vals[8], LiteralValue::MethodAffiliate(1));
    assert_eq!(vals[9], LiteralValue::AsyncGeneratorMethod(0));
    assert_eq!(
        vals[10],
        LiteralValue::LiteralBufferIndex(abcd_file::LiteralArrayIdx(7))
    );
    assert_eq!(vals[11], LiteralValue::BuiltinTypeIndex(3));
    assert_eq!(vals[12], LiteralValue::Getter(0));
    assert_eq!(vals[13], LiteralValue::Setter(0));
    assert_eq!(vals[14], LiteralValue::NullValue(0));
}

#[test]
fn nested_literal_arrays_roundtrip() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);

    let inner = b.add_literal_array("inner");
    b.literal_array_add_integer(inner, 5);
    let outer = b.add_literal_array("outer");
    b.literal_array_add_literalarray(outer, inner);

    let data = b.finalize().expect("finalize");
    let file = decode(&data).expect("decode");
    assert_eq!(file.literal_arrays.len(), 2);
    // The literal-array table order is not guaranteed (upstream keeps an
    // unordered map), so locate the outer array by its content.
    let outer = file
        .literal_arrays
        .iter()
        .find(|la| {
            la.values
                .iter()
                .any(|v| matches!(v, LiteralValue::LiteralArray(_)))
        })
        .expect("outer array with a nested reference");
    assert_eq!(outer.values.len(), 1);
    match &outer.values[0] {
        LiteralValue::LiteralArray(idx) => {
            let referenced = &file.literal_arrays[idx.0 as usize].values;
            assert_eq!(referenced, &vec![LiteralValue::Integer(5)]);
        }
        other => panic!("expected nested LiteralArray, got {other:?}"),
    }
}
