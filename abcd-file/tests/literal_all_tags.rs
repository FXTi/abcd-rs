//! Test group F — literal arrays: nested references and the full literal
//! tag matrix on the decode side (patched raw pairs), plus the typed
//! ARRAY_* segment semantics.

use abcd_file::{AccessFlags, Builder, LiteralValue, SourceLang, Type, decode, encode};

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

    // The nested reference must also survive an encode round-trip: the
    // encoder resolves the table index to the re-emitted array and the
    // decoder rewrites the new file offset back to a table index.
    let encoded = encode(&file).expect("encode");
    let file2 = decode(&encoded).expect("decode re-encoded");
    assert_eq!(file2.literal_arrays.len(), 2);
    let outer2 = file2
        .literal_arrays
        .iter()
        .find(|la| {
            la.values
                .iter()
                .any(|v| matches!(v, LiteralValue::LiteralArray(_)))
        })
        .expect("outer array with a nested reference (re-encoded)");
    match &outer2.values[0] {
        LiteralValue::LiteralArray(idx) => {
            let referenced = &file2.literal_arrays[idx.0 as usize].values;
            assert_eq!(referenced, &vec![LiteralValue::Integer(5)]);
        }
        other => panic!("expected nested LiteralArray after re-encode, got {other:?}"),
    }
}

/// Finding #4, model level: typed ARRAY_* literal values must be DELIVERED
/// to the model — the tolerant enumerator once returned without invoking
/// the callback for ARRAY_U1…ARRAY_STRING, silently dropping every
/// typed-array literal. (Bridge-level delivery is pinned by abcd-file-sys's
/// `literal_array_tag_value_is_delivered`; this pins the model mapping.)
///
/// Format facts (vendored `literal_data_accessor-inl.h:94-115`): an ARRAY_*
/// item is always the LAST item of its literal array — the tag byte is
/// followed by the array payload, not by more [tag][value] pairs — and the
/// delivered value is the payload's file offset, delivered once.
#[test]
fn typed_array_tags_decode_to_model_values() {
    let (mut data, array_off) = build_one_string_array();

    // In-place rewrite (exactly the old 9 bytes, so no offset fixups): the
    // array holds a single ARRAY_U8 literal. Per the vendored format an
    // ARRAY_* item is always LAST — the tag byte is followed by the array
    // payload, not by more [tag][value] pairs — and the delivered value is
    // the payload's file offset, delivered once (vendor
    // `literal_data_accessor-inl.h:94-115`).
    let payload_off = (array_off + 4 + 1) as u32; // after count + tag byte
    let new_arr: Vec<u8> = [
        &2u32.to_le_bytes()[..], // one literal = one [tag][payload] pair
        &[0x0b],                 // ARRAY_U8
        &0u32.to_le_bytes()[..], // payload: element count 0 (no elements)
    ]
    .concat();
    assert_eq!(new_arr.len(), 4 + 5, "must match the old array size");
    data[array_off..array_off + new_arr.len()].copy_from_slice(&new_arr);

    let file = decode(&data).expect("decode");
    let vals = &file.literal_arrays[0].values;
    assert_eq!(
        vals.as_slice(),
        &[LiteralValue::ArrayU8(abcd_file::LiteralArrayIdx(
            payload_off
        ))],
        "the typed-array value must be delivered, not silently dropped"
    );
}

// ---------------------------------------------------------------------------
// Encode-side matrix (decode -> hand-built model -> encode -> decode)
// ---------------------------------------------------------------------------

/// Canonical text form of a literal value: StringIds are resolved through
/// the pool and method offsets through the method table (both are
/// pool/layout-local and differ between two decodes of one model).
/// Typed-array (`ArrayXxx`) values compare by discriminant only: their
/// payload is a file offset that legitimately moves on re-encode.
fn canon_literal(file: &abcd_file::File, v: &LiteralValue) -> String {
    let r = |sid: abcd_file::StringId| file.strings.resolve(sid).unwrap_or("<dangling>");
    let method_name_at = |off: u32| {
        if let Some((_, m)) = file.all_methods().find(|(_, m)| m.offset == off) {
            return file.strings.resolve(m.name).unwrap_or("?").to_string();
        }
        // Offset 0 is the hand-built-model sentinel; the encoder falls back
        // to entity_map[0] for it, so do the same here.
        if off == 0
            && let Some(sid) = file.entity_map.get(&0)
        {
            return file.strings.resolve(*sid).unwrap_or("?").to_string();
        }
        "<unresolved>".to_string()
    };
    match v {
        LiteralValue::String(sid) => format!("String({})", r(*sid)),
        LiteralValue::EtsImplements(sid) => format!("EtsImplements({})", r(*sid)),
        LiteralValue::Method(off) => format!("Method({})", method_name_at(*off)),
        LiteralValue::GeneratorMethod(off) => {
            format!("GeneratorMethod({})", method_name_at(*off))
        }
        LiteralValue::AsyncGeneratorMethod(off) => {
            format!("AsyncGeneratorMethod({})", method_name_at(*off))
        }
        LiteralValue::Getter(off) => format!("Getter({})", method_name_at(*off)),
        LiteralValue::Setter(off) => format!("Setter({})", method_name_at(*off)),
        // Content-based recursion: the table order is not guaranteed, so
        // comparing by content is order-independent.
        LiteralValue::LiteralArray(idx) => format!(
            "LiteralArray[{}]",
            file.literal_arrays[idx.0 as usize]
                .values
                .iter()
                .map(|v| canon_literal(file, v))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        LiteralValue::ArrayU1(_) => "ArrayU1".into(),
        LiteralValue::ArrayU8(_) => "ArrayU8".into(),
        LiteralValue::ArrayI8(_) => "ArrayI8".into(),
        LiteralValue::ArrayU16(_) => "ArrayU16".into(),
        LiteralValue::ArrayI16(_) => "ArrayI16".into(),
        LiteralValue::ArrayU32(_) => "ArrayU32".into(),
        LiteralValue::ArrayI32(_) => "ArrayI32".into(),
        LiteralValue::ArrayU64(_) => "ArrayU64".into(),
        LiteralValue::ArrayI64(_) => "ArrayI64".into(),
        LiteralValue::ArrayF32(_) => "ArrayF32".into(),
        LiteralValue::ArrayF64(_) => "ArrayF64".into(),
        LiteralValue::ArrayString(_) => "ArrayString".into(),
        other => format!("{other:?}"),
    }
}

/// Canonical form of a whole literal-array TABLE, order-independent.
fn canon_table(file: &abcd_file::File) -> Vec<String> {
    let mut v: Vec<String> = file
        .literal_arrays
        .iter()
        .map(|la| {
            la.values
                .iter()
                .map(|v| canon_literal(file, v))
                .collect::<Vec<_>>()
                .join(", ")
        })
        .collect();
    v.sort();
    v
}

/// The full `LiteralValue` matrix through the model literal-array encode
/// path (`encode_literal_value`): every scalar kind, all five
/// method-reference kinds (by source offset AND the offset-0 name fallback
/// for hand-built models), a nested literal-array reference, the index
/// kinds, and each of the 12 typed-array kinds (each in its OWN array —
/// upstream emits an ARRAY_* item only as the LAST item of an array).
#[test]
fn full_literal_tag_matrix_encodes() {
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
    let data = b.finalize().expect("finalize");
    let mut file = decode(&data).expect("decode");

    let target_off = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .map(|(_, m)| m.offset)
        .expect("method");
    assert_ne!(target_off, 0);

    let str_sid = file.strings.get_or_intern("lit_str");
    let impl_sid = file.strings.get_or_intern("LImpl;");
    // The offset-0 name fallback (hand-built models carry no offsets).
    let target_name = file.strings.get("func_main_0").expect("interned");
    file.entity_map.insert(0, target_name);

    file.literal_arrays = vec![
        abcd_file::LiteralArray {
            values: vec![
                LiteralValue::Bool(true),
                LiteralValue::Integer8(5),
                LiteralValue::Integer(42),
                LiteralValue::Float(1.5),
                LiteralValue::Double(2.5),
                LiteralValue::String(str_sid),
                LiteralValue::Method(target_off),
                LiteralValue::GeneratorMethod(target_off),
                LiteralValue::AsyncGeneratorMethod(target_off),
                LiteralValue::Getter(target_off),
                LiteralValue::Setter(target_off),
                LiteralValue::Method(0), // offset-0 name fallback
                LiteralValue::Accessor(1),
                LiteralValue::MethodAffiliate(9),
                LiteralValue::LiteralArray(abcd_file::LiteralArrayIdx(1)),
                LiteralValue::LiteralBufferIndex(abcd_file::LiteralArrayIdx(7)),
                LiteralValue::BuiltinTypeIndex(3),
                LiteralValue::EtsImplements(impl_sid),
                LiteralValue::NullValue(0),
            ],
        },
        // Nested reference target (referenced by index 1 above).
        abcd_file::LiteralArray {
            values: vec![LiteralValue::Integer(99)],
        },
    ];
    // One single-element array per typed-array kind (ARRAY_* is always the
    // last item of its array upstream). LiteralArrayIdx(0) encodes as an
    // empty payload (element count 0), which reads back cleanly.
    for v in [
        LiteralValue::ArrayU1(abcd_file::LiteralArrayIdx(0)),
        LiteralValue::ArrayU8(abcd_file::LiteralArrayIdx(0)),
        LiteralValue::ArrayI8(abcd_file::LiteralArrayIdx(0)),
        LiteralValue::ArrayU16(abcd_file::LiteralArrayIdx(0)),
        LiteralValue::ArrayI16(abcd_file::LiteralArrayIdx(0)),
        LiteralValue::ArrayU32(abcd_file::LiteralArrayIdx(0)),
        LiteralValue::ArrayI32(abcd_file::LiteralArrayIdx(0)),
        LiteralValue::ArrayU64(abcd_file::LiteralArrayIdx(0)),
        LiteralValue::ArrayI64(abcd_file::LiteralArrayIdx(0)),
        LiteralValue::ArrayF32(abcd_file::LiteralArrayIdx(0)),
        LiteralValue::ArrayF64(abcd_file::LiteralArrayIdx(0)),
        LiteralValue::ArrayString(abcd_file::LiteralArrayIdx(0)),
    ] {
        file.literal_arrays
            .push(abcd_file::LiteralArray { values: vec![v] });
    }

    let before = canon_table(&file);
    let encoded = encode(&file).expect("encode");
    let file2 = decode(&encoded).expect("decode re-encoded");
    let after = canon_table(&file2);
    assert_eq!(
        before, after,
        "literal tag matrix must round-trip through encode"
    );
}
