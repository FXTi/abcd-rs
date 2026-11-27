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
    let method_off = decode(&data)
        .expect("decode initial")
        .all_methods()
        .next()
        .expect("func_main_0")
        .1
        .offset
        .to_le_bytes();
    let orig_str_off: [u8; 4] = data[array_off + 5..array_off + 9].try_into().unwrap();

    // Rebuild the array: count = 2 * K pairs, first pair is the original
    // [STRING][offset], then patched pairs for every scalar tag.
    let mut body: Vec<u8> = Vec::new();
    body.extend_from_slice(&[0x05]); // STRING
    body.extend_from_slice(&orig_str_off);
    body.push(0x06); // METHOD -> MethodIdx(0)
    body.extend_from_slice(&method_off);
    body.extend_from_slice(&[0x01, 0x01]); // BOOL true
    body.extend_from_slice(&[0x02]); // INTEGER 42
    body.extend_from_slice(&42u32.to_le_bytes());
    body.extend_from_slice(&[0x03]); // FLOAT 1.5
    body.extend_from_slice(&1.5f32.to_bits().to_le_bytes());
    body.extend_from_slice(&[0x04]); // DOUBLE 2.5
    body.extend_from_slice(&2.5f64.to_bits().to_le_bytes());
    body.push(0x07); // GENERATORMETHOD -> MethodIdx(0)
    body.extend_from_slice(&method_off);
    body.extend_from_slice(&[0x08, 0x01]); // ACCESSOR 1
    body.extend_from_slice(&[0x09, 0x01, 0x00]); // METHODAFFILIATE 1
    body.push(0x16); // ASYNCGENERATORMETHOD -> MethodIdx(0)
    body.extend_from_slice(&method_off);
    body.extend_from_slice(&[0x17]); // LITERALBUFFERINDEX header slot 0 -> LiteralArrayIdx(0)
    body.extend_from_slice(&0u32.to_le_bytes());
    body.extend_from_slice(&[0x19, 0x03]); // BUILTINTYPEINDEX 3
    body.push(0x1a); // GETTER -> MethodIdx(0)
    body.extend_from_slice(&method_off);
    body.push(0x1b); // SETTER -> MethodIdx(0)
    body.extend_from_slice(&method_off);
    body.extend_from_slice(&[0xff, 0x00]); // NULLVALUE

    // Each logical literal is a [tag][value] pair = 2 items; 15 literals.
    let item_count = 15 * 2;
    let mut new_arr = Vec::new();
    new_arr.extend_from_slice(&(item_count as u32).to_le_bytes());
    new_arr.extend_from_slice(&body);

    // Append the rebuilt array at the end of the file and repoint the header
    // literal-array table slot so existing string/entity offsets stay intact.
    let literalarray_idx_off = u32::from_le_bytes(data[48..52].try_into().unwrap()) as usize;
    let new_array_off = data.len() as u32;
    data.extend_from_slice(&new_arr);
    data[literalarray_idx_off..literalarray_idx_off + 4]
        .copy_from_slice(&new_array_off.to_le_bytes());
    let file_size = data.len() as u32;
    data[16..20].copy_from_slice(&file_size.to_le_bytes());

    let file = decode(&data).expect("decode");
    let la = &file.literal_arrays[0];
    let vals = &la.values;
    let m0 = abcd_file::MethodIdx(0);
    assert_eq!(vals.len(), 15);
    assert_eq!(
        vals[0],
        LiteralValue::String(file.strings.get("hello").expect("hello string"))
    );
    assert_eq!(vals[1], LiteralValue::Method(m0));
    assert_eq!(vals[2], LiteralValue::Bool(true));
    assert_eq!(vals[3], LiteralValue::Integer(42));
    assert_eq!(vals[4], LiteralValue::Float(1.5));
    assert_eq!(vals[5], LiteralValue::Double(2.5));
    assert_eq!(vals[6], LiteralValue::GeneratorMethod(m0));
    assert_eq!(vals[7], LiteralValue::Accessor(1));
    assert_eq!(vals[8], LiteralValue::MethodAffiliate(1));
    assert_eq!(vals[9], LiteralValue::AsyncGeneratorMethod(m0));
    assert_eq!(
        vals[10],
        LiteralValue::LiteralBufferIndex(abcd_file::LiteralArrayIdx(0))
    );
    assert_eq!(vals[11], LiteralValue::BuiltinTypeIndex(3));
    assert_eq!(vals[12], LiteralValue::Getter(m0));
    assert_eq!(vals[13], LiteralValue::Setter(m0));
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
    let new_arr: Vec<u8> = [
        &2u32.to_le_bytes()[..], // one literal = one [tag][payload] pair
        &[0x0b],                 // ARRAY_U8
        &0u32.to_le_bytes()[..], // payload: element count 0 (no elements)
    ]
    .concat();
    assert_eq!(new_arr.len(), 4 + 5, "must match the old array size");
    data[array_off..array_off + new_arr.len()].copy_from_slice(&new_arr);

    let file = decode(&data).expect("decode");
    assert_eq!(file.literal_arrays[0].source_offset, Some(array_off as u32));
    let vals = &file.literal_arrays[0].values;
    assert_eq!(
        vals.as_slice(),
        &[LiteralValue::ArrayU8(Vec::new())],
        "the typed-array value must decode into its owned element Vec"
    );
}

// ---------------------------------------------------------------------------
// Encode-side matrix (decode -> hand-built model -> encode -> decode)
// ---------------------------------------------------------------------------

/// Canonical text form of a literal-array slice using an explicit workstack.
fn canon_literal_slice(file: &abcd_file::File, root_values: &[LiteralValue]) -> String {
    enum Step<'a> {
        Text(&'static str),
        Slice(&'a [LiteralValue], usize),
        Val(&'a LiteralValue),
    }
    let r = |sid: abcd_file::StringId| file.strings.resolve(sid).unwrap_or("<dangling>");
    let method_name_by_idx = |idx: abcd_file::MethodIdx| {
        file.method_by_idx(idx)
            .and_then(|(_, _, m)| file.strings.resolve(m.name))
            .unwrap_or("<unresolved>")
            .to_string()
    };
    let mut out = String::new();
    let mut stack = vec![Step::Slice(root_values, 0)];
    while let Some(step) = stack.pop() {
        match step {
            Step::Text(s) => out.push_str(s),
            Step::Slice(slice, idx) => {
                if idx < slice.len() {
                    if idx > 0 {
                        out.push_str(", ");
                    }
                    stack.push(Step::Slice(slice, idx + 1));
                    stack.push(Step::Val(&slice[idx]));
                }
            }
            Step::Val(v) => match v {
                LiteralValue::String(sid) => out.push_str(&format!("String({})", r(*sid))),
                LiteralValue::EtsImplements(sid) => {
                    out.push_str(&format!("EtsImplements({})", r(*sid)));
                }
                LiteralValue::Method(idx) => {
                    out.push_str(&format!("Method({})", method_name_by_idx(*idx)));
                }
                LiteralValue::GeneratorMethod(idx) => {
                    out.push_str(&format!("GeneratorMethod({})", method_name_by_idx(*idx)));
                }
                LiteralValue::AsyncGeneratorMethod(idx) => out.push_str(&format!(
                    "AsyncGeneratorMethod({})",
                    method_name_by_idx(*idx)
                )),
                LiteralValue::Getter(idx) => {
                    out.push_str(&format!("Getter({})", method_name_by_idx(*idx)));
                }
                LiteralValue::Setter(idx) => {
                    out.push_str(&format!("Setter({})", method_name_by_idx(*idx)));
                }
                LiteralValue::LiteralArray(idx) => {
                    out.push_str("LiteralArray[");
                    stack.push(Step::Text("]"));
                    stack.push(Step::Slice(&file.literal_arrays[idx.0 as usize].values, 0));
                }
                LiteralValue::ArrayString(sids) => out.push_str(&format!(
                    "ArrayString({:?})",
                    sids.iter().map(|&s| r(s)).collect::<Vec<_>>()
                )),
                other => out.push_str(&format!("{other:?}")),
            },
        }
    }
    out
}

/// Canonical form of a whole literal-array TABLE, order-independent.
fn canon_table(file: &abcd_file::File) -> Vec<String> {
    let mut v: Vec<String> = file
        .literal_arrays
        .iter()
        .map(|la| canon_literal_slice(file, &la.values))
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

    let target_idx = abcd_file::MethodIdx(0);
    assert_eq!(
        file.method_by_idx(target_idx)
            .and_then(|(_, _, m)| file.strings.resolve(m.name)),
        Some("func_main_0")
    );

    let str_sid = file.strings.get_or_intern("lit_str");
    let impl_sid = file.strings.get_or_intern("LImpl;");

    file.literal_arrays = vec![
        abcd_file::LiteralArray::new(vec![
            LiteralValue::Bool(true),
            LiteralValue::Integer8(5),
            LiteralValue::Integer(42),
            LiteralValue::Float(1.5),
            LiteralValue::Double(2.5),
            LiteralValue::String(str_sid),
            LiteralValue::Method(target_idx),
            LiteralValue::GeneratorMethod(target_idx),
            LiteralValue::AsyncGeneratorMethod(target_idx),
            LiteralValue::Getter(target_idx),
            LiteralValue::Setter(target_idx),
            LiteralValue::Accessor(1),
            LiteralValue::MethodAffiliate(9),
            LiteralValue::LiteralArray(abcd_file::LiteralArrayIdx(1)),
            LiteralValue::LiteralBufferIndex(abcd_file::LiteralArrayIdx(0)),
            LiteralValue::BuiltinTypeIndex(3),
            LiteralValue::EtsImplements(impl_sid),
            LiteralValue::NullValue(0),
        ]),
        // Nested reference target (referenced by index 1 above).
        abcd_file::LiteralArray::new(vec![LiteralValue::Integer(99)]),
    ];
    // One single-element array per typed-array kind (ARRAY_* is always the
    // sole item of its array upstream), carrying non-empty payloads.
    let arr_s0 = file.strings.get_or_intern("arr_alpha");
    let arr_s1 = file.strings.get_or_intern("arr_beta");
    for v in [
        LiteralValue::ArrayU1(vec![true, false, true]),
        LiteralValue::ArrayU8(vec![0, 42, 255]),
        LiteralValue::ArrayI8(vec![-128, 0, 127]),
        LiteralValue::ArrayU16(vec![0, 1024, u16::MAX]),
        LiteralValue::ArrayI16(vec![i16::MIN, -1, i16::MAX]),
        LiteralValue::ArrayU32(vec![0, 0xDEAD_BEEF, u32::MAX]),
        LiteralValue::ArrayI32(vec![i32::MIN, -42, i32::MAX]),
        LiteralValue::ArrayU64(vec![0, 0x0123_4567_89AB_CDEF, u64::MAX]),
        LiteralValue::ArrayI64(vec![i64::MIN, -99, i64::MAX]),
        LiteralValue::ArrayF32(vec![-0.0, 1.5, -3.25]),
        LiteralValue::ArrayF64(vec![-0.0, 2.5, 1e100]),
        LiteralValue::ArrayString(vec![arr_s0, arr_s1]),
    ] {
        file.literal_arrays
            .push(abcd_file::LiteralArray::new(vec![v]));
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
