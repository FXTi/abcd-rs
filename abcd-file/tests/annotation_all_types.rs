//! Test group D — annotation element coverage: every scalar tag, every
//! array tag (K..U, V..@, #), method handles, nested annotations, void and
//! string-nullptr.

use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationElemDefEx, AnnotationElemValue,
    AnnotationValue, Builder, LiteralValue, MethodHandleType, SourceLang, Type, decode, encode,
};

fn finish(b: &mut Builder, cls: abcd_file::ClassHandle) -> Vec<u8> {
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
    b.finalize().expect("finalize")
}

// ---------------------------------------------------------------------------
// Encode round-trip helpers
// ---------------------------------------------------------------------------

/// Resolve a method item offset to its name (entity identity across a
/// re-encode: offsets move, names don't — tests here use unique names).
/// Offset 0 is the hand-built-model sentinel; fall back to entity_map[0],
/// the same fallback the encoder uses.
fn method_name_at(file: &abcd_file::File, off: u32) -> String {
    if let Some((_, m)) = file.all_methods().find(|(_, m)| m.offset == off) {
        return file.strings.resolve(m.name).unwrap_or("?").to_string();
    }
    if off == 0
        && let Some(sid) = file.entity_map.get(&0)
    {
        return file.strings.resolve(*sid).unwrap_or("?").to_string();
    }
    "<unresolved>".to_string()
}

/// Canonical text form of a literal value: StringIds are resolved through
/// the pool and method offsets through the method table, because both are
/// pool/file-layout-local and differ between two decodes of one model.
/// Typed-array (`ArrayXxx`) values compare by discriminant only: their
/// payload is a file offset that legitimately moves on re-encode.
fn canon_literal(file: &abcd_file::File, v: &LiteralValue) -> String {
    let r = |sid: abcd_file::StringId| file.strings.resolve(sid).unwrap_or("<dangling>");
    match v {
        LiteralValue::String(sid) => format!("String({})", r(*sid)),
        LiteralValue::EtsImplements(sid) => format!("EtsImplements({})", r(*sid)),
        LiteralValue::Method(off) => format!("Method({})", method_name_at(file, *off)),
        LiteralValue::GeneratorMethod(off) => {
            format!("GeneratorMethod({})", method_name_at(file, *off))
        }
        LiteralValue::AsyncGeneratorMethod(off) => {
            format!("AsyncGeneratorMethod({})", method_name_at(file, *off))
        }
        LiteralValue::Getter(off) => format!("Getter({})", method_name_at(file, *off)),
        LiteralValue::Setter(off) => format!("Setter({})", method_name_at(file, *off)),
        // Content-based recursion: the literal-array table order is not
        // guaranteed, so comparing by content is order-independent. The
        // payload is a table index for model arrays and a RAW FILE OFFSET
        // for annotation-embedded arrays (never rewritten — literal.rs
        // LiteralArray doc); resolve both forms.
        LiteralValue::LiteralArray(idx) => {
            let values = if (idx.0 as usize) < file.literal_arrays.len() {
                &file.literal_arrays[idx.0 as usize].values
            } else {
                let table_idx = file
                    .literal_array_offsets
                    .get(&idx.0)
                    .unwrap_or_else(|| panic!("unresolvable literal-array payload {idx:?}"));
                &file.literal_arrays[*table_idx as usize].values
            };
            format!("LiteralArray[{}]", canon_literals(file, values))
        }
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

fn canon_literals(file: &abcd_file::File, values: &[LiteralValue]) -> String {
    values
        .iter()
        .map(|v| canon_literal(file, v))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Canonical text form of an annotation element value (see
/// [`canon_literal`]). Method/Enum/MethodHandle references compare by
/// resolved name; nested annotations/arrays recurse.
fn canon_value(file: &abcd_file::File, v: &AnnotationValue) -> String {
    let r = |sid: abcd_file::StringId| file.strings.resolve(sid).unwrap_or("<dangling>");
    match v {
        AnnotationValue::String(sid) => format!("String({})", r(*sid)),
        AnnotationValue::Record(sid) => format!("Record({})", r(*sid)),
        AnnotationValue::Method { name, .. } => format!("Method({})", r(*name)),
        AnnotationValue::Enum { name, .. } => format!("Enum({})", r(*name)),
        AnnotationValue::Annotation(inner) => format!(
            "Annotation({})[{}]",
            r(inner.class_descriptor),
            canon_elements(file, &inner.elements)
        ),
        AnnotationValue::MethodHandle(mh) => {
            format!("MethodHandle({}, {})", mh.handle_type as u8, r(mh.entity))
        }
        AnnotationValue::LiteralArray(values) => {
            format!("LiteralArray[{}]", canon_literals(file, values))
        }
        AnnotationValue::Array { tag, values } => format!(
            "Array({})[{}]",
            *tag as char,
            values
                .iter()
                .map(|v| canon_value(file, v))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        other => format!("{other:?}"),
    }
}

fn canon_elements(file: &abcd_file::File, elems: &[AnnotationElem]) -> String {
    elems
        .iter()
        .map(|e| {
            format!(
                "{}={}",
                file.strings.resolve(e.name).unwrap_or("<dangling>"),
                canon_value(file, &e.value)
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// Encode the model and re-decode, returning the canonical form of the
/// global class's first compile-time annotation in both files for
/// comparison.
fn roundtrip_first_annotation(file: &abcd_file::File) -> (String, String) {
    let g1 = file.classes.values().find(|c| !c.is_external).unwrap();
    let before = canon_elements(file, &g1.annotations.compile_time[0].elements);
    let encoded = encode(file).expect("encode");
    let file2 = decode(&encoded).expect("decode re-encoded");
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    let after = canon_elements(&file2, &g2.annotations.compile_time[0].elements);
    (before, after)
}

#[test]
fn scalar_tags_all_decode() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let s = b.add_string("sval");
    let rec = b.add_foreign_class("LRec;");

    let elems: Vec<AnnotationElemDefEx> = vec![
        (b.add_string("b1"), b'1', AnnotationElemValue::Scalar(1)),
        (b.add_string("i8"), b'2', AnnotationElemValue::Scalar(0xfe)),
        (b.add_string("u8"), b'3', AnnotationElemValue::Scalar(0xff)),
        (
            b.add_string("i16"),
            b'4',
            AnnotationElemValue::Scalar(0xfffe),
        ),
        (
            b.add_string("u16"),
            b'5',
            AnnotationElemValue::Scalar(0xffff),
        ),
        (
            b.add_string("i32"),
            b'6',
            AnnotationElemValue::Scalar(0xfffffffe),
        ),
        (
            b.add_string("u32"),
            b'7',
            AnnotationElemValue::Scalar(0xffffffff),
        ),
        (
            b.add_string("i64"),
            b'8',
            AnnotationElemValue::Scalar64(i64::MIN as u64),
        ),
        (
            b.add_string("u64"),
            b'9',
            AnnotationElemValue::Scalar64(u64::MAX),
        ),
        (
            b.add_string("f32"),
            b'A',
            AnnotationElemValue::Scalar(1.5f32.to_bits()),
        ),
        (
            b.add_string("f64"),
            b'B',
            AnnotationElemValue::Scalar64(2.5f64.to_bits()),
        ),
        (
            b.add_string("str"),
            b'C',
            AnnotationElemValue::EntityRef(s.as_raw()),
        ),
        (
            b.add_string("rec"),
            b'D',
            AnnotationElemValue::EntityRef(rec.as_raw()),
        ),
        (b.add_string("void"), b'I', AnnotationElemValue::Scalar(0)),
        (b.add_string("sn"), b'*', AnnotationElemValue::Scalar(0)),
    ]
    .into_iter()
    .map(|(name, tag, value)| AnnotationElemDefEx { name, tag, value })
    .collect();

    let ann = b.create_annotation_ex(cls, &elems);
    b.class_add_runtime_annotation(cls, ann);

    let data = finish(&mut b, cls);
    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let ann = &g.annotations.compile_time[0];
    assert_eq!(ann.elements.len(), 15);

    let vals: Vec<&AnnotationValue> = ann.elements.iter().map(|e| &e.value).collect();
    assert_eq!(vals[0], &AnnotationValue::Bool(true));
    assert_eq!(vals[1], &AnnotationValue::I8(-2));
    assert_eq!(vals[2], &AnnotationValue::U8(0xff));
    assert_eq!(vals[3], &AnnotationValue::I16(-2));
    assert_eq!(vals[4], &AnnotationValue::U16(0xffff));
    assert_eq!(vals[5], &AnnotationValue::I32(-2));
    assert_eq!(vals[6], &AnnotationValue::U32(0xffffffff));
    assert_eq!(vals[7], &AnnotationValue::I64(i64::MIN));
    assert_eq!(vals[8], &AnnotationValue::U64(u64::MAX));
    assert_eq!(vals[9], &AnnotationValue::F32(1.5));
    assert_eq!(vals[10], &AnnotationValue::F64(2.5));
    assert_eq!(vals[11], &AnnotationValue::String(*vals[11].as_str_sid()));
    let rec_sid = match vals[12] {
        AnnotationValue::Record(sid) => sid,
        other => panic!("expected Record, got {other:?}"),
    };
    assert_eq!(file.strings.resolve(*rec_sid), Some("LRec;"));
    assert_eq!(vals[13], &AnnotationValue::Void);
    assert_eq!(vals[14], &AnnotationValue::StringNullptr);

    // Encode round-trip: every scalar/entity value kind must survive
    // decode -> encode -> decode unchanged.
    let (before, after) = roundtrip_first_annotation(&file);
    assert_eq!(
        before, after,
        "scalar matrix must round-trip through encode"
    );
}

trait AsStrSid {
    fn as_str_sid(&self) -> &abcd_file::StringId;
}
impl AsStrSid for AnnotationValue {
    fn as_str_sid(&self) -> &abcd_file::StringId {
        match self {
            AnnotationValue::String(sid) => sid,
            other => panic!("expected String, got {other:?}"),
        }
    }
}

#[test]
fn array_tags_all_decode() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let s = b.add_string("arr_s");
    let rec = b.add_foreign_class("LRec;");
    let f = b.add_foreign_field(cls, "fx", Type::I32);
    let proto = b.create_proto(Type::Tagged, &[]);
    let fm = b.add_foreign_method(cls, "fm", proto, AccessFlags::PUBLIC);
    let la = b.add_literal_array("arr_la");
    b.literal_array_add_integer(la, 7);

    let elems: Vec<AnnotationElemDefEx> = vec![
        (
            b.add_string("au1"),
            b'K',
            AnnotationElemValue::Array(vec![1, 0]),
        ),
        (
            b.add_string("ai8"),
            b'L',
            AnnotationElemValue::Array(vec![0xfe]),
        ),
        (
            b.add_string("au8"),
            b'M',
            AnnotationElemValue::Array(vec![0xff]),
        ),
        (
            b.add_string("ai16"),
            b'N',
            AnnotationElemValue::Array(vec![0xfffe]),
        ),
        (
            b.add_string("au16"),
            b'O',
            AnnotationElemValue::Array(vec![0xffff]),
        ),
        (
            b.add_string("ai32"),
            b'P',
            AnnotationElemValue::Array(vec![0xfffffffe]),
        ),
        (
            b.add_string("au32"),
            b'Q',
            AnnotationElemValue::Array(vec![0xffffffff]),
        ),
        (
            b.add_string("af32"),
            b'T',
            AnnotationElemValue::Array(vec![1.5f32.to_bits()]),
        ),
        (
            b.add_string("astr"),
            b'V',
            AnnotationElemValue::EntityArray(vec![s.as_raw()]),
        ),
        (
            b.add_string("arec"),
            b'W',
            AnnotationElemValue::EntityArray(vec![rec.as_raw()]),
        ),
        (
            b.add_string("aenum"),
            b'Y',
            AnnotationElemValue::EntityArray(vec![f.as_raw()]),
        ),
        (
            b.add_string("ameth"),
            b'X',
            AnnotationElemValue::EntityArray(vec![fm.as_raw()]),
        ),
        // '#' is the SCALAR literal-array tag in the vendored data model
        // (pandasm annotation.h: GetCharAsType '#' -> LITERALARRAY;
        // GetArrayTypeAsChar has no literal-array case — arrays of literal
        // arrays are not representable upstream).
        (
            b.add_string("alla"),
            b'#',
            AnnotationElemValue::EntityRef(la.as_raw()),
        ),
    ]
    .into_iter()
    .map(|(name, tag, value)| AnnotationElemDefEx { name, tag, value })
    .collect();

    let ann = b.create_annotation_ex(cls, &elems);
    b.class_add_runtime_annotation(cls, ann);

    let data = finish(&mut b, cls);
    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let ann = &g.annotations.compile_time[0];
    assert_eq!(ann.elements.len(), 13);

    let vals: Vec<&AnnotationValue> = ann.elements.iter().map(|e| &e.value).collect();
    // Scalar arrays decode per element type (K..Q, T).
    assert_eq!(
        vals[0],
        &AnnotationValue::Array {
            tag: b'K',
            values: vec![AnnotationValue::Bool(true), AnnotationValue::Bool(false)]
        }
    );
    assert_eq!(
        vals[1],
        &AnnotationValue::Array {
            tag: b'L',
            values: vec![AnnotationValue::I8(-2)]
        }
    );
    assert_eq!(
        vals[2],
        &AnnotationValue::Array {
            tag: b'M',
            values: vec![AnnotationValue::U8(0xff)]
        }
    );
    assert_eq!(
        vals[3],
        &AnnotationValue::Array {
            tag: b'N',
            values: vec![AnnotationValue::I16(-2)]
        }
    );
    assert_eq!(
        vals[4],
        &AnnotationValue::Array {
            tag: b'O',
            values: vec![AnnotationValue::U16(0xffff)]
        }
    );
    assert_eq!(
        vals[5],
        &AnnotationValue::Array {
            tag: b'P',
            values: vec![AnnotationValue::I32(-2)]
        }
    );
    assert_eq!(
        vals[6],
        &AnnotationValue::Array {
            tag: b'Q',
            values: vec![AnnotationValue::U32(0xffffffff)]
        }
    );
    assert_eq!(
        vals[7],
        &AnnotationValue::Array {
            tag: b'T',
            values: vec![AnnotationValue::F32(1.5)]
        }
    );
    // Entity arrays.
    match vals[8] {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'V');
            assert_eq!(values.len(), 1);
            match &values[0] {
                AnnotationValue::String(sid) => {
                    assert_eq!(file.strings.resolve(*sid), Some("arr_s"))
                }
                other => panic!("expected String element, got {other:?}"),
            }
        }
        other => panic!("expected V array, got {other:?}"),
    }
    match vals[9] {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'W');
            match &values[0] {
                AnnotationValue::Record(sid) => {
                    assert_eq!(file.strings.resolve(*sid), Some("LRec;"))
                }
                other => panic!("expected Record element, got {other:?}"),
            }
        }
        other => panic!("expected W array, got {other:?}"),
    }
    match vals[10] {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'Y');
            match &values[0] {
                AnnotationValue::Enum { name, .. } => {
                    assert_eq!(file.strings.resolve(*name), Some("fx"))
                }
                other => panic!("expected Enum element, got {other:?}"),
            }
        }
        other => panic!("expected Y array, got {other:?}"),
    }
    match vals[11] {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'X');
            match &values[0] {
                AnnotationValue::Method { name, .. } => {
                    assert_eq!(file.strings.resolve(*name), Some("fm"))
                }
                other => panic!("expected Method element, got {other:?}"),
            }
        }
        other => panic!("expected X array, got {other:?}"),
    }
    // The scalar '#' element decodes as the literal array's contents.
    match vals[12] {
        AnnotationValue::LiteralArray(vals_la) => {
            // the referenced array holds one INTEGER 7
            assert_eq!(vals_la.len(), 1);
            match &vals_la[0] {
                abcd_file::LiteralValue::Integer(7) => {}
                other => panic!("expected Integer(7) in referenced array, got {other:?}"),
            }
        }
        other => panic!("expected scalar # literal array, got {other:?}"),
    }
}

#[test]
fn nested_annotation_and_method_handle_decode() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(cls, "target", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);

    let k = b.add_string("k");
    let inner = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name: k,
            tag: b'7',
            value: AnnotationElemValue::Scalar(9),
        }],
    );
    let mh = b.create_method_handle(4, m.as_raw()); // INVOKE_STATIC → target method

    let nested_name = b.add_string("nested");
    let mh_name = b.add_string("mh");
    let ann = b.create_annotation_ex(
        cls,
        &[
            AnnotationElemDefEx {
                name: nested_name,
                tag: b'G',
                value: AnnotationElemValue::EntityRef(inner.as_raw()),
            },
            AnnotationElemDefEx {
                name: mh_name,
                tag: b'J',
                value: AnnotationElemValue::EntityRef(mh.as_raw()),
            },
        ],
    );
    b.class_add_runtime_annotation(cls, ann);

    let data = finish(&mut b, cls);
    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let ann = &g.annotations.compile_time[0];
    assert_eq!(ann.elements.len(), 2);

    match &ann.elements[0].value {
        AnnotationValue::Annotation(nested) => {
            assert_eq!(nested.elements.len(), 1);
            assert_eq!(nested.elements[0].value, AnnotationValue::U32(9));
        }
        other => panic!("expected nested Annotation, got {other:?}"),
    }
    match &ann.elements[1].value {
        AnnotationValue::MethodHandle(mh) => {
            assert_eq!(mh.handle_type as u8, 4);
            assert_eq!(
                file.strings.resolve(mh.entity),
                Some("target"),
                "method handle entity must resolve to the target method name"
            );
        }
        other => panic!("expected MethodHandle, got {other:?}"),
    }

    // Encode round-trip: nested annotations and method handles must survive
    // decode -> encode -> decode unchanged.
    let (before, after) = roundtrip_first_annotation(&file);
    assert_eq!(
        before, after,
        "nested annotation + method handle must round-trip through encode"
    );
}

// ---------------------------------------------------------------------------
// Encode-side matrix (decode -> encode -> decode)
// ---------------------------------------------------------------------------

/// Minimal base file: one global class with one trivial method, decoded to
/// a model for hand-mutation.
fn base_model() -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let data = finish(&mut b, cls);
    decode(&data).expect("decode base")
}

/// The full array-tag matrix (K..U scalar arrays, V/W entity arrays, X/Y
/// member arrays, '#' literal array) through encode. Unlike
/// `array_tags_all_decode` — whose Method/Enum elements reference FOREIGN
/// members and therefore cannot re-encode (unresolvable references are a
/// loud error by contract, audit #6/#7) — the member elements here reference
/// LOCAL entities so the model round-trips.
#[test]
fn array_tags_all_encode_roundtrip() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let s = b.add_string("arr_s");
    let rec = b.add_foreign_class("LRec;");
    // Local members: resolvable on re-encode.
    let fld = b.class_add_field(cls, "local_field", Type::I32, AccessFlags::PUBLIC);
    let proto = b.create_proto(Type::Tagged, &[]);
    let local = b.class_add_method(
        cls,
        "local_method",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(local, SourceLang::EcmaScript);
    let la = b.add_literal_array("arr_la");
    b.literal_array_add_integer(la, 7);

    let elems: Vec<AnnotationElemDefEx> = vec![
        (
            b.add_string("au1"),
            b'K',
            AnnotationElemValue::Array(vec![1, 0]),
        ),
        (
            b.add_string("ai8"),
            b'L',
            AnnotationElemValue::Array(vec![0xfe]),
        ),
        (
            b.add_string("au8"),
            b'M',
            AnnotationElemValue::Array(vec![0xff]),
        ),
        (
            b.add_string("ai16"),
            b'N',
            AnnotationElemValue::Array(vec![0xfffe]),
        ),
        (
            b.add_string("au16"),
            b'O',
            AnnotationElemValue::Array(vec![0xffff]),
        ),
        (
            b.add_string("ai32"),
            b'P',
            AnnotationElemValue::Array(vec![0xfffffffe]),
        ),
        (
            b.add_string("au32"),
            b'Q',
            AnnotationElemValue::Array(vec![0xffffffff]),
        ),
        (
            b.add_string("af32"),
            b'T',
            AnnotationElemValue::Array(vec![1.5f32.to_bits()]),
        ),
        (
            b.add_string("astr"),
            b'V',
            AnnotationElemValue::EntityArray(vec![s.as_raw()]),
        ),
        (
            b.add_string("arec"),
            b'W',
            AnnotationElemValue::EntityArray(vec![rec.as_raw()]),
        ),
        (
            b.add_string("aenum"),
            b'Y',
            AnnotationElemValue::EntityArray(vec![fld.as_raw()]),
        ),
        (
            b.add_string("ameth"),
            b'X',
            AnnotationElemValue::EntityArray(vec![local.as_raw()]),
        ),
        (
            b.add_string("alla"),
            b'#',
            AnnotationElemValue::EntityRef(la.as_raw()),
        ),
    ]
    .into_iter()
    .map(|(name, tag, value)| AnnotationElemDefEx { name, tag, value })
    .collect();

    let ann = b.create_annotation_ex(cls, &elems);
    b.class_add_runtime_annotation(cls, ann);

    let data = finish(&mut b, cls);
    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let ann = &g.annotations.compile_time[0];
    assert_eq!(ann.elements.len(), 13);
    // Spot-check the member references resolved to the LOCAL entities.
    match &ann.elements[10].value {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'Y');
            match &values[0] {
                AnnotationValue::Enum { name, .. } => {
                    assert_eq!(file.strings.resolve(*name), Some("local_field"))
                }
                other => panic!("expected Enum element, got {other:?}"),
            }
        }
        other => panic!("expected Y array, got {other:?}"),
    }
    match &ann.elements[11].value {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'X');
            match &values[0] {
                AnnotationValue::Method { name, .. } => {
                    assert_eq!(file.strings.resolve(*name), Some("local_method"))
                }
                other => panic!("expected Method element, got {other:?}"),
            }
        }
        other => panic!("expected X array, got {other:?}"),
    }

    let (before, after) = roundtrip_first_annotation(&file);
    assert_eq!(before, after, "array matrix must round-trip through encode");
}

/// Scalar Method ('E') and Enum ('F') elements plus method handles of BOTH
/// operation classes: field ops (handle_type 0-3, `is_field_op() == true`)
/// and method ops (4-8). The field-op handle drives the field-resolution
/// branch of the encoder's method-handle arm.
#[test]
fn scalar_method_enum_and_handles_encode_roundtrip() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let target = b.class_add_method(cls, "target", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(target, SourceLang::EcmaScript);
    let fld = b.class_add_field(cls, "f0", Type::I32, AccessFlags::PUBLIC);

    let mh_field = b.create_method_handle(MethodHandleType::PutStatic as u8, fld.as_raw());
    let mh_method = b.create_method_handle(MethodHandleType::InvokeStatic as u8, target.as_raw());

    let elems: Vec<AnnotationElemDefEx> = vec![
        (
            b.add_string("m"),
            b'E',
            AnnotationElemValue::EntityRef(target.as_raw()),
        ),
        (
            b.add_string("e"),
            b'F',
            AnnotationElemValue::EntityRef(fld.as_raw()),
        ),
        (
            b.add_string("hf"),
            b'J',
            AnnotationElemValue::EntityRef(mh_field.as_raw()),
        ),
        (
            b.add_string("hm"),
            b'J',
            AnnotationElemValue::EntityRef(mh_method.as_raw()),
        ),
    ]
    .into_iter()
    .map(|(name, tag, value)| AnnotationElemDefEx { name, tag, value })
    .collect();
    let ann = b.create_annotation_ex(cls, &elems);
    b.class_add_runtime_annotation(cls, ann);

    let data = finish(&mut b, cls);
    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let ann = &g.annotations.compile_time[0];
    assert_eq!(ann.elements.len(), 4);
    match &ann.elements[0].value {
        AnnotationValue::Method { name, offset } => {
            assert_eq!(file.strings.resolve(*name), Some("target"));
            assert_ne!(*offset, 0);
        }
        other => panic!("expected Method, got {other:?}"),
    }
    match &ann.elements[1].value {
        AnnotationValue::Enum { name, .. } => {
            assert_eq!(file.strings.resolve(*name), Some("f0"));
        }
        other => panic!("expected Enum, got {other:?}"),
    }
    match &ann.elements[2].value {
        AnnotationValue::MethodHandle(mh) => {
            assert_eq!(mh.handle_type, MethodHandleType::PutStatic);
            assert!(mh.handle_type.is_field_op());
            assert_eq!(file.strings.resolve(mh.entity), Some("f0"));
        }
        other => panic!("expected field-op MethodHandle, got {other:?}"),
    }
    match &ann.elements[3].value {
        AnnotationValue::MethodHandle(mh) => {
            assert_eq!(mh.handle_type, MethodHandleType::InvokeStatic);
            assert!(!mh.handle_type.is_field_op());
            assert_eq!(file.strings.resolve(mh.entity), Some("target"));
        }
        other => panic!("expected method-op MethodHandle, got {other:?}"),
    }

    let (before, after) = roundtrip_first_annotation(&file);
    assert_eq!(
        before, after,
        "Method/Enum/handle elements must round-trip through encode"
    );
}

/// Arrays of method handles ('@') and of nested annotations ('Z'): both
/// entity-array kinds the corpus never carries.
#[test]
fn handle_and_annotation_arrays_encode_roundtrip() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let target = b.class_add_method(cls, "target", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(target, SourceLang::EcmaScript);
    let fld = b.class_add_field(cls, "f0", Type::I32, AccessFlags::PUBLIC);

    let k = b.add_string("k");
    let inner = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name: k,
            tag: b'7',
            value: AnnotationElemValue::Scalar(9),
        }],
    );
    let mh_field = b.create_method_handle(MethodHandleType::GetInstance as u8, fld.as_raw());
    let mh_method = b.create_method_handle(MethodHandleType::InvokeStatic as u8, target.as_raw());

    let elems: Vec<AnnotationElemDefEx> = vec![
        (
            b.add_string("mhs"),
            b'@',
            AnnotationElemValue::EntityArray(vec![mh_field.as_raw(), mh_method.as_raw()]),
        ),
        (
            b.add_string("anns"),
            b'Z',
            AnnotationElemValue::EntityArray(vec![inner.as_raw()]),
        ),
    ]
    .into_iter()
    .map(|(name, tag, value)| AnnotationElemDefEx { name, tag, value })
    .collect();
    let ann = b.create_annotation_ex(cls, &elems);
    b.class_add_runtime_annotation(cls, ann);

    let data = finish(&mut b, cls);
    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let ann = &g.annotations.compile_time[0];
    assert_eq!(ann.elements.len(), 2);

    match &ann.elements[0].value {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'@');
            assert_eq!(values.len(), 2);
            match &values[0] {
                AnnotationValue::MethodHandle(mh) => {
                    assert_eq!(mh.handle_type, MethodHandleType::GetInstance);
                    assert_eq!(file.strings.resolve(mh.entity), Some("f0"));
                }
                other => panic!("expected MethodHandle element, got {other:?}"),
            }
            match &values[1] {
                AnnotationValue::MethodHandle(mh) => {
                    assert_eq!(mh.handle_type, MethodHandleType::InvokeStatic);
                    assert_eq!(file.strings.resolve(mh.entity), Some("target"));
                }
                other => panic!("expected MethodHandle element, got {other:?}"),
            }
        }
        other => panic!("expected @ array, got {other:?}"),
    }
    match &ann.elements[1].value {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'Z');
            assert_eq!(values.len(), 1);
            match &values[0] {
                AnnotationValue::Annotation(inner) => {
                    assert_eq!(inner.elements.len(), 1);
                    assert_eq!(inner.elements[0].value, AnnotationValue::U32(9));
                }
                other => panic!("expected nested Annotation element, got {other:?}"),
            }
        }
        other => panic!("expected Z array, got {other:?}"),
    }

    let (before, after) = roundtrip_first_annotation(&file);
    assert_eq!(
        before, after,
        "handle/annotation arrays must round-trip through encode"
    );
}

/// Void and StringNullptr array elements carry no payload; the 32-bit
/// builder array ABI encodes them as 0. Pin that mapping exactly.
#[test]
fn array_void_and_nullptr_elems_encode_as_zero() {
    let mut file = base_model();
    let desc = file.strings.get_or_intern("LAnno;");
    let name = file.strings.get_or_intern("vals");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.annotations.compile_time.push(Annotation {
        class_descriptor: desc,
        elements: vec![AnnotationElem {
            name,
            value: AnnotationValue::Array {
                tag: b'Q',
                values: vec![
                    AnnotationValue::U32(7),
                    AnnotationValue::Void,
                    AnnotationValue::StringNullptr,
                ],
            },
        }],
    });

    let encoded = encode(&file).expect("encode");
    let file2 = decode(&encoded).expect("decode re-encoded");
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    let ann = &g2.annotations.compile_time[0];
    assert_eq!(
        ann.elements[0].value,
        AnnotationValue::Array {
            tag: b'Q',
            values: vec![
                AnnotationValue::U32(7),
                AnnotationValue::U32(0),
                AnnotationValue::U32(0)
            ]
        },
        "Void/StringNullptr array elements encode as 0 (32-bit array ABI)"
    );
}

/// An annotation-embedded literal array holding every `LiteralValue` kind,
/// driven through `encode_literal_value_simple`: scalar kinds, all five
/// method-reference kinds (by source offset AND by the offset-0 name
/// fallback for hand-built models), index kinds, a nested literal-array
/// reference, and each typed-array kind (as its own trailing element —
/// upstream emits an ARRAY_* item only as the LAST item of an array).
#[test]
fn annotation_embedded_literal_array_all_kinds_encode_roundtrip() {
    let mut file = base_model();
    let target_off = {
        let cls = file.classes.values().find(|c| !c.is_external).unwrap();
        cls.methods
            .iter()
            .find(|m| file.strings.resolve(m.name) == Some("func_main_0"))
            .expect("method")
            .offset
    };
    assert_ne!(target_off, 0);

    let desc = file.strings.get_or_intern("LAnno;");
    let str_sid = file.strings.get_or_intern("embedded_str");
    let impl_sid = file.strings.get_or_intern("LImpl;");
    let name = |file: &mut abcd_file::File, s: &str| file.strings.get_or_intern(s);

    // The offset-0 name fallback: hand-built models carry no source offset;
    // entity_map[0] supplies the name (same contract as the model path).
    let target_name = file
        .strings
        .get("func_main_0")
        .expect("method name interned");
    file.entity_map.insert(0, target_name);

    // NOTE: no nested `LiteralValue::LiteralArray` element here — the
    // vendored writer/reader pair corrupts every item AFTER a LITERALARRAY
    // item inside an annotation-embedded array (the nested reference is
    // written but the trailing items decode shifted; upstream treats arrays
    // of literal arrays as unrepresentable). The encoder's nested-LA error
    // arm is covered in encode_errors.rs.
    let matrix: Vec<LiteralValue> = vec![
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
        LiteralValue::LiteralBufferIndex(abcd_file::LiteralArrayIdx(7)),
        LiteralValue::BuiltinTypeIndex(3),
        LiteralValue::EtsImplements(impl_sid),
        LiteralValue::NullValue(0),
    ];
    let typed_arrays = [
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
    ];

    let mut elements = vec![
        AnnotationElem {
            name: name(&mut file, "matrix"),
            value: AnnotationValue::LiteralArray(matrix),
        },
        AnnotationElem {
            // Nested annotation carrying its own literal array: drives the
            // nested-Annotation arms of validate_annotation_arrays and
            // count_annotation_literal_arrays plus the recursive encode.
            name: name(&mut file, "nested"),
            value: AnnotationValue::Annotation(Box::new(Annotation {
                class_descriptor: desc,
                elements: vec![AnnotationElem {
                    name: name(&mut file, "inner_la"),
                    value: AnnotationValue::LiteralArray(vec![LiteralValue::Integer(7)]),
                }],
            })),
        },
    ];
    // Each typed array as its own trailing element (see doc comment).
    for (i, v) in typed_arrays.into_iter().enumerate() {
        elements.push(AnnotationElem {
            name: name(&mut file, &format!("arr{i}")),
            value: AnnotationValue::LiteralArray(vec![v]),
        });
    }

    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.annotations.compile_time.push(Annotation {
        class_descriptor: desc,
        elements,
    });

    let (before, after) = roundtrip_first_annotation(&file);
    assert_eq!(
        before, after,
        "embedded literal matrix must round-trip through encode"
    );
}

/// Every annotation category on every target: class/method/field ×
/// compile_time/runtime/compile_time_type/runtime_type, plus param
/// annotations (both buckets) on a method with a reference-typed argument.
/// Drives the 12 `encode_annotations_on` attach arms, the four field/method
/// Builder wrappers, and the param-annotation fold.
#[test]
fn annotation_categories_encode_roundtrip() {
    let mut file = base_model();

    let desc = file.strings.get_or_intern("LAnno;");
    let ref_desc = file.strings.get_or_intern("LWidget;");
    let mk_ann = |file: &mut abcd_file::File, elem: &str, v: u32| {
        let name = file.strings.get_or_intern(elem);
        Annotation {
            class_descriptor: desc,
            elements: vec![AnnotationElem {
                name,
                value: AnnotationValue::U32(v),
            }],
        }
    };

    // Build every annotation first (each mk_ann needs &mut file for the
    // pool), then mutate the model.
    let class_anns = [
        mk_ann(&mut file, "c1", 1),
        mk_ann(&mut file, "c2", 2),
        mk_ann(&mut file, "c3", 3),
        mk_ann(&mut file, "c4", 4),
    ];
    let field_anns = [
        mk_ann(&mut file, "f1", 11),
        mk_ann(&mut file, "f2", 12),
        mk_ann(&mut file, "f3", 13),
        mk_ann(&mut file, "f4", 14),
    ];
    let method_anns = [
        mk_ann(&mut file, "m1", 21),
        mk_ann(&mut file, "m2", 22),
        mk_ann(&mut file, "m3", 23),
        mk_ann(&mut file, "m4", 24),
    ];
    let param_compile = mk_ann(&mut file, "p1", 31);
    let param_runtime = mk_ann(&mut file, "p2", 32);
    let field_name = file.strings.get_or_intern("fld");
    let main_name = file.strings.get("func_main_0").expect("method name");

    let [c1, c2, c3, c4] = class_anns;
    let [f1, f2, f3, f4] = field_anns;
    let [m1, m2, m3, m4] = method_anns;

    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    // One annotation per category bucket on the class.
    cls.annotations.compile_time.push(c1);
    cls.annotations.runtime.push(c2);
    cls.annotations.compile_time_type.push(c3);
    cls.annotations.runtime_type.push(c4);

    // A field carrying all four categories.
    cls.fields.push(abcd_file::Field {
        name: field_name,
        offset: 0,
        field_type: Type::I32,
        access_flags: AccessFlags::PUBLIC,
        is_external: false,
        initial_value: None,
        annotations: abcd_file::Annotations {
            compile_time: vec![f1],
            runtime: vec![f2],
            compile_time_type: vec![f3],
            runtime_type: vec![f4],
        },
    });

    // All four categories on the method, a reference-typed arg, and param
    // annotations in both buckets.
    let m = cls
        .methods
        .iter_mut()
        .find(|m| m.name == main_name)
        .unwrap();
    m.annotations.compile_time.push(m1);
    m.annotations.runtime.push(m2);
    m.annotations.compile_time_type.push(m3);
    m.annotations.runtime_type.push(m4);
    m.arg_types = vec![Type::Reference(ref_desc)];
    m.param_annotations.compile_time = vec![vec![param_compile]];
    m.param_annotations.runtime = vec![vec![param_runtime]];

    let encoded = encode(&file).expect("encode");
    let file2 = decode(&encoded).expect("decode re-encoded");

    /// All U32 annotation values across the four buckets of one target.
    fn all_u32s(anns: &abcd_file::Annotations) -> Vec<u32> {
        let mut v: Vec<u32> = [
            &anns.compile_time,
            &anns.runtime,
            &anns.compile_time_type,
            &anns.runtime_type,
        ]
        .into_iter()
        .flat_map(|bucket| bucket.iter())
        .flat_map(|a| a.elements.iter())
        .filter_map(|e| match e.value {
            AnnotationValue::U32(v) => Some(v),
            _ => None,
        })
        .collect();
        v.sort_unstable();
        v
    }

    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    assert_eq!(all_u32s(&g2.annotations), vec![1, 2, 3, 4]);
    assert_eq!(all_u32s(&g2.fields[0].annotations), vec![11, 12, 13, 14]);
    let m2 = g2
        .methods
        .iter()
        .find(|m| file2.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method");
    assert_eq!(all_u32s(&m2.annotations), vec![21, 22, 23, 24]);
    // Param annotations fold to one bucket pair-wise (contract, finding #9):
    // both values land on param 0 regardless of the sealed category.
    let param_vals: Vec<u32> = m2
        .param_annotations
        .compile_time
        .iter()
        .chain(m2.param_annotations.runtime.iter())
        .flat_map(|v| v.iter())
        .flat_map(|a| a.elements.iter())
        .filter_map(|e| match e.value {
            AnnotationValue::U32(v) => Some(v),
            _ => None,
        })
        .collect();
    assert_eq!(param_vals, vec![31, 32]);
}
