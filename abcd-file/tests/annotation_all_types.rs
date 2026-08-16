//! Test group D — annotation element coverage: every scalar tag, every
//! array tag (K..U, V..@, #), method handles, nested annotations, void and
//! string-nullptr.

use abcd_file::{
    AccessFlags, AnnotationElemDefEx, AnnotationElemValue, AnnotationValue, Builder, SourceLang,
    Type, decode,
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
        (
            b.add_string("alla"),
            b'#',
            AnnotationElemValue::EntityArray(vec![la.as_raw()]),
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
    match vals[12] {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'#');
            assert_eq!(values.len(), 1);
            match &values[0] {
                AnnotationValue::LiteralArray(vals_la) => {
                    // the referenced array holds one INTEGER 7
                    assert_eq!(vals_la.len(), 1);
                    match &vals_la[0] {
                        abcd_file::LiteralValue::Integer(7) => {}
                        other => panic!("expected Integer(7) in referenced array, got {other:?}"),
                    }
                }
                other => panic!("expected LiteralArray element, got {other:?}"),
            }
        }
        other => panic!("expected # array, got {other:?}"),
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
}
