//! Regression tests for audit finding #B1: annotation array component
//! types and entity-array element resolution used the wrong tag chars
//! (upstream is 'T'=ArrayF32, 'U'=ArrayF64; entity arrays are
//! 'V'/'W'/'X'/'Y'/'Z'/'@'). Both were masked because every involved
//! element is 4 bytes wide.

use abcd_file::{
    AccessFlags, AnnotationElemDefEx, AnnotationElemValue, AnnotationValue, Builder, SourceLang,
    Type, decode, encode,
};

fn build_with_array_annotation() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);

    let name = b.add_string("vals");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name,
            // 'T' = ArrayF32 (audit #B1)
            tag: b'T',
            value: AnnotationElemValue::Array(vec![1.5f32.to_bits(), (-2.0f32).to_bits()]),
        }],
    );
    b.class_add_runtime_annotation(cls, ann);

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
fn f32_array_element_roundtrips_with_correct_tag() {
    let file = decode(&build_with_array_annotation()).expect("decode");
    let cls = file
        .classes
        .values()
        .find(|c| !c.is_external)
        .expect("global class");

    // Category collapse (#9): everything lands in compile_time.
    let ann = &cls.annotations.compile_time[0];
    let elem = &ann.elements[0];
    match &elem.value {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'T', "array tag must round-trip as ArrayF32");
            assert_eq!(
                values,
                &vec![AnnotationValue::F32(1.5), AnnotationValue::F32(-2.0)],
                "F32 array elements must decode as floats"
            );
        }
        other => panic!("expected Array element, got {other:?}"),
    }

    // And through a full encode round-trip.
    let encoded = encode(&file).expect("encode");
    let file2 = decode(&encoded).expect("second decode");
    let cls2 = file2
        .classes
        .values()
        .find(|c| !c.is_external)
        .expect("global class (re-encoded)");
    let elem2 = &cls2.annotations.compile_time[0].elements[0];
    match &elem2.value {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'T');
            assert_eq!(
                values,
                &vec![AnnotationValue::F32(1.5), AnnotationValue::F32(-2.0)]
            );
        }
        other => panic!("expected Array element after round-trip, got {other:?}"),
    }
}

#[test]
fn record_array_element_resolves_to_entity_offset() {
    // Entity-array elements must resolve to item offsets, not raw handle
    // indices (audit #B1): tag 'W' = ArrayRecord.
    let file = decode(&build_with_array_annotation()).expect("decode");
    let cls = file
        .classes
        .values()
        .find(|c| !c.is_external)
        .expect("global class");

    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let gcls = b.add_global_class();
    b.class_set_source_lang(gcls, SourceLang::EcmaScript);
    let rec = b.add_foreign_class("LRec;");
    let name = b.add_string("r");
    let ann = b.create_annotation_ex(
        gcls,
        &[AnnotationElemDefEx {
            name,
            tag: b'W', // ArrayRecord
            value: AnnotationElemValue::EntityArray(vec![rec.as_raw()]),
        }],
    );
    b.class_add_runtime_annotation(gcls, ann);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(gcls, "f", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let data = b.finalize().expect("finalize");

    let decoded = decode(&data).expect("decode");
    let g = decoded.classes.values().find(|c| !c.is_external).unwrap();
    let elem = &g.annotations.compile_time[0].elements[0];
    match &elem.value {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'W');
            assert_eq!(values.len(), 1);
            match &values[0] {
                AnnotationValue::Record(sid) => {
                    assert_eq!(
                        decoded.strings.resolve(*sid),
                        Some("LRec;"),
                        "record array element must decode to the class descriptor"
                    );
                }
                other => panic!("expected Record element, got {other:?}"),
            }
        }
        other => panic!("expected Array element, got {other:?}"),
    }
    let _ = cls;
}
