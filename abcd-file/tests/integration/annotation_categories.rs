//! Acceptance tests for review finding #9: upstream API-24 writers emit a
//! single ANNOTATION category, so the four builder attach APIs collapse onto
//! one vector and decode surfaces everything in the `compile_time` bucket.
//! This pins the *documented* contract (see design/file-format.md), not byte
//! equality with legacy four-bucket files.

use abcd_file::{AccessFlags, AnnotationElemDef, Builder, SourceLang, Type, decode, encode};

/// Build a file whose class carries one annotation attached through each of
/// the four category APIs; the U32 element values make them distinguishable.
fn build_four_buckets() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);

    for i in 1u32..=4 {
        let name = b.add_string("level");
        let ann = b.create_annotation(
            cls,
            &[AnnotationElemDef {
                name,
                tag: b'7', // U32 element
                value: i,
            }],
        );
        match i {
            1 => b.class_add_annotation(cls, ann),
            2 => b.class_add_runtime_annotation(cls, ann),
            3 => b.class_add_type_annotation(cls, ann),
            _ => b.class_add_runtime_type_annotation(cls, ann),
        }
    }

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

fn u32_values(file: &abcd_file::File, anns: &[abcd_file::Annotation]) -> Vec<u32> {
    let mut out = Vec::new();
    for ann in anns {
        for e in &ann.elements {
            if let abcd_file::AnnotationValue::U32(v) = e.value {
                out.push(v);
            }
        }
    }
    out.sort_unstable();
    let _ = file;
    out
}

#[test]
fn all_four_categories_collapse_into_compile_time() {
    let file = decode(&build_four_buckets()).expect("decode");
    let cls = file
        .classes
        .values()
        .find(|c| !c.is_external)
        .expect("global class");

    // Everything lands in the compile_time bucket…
    assert_eq!(
        u32_values(&file, &cls.annotations.compile_time),
        vec![1, 2, 3, 4]
    );
    // …and the legacy buckets stay empty.
    assert!(cls.annotations.runtime.is_empty());
    assert!(cls.annotations.compile_time_type.is_empty());
    assert!(cls.annotations.runtime_type.is_empty());
}

#[test]
fn collapsed_categories_survive_encode_round_trip() {
    let file1 = decode(&build_four_buckets()).expect("first decode");
    let encoded = encode(&file1).expect("encode");
    let file2 = decode(&encoded).expect("second decode");

    let cls2 = file2
        .classes
        .values()
        .find(|c| !c.is_external)
        .expect("global class (re-encoded)");
    assert_eq!(
        u32_values(&file2, &cls2.annotations.compile_time),
        vec![1, 2, 3, 4],
        "the collapsed bucket must round-trip"
    );
    assert!(cls2.annotations.runtime.is_empty());
    assert!(cls2.annotations.compile_time_type.is_empty());
    assert!(cls2.annotations.runtime_type.is_empty());
}
