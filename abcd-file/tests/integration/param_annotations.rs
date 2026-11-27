//! Regression tests for finding #17 and Issue #91 — per-parameter annotations.
//!
//! Model contract: decode and encode both keep compile-time
//! (`MethodTag::PARAM_ANNOTATION`) and runtime
//! (`MethodTag::RUNTIME_PARAM_ANNOTATION`) parameter annotation buckets
//! strictly isolated without cross-bucket folding or duplication.

use abcd_file::{
    AccessFlags, Annotation, AnnotationElemDefEx, AnnotationElemValue, AnnotationValue, Builder,
    SourceLang, Type, decode, encode,
};

/// Collect the U32 element values carried by a list of annotations.
fn u32_values(anns: &[Annotation]) -> Vec<u32> {
    anns.iter()
        .flat_map(|a| a.elements.iter())
        .filter_map(|e| match e.value {
            AnnotationValue::U32(v) => Some(v),
            _ => None,
        })
        .collect()
}

fn build_method_with_two_params(
    b: &mut Builder,
) -> (abcd_file::ClassHandle, abcd_file::MethodHandle) {
    // API 9: the 12.x builder output currently decodes with an empty proto
    // (pre-existing quirk, see proto_queries.rs which pins API 9 for the
    // same reason); param-annotation bucket sizing is based on arg_types.
    b.set_api(9, "");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[Type::Tagged, Type::Tagged]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        3,
        2,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    (cls, m)
}

/// Build: method with two TAGGED params; compile-time annotation (U32 1111)
/// on param 0 sealed first, then runtime annotation (U32 2222) on param 1
/// sealed as runtime.
///
/// The compile-time seal happens BEFORE the runtime annotation is staged:
/// the vendored MethodParamItem keeps a single annotation vector per param
/// and each seal snapshots whatever is staged (worker G's bridge smoke
/// test), so the runtime item ends up also containing param 0's annotation.
fn build_compile_and_runtime() -> Vec<u8> {
    let mut b = Builder::new();
    let (cls, m) = build_method_with_two_params(&mut b);
    let p0 = b.method_add_param(m, Type::Tagged);
    let p1 = b.method_add_param(m, Type::Tagged);

    let name = b.add_string("value");
    let mk_ann = |b: &mut Builder, value: u32| {
        b.create_annotation_ex(
            cls,
            &[AnnotationElemDefEx {
                name,
                tag: b'7', // U32
                value: AnnotationElemValue::Scalar(value),
            }],
        )
    };

    let ann_a = mk_ann(&mut b, 1111);
    b.method_param_add_annotation(m, p0, ann_a);
    b.method_seal_param_annotations(m, false)
        .expect("seal compile-time");

    let ann_b = mk_ann(&mut b, 2222);
    b.method_param_add_runtime_annotation(m, p1, ann_b);
    b.method_seal_param_annotations(m, true)
        .expect("seal runtime");

    b.finalize().expect("finalize")
}

/// Build: runtime-only param annotation (U32 2222) on param 1, sealed as
/// runtime; the compile-time bucket is never touched.
fn build_runtime_only() -> Vec<u8> {
    let mut b = Builder::new();
    let (cls, m) = build_method_with_two_params(&mut b);
    let _p0 = b.method_add_param(m, Type::Tagged);
    let p1 = b.method_add_param(m, Type::Tagged);

    let name = b.add_string("value");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name,
            tag: b'7',
            value: AnnotationElemValue::Scalar(2222),
        }],
    );
    b.method_param_add_runtime_annotation(m, p1, ann);
    b.method_seal_param_annotations(m, true)
        .expect("seal runtime");

    b.finalize().expect("finalize")
}

#[test]
fn param_annotations_decode_and_dual_bucket_roundtrip() {
    let file1 = decode(&build_compile_and_runtime()).expect("decode #1");
    let g1 = file1.classes.values().find(|c| !c.is_external).unwrap();
    let pa1 = &g1.methods[0].param_annotations;

    // Decode: both buckets filled independently, indexed by parameter position.
    assert_eq!(pa1.compile_time.len(), 2);
    assert_eq!(u32_values(&pa1.compile_time[0]), vec![1111]);
    assert!(pa1.compile_time[1].is_empty());
    assert_eq!(pa1.runtime.len(), 2);
    assert!(pa1.runtime[0].is_empty());
    assert_eq!(u32_values(&pa1.runtime[1]), vec![2222]);

    // Encode seals both buckets independently without cross-bucket duplication.
    let bytes2 = encode(&file1).expect("encode");
    let file2 = decode(&bytes2).expect("decode #2");
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    let pa2 = &g2.methods[0].param_annotations;

    assert_eq!(pa2.compile_time.len(), 2);
    assert_eq!(u32_values(&pa2.compile_time[0]), vec![1111]);
    assert!(pa2.compile_time[1].is_empty());
    assert_eq!(pa2.runtime.len(), 2);
    assert!(pa2.runtime[0].is_empty());
    assert_eq!(u32_values(&pa2.runtime[1]), vec![2222]);
}

#[test]
fn runtime_only_bucket_seals_as_runtime() {
    let file1 = decode(&build_runtime_only()).expect("decode #1");
    let g1 = file1.classes.values().find(|c| !c.is_external).unwrap();
    let pa1 = &g1.methods[0].param_annotations;
    assert!(pa1.compile_time.is_empty());
    assert_eq!(pa1.runtime.len(), 2);
    assert_eq!(u32_values(&pa1.runtime[1]), vec![2222]);

    // Runtime-only input seals as runtime (no fold): the bucket survives.
    let bytes2 = encode(&file1).expect("encode");
    let file2 = decode(&bytes2).expect("decode #2");
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    let pa2 = &g2.methods[0].param_annotations;
    assert!(pa2.compile_time.is_empty(), "compile bucket stays empty");
    assert_eq!(pa2.runtime.len(), 2);
    assert_eq!(u32_values(&pa2.runtime[1]), vec![2222]);
}
