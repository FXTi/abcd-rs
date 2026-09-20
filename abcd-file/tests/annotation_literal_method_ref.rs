//! F-new-2 (design/review-bridge-wrapper.md): annotation-embedded literal
//! arrays (`AnnotationValue::LiteralArray`) were written by
//! `encode_literal_value_simple`, which had no entity context and stored
//! method references as the RAW source-file offset u32. The new file's
//! layout differs, so the reference dangled. Method references now resolve
//! through the same entity handles as the model literal-array path (audit
//! findings #6/#7 contract: unresolvable is a hard error, never a silent
//! raw value).

use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationValue, Builder, LiteralValue, Type, decode,
    encode,
};

/// Build a base file with one method, attach a class annotation carrying a
/// literal array with a method reference to it, rewrite, and return the
/// decoded rewrite.
fn rewrite_with_annotation_method_ref() -> (abcd_file::File, u32) {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Tagged, &[]);
    b.class_add_method(
        cls,
        "target",
        proto,
        AccessFlags::PUBLIC,
        &[0x65, 0x65],
        1,
        0,
    );
    let base = b.finalize().expect("finalize");
    let mut file = decode(&base).expect("decode base");

    let target_off = {
        let cls = file.classes.values().find(|c| !c.is_external).unwrap();
        cls.methods
            .iter()
            .find(|m| file.strings.resolve(m.name) == Some("target"))
            .expect("target present")
            .offset
    };
    assert_ne!(target_off, 0, "decoded methods carry source offsets");

    let ann_desc = file.strings.get_or_intern("LAnno;");
    let elem_name = file.strings.get_or_intern("v");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.annotations.compile_time.push(Annotation {
        class_descriptor: ann_desc,
        elements: vec![AnnotationElem {
            name: elem_name,
            value: AnnotationValue::LiteralArray(vec![
                LiteralValue::Integer(7),
                LiteralValue::Method(target_off),
            ]),
        }],
    });

    let bytes = encode(&file).expect("encode");
    (decode(&bytes).expect("decode rewritten"), target_off)
}

#[test]
fn annotation_literal_array_method_ref_relocates() {
    let (file2, old_off) = rewrite_with_annotation_method_ref();

    let g = file2.classes.values().find(|c| !c.is_external).unwrap();
    let new_off = g
        .methods
        .iter()
        .find(|m| file2.strings.resolve(m.name) == Some("target"))
        .expect("target present in rewrite")
        .offset;
    assert_ne!(
        old_off, new_off,
        "test setup: the rewrite must move the target method (else the probe is vacuous)"
    );

    let ann = g
        .annotations
        .compile_time
        .iter()
        .find(|a| file2.strings.resolve(a.class_descriptor) == Some("LAnno;"))
        .expect("annotation preserved");
    let AnnotationValue::LiteralArray(values) = &ann.elements[0].value else {
        panic!(
            "annotation element must stay a literal array, got {:?} (all annotations: {:?})",
            ann.elements[0].value, g.annotations
        );
    };
    let method_ref = values.iter().find_map(|v| match v {
        LiteralValue::Method(off) => Some(*off),
        _ => None,
    });
    assert_eq!(
        method_ref,
        Some(new_off),
        "method reference inside an annotation literal array must be relocated \
         to the method's NEW offset, not written back as the raw source offset"
    );
}

/// The #6/#7 contract holds for the embedded path too: a reference that
/// resolves to nothing must be a hard error, never a silent raw u32.
#[test]
fn annotation_literal_array_method_ref_unresolvable_is_error() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Tagged, &[]);
    b.class_add_method(
        cls,
        "target",
        proto,
        AccessFlags::PUBLIC,
        &[0x65, 0x65],
        1,
        0,
    );
    let base = b.finalize().expect("finalize");
    let mut file = decode(&base).expect("decode base");

    let ann_desc = file.strings.get_or_intern("LAnno;");
    let elem_name = file.strings.get_or_intern("v");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.annotations.compile_time.push(Annotation {
        class_descriptor: ann_desc,
        elements: vec![AnnotationElem {
            name: elem_name,
            // 0x77777 is not any method's source offset.
            value: AnnotationValue::LiteralArray(vec![LiteralValue::Method(0x77777)]),
        }],
    });

    let err = encode(&file).expect_err("unresolvable method reference must fail");
    assert!(
        err.to_string().contains("cannot be resolved"),
        "unexpected error: {err}"
    );
}
