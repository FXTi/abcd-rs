//! Test group A — foreign (external) fields and methods.
//!
//! Format facts under test (see design/test-plan.md):
//! * foreign items live in the file's foreign region and are reachable by
//!   offset (annotation ENUM/METHOD elements, method handles) — they are
//!   NOT members of any class's field/method stream, so decode cannot
//!   enumerate them as class members.
//! * annotation elements that reference a foreign field/method must still
//!   resolve their name through the foreign item's name offset.

use abcd_file::{
    AccessFlags, AnnotationElemDefEx, AnnotationElemValue, AnnotationValue, Builder, SourceLang,
    Type, decode,
};

fn build_foreign_members() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let _ff = b.add_foreign_field(cls, "fx", Type::I32);
    let proto = b.create_proto(Type::Tagged, &[]);
    let _fm = b.add_foreign_method(cls, "fm", proto, AccessFlags::PUBLIC);
    b.finalize().expect("finalize")
}

#[test]
fn foreign_members_encode_and_are_not_class_members() {
    // Foreign items are written to the foreign region; the class member
    // streams only contain locally defined members, so decode surfaces an
    // empty member list for them. This is a format fact, not a decode bug.
    let file = decode(&build_foreign_members()).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    assert!(g.fields.is_empty(), "foreign fields are not class members");
    assert!(
        g.methods.is_empty(),
        "foreign methods are not class members"
    );
}

/// Build: global class + foreign field "fx" + one annotation whose element
/// is an ENUM reference to that foreign field.
fn build_enum_ref_to_foreign_field() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let fx = b.add_foreign_field(cls, "fx", Type::I32);

    let name = b.add_string("e");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name,
            tag: b'F', // Enum (field reference)
            value: AnnotationElemValue::EntityRef(fx.as_raw()),
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
fn enum_element_referencing_foreign_field_resolves_name() {
    let file = decode(&build_enum_ref_to_foreign_field()).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let ann = &g.annotations.compile_time[0];
    let elem = &ann.elements[0];
    match &elem.value {
        AnnotationValue::Enum { name, .. } => {
            assert_eq!(
                file.strings.resolve(*name),
                Some("fx"),
                "ENUM element must resolve the foreign field's name"
            );
        }
        other => panic!("expected Enum element, got {other:?}"),
    }
}

/// Build: global class + foreign method "fm" + annotation element that is a
/// METHOD reference to that foreign method.
fn build_method_ref_to_foreign_method() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let fm = b.add_foreign_method(cls, "fm", proto, AccessFlags::PUBLIC);

    let name = b.add_string("m");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name,
            tag: b'E', // Method reference
            value: AnnotationElemValue::EntityRef(fm.as_raw()),
        }],
    );
    b.class_add_runtime_annotation(cls, ann);

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
fn method_element_referencing_foreign_method_resolves_name() {
    let file = decode(&build_method_ref_to_foreign_method()).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let ann = &g.annotations.compile_time[0];
    let elem = &ann.elements[0];
    match &elem.value {
        AnnotationValue::Method { name, .. } => {
            assert_eq!(
                file.strings.resolve(*name),
                Some("fm"),
                "METHOD element must resolve the foreign method's name"
            );
        }
        other => panic!("expected Method element, got {other:?}"),
    }
}
