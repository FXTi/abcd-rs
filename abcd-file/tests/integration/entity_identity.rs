//! Regression tests for review finding #6 (encode handle maps keyed by name
//! collided for same-named methods/fields across classes). The model now
//! carries entity offsets, so decode-side identity is unique even when
//! names repeat.

use abcd_file::{AccessFlags, Builder, LiteralValue, SourceLang, Type, decode};

/// Build a file with two classes that each define a method named `foo` and
/// a field named `x`, plus a literal array referencing `A.foo`.
fn build_duplicate_names() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let a = b.add_global_class();
    b.class_set_source_lang(a, SourceLang::EcmaScript);
    let bcls = b.add_class("LB;");
    b.class_set_source_lang(bcls, SourceLang::EcmaScript);

    let proto = b.create_proto(Type::Tagged, &[]);
    let a_foo = b.class_add_method(a, "foo", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(a_foo, SourceLang::EcmaScript);
    let b_foo = b.class_add_method(bcls, "foo", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(b_foo, SourceLang::EcmaScript);
    let _ = b.class_add_field(a, "x", Type::I32, AccessFlags::PUBLIC);
    let _ = b.class_add_field(bcls, "x", Type::I32, AccessFlags::PUBLIC);

    // The literal array references A.foo specifically.
    let la = b.add_literal_array("m");
    b.literal_array_add_method(la, a_foo);

    b.finalize().expect("finalize")
}

#[test]
fn decoded_methods_and_fields_carry_unique_offsets() {
    let file = decode(&build_duplicate_names()).expect("decode");

    let global = file
        .classes
        .values()
        .find(|c| file.strings.resolve(c.descriptor) == Some("L_GLOBAL;"))
        .expect("global class");
    let bcls = file
        .classes
        .values()
        .find(|c| file.strings.resolve(c.descriptor) == Some("LB;"))
        .expect("LB; class");

    let a_foo = global
        .methods
        .iter()
        .find(|m| file.strings.resolve(m.name) == Some("foo"))
        .expect("global foo");
    let b_foo = bcls
        .methods
        .iter()
        .find(|m| file.strings.resolve(m.name) == Some("foo"))
        .expect("LB; foo");
    assert_ne!(a_foo.offset, 0);
    assert_ne!(b_foo.offset, 0);
    assert_ne!(
        a_foo.offset, b_foo.offset,
        "same-named methods must have distinct offsets"
    );

    let a_x = global
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("x"))
        .expect("global x");
    let b_x = bcls
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("x"))
        .expect("LB; x");
    assert_ne!(a_x.offset, 0);
    assert_ne!(b_x.offset, 0);
    assert_ne!(
        a_x.offset, b_x.offset,
        "same-named fields must have distinct offsets"
    );

    // The literal array referenced A.foo; the stored entity offset must be
    // A's method, not B's same-named one.
    let la = file.literal_arrays.first().expect("literal array");
    let mut saw_method = false;
    for v in &la.values {
        if let LiteralValue::Method(off) = v {
            saw_method = true;
            assert_eq!(
                *off, a_foo.offset,
                "literal array must reference the global foo by offset"
            );
        }
    }
    assert!(
        saw_method,
        "literal array must contain the method reference"
    );
}
