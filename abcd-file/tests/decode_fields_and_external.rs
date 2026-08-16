//! Regression tests for review findings #1 (foreign classes crashed decode)
//! and #2 (primitive-typed fields failed to decode).

use abcd_file::{AccessFlags, Builder, ClassHandle, SourceLang, Type, decode};

/// Build a minimal file: a global class with one `returnundefined` method.
/// `configure` runs after the global class is created and can add fields/classes.
fn build(configure: impl FnOnce(&mut Builder, ClassHandle)) -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    configure(&mut b, cls);
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
fn foreign_class_decode() {
    let data = build(|b, _cls| {
        let _ext = b.add_foreign_class("LExternal;");
    });

    let file = decode(&data).expect("decode must succeed with a foreign class present");

    let external = file
        .classes
        .values()
        .find(|c| c.is_external)
        .expect("foreign class must be surfaced as an external Class entry");
    let desc = file.strings.resolve(external.descriptor).unwrap();
    assert_eq!(desc, "LExternal;");
    assert!(external.methods.is_empty());
    assert!(external.fields.is_empty());
    // The foreign class descriptor is registered in the entity map.
    assert!(file.entity_map.values().any(|&v| v == external.descriptor));
}

#[test]
fn primitive_field_types_decode() {
    // (builder type, expected decoded type)
    let cases: &[(Type, fn() -> Type)] = &[
        (Type::Bool, || Type::Bool),
        (Type::I8, || Type::I8),
        (Type::U8, || Type::U8),
        (Type::I16, || Type::I16),
        (Type::U16, || Type::U16),
        (Type::I32, || Type::I32),
        (Type::U32, || Type::U32),
        (Type::I64, || Type::I64),
        (Type::U64, || Type::U64),
        (Type::F32, || Type::F32),
        (Type::F64, || Type::F64),
        (Type::Tagged, || Type::Tagged),
    ];

    for (i, (ty, expected)) in cases.iter().enumerate() {
        let name = format!("f{i}");
        let data = build(|b, cls| {
            let _f = b.class_add_field(cls, &name, *ty, AccessFlags::PUBLIC);
        });
        let file = decode(&data).unwrap_or_else(|e| panic!("decode failed for {ty:?}: {e}"));
        let global = file
            .classes
            .values()
            .find(|c| !c.is_external)
            .expect("global class");
        let field = global
            .fields
            .iter()
            .find(|f| file.strings.resolve(f.name) == Some(name.as_str()))
            .unwrap_or_else(|| panic!("field {name} missing"));
        assert_eq!(
            field.field_type,
            expected(),
            "field type mismatch for {ty:?}"
        );
    }
}

#[test]
fn reference_field_type_decodes() {
    let data = build(|b, cls| {
        let ext = b.add_foreign_class("LExternal;");
        let mut pool = abcd_file::StringPool::default();
        let dummy = pool.get_or_intern("LExternal;");
        let _f = b.class_add_field_ex(cls, "obj", Type::Reference(dummy), ext, AccessFlags::PUBLIC);
    });

    let file = decode(&data).expect("decode");
    let global = file.classes.values().find(|c| !c.is_external).unwrap();
    let field = global
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("obj"))
        .unwrap();
    match field.field_type {
        Type::Reference(sid) => {
            assert_eq!(file.strings.resolve(sid), Some("LExternal;"));
        }
        other => panic!("expected Reference, got {other:?}"),
    }
}

#[test]
fn field_initial_values_decode() {
    let data = build(|b, cls| {
        let i32f = b.class_add_field(cls, "vi32", Type::I32, AccessFlags::PUBLIC);
        b.field_set_value_i32(i32f, -42);
        let i64f = b.class_add_field(cls, "vi64", Type::I64, AccessFlags::PUBLIC);
        b.field_set_value_i64(i64f, 0x1_0000_0001);
        let f32f = b.class_add_field(cls, "vf32", Type::F32, AccessFlags::PUBLIC);
        b.field_set_value_f32(f32f, 3.5);
        let f64f = b.class_add_field(cls, "vf64", Type::F64, AccessFlags::PUBLIC);
        b.field_set_value_f64(f64f, -2.25);
    });

    let file = decode(&data).expect("decode");
    let global = file.classes.values().find(|c| !c.is_external).unwrap();
    let get = |name: &str| {
        global
            .fields
            .iter()
            .find(|f| file.strings.resolve(f.name) == Some(name))
            .and_then(|f| f.initial_value.clone())
            .unwrap_or_else(|| panic!("field {name} value missing"))
    };
    assert!(matches!(get("vi32"), abcd_file::FieldValue::I32(-42)));
    assert!(matches!(get("vi64"), abcd_file::FieldValue::I64(v) if v == 0x1_0000_0001));
    assert!(matches!(get("vf32"), abcd_file::FieldValue::F32(v) if v == 3.5));
    assert!(matches!(get("vf64"), abcd_file::FieldValue::F64(v) if v == -2.25));
}
