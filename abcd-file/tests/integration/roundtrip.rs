use abcd_file::{
    AccessFlags, AnnotationElemDef, Builder, Bytecode, SourceLang, Type, decode, encode,
};

/// Build a minimal ABC file with one global class and one method.
fn build_minimal() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");

    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);

    let proto = b.create_proto(Type::Tagged, &[]);
    // 0x65 = returnundefined
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
    b.method_set_function_kind(m, abcd_file::FunctionKind::Function);

    b.finalize().expect("finalize should succeed")
}

/// Build a richer file covering the item kinds the dedup passes walk:
/// a field with an initial value, a class annotation, debug info with a
/// line table, and a literal array.
fn build_rich() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");

    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);

    let f = b.class_add_field(cls, "count", Type::I32, AccessFlags::PUBLIC);
    b.field_set_value_i32(f, 42);

    // Class annotation with one U32 element (tag b'7').
    let ann_name = b.add_string("level");
    let ann = b.create_annotation(
        cls,
        &[AnnotationElemDef {
            name: ann_name,
            tag: b'7',
            value: 9,
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

    // Debug info with a source file and a line table. Regression test for
    // design/review-isa-file.md #16 (line-number programs were emitted
    // before layout, recording string offsets of 0).
    let lnp = b.create_lnp();
    let debug = b.create_debug_info(lnp, 1);
    let src_file = b.add_string("main.js");
    b.lnp_emit_set_file(lnp, debug, src_file);
    b.lnp_emit_advance_pc(lnp, debug, 1);
    b.lnp_emit_advance_line(lnp, debug, 2);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m, debug);

    let la = b.add_literal_array("lit");
    let hello = b.add_string("hello");
    b.literal_array_add_string(la, hello);

    b.finalize().expect("finalize should succeed")
}

#[test]
fn builder_roundtrip() {
    let data = build_minimal();
    assert!(!data.is_empty());

    let file = decode(&data).expect("should decode");
    assert!(!file.classes.is_empty());

    assert!(
        file.version.major() > 0 || file.version.minor() > 0,
        "version should be non-zero"
    );
}

#[test]
fn read_class_and_method() {
    let data = build_minimal();
    let file = decode(&data).expect("should decode");

    // Classes are keyed by descriptor (StringId).
    let (&desc, cls) = file.classes.iter().next().expect("should have a class");
    let desc_str = file.strings.resolve(desc).unwrap();
    assert!(
        desc_str.contains("GLOBAL"),
        "descriptor should contain GLOBAL: {desc_str}"
    );

    assert_eq!(cls.methods.len(), 1);
    let m = &cls.methods[0];
    let m_name = file.strings.resolve(m.name).unwrap();
    assert_eq!(m_name, "func_main_0");
    assert!(m.access_flags.contains(AccessFlags::PUBLIC));
    assert_eq!(m.function_kind, abcd_file::FunctionKind::Function);

    let body = m.body.as_ref().expect("should have body");
    // Bytecode should be decoded.
    assert!(!body.bytecodes.is_empty());
    assert!(matches!(body.bytecodes[0], Bytecode::Returnundefined));
}

#[test]
fn file_type_detection() {
    let data = build_minimal();
    let file = decode(&data).expect("should decode");
    assert_eq!(file.file_type, abcd_file_sys::FileType::Dynamic);
}

#[test]
fn encode_roundtrip() {
    // Build → decode → encode → decode again, compare. Regression test for
    // review finding #3: encode() round-trip was disabled because
    // DeduplicateItems was invoked without a layout pass, so its hash
    // computation dereferenced unset index ranges.
    let original_data = build_minimal();
    let file1 = decode(&original_data).expect("first decode");

    let encoded = encode(&file1).expect("encode should succeed");
    assert!(!encoded.is_empty(), "encoded output should be non-empty");

    let file2 = decode(&encoded).expect("second decode");

    // Compare class count
    assert_eq!(
        file1.classes.len(),
        file2.classes.len(),
        "class count mismatch"
    );

    // Compare each class
    for (&desc, cls1) in &file1.classes {
        let desc_str = file1.strings.resolve(desc).unwrap();
        let cls2 = file2
            .class_by_str(desc_str)
            .unwrap_or_else(|| panic!("missing class {desc_str}"));

        assert_eq!(
            cls1.access_flags, cls2.access_flags,
            "access_flags mismatch for {desc_str}"
        );
        assert_eq!(
            cls1.source_lang, cls2.source_lang,
            "source_lang mismatch for {desc_str}"
        );
        assert_eq!(
            cls1.is_external, cls2.is_external,
            "is_external mismatch for {desc_str}"
        );
        assert_eq!(
            cls1.methods.len(),
            cls2.methods.len(),
            "method count mismatch for {desc_str}"
        );

        for (m1, m2) in cls1.methods.iter().zip(cls2.methods.iter()) {
            let m1_name = file1.strings.resolve(m1.name).unwrap();
            let m2_name = file2.strings.resolve(m2.name).unwrap();
            assert_eq!(m1_name, m2_name, "method name mismatch");
            assert_eq!(m1.access_flags, m2.access_flags, "method flags mismatch");
            assert_eq!(m1.function_kind, m2.function_kind, "function_kind mismatch");
            assert_eq!(
                m1.is_external, m2.is_external,
                "method is_external mismatch"
            );

            // Compare bytecodes
            match (&m1.body, &m2.body) {
                (Some(b1), Some(b2)) => {
                    assert_eq!(
                        b1.bytecodes.len(),
                        b2.bytecodes.len(),
                        "bytecode count mismatch for {m1_name}",
                    );
                    for (i, (bc1, bc2)) in b1.bytecodes.iter().zip(b2.bytecodes.iter()).enumerate()
                    {
                        assert_eq!(
                            format!("{bc1:?}"),
                            format!("{bc2:?}"),
                            "bytecode mismatch at index {i} in {m1_name}",
                        );
                    }
                }
                (None, None) => {}
                _ => panic!("body presence mismatch for {m1_name}"),
            }
        }

        assert_eq!(
            cls1.fields.len(),
            cls2.fields.len(),
            "field count mismatch for {desc_str}"
        );
        for (f1, f2) in cls1.fields.iter().zip(cls2.fields.iter()) {
            assert_eq!(f1.name, f2.name, "field name mismatch");
            assert_eq!(f1.access_flags, f2.access_flags, "field flags mismatch");
        }
    }
}

#[test]
fn encode_roundtrip_rich() {
    // Same as encode_roundtrip but through the item kinds the dedup passes
    // walk: field initial value, class annotation, debug info, literal array.
    let data = build_rich();
    let file1 = decode(&data).expect("first decode");
    let encoded = encode(&file1).expect("encode should succeed");
    let file2 = decode(&encoded).expect("second decode");

    let g1 = file1
        .classes
        .values()
        .find(|c| !c.is_external)
        .expect("global class (original)");
    let g2 = file2
        .classes
        .values()
        .find(|c| !c.is_external)
        .expect("global class (re-encoded)");

    assert_eq!(g1.fields.len(), g2.fields.len());
    assert_eq!(
        g1.fields[0].initial_value, g2.fields[0].initial_value,
        "field initial value must round-trip"
    );

    // Annotation categories collapse to the ANNOTATION section on write
    // (upstream API-24 behavior, review finding #9); decode surfaces it as
    // compile_time, so assert on that bucket.
    assert_eq!(
        g1.annotations.compile_time.len(),
        g2.annotations.compile_time.len()
    );
    assert_eq!(
        g1.annotations.compile_time[0].elements.len(),
        g2.annotations.compile_time[0].elements.len(),
        "annotation element count must round-trip"
    );

    // Debug info round-trips: the original file extracts it, and so does
    // the re-encoded one (see #16).
    let d1 = g1.methods[0]
        .debug
        .as_ref()
        .expect("debug info must decode from the original file");
    let src1 = d1.source_file.map(|s| file1.strings.resolve(s).unwrap());
    assert_eq!(src1, Some("main.js"), "source file must decode correctly");
    assert!(!d1.line_table.is_empty(), "line table must decode");

    let m2 = &g2.methods[0];
    assert!(m2.body.is_some(), "method body must round-trip");
    let d2 = m2.debug.as_ref().expect("debug info must round-trip");
    let src2 = d2.source_file.map(|s| file2.strings.resolve(s).unwrap());
    assert_eq!(src2, Some("main.js"), "source file must round-trip");
    assert!(!d2.line_table.is_empty(), "line table must round-trip");

    assert_eq!(
        file1.literal_arrays.len(),
        file2.literal_arrays.len(),
        "literal array count must round-trip"
    );
    let resolve = |f: &abcd_file::File, v: &abcd_file::LiteralValue| -> String {
        match v {
            abcd_file::LiteralValue::String(sid) => f.strings.resolve(*sid).unwrap().to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(
        file1.literal_arrays[0]
            .values
            .iter()
            .map(|v| resolve(&file1, v))
            .collect::<Vec<_>>(),
        file2.literal_arrays[0]
            .values
            .iter()
            .map(|v| resolve(&file2, v))
            .collect::<Vec<_>>(),
        "literal array values must round-trip"
    );
}
