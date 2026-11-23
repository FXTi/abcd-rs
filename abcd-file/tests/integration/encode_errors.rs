//! Encode-side error paths: builder-misuse rejections (cross-builder
//! handles, bad relocation targets) and hand-built model errors (dangling
//! StringIds, unresolvable entity references, nested annotation arrays,
//! nested literal arrays inside annotation-embedded literal arrays (c-COV
//! W5 ruling), out-of-range literal-array indices, oversized module request
//! indices).
//! Each test asserts the exact `Error` variant — the encoder fails loudly,
//! never silently, on models it cannot represent (audit #6/#7 contract).

use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationValue, Builder, CodeEntity, Error,
    FieldValue, LiteralValue, MethodDebugInfo, ModuleData, ModuleRecord, ParamInfo, SourceLang,
    Type, decode, encode,
};
use abcd_isa::{Bytecode, EntityId, EntityKind};

/// Minimal base: one global class with one trivial method, decoded to a
/// model for hand-mutation.
fn base_model() -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65], // returnundefined
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let data = b.finalize().expect("finalize");
    decode(&data).expect("decode base")
}

/// A StringId that dangles for `file.strings`: interned in a scratch pool
/// far past the real pool's size.
fn dangling_sid() -> abcd_file::StringId {
    let mut scratch = abcd_file::StringPool::default();
    for i in 0..1000 {
        scratch.get_or_intern(format!("scratch{i}"));
    }
    scratch.get_or_intern("dangling")
}

/// Push a one-element class annotation onto the global class.
fn push_class_annotation(file: &mut abcd_file::File, value: AnnotationValue) {
    let desc = file.strings.get_or_intern("LAnno;");
    let name = file.strings.get_or_intern("e");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.annotations.compile_time.push(Annotation {
        class_descriptor: desc,
        elements: vec![AnnotationElem { name, value }],
    });
}

// ---------------------------------------------------------------------------
// Builder misuse (bridge rejections)
// ---------------------------------------------------------------------------

/// `field_set_value_literalarray` rejects a literal-array handle belonging
/// to a DIFFERENT builder (the bridge bounds-checks the handle against the
/// receiving builder's table).
#[test]
fn field_set_value_literalarray_cross_builder_rejected() {
    let mut b1 = Builder::new();
    b1.set_api(12, "beta1");
    let cls = b1.add_global_class();
    let f = b1.class_add_field(cls, "f", Type::I32, AccessFlags::PUBLIC);

    let mut b2 = Builder::new();
    b2.set_api(12, "beta1");
    // Two arrays so the handle (index 1) is past b1's empty table even if
    // b1 later grows one array.
    b2.add_literal_array("a");
    let foreign_la = b2.add_literal_array("b");

    let err = b1
        .field_set_value_literalarray(f, foreign_la)
        .expect_err("cross-builder literal-array handle must be rejected");
    assert!(
        matches!(err, Error::ModuleData(ref msg) if msg.contains("invalid field or literal-array handle")),
        "unexpected error: {err:?}"
    );
}

/// `literal_array_add_module_data` rejects a cross-builder array handle and
/// (same-builder) cross-builder record string handles, staging nothing.
#[test]
fn module_data_staging_rejected() {
    let mut b1 = Builder::new();
    b1.set_api(12, "beta1");
    let la1 = b1.add_literal_array("la1");

    let mut b2 = Builder::new();
    b2.set_api(12, "beta1");
    b2.add_literal_array("a");
    let foreign_la = b2.add_literal_array("b");

    // Cross-builder literal-array handle.
    let err = b1
        .literal_array_add_module_data(foreign_la, &[], &[])
        .expect_err("cross-builder literal-array handle must be rejected");
    assert!(
        matches!(err, Error::ModuleData(ref msg) if msg.contains("staging rejected")),
        "unexpected error: {err:?}"
    );

    // Valid array, but the record carries a string handle from b2.
    let mut b3 = Builder::new();
    b3.set_api(12, "beta1");
    b3.add_string("x");
    b3.add_string("y");
    let foreign_name = b3.add_string("z"); // index 2 > b1's string table
    let err = b1
        .literal_array_add_module_data(
            la1,
            &[],
            &[abcd_file::ModuleRecordDef::NamespaceImport {
                local_name: foreign_name,
                module_request_idx: 0,
            }],
        )
        .expect_err("cross-builder record string handle must be rejected");
    assert!(
        matches!(err, Error::ModuleData(ref msg) if msg.contains("staging rejected")),
        "unexpected error: {err:?}"
    );
}

/// `literal_array_add_module_request_phase` rejects a cross-builder array
/// handle.
#[test]
fn module_request_phase_staging_cross_builder_rejected() {
    let mut b1 = Builder::new();
    b1.set_api(12, "beta1");

    let mut b2 = Builder::new();
    b2.set_api(12, "beta1");
    b2.add_literal_array("a");
    let foreign_la = b2.add_literal_array("b");

    let err = b1
        .literal_array_add_module_request_phase(foreign_la, &[0, 1])
        .expect_err("cross-builder literal-array handle must be rejected");
    assert!(
        matches!(err, Error::ModuleData(ref msg) if msg.contains("staging rejected")),
        "unexpected error: {err:?}"
    );
}

/// `relocate_code_id` rejects a byte offset that is not an instruction
/// location the bridge can patch (past the code item).
#[test]
fn relocate_code_id_rejects_bad_location() {
    let mut b = Builder::new();
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = abcd_isa::encode(&[Bytecode::Returnundefined]).unwrap();
    let owner = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 0, 0);
    let text = b.add_string("unused");
    let err = b
        .relocate_code_id(owner, 0xFFFF, 0, CodeEntity::String(text))
        .expect_err("a byte offset past the code item must be rejected");
    assert!(
        matches!(err, Error::CodeRelocation(ref msg) if msg.contains("invalid builder target or code location")),
        "unexpected error: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Hand-built model errors
// ---------------------------------------------------------------------------

/// A class key (descriptor) that dangles in the pool fails at the very
/// first encode pass.
#[test]
fn dangling_class_descriptor_string_id() {
    let mut file = base_model();
    let dangling = dangling_sid();
    file.classes.insert(
        dangling,
        abcd_file::Class {
            descriptor: dangling,
            name: dangling,
            access_flags: AccessFlags::empty(),
            source_lang: SourceLang::EcmaScript,
            source_file: None,
            is_external: true, // first pass: foreign classes
            super_class: None,
            interfaces: Vec::new(),
            methods: Vec::new(),
            fields: Vec::new(),
            annotations: Default::default(),
        },
    );
    let err = encode(&file).expect_err("dangling class descriptor must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "string_id",
                ..
            }
        ),
        "unexpected error: {err:?}"
    );
}

/// A method name that dangles in the pool fails through the same `rs()`
/// guard on the method pass.
#[test]
fn dangling_method_name_string_id() {
    let mut file = base_model();
    let dangling = dangling_sid();
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.methods[0].name = dangling;
    let err = encode(&file).expect_err("dangling method name must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "string_id",
                ..
            }
        ),
        "unexpected error: {err:?}"
    );
}

/// A dangling StringId inside a debug record propagates out of
/// `encode_debug_info` (params are interned unconditionally).
#[test]
fn debug_record_dangling_param_name() {
    let mut file = base_model();
    let dangling = dangling_sid();
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.methods[0].debug = Some(MethodDebugInfo {
        source_file: None,
        source_code: None,
        line_table: Vec::new(),
        column_table: Vec::new(),
        local_vars: Vec::new(),
        params: vec![ParamInfo {
            name: dangling,
            signature: dangling,
        }],
    });
    let err = encode(&file).expect_err("dangling debug param name must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "string_id",
                ..
            }
        ),
        "unexpected error: {err:?}"
    );
}

/// A super-class descriptor that dangles in the pool fails in the
/// `resolve_class_id` miss path (the error sub-arm before the auto-foreign
/// fallback).
#[test]
fn super_class_dangling_string_id() {
    let mut file = base_model();
    let dangling = dangling_sid();
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.super_class = Some(dangling);
    let err = encode(&file).expect_err("dangling super-class descriptor must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "string_id",
                ..
            }
        ),
        "unexpected error: {err:?}"
    );
}

/// A dangling element name in a METHOD annotation propagates out of the
/// method-annotation encode.
#[test]
fn method_annotation_dangling_element_name() {
    let mut file = base_model();
    let desc = file.strings.get_or_intern("LAnno;");
    let dangling = dangling_sid();
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.methods[0].annotations.compile_time.push(Annotation {
        class_descriptor: desc,
        elements: vec![AnnotationElem {
            name: dangling,
            value: AnnotationValue::U32(1),
        }],
    });
    let err = encode(&file).expect_err("dangling method-annotation name must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "string_id",
                ..
            }
        ),
        "unexpected error: {err:?}"
    );
}

/// A dangling element name in a FIELD annotation propagates out of the
/// field-annotation encode.
#[test]
fn field_annotation_dangling_element_name() {
    let mut file = base_model();
    let desc = file.strings.get_or_intern("LAnno;");
    let dangling = dangling_sid();
    let field_name = file.strings.get_or_intern("fld");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.fields.push(abcd_file::Field {
        name: field_name,
        offset: 0,
        field_type: Type::I32,
        access_flags: AccessFlags::PUBLIC,
        is_external: false,
        initial_value: None,
        annotations: abcd_file::Annotations {
            compile_time: vec![Annotation {
                class_descriptor: desc,
                elements: vec![AnnotationElem {
                    name: dangling,
                    value: AnnotationValue::U32(1),
                }],
            }],
            ..Default::default()
        },
    });
    let err = encode(&file).expect_err("dangling field-annotation name must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "string_id",
                ..
            }
        ),
        "unexpected error: {err:?}"
    );
}

/// An annotation whose CLASS DESCRIPTOR dangles fails in
/// `resolve_class_for_ann`.
#[test]
fn annotation_dangling_class_descriptor() {
    let mut file = base_model();
    let dangling = dangling_sid();
    let name = file.strings.get_or_intern("e");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.annotations.compile_time.push(Annotation {
        class_descriptor: dangling,
        elements: vec![AnnotationElem {
            name,
            value: AnnotationValue::U32(1),
        }],
    });
    let err = encode(&file).expect_err("dangling annotation class descriptor must fail");
    assert!(
        matches!(err, Error::Malformed { field: "string_id", ref context } if context.contains("annotation class descriptor")),
        "unexpected error: {err:?}"
    );
}

/// Annotation array Method/Enum elements that resolve to nothing (foreign
/// or absent members) are a hard error, never a silent 0 (audit #7).
#[test]
fn annotation_array_member_elem_unresolvable() {
    // Method element (tag 'X' = ArrayMethod).
    let mut file = base_model();
    let name = file.strings.get_or_intern("no_such_method");
    push_class_annotation(
        &mut file,
        AnnotationValue::Array {
            tag: b'X',
            values: vec![AnnotationValue::Method {
                name,
                offset: 0x77777,
            }],
        },
    );
    let err = encode(&file).expect_err("unresolvable array method element must fail");
    assert!(
        matches!(err, Error::CodeRelocation(ref msg) if msg.contains("annotation array method reference")),
        "unexpected error: {err:?}"
    );

    // Enum element (tag 'Y' = ArrayEnum).
    let mut file = base_model();
    let name = file.strings.get_or_intern("no_such_field");
    push_class_annotation(
        &mut file,
        AnnotationValue::Array {
            tag: b'Y',
            values: vec![AnnotationValue::Enum {
                name,
                offset: 0x77777,
            }],
        },
    );
    let err = encode(&file).expect_err("unresolvable array enum element must fail");
    assert!(
        matches!(err, Error::CodeRelocation(ref msg) if msg.contains("annotation array enum reference")),
        "unexpected error: {err:?}"
    );
}

/// An annotation array method-handle element whose entity resolves to
/// nothing is a hard error (the '@' array arm of the element converter).
#[test]
fn annotation_array_method_handle_elem_unresolvable() {
    let mut file = base_model();
    let name = file.strings.get_or_intern("no_such_method");
    push_class_annotation(
        &mut file,
        AnnotationValue::Array {
            tag: b'@',
            values: vec![AnnotationValue::MethodHandle(
                abcd_file::ResolvedMethodHandle {
                    handle_type: abcd_file::MethodHandleType::InvokeStatic,
                    entity: name,
                    entity_offset: 0x77777,
                },
            )],
        },
    );
    let err = encode(&file).expect_err("unresolvable array method-handle element must fail");
    assert!(
        matches!(err, Error::CodeRelocation(ref msg) if msg.contains("annotation array method-handle reference")),
        "unexpected error: {err:?}"
    );
}

/// Nested annotation arrays pass `validate_annotation_arrays` (its
/// recursion only rejects 64-bit elements) and then fail loudly at the
/// array-element conversion: the builder ABI has no nested arrays.
#[test]
fn nested_annotation_arrays_rejected() {
    let mut file = base_model();
    push_class_annotation(
        &mut file,
        AnnotationValue::Array {
            tag: b'Q',
            values: vec![AnnotationValue::Array {
                tag: b'Q',
                values: vec![AnnotationValue::U32(1)],
            }],
        },
    );
    let err = encode(&file).expect_err("nested annotation arrays must fail");
    assert!(
        matches!(err, Error::CodeRelocation(ref msg) if msg.contains("nested annotation arrays are not supported")),
        "unexpected error: {err:?}"
    );
}

/// An annotation-embedded literal array carrying ANY nested literal-array
/// reference — even an out-of-bounds one — is rejected by the validation
/// pass BEFORE writing (c-COV W5). The write path's bounds-check arm in
/// `encode_literal_value_simple` is defense-only after the ruling, so the
/// observed error is the structured rejection, not the bounds error.
#[test]
fn embedded_nested_literal_array_index_out_of_bounds() {
    let mut file = base_model();
    push_class_annotation(
        &mut file,
        AnnotationValue::LiteralArray(vec![LiteralValue::LiteralArray(
            abcd_file::LiteralArrayIdx(99),
        )]),
    );
    let err = encode(&file).expect_err("out-of-bounds embedded nested array must fail");
    assert!(
        matches!(
            err,
            Error::NestedLiteralArrayInAnnotation {
                item_index: 0,
                nested_index: 99,
                ..
            }
        ),
        "unexpected error: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// c-COV W5 ruling: nested LiteralValue::LiteralArray inside an
// annotation-embedded literal array is REJECTED before writing (the vendored
// writer/reader pair corrupts the shape; upstream pandasm cannot express it).
// ---------------------------------------------------------------------------

/// The core rejection: a nested literal-array reference at any position of
/// an annotation-embedded literal array is a structured error, even when the
/// referenced model table index is IN BOUNDS (the pre-fix bounds check would
/// have accepted it and the writer would have corrupted the file: every item
/// after the nested reference decodes shifted and the reference resolves to
/// a wrong array).
#[test]
fn embedded_nested_literal_array_rejected() {
    let mut file = base_model();
    // In-bounds target: the rejection is about the SHAPE, not the index.
    file.literal_arrays.push(abcd_file::LiteralArray {
        values: vec![LiteralValue::Integer(0x1111)],
    });
    push_class_annotation(
        &mut file,
        AnnotationValue::LiteralArray(vec![
            LiteralValue::Integer(10),
            LiteralValue::LiteralArray(abcd_file::LiteralArrayIdx(0)),
            LiteralValue::Integer(20),
        ]),
    );
    let err = encode(&file)
        .expect_err("a nested literal array in an annotation-embedded array must be rejected");
    assert_eq!(
        err,
        Error::NestedLiteralArrayInAnnotation {
            annotation: "LAnno;".to_owned(),
            element_name: "e".to_owned(),
            owner: "class L_GLOBAL;".to_owned(),
            item_index: 1,
            nested_index: 0,
        }
    );
    // The Display text carries the full field/context.
    let msg = err.to_string();
    for fragment in [
        "LAnno;",
        "'e'",
        "class L_GLOBAL;",
        "item 1",
        "model table index 0",
        "no representation inside annotation-embedded literal arrays",
    ] {
        assert!(
            msg.contains(fragment),
            "message must contain {fragment:?}: {msg}"
        );
    }
}

/// The owner context names the entity the annotation is attached to:
/// method and field targets, in every annotation bucket.
#[test]
fn embedded_nested_literal_array_owner_contexts() {
    let nested = |file: &mut abcd_file::File| {
        file.literal_arrays.push(abcd_file::LiteralArray {
            values: vec![LiteralValue::Integer(1)],
        });
        let desc = file.strings.get_or_intern("LAnno;");
        let name = file.strings.get_or_intern("v");
        Annotation {
            class_descriptor: desc,
            elements: vec![AnnotationElem {
                name,
                value: AnnotationValue::LiteralArray(vec![LiteralValue::LiteralArray(
                    abcd_file::LiteralArrayIdx(0),
                )]),
            }],
        }
    };

    // Method annotation (runtime bucket).
    let mut file = base_model();
    let ann = nested(&mut file);
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.methods[0].annotations.runtime.push(ann);
    let err = encode(&file).expect_err("method-owner nested array must fail");
    assert!(
        matches!(
            err,
            Error::NestedLiteralArrayInAnnotation { ref owner, item_index: 0, .. }
                if owner == "method L_GLOBAL;::func_main_0"
        ),
        "unexpected error: {err:?}"
    );

    // Field annotation (type bucket).
    let mut file = base_model();
    let ann = nested(&mut file);
    let field_name = file.strings.get_or_intern("fld");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.fields.push(abcd_file::Field {
        name: field_name,
        offset: 0,
        field_type: Type::I32,
        access_flags: AccessFlags::PUBLIC,
        is_external: false,
        initial_value: None,
        annotations: abcd_file::Annotations {
            compile_time_type: vec![ann],
            ..Default::default()
        },
    });
    let err = encode(&file).expect_err("field-owner nested array must fail");
    assert!(
        matches!(
            err,
            Error::NestedLiteralArrayInAnnotation { ref owner, item_index: 0, .. }
                if owner == "field L_GLOBAL;::fld"
        ),
        "unexpected error: {err:?}"
    );
}

/// When the embedded literal array sits inside a NESTED annotation, the
/// reported site re-seats to the inner annotation and element.
#[test]
fn embedded_nested_literal_array_nested_annotation_site() {
    let mut file = base_model();
    let desc = file.strings.get_or_intern("LOuter;");
    let inner_desc = file.strings.get_or_intern("LInner;");
    let outer_name = file.strings.get_or_intern("outer");
    let inner_name = file.strings.get_or_intern("inner");
    push_class_annotation(
        &mut file,
        AnnotationValue::LiteralArray(vec![LiteralValue::Integer(1)]), // decoy, valid
    );
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.annotations.compile_time.push(Annotation {
        class_descriptor: desc,
        elements: vec![AnnotationElem {
            name: outer_name,
            value: AnnotationValue::Annotation(Box::new(Annotation {
                class_descriptor: inner_desc,
                elements: vec![AnnotationElem {
                    name: inner_name,
                    value: AnnotationValue::LiteralArray(vec![
                        LiteralValue::Integer(1),
                        LiteralValue::Integer(2),
                        LiteralValue::LiteralArray(abcd_file::LiteralArrayIdx(7)),
                    ]),
                }],
            })),
        }],
    });
    let err = encode(&file).expect_err("nested-annotation embedded array must fail");
    assert_eq!(
        err,
        Error::NestedLiteralArrayInAnnotation {
            annotation: "LInner;".to_owned(),
            element_name: "inner".to_owned(),
            owner: "class L_GLOBAL;".to_owned(),
            item_index: 2,
            nested_index: 7,
        }
    );
}

/// A literal array reached through an array-typed ('#') annotation element
/// is annotation-embedded too: the recursion must catch the nested
/// reference inside it.
#[test]
fn embedded_nested_literal_array_through_array_element() {
    let mut file = base_model();
    file.literal_arrays.push(abcd_file::LiteralArray {
        values: vec![LiteralValue::Integer(1)],
    });
    push_class_annotation(
        &mut file,
        AnnotationValue::Array {
            tag: b'#',
            values: vec![AnnotationValue::LiteralArray(vec![
                LiteralValue::LiteralArray(abcd_file::LiteralArrayIdx(0)),
            ])],
        },
    );
    let err = encode(&file).expect_err("nested array through a '#' element must fail");
    assert!(
        matches!(
            err,
            Error::NestedLiteralArrayInAnnotation {
                ref annotation,
                item_index: 0,
                nested_index: 0,
                ..
            } if annotation == "LAnno;"
        ),
        "unexpected error: {err:?}"
    );
}

/// Parameter annotations encode through the same annotation path
/// (`encode_single_annotation`), so an embedded array there carries the
/// same unrepresentable shape and is rejected with the param owner.
#[test]
fn param_annotation_nested_literal_array_rejected() {
    let mut file = base_model();
    file.literal_arrays.push(abcd_file::LiteralArray {
        values: vec![LiteralValue::Integer(1)],
    });
    let desc = file.strings.get_or_intern("LAnno;");
    let name = file.strings.get_or_intern("p");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    let m = &mut cls.methods[0];
    m.arg_types = vec![Type::Tagged];
    m.param_annotations.compile_time = vec![vec![Annotation {
        class_descriptor: desc,
        elements: vec![AnnotationElem {
            name,
            value: AnnotationValue::LiteralArray(vec![
                LiteralValue::Integer(1),
                LiteralValue::LiteralArray(abcd_file::LiteralArrayIdx(0)),
            ]),
        }],
    }]];
    let err = encode(&file).expect_err("param-annotation nested array must fail");
    assert!(
        matches!(
            err,
            Error::NestedLiteralArrayInAnnotation { ref owner, item_index: 1, .. }
                if owner == "parameter 0 of method L_GLOBAL;::func_main_0"
        ),
        "unexpected error: {err:?}"
    );
}

/// Scoping guard: a PLAIN annotation-embedded literal array on a method
/// parameter (no nested reference) is unaffected by the W5 rejection and
/// round-trips. Param annotations consume `ann_la_*` builder handles during
/// class configuration, so this also pins that the model literal-array
/// handle arithmetic counts them (`count_annotation_literal_arrays`).
#[test]
fn param_annotation_plain_literal_array_unaffected() {
    let mut file = base_model();
    // A model literal array AFTER the param-annotation one: with a
    // miscounting ann_la_base the debug handle assertion fires.
    file.literal_arrays.push(abcd_file::LiteralArray {
        values: vec![LiteralValue::Integer(99)],
    });
    let desc = file.strings.get_or_intern("LAnno;");
    let name = file.strings.get_or_intern("p");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    let m = &mut cls.methods[0];
    m.arg_types = vec![Type::Tagged];
    m.param_annotations.compile_time = vec![vec![Annotation {
        class_descriptor: desc,
        elements: vec![AnnotationElem {
            name,
            value: AnnotationValue::LiteralArray(vec![
                LiteralValue::Integer(11),
                LiteralValue::Integer(22),
            ]),
        }],
    }]];
    let encoded = encode(&file).expect("plain param-annotation literal array must encode");
    let file2 = decode(&encoded).expect("decode re-encoded");
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    let values: Vec<LiteralValue> = g2.methods[0]
        .param_annotations
        .compile_time
        .iter()
        .chain(g2.methods[0].param_annotations.runtime.iter())
        .flat_map(|v| v.iter())
        .flat_map(|a| a.elements.iter())
        .filter_map(|e| match &e.value {
            AnnotationValue::LiteralArray(values) => Some(values.iter().cloned()),
            _ => None,
        })
        .flatten()
        .collect();
    assert!(
        values.contains(&LiteralValue::Integer(11)) && values.contains(&LiteralValue::Integer(22)),
        "the param-annotation literal array content must survive: {values:?}"
    );
    // The model array survives alongside it.
    assert!(
        file2
            .literal_arrays
            .iter()
            .any(|la| la.values == vec![LiteralValue::Integer(99)]),
        "the model literal array must survive"
    );
}

/// Scoping guard: TOP-LEVEL (model) literal-array nesting stays supported —
/// the rejection is scoped to annotation-embedded arrays only. A model with
/// an in-bounds nested reference AND a plain (non-nesting) embedded array
/// encodes cleanly.
#[test]
fn model_nested_literal_array_unaffected_by_annotation_rejection() {
    let mut file = base_model();
    // Model-level nesting: array 0 references array 1.
    file.literal_arrays.push(abcd_file::LiteralArray {
        values: vec![LiteralValue::LiteralArray(abcd_file::LiteralArrayIdx(1))],
    });
    file.literal_arrays.push(abcd_file::LiteralArray {
        values: vec![LiteralValue::Integer(7)],
    });
    // A plain annotation-embedded literal array (no nested reference).
    push_class_annotation(
        &mut file,
        AnnotationValue::LiteralArray(vec![LiteralValue::Integer(42)]),
    );
    let encoded = encode(&file).expect("model-level nesting must stay supported");
    let file2 = decode(&encoded).expect("decode re-encoded");
    let target_ok = file2.literal_arrays.iter().any(|la| {
        matches!(
            la.values.as_slice(),
            [LiteralValue::LiteralArray(idx)]
                if file2
                    .literal_arrays
                    .get(idx.0 as usize)
                    .is_some_and(|t| t.values == vec![LiteralValue::Integer(7)])
        )
    });
    assert!(target_ok, "the model-level nested reference must survive");
}

/// A model literal array whose nested literal-array index is out of bounds
/// fails loudly (model path).
#[test]
fn model_nested_literal_array_index_out_of_bounds() {
    let mut file = base_model();
    file.literal_arrays.push(abcd_file::LiteralArray {
        values: vec![LiteralValue::LiteralArray(abcd_file::LiteralArrayIdx(5))],
    });
    let err = encode(&file).expect_err("out-of-bounds nested array must fail");
    assert!(
        matches!(err, Error::CodeRelocation(ref msg) if msg.contains("nested literal array index 5 out of bounds")),
        "unexpected error: {err:?}"
    );
}

/// Model literal-array method references that resolve to nothing fail
/// loudly (Method and GeneratorMethod arms).
#[test]
fn model_literal_method_refs_unresolvable() {
    let mut file = base_model();
    file.literal_arrays.push(abcd_file::LiteralArray {
        values: vec![LiteralValue::Method(0x77777)],
    });
    let err = encode(&file).expect_err("unresolvable method literal must fail");
    assert!(
        matches!(err, Error::CodeRelocation(ref msg) if msg.contains("literal array method reference")),
        "unexpected error: {err:?}"
    );

    let mut file = base_model();
    file.literal_arrays.push(abcd_file::LiteralArray {
        values: vec![LiteralValue::GeneratorMethod(0x77777)],
    });
    let err = encode(&file).expect_err("unresolvable generator-method literal must fail");
    assert!(
        matches!(err, Error::CodeRelocation(ref msg) if msg.contains("generator-method reference")),
        "unexpected error: {err:?}"
    );

    // The async-generator / getter / setter arms share the same contract.
    for (mk, what) in [
        (
            LiteralValue::AsyncGeneratorMethod as fn(u32) -> LiteralValue,
            "async-generator-method",
        ),
        (LiteralValue::Getter as fn(u32) -> LiteralValue, "getter"),
        (LiteralValue::Setter as fn(u32) -> LiteralValue, "setter"),
    ] {
        let mut file = base_model();
        file.literal_arrays.push(abcd_file::LiteralArray {
            values: vec![mk(0x77777)],
        });
        let err = encode(&file).expect_err("unresolvable method-kind literal must fail");
        assert!(
            matches!(err, Error::CodeRelocation(ref msg) if msg.contains(&format!("{what} reference"))),
            "{what}: unexpected error: {err:?}"
        );
    }
}

/// A literal-array entity operand whose offset maps to an out-of-range
/// literal-array table index fails loudly in the relocation pass.
#[test]
fn code_ref_literal_array_index_out_of_range() {
    let mut file = model_with_entity_ref(EntityKind::LiteralarrayId, 0x1234);
    // The offset resolves through the map, but the table index dangles.
    file.literal_array_offsets.insert(0x1234, 99);
    let err = encode(&file).expect_err("out-of-range literal-array index must fail");
    assert!(
        matches!(err, Error::CodeRelocation(ref msg) if msg.contains("LiteralarrayId index 0")),
        "unexpected error: {err:?}"
    );
}

/// A literal-array string element with a dangling StringId fails at
/// `get_or_add_string_id`.
#[test]
fn literal_string_dangling_string_id() {
    let mut file = base_model();
    let dangling = dangling_sid();
    file.literal_arrays.push(abcd_file::LiteralArray {
        values: vec![LiteralValue::String(dangling)],
    });
    let err = encode(&file).expect_err("dangling literal string must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "string_id",
                ..
            }
        ),
        "unexpected error: {err:?}"
    );
}

/// A scope-names field reference whose source offset was never decoded is
/// a hard error, as is a decoded-but-out-of-range table index.
#[test]
fn scope_names_reference_errors() {
    // Offset absent from the offset map.
    let mut file = base_model();
    let field_name = file.strings.get_or_intern("scope_names");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.fields.push(abcd_file::Field {
        name: field_name,
        offset: 0,
        field_type: Type::U32,
        access_flags: AccessFlags::PUBLIC,
        is_external: false,
        initial_value: Some(FieldValue::LiteralArrayRef(0xdead)),
        annotations: Default::default(),
    });
    let err = encode(&file).expect_err("undecoded scope-names offset must fail");
    assert!(
        matches!(err, Error::ModuleData(ref msg) if msg.contains("was not decoded")),
        "unexpected error: {err:?}"
    );

    // Offset present in the map but the table index is out of range.
    let mut file = base_model();
    file.literal_array_offsets.insert(0xdead, 99);
    let field_name = file.strings.get_or_intern("scope_names");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.fields.push(abcd_file::Field {
        name: field_name,
        offset: 0,
        field_type: Type::U32,
        access_flags: AccessFlags::PUBLIC,
        is_external: false,
        initial_value: Some(FieldValue::LiteralArrayRef(0xdead)),
        annotations: Default::default(),
    });
    let err = encode(&file).expect_err("out-of-range scope-names index must fail");
    assert!(
        matches!(err, Error::ModuleData(ref msg) if msg.contains("out of range")),
        "unexpected error: {err:?}"
    );
}

/// Build a model whose single method body has one unresolved code
/// reference of the given kind.
fn model_with_entity_ref(kind: EntityKind, entity_offset: u32) -> abcd_file::File {
    let mut file = base_model();
    let bytecode = match kind {
        EntityKind::StringId => Bytecode::LdaStr(EntityId(0)),
        EntityKind::MethodId => {
            Bytecode::Definefunc(abcd_isa::Imm(0), EntityId(0), abcd_isa::Imm(0))
        }
        EntityKind::LiteralarrayId => {
            Bytecode::Createarraywithbuffer(abcd_isa::Imm(0), EntityId(0))
        }
    };
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    let body = cls.methods[0].body.as_mut().expect("body");
    body.bytecodes = vec![bytecode, Bytecode::Returnundefined];
    body.entity_offsets.insert((kind, 0), entity_offset);
    file
}

/// The code-reference relocation pass fails loudly when the body's
/// entity-offset map entry itself dangles.
#[test]
fn code_ref_missing_entity_offset_entry() {
    let mut file = base_model();
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    let body = cls.methods[0].body.as_mut().expect("body");
    body.bytecodes = vec![Bytecode::LdaStr(EntityId(0)), Bytecode::Returnundefined];
    // No entity_offsets entry for (StringId, 0).
    let err = encode(&file).expect_err("missing entity-offset entry must fail");
    assert!(
        matches!(err, Error::CodeRelocation(ref msg) if msg.contains("StringId index 0")),
        "unexpected error: {err:?}"
    );
}

/// A string operand whose resolved offset is absent from the file's
/// entity map is a hard error.
#[test]
fn code_ref_string_entity_map_miss() {
    let file = model_with_entity_ref(EntityKind::StringId, 0x1234);
    let err = encode(&file).expect_err("entity-map miss must fail");
    assert!(
        matches!(err, Error::CodeRelocation(ref msg) if msg.contains("StringId index 0")),
        "unexpected error: {err:?}"
    );
}

/// A string operand whose entity-map StringId dangles in the pool fails at
/// the string-table intern.
#[test]
fn code_ref_string_entity_dangling_id() {
    let mut file = model_with_entity_ref(EntityKind::StringId, 0x1234);
    let dangling = dangling_sid();
    file.entity_map.insert(0x1234, dangling);
    let err = encode(&file).expect_err("dangling string entity must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "string_id",
                ..
            }
        ),
        "unexpected error: {err:?}"
    );
}

/// A method operand whose resolved offset names no known method is a hard
/// error.
#[test]
fn code_ref_method_offset_miss() {
    let file = model_with_entity_ref(EntityKind::MethodId, 0x1234);
    let err = encode(&file).expect_err("unresolvable method offset must fail");
    assert!(
        matches!(err, Error::CodeRelocation(ref msg) if msg.contains("MethodId index 0")),
        "unexpected error: {err:?}"
    );
}

/// A literal-array operand whose resolved offset is absent from the
/// literal-array offset map is a hard error.
#[test]
fn code_ref_literal_array_offset_miss() {
    let file = model_with_entity_ref(EntityKind::LiteralarrayId, 0x1234);
    let err = encode(&file).expect_err("unresolvable literal-array offset must fail");
    assert!(
        matches!(err, Error::CodeRelocation(ref msg) if msg.contains("LiteralarrayId index 0")),
        "unexpected error: {err:?}"
    );
}

/// A module record whose request index exceeds the vendored u16 slot is a
/// hard error (pre-empts the bridge's own check, which would reject the
/// whole staging).
#[test]
fn module_request_idx_exceeds_u16() {
    let mut file = base_model();
    let req = file.strings.get_or_intern("./dep");
    let local = file.strings.get_or_intern("dep");
    let field_name = file.strings.get_or_intern("_ESModuleRecord");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.fields.push(abcd_file::Field {
        name: field_name,
        offset: 0,
        field_type: Type::U32,
        access_flags: AccessFlags::PUBLIC,
        is_external: false,
        initial_value: Some(FieldValue::ModuleData(ModuleData {
            source_offset: 0,
            requests: vec![req],
            records: vec![ModuleRecord::RegularImport {
                local_name: local,
                import_name: local,
                module_request_idx: u32::MAX,
            }],
        })),
        annotations: Default::default(),
    });
    let err = encode(&file).expect_err("oversized module request index must fail");
    assert!(
        matches!(err, Error::ModuleData(ref msg) if msg.contains("exceeds the vendored u16 slot")),
        "unexpected error: {err:?}"
    );
}

/// A module-record blob whose request string dangles in the pool fails at
/// the string intern inside the deferred field-value pass.
#[test]
fn module_data_dangling_request_string() {
    let mut file = base_model();
    let dangling = dangling_sid();
    let field_name = file.strings.get_or_intern("_ESModuleRecord");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.fields.push(abcd_file::Field {
        name: field_name,
        offset: 0,
        field_type: Type::U32,
        access_flags: AccessFlags::PUBLIC,
        is_external: false,
        initial_value: Some(FieldValue::ModuleData(ModuleData {
            source_offset: 0,
            requests: vec![dangling],
            records: Vec::new(),
        })),
        annotations: Default::default(),
    });
    let err = encode(&file).expect_err("dangling module request string must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "string_id",
                ..
            }
        ),
        "unexpected error: {err:?}"
    );
}
