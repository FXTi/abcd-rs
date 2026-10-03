//! Encode-side rare arms: class shapes (super class, interfaces, source
//! file), reference-typed protos and fields, external members, non-I32
//! field initial values, debug-info shapes, and the CodeEntity::Class/Field
//! relocation arms. The corpus fixtures never carry these shapes, so the
//! encode path over them is exercised only here.

use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationValue, Builder, CodeEntity, ColumnEntry,
    FieldValue, FunctionKind, LineEntry, LocalVarInfo, MethodDebugInfo, ParamInfo, SourceLang,
    Type, decode, encode,
};

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

/// A class with a super class, an interface, and a source file: the decode
/// side reads all three (cold corpus-wide), and the re-encode walks the
/// `class_set_super_class` / `class_add_interface` / `class_set_source_file`
/// wrapper arms plus the auto-foreign fallback of `resolve_class_id` (the
/// super class is not a declared class of the file).
#[test]
fn class_super_interface_source_file_roundtrip() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let sup = b.add_foreign_class("LSuper;");
    let iface = b.add_foreign_class("LIface;");
    let cls = b.add_class("LDerived;");
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    b.class_set_super_class(cls, sup);
    b.class_add_interface(cls, iface);
    let sf = b.add_string("derived.ets");
    b.class_set_source_file(cls, sf);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(cls, "m", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let data = b.finalize().expect("finalize");

    let assert_shape = |file: &abcd_file::File, who: &str| {
        let c = file
            .class_by_str("LDerived;")
            .unwrap_or_else(|| panic!("LDerived; present ({who})"));
        let super_name = c
            .super_class
            .and_then(|sid| file.strings.resolve(sid))
            .unwrap_or("<none>");
        assert_eq!(super_name, "LSuper;", "super class ({who})");
        let ifaces: Vec<&str> = c
            .interfaces
            .iter()
            .filter_map(|sid| file.strings.resolve(*sid))
            .collect();
        assert_eq!(ifaces, vec!["LIface;"], "interfaces ({who})");
        let src = c
            .source_file
            .and_then(|sid| file.strings.resolve(sid))
            .unwrap_or("<none>");
        assert_eq!(src, "derived.ets", "source file ({who})");
    };

    let file = decode(&data).expect("decode");
    assert_shape(&file, "decoded");

    let encoded = encode(&file).expect("encode");
    let file2 = decode(&encoded).expect("decode re-encoded");
    assert_shape(&file2, "re-encoded");
}

/// Reference-typed protos: a method whose return type and argument are
/// class references. Drives the cold typed-proto decode path
/// (`abc_proto_get_reference_type`) and the encoder's `ret_class` /
/// `arg_classes` resolution arms.
#[test]
fn reference_typed_proto_roundtrip() {
    let mut b = Builder::new();
    // API 9: the 12.x builder output decodes with an empty proto
    // (pre-existing quirk, see proto_queries.rs).
    b.set_api(9, "");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let widget = b.add_foreign_class("LWidget;");
    // The Builder API takes descriptor strings; the StringId inside
    // `Type::Reference` is only inspected for its TypeId tag on this path,
    // so a scratch pool's interning is fine.
    let mut scratch = abcd_file::StringPool::default();
    let widget_ty = Type::Reference(scratch.get_or_intern("LWidget;"));
    let proto = b.create_proto_ex(
        &widget_ty,
        Some(widget),
        &[widget_ty, Type::I32],
        &[Some(widget), None],
    );
    let m = b.class_add_method(cls, "f", proto, AccessFlags::PUBLIC, &[0x65], 3, 2);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let data = b.finalize().expect("finalize");

    let file = decode(&data).expect("decode");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("f"))
        .expect("method f")
        .1;
    let widget_sid = file.strings.get("LWidget;").expect("widget interned");
    assert_eq!(m.return_type, Some(Type::Reference(widget_sid)));
    assert_eq!(
        m.arg_types,
        vec![Type::Reference(widget_sid), Type::I32],
        "reference-typed proto arguments must decode"
    );

    // Re-encode: the reference return/arg arms resolve the descriptor to a
    // class handle (auto-foreign fallback) and rebuild the proto.
    let encoded = encode(&file).expect("encode");
    let file2 = decode(&encoded).expect("decode re-encoded");
    let m2 = file2
        .all_methods()
        .find(|(_, m)| file2.strings.resolve(m.name) == Some("f"))
        .expect("method f (re-encoded)")
        .1;
    let widget_sid2 = file2.strings.get("LWidget;").expect("widget interned");
    assert_eq!(m2.return_type, Some(Type::Reference(widget_sid2)));
    assert_eq!(m2.arg_types, vec![Type::Reference(widget_sid2), Type::I32]);
}

/// Hand-built model: external (foreign) members drive the `is_external`
/// arms of the method/field encode loops.
#[test]
fn external_members_encode() {
    let mut file = base_model();
    let ext_meth = file.strings.get_or_intern("ext_method");
    let ext_field = file.strings.get_or_intern("ext_field");

    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.methods.push(abcd_file::Method {
        name: ext_meth,
        offset: 0,
        access_flags: AccessFlags::PUBLIC,
        function_kind: FunctionKind::None,
        source_lang: SourceLang::EcmaScript,
        is_external: true,
        return_type: Some(Type::Tagged),
        arg_types: Vec::new(),
        body: None,
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    });
    cls.fields.push(abcd_file::Field {
        name: ext_field,
        offset: 0,
        field_type: Type::I32,
        access_flags: AccessFlags::PUBLIC,
        is_external: true,
        initial_value: None,
        annotations: Default::default(),
    });

    let encoded = encode(&file).expect("encode");
    let file2 = decode(&encoded).expect("decode re-encoded");
    // Foreign members live in the foreign region; they are NOT class
    // members at decode (format fact, see foreign_items.rs).
    let g = file2.classes.values().find(|c| !c.is_external).unwrap();
    assert!(
        g.methods
            .iter()
            .all(|m| file2.strings.resolve(m.name) != Some("ext_method")),
        "external method must not become a class member"
    );
    assert!(
        g.fields
            .iter()
            .all(|f| file2.strings.resolve(f.name) != Some("ext_field")),
        "external field must not become a class member"
    );
}

/// Reference-typed and I64/F32/F64 field initial values through encode.
#[test]
fn field_types_and_initial_values_roundtrip() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let i64f = b.class_add_field(cls, "vi64", Type::I64, AccessFlags::PUBLIC);
    b.field_set_value_i64(i64f, 0x1_0000_0001);
    let f32f = b.class_add_field(cls, "vf32", Type::F32, AccessFlags::PUBLIC);
    b.field_set_value_f32(f32f, 3.5);
    let f64f = b.class_add_field(cls, "vf64", Type::F64, AccessFlags::PUBLIC);
    b.field_set_value_f64(f64f, -2.25);
    // Reference-typed field (drives `class_add_field_ex` on re-encode).
    let widget = b.add_foreign_class("LWidget;");
    let mut scratch = abcd_file::StringPool::default();
    let widget_ty = Type::Reference(scratch.get_or_intern("LWidget;"));
    b.class_add_field_ex(cls, "vref", widget_ty, widget, AccessFlags::PUBLIC);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(cls, "g", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let data = b.finalize().expect("finalize");

    let field_value = |file: &abcd_file::File, name: &str| -> Option<FieldValue> {
        let g = file.classes.values().find(|c| !c.is_external).unwrap();
        g.fields
            .iter()
            .find(|f| file.strings.resolve(f.name) == Some(name))
            .map(|f| f.initial_value.clone())
            .unwrap_or(None)
    };

    let file = decode(&data).expect("decode");
    assert_eq!(
        field_value(&file, "vi64"),
        Some(FieldValue::I64(0x1_0000_0001))
    );
    assert_eq!(field_value(&file, "vf32"), Some(FieldValue::F32(3.5)));
    assert_eq!(field_value(&file, "vf64"), Some(FieldValue::F64(-2.25)));
    // The reference-typed field decodes with a resolved descriptor.
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let vref = g
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("vref"))
        .expect("vref field");
    let widget_sid = file.strings.get("LWidget;").expect("widget interned");
    assert_eq!(vref.field_type, Type::Reference(widget_sid));

    let encoded = encode(&file).expect("encode");
    let file2 = decode(&encoded).expect("decode re-encoded");
    assert_eq!(
        field_value(&file2, "vi64"),
        Some(FieldValue::I64(0x1_0000_0001))
    );
    assert_eq!(field_value(&file2, "vf32"), Some(FieldValue::F32(3.5)));
    assert_eq!(field_value(&file2, "vf64"), Some(FieldValue::F64(-2.25)));
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    let vref2 = g2
        .fields
        .iter()
        .find(|f| file2.strings.resolve(f.name) == Some("vref"))
        .expect("vref field (re-encoded)");
    let widget_sid2 = file2.strings.get("LWidget;").expect("widget interned");
    assert_eq!(vref2.field_type, Type::Reference(widget_sid2));
}

/// Debug info shapes the corpus never encodes: content WITHOUT a line table
/// (the `has_content` short-circuit continuation), params, and a local
/// variable WITHOUT a type signature (`lnp_emit_start_local` else-branch).
#[test]
fn debug_shapes_encode_roundtrip() {
    let mut file = base_model();

    let sf = file.strings.get_or_intern("shapes.ets");
    let sc = file.strings.get_or_intern("function f() {}");
    let param = file.strings.get_or_intern("param0");
    let sig = file.strings.get_or_intern("");
    let lv_name = file.strings.get_or_intern("local0");
    let lv_type = file.strings.get_or_intern("I");
    let lv_sig = file.strings.get_or_intern("");

    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    let m = &mut cls.methods[0];
    m.debug = Some(MethodDebugInfo {
        source_file: Some(sf),
        source_code: Some(sc),
        line_table: Vec::new(), // content without a line table
        column_table: Vec::new(),
        local_vars: vec![LocalVarInfo {
            name: lv_name,
            type_name: lv_type,
            type_signature: lv_sig, // signature-less local var
            reg_number: 2,
            start: 0,
            end: 1,
        }],
        params: vec![ParamInfo {
            name: param,
            signature: sig,
        }],
    });

    let encoded = encode(&file).expect("encode");
    let file2 = decode(&encoded).expect("decode re-encoded");
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    let d2 = g2.methods[0]
        .debug
        .as_ref()
        .expect("debug info must round-trip");
    let sf2 = d2.source_file.map(|s| file2.strings.resolve(s).unwrap());
    assert_eq!(sf2, Some("shapes.ets"), "source file must round-trip");
    let sc2 = d2.source_code.map(|s| file2.strings.resolve(s).unwrap());
    assert_eq!(sc2, Some("function f() {}"), "source code must round-trip");
    assert_eq!(d2.params.len(), 1, "param must round-trip");
    assert_eq!(
        d2.params[0].name,
        file2.strings.get("param0").expect("param interned")
    );
    assert_eq!(d2.local_vars.len(), 1, "local var must round-trip");
    assert_eq!(
        d2.local_vars[0].name,
        file2.strings.get("local0").expect("local interned")
    );
}

/// A completely contentless debug record is skipped by the encoder (the
/// vendored extractor cannot represent it); decode then reports no debug
/// info for the method.
#[test]
fn contentless_debug_record_is_skipped() {
    let mut file = base_model();
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.methods[0].debug = Some(MethodDebugInfo {
        source_file: None,
        source_code: None,
        line_table: Vec::new(),
        column_table: Vec::new(),
        local_vars: Vec::new(),
        params: Vec::new(),
    });

    let encoded = encode(&file).expect("encode");
    let file2 = decode(&encoded).expect("decode re-encoded");
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    assert!(
        g2.methods[0].debug.is_none(),
        "contentless debug record must not be emitted"
    );
}

/// A debug record with a line table plus all content kinds (the encoder's
/// full path: set_file, set_source_code, params, line deltas, local vars
/// with a signature).
#[test]
fn debug_full_shape_encode_roundtrip() {
    let mut file = base_model();

    let sf = file.strings.get_or_intern("full.ets");
    let sc = file.strings.get_or_intern("source text");
    let param = file.strings.get_or_intern("p");
    let sig = file.strings.get_or_intern("sig");
    let lv_name = file.strings.get_or_intern("v");
    let lv_type = file.strings.get_or_intern("LType;");
    let lv_sig = file.strings.get_or_intern("LType;");

    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    let m = &mut cls.methods[0];
    m.debug = Some(MethodDebugInfo {
        source_file: Some(sf),
        source_code: Some(sc),
        line_table: vec![
            LineEntry { index: 0, line: 10 },
            LineEntry { index: 1, line: 14 },
        ],
        column_table: vec![
            ColumnEntry {
                index: 0,
                column: 3,
            },
            ColumnEntry {
                index: 1,
                column: 9,
            },
        ],
        local_vars: vec![LocalVarInfo {
            name: lv_name,
            type_name: lv_type,
            type_signature: lv_sig, // WITH signature: extended emit
            reg_number: 1,
            start: 0,
            end: 1,
        }],
        params: vec![ParamInfo {
            name: param,
            signature: sig,
        }],
    });

    let encoded = encode(&file).expect("encode");
    let file2 = decode(&encoded).expect("decode re-encoded");
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    let d2 = g2.methods[0]
        .debug
        .as_ref()
        .expect("debug info must round-trip");
    assert!(!d2.line_table.is_empty(), "line table must round-trip");
    assert_eq!(d2.column_table.len(), 2, "column table must round-trip");
    assert_eq!(d2.local_vars.len(), 1);
    assert_eq!(d2.params.len(), 1);
}

/// `relocate_code_id` accepts Class and Field entities (the two
/// `CodeEntity` arms no other test drives). The bridge registers the
/// dependency and defers the actual patch to finalize; no bytecode's
/// operand is ISA-typed as a class/field reference, so this drives the
/// registration arms only (a patched operand would decode as the
/// instruction's declared string/method kind).
#[test]
fn relocate_code_id_class_and_field_entities() {
    use abcd_isa::{Bytecode, EntityId, Imm};

    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let other = b.add_class("LOther;");
    let fld = b.class_add_field(cls, "fld", Type::I32, AccessFlags::PUBLIC);
    let proto = b.create_proto(Type::Tagged, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = abcd_isa::encode(&[
        Bytecode::Definefunc(Imm(0), placeholder, Imm(0)),
        Bytecode::LdaStr(placeholder),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let owner = b.class_add_method(cls, "caller", proto, AccessFlags::STATIC, &code, 0, 0);
    b.method_set_source_lang(owner, SourceLang::EcmaScript);
    b.relocate_code_id(owner, offsets[0], 0, CodeEntity::Class(other))
        .expect("class relocation");
    b.relocate_code_id(owner, offsets[1], 0, CodeEntity::Field(fld))
        .expect("field relocation");
}

/// `Builder::default()` smoke test (kept for `clippy::new_without_default`;
/// zero production callers).
#[test]
fn builder_default_smoke() {
    let mut b = Builder::default();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    b.class_add_method(cls, "f", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    let data = b.finalize().expect("finalize");
    decode(&data).expect("decode");
}

/// Direct Builder coverage for the param-annotation wrappers the model
/// encoder never calls (the fold contract stages everything through the
/// compile-time adder and seals once).
#[test]
fn param_type_annotation_wrappers() {
    let mut b = Builder::new();
    b.set_api(9, "");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[Type::Tagged]);
    let m = b.class_add_method(cls, "f", proto, AccessFlags::PUBLIC, &[0x65], 2, 1);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let p0 = b.method_add_param(m, Type::Tagged);

    let name = b.add_string("value");
    let ann = b.create_annotation_ex(
        cls,
        &[abcd_file::AnnotationElemDefEx {
            name,
            tag: b'7',
            value: abcd_file::AnnotationElemValue::Scalar(42),
        }],
    );
    // The type/runtime-type wrappers exist for ABI parity; the vendored
    // MethodParamItem snapshots the staged vector on seal regardless.
    b.method_param_add_type_annotation(m, p0, ann);
    b.method_param_add_runtime_type_annotation(m, p0, ann);
    b.method_seal_param_annotations(m, false);

    let data = b.finalize().expect("finalize");
    let file = decode(&data).expect("decode");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("f"))
        .expect("method f")
        .1;
    let has_42 = m
        .param_annotations
        .compile_time
        .iter()
        .chain(m.param_annotations.runtime.iter())
        .flat_map(|v| v.iter())
        .flat_map(|a: &Annotation| a.elements.iter())
        .any(|e: &AnnotationElem| e.value == AnnotationValue::U32(42));
    assert!(has_42, "the staged param annotation must decode");
}

/// N73: a body carrying a lowered IC-slot consumption (`ic_size`) re-syncs
/// the `_ESSlotNumberAnnotation`/`SlotNumber` element on encode (the runtime
/// sizes `ProfileTypeInfo` from it and indexes it without bounds checks).
#[test]
fn slot_number_annotation_syncs_to_lowered_ic_size() {
    let mut file = base_model();

    let ann_cls = file.strings.get_or_intern("L_ESSlotNumberAnnotation;");
    let elem_name = file.strings.get_or_intern("SlotNumber");
    let other_cls = file.strings.get_or_intern("LOther;");
    let other_elem = file.strings.get_or_intern("value");

    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    let m = &mut cls.methods[0];
    // The slot-number annotation with a STALE count, plus an unrelated
    // annotation that must pass through untouched.
    m.annotations.compile_time.push(Annotation {
        class_descriptor: ann_cls,
        elements: vec![AnnotationElem {
            name: elem_name,
            value: AnnotationValue::U32(319),
        }],
    });
    m.annotations.compile_time.push(Annotation {
        class_descriptor: other_cls,
        elements: vec![AnnotationElem {
            name: other_elem,
            value: AnnotationValue::U32(77),
        }],
    });
    m.body.as_mut().expect("body").ic_size = Some(325);

    let encoded = encode(&file).expect("encode");
    let file2 = decode(&encoded).expect("decode re-encoded");
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    let m2 = &g2.methods[0];

    let mut slot = None;
    let mut other = None;
    for ann in &m2.annotations.compile_time {
        for e in &ann.elements {
            match file2.strings.resolve(e.name) {
                Some("SlotNumber") => slot = Some(e.value.clone()),
                _ => other = Some(e.value.clone()),
            }
        }
    }
    assert_eq!(
        slot,
        Some(AnnotationValue::U32(325)),
        "SlotNumber must be re-synced to the lowered IC consumption"
    );
    assert_eq!(
        other,
        Some(AnnotationValue::U32(77)),
        "unrelated annotations must pass through untouched"
    );
}
