//! Coverage for the metadata half of the v0.2 lift
//! (abcd-lift/src/metadata.rs): the TS/ArkTS-shaped inputs ets2panda
//! produces but es2abc (the whole 5517-fixture corpus) never does —
//! modifier flags (PRIVATE/PROTECTED/FINAL/ENUM), TypeScript/ArkTs
//! source languages, typed protos, I64/F32/F64 field initial values,
//! the full annotation element-kind matrix, external (body-less)
//! methods, and the debug-record edge guards — plus the hand-built
//! error paths (dangling descriptors/names, MalformedModuleData).
//!
//! Two construction styles, per shape:
//! - **Builder round-trip** (encode → decode → lift) for shapes the
//!   vendored writer/reader pair round-trips (probe-verified:
//!   class flags, source langs, api-9 typed protos, field values, the
//!   annotation matrix, function kinds except CONSTRUCTOR).
//! - **Struct-literal models** (the lift_unit.rs precedent) for shapes
//!   the Builder cannot express: dangling ids, body-less external
//!   methods, the CONSTRUCTOR access flag (the Builder drops it),
//!   empty debug records, TypeSummaryOffset fields.

use std::collections::HashMap;

use abcd_file::{
    AccessFlags, AnnotationElemDefEx, AnnotationElemValue, Builder, FieldValue, FileType,
    FunctionKind as FileFunctionKind, MethodDebugInfo, SourceLang as FileSourceLang, Type, Version,
    decode,
};
use abcd_ir::{AnnValue, Const, FunctionKind, Modifiers, SourceLang, StaticTy, Ty};
use abcd_isa::{Bytecode, encode as encode_bytecodes};
use abcd_lift::{LiftError, lift_file};

fn verify_clean(m: &abcd_ir::Module) {
    let report = abcd_ir::verify_module(m);
    assert!(
        report.errors.is_empty(),
        "verifier errors: {:?}",
        report.errors
    );
}

fn resolve(m: &abcd_ir::Module, s: abcd_ir::Sym) -> &str {
    m.sym.resolve(s).expect("dangling sym")
}

/// The class-table index of the class with the given descriptor.
fn class_id_of(m: &abcd_ir::Module, descriptor: &str) -> abcd_ir::ClassId {
    m.classes
        .iter()
        .position(|c| resolve(m, c.descriptor) == descriptor)
        .map(|i| abcd_ir::ClassId::new(i as u32))
        .expect("class present")
}

// ── modifiers(): PRIVATE / PROTECTED / FINAL / ENUM ──────────────────

#[test]
fn class_modifiers_map_all_flag_bits() {
    // metadata.rs:45,48,54,63 — es2abc-JS classes never carry these
    // JVM-legacy bits; ets2panda does.
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_class("LFlags;");
    b.class_set_access_flags(
        cls,
        AccessFlags::PUBLIC
            | AccessFlags::PRIVATE
            | AccessFlags::PROTECTED
            | AccessFlags::FINAL
            | AccessFlags::ENUM,
    );
    let g = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
    b.class_add_method(g, "f", proto, AccessFlags::STATIC, &code, 0, 0);
    let file = decode(&b.finalize().unwrap()).unwrap();

    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let mods = &m.classes[class_id_of(&m, "LFlags;").index()].modifiers;
    assert!(mods.contains(Modifiers::PUBLIC));
    assert!(mods.contains(Modifiers::PRIVATE));
    assert!(mods.contains(Modifiers::PROTECTED));
    assert!(mods.contains(Modifiers::FINAL));
    assert!(mods.contains(Modifiers::ENUM));
    assert!(!mods.contains(Modifiers::STATIC), "not set → not mapped");
}

// ── source_lang(): TypeScript / ArkTs ────────────────────────────────

#[test]
fn source_lang_maps_typescript_and_arkts() {
    // metadata.rs:79-80 — every corpus file is '.language ECMAScript'.
    let mut b = Builder::new();
    b.set_api(12, "");
    let ts = b.add_class("LTs;");
    b.class_set_source_lang(ts, FileSourceLang::TypeScript);
    let ark = b.add_class("LArk;");
    b.class_set_source_lang(ark, FileSourceLang::ArkTs);
    let g = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
    b.class_add_method(g, "f", proto, AccessFlags::STATIC, &code, 0, 0);
    let file = decode(&b.finalize().unwrap()).unwrap();

    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    assert_eq!(
        m.classes[class_id_of(&m, "LTs;").index()].source_lang,
        SourceLang::TypeScript
    );
    assert_eq!(
        m.classes[class_id_of(&m, "LArk;").index()].source_lang,
        SourceLang::ArkTS
    );
}

// ── function_kind(): CONSTRUCTOR flag + AsyncNcFunction ──────────────

/// A minimal struct-literal model: one class with the given methods.
/// The pool is the CALLER's — method/field names were interned in it.
fn model_with_methods(
    mut strings: abcd_file::StringPool,
    methods: Vec<abcd_file::Method>,
) -> abcd_file::File {
    let desc = strings.get_or_intern("LModel;");
    let class = abcd_file::Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods,
        fields: Vec::new(),
        annotations: Default::default(),
    };
    abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(desc, class)].into_iter().collect(),
        literal_arrays: Vec::new(),
        entity_map: Default::default(),
        literal_array_offsets: Default::default(),
        literal_array_header_offsets: Vec::new(),
        string_raw_bytes: Default::default(),
    }
}

/// A plain method with a `returnundefined` body.
fn model_method(
    strings: &mut abcd_file::StringPool,
    name: &str,
    flags: AccessFlags,
    kind: FileFunctionKind,
) -> abcd_file::Method {
    abcd_file::Method {
        name: strings.get_or_intern(name),
        offset: 0,
        access_flags: flags,
        function_kind: kind,
        source_lang: FileSourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(abcd_file::MethodBody {
            num_vregs: 0,
            num_args: 0,
            bytecodes: vec![Bytecode::Returnundefined],
            entity_offsets: HashMap::new(),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    }
}

#[test]
fn constructor_access_flag_selects_constructor_kind() {
    // metadata.rs:93-94. The Builder drops the CONSTRUCTOR access flag
    // (probe-verified — lift_unit.rs:643-645 documents this), so the
    // shape is a struct-literal model.
    let mut strings = abcd_file::StringPool::default();
    let ctor = model_method(
        &mut strings,
        "ctor",
        AccessFlags::PUBLIC | AccessFlags::CONSTRUCTOR,
        FileFunctionKind::None,
    );
    let plain = model_method(
        &mut strings,
        "plain",
        AccessFlags::PUBLIC,
        FileFunctionKind::None,
    );
    let file = model_with_methods(strings, vec![ctor, plain]);
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let kind_of = |name: &str| {
        m.functions
            .iter()
            .find(|f| resolve(&m, f.name) == name)
            .map(|f| f.kind)
            .expect("function")
    };
    assert_eq!(kind_of("ctor"), FunctionKind::Constructor);
    assert_eq!(kind_of("plain"), FunctionKind::Function);
}

#[test]
fn async_nc_function_maps_to_async_arrow() {
    // metadata.rs:101 — the NC ("non-constructible") kinds are arrows.
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
    let m1 = b.class_add_method(cls, "anc", proto, AccessFlags::STATIC, &code, 0, 0);
    b.method_set_function_kind(m1, FileFunctionKind::AsyncNcFunction);
    let file = decode(&b.finalize().unwrap()).unwrap();

    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let f = m
        .functions
        .iter()
        .find(|f| resolve(&m, f.name) == "anc")
        .expect("function");
    assert_eq!(f.kind, FunctionKind::AsyncArrow);
}

// ── ty_of(): the typed-proto lattice (api 9 — 12+ carries no shorty) ─

#[test]
fn typed_proto_maps_every_static_type() {
    // metadata.rs:117-130 — typed protos come from ets2panda; es2abc
    // protos are any/void. Probe-verified: api-9 files round-trip
    // proto types (12.x does not — #A7).
    let mut b = Builder::new();
    b.set_api(9, "");
    let cls = b.add_global_class();
    let other = b.add_class("LOther;");
    let mut pool = abcd_file::StringPool::default();
    let ref_sid = pool.get_or_intern("LOther;");
    let proto = b.create_proto_ex(
        &Type::Reference(ref_sid),
        Some(other),
        &[
            Type::Reference(ref_sid),
            Type::I8,
            Type::I16,
            Type::U16,
            Type::I64,
            Type::U64,
            Type::F32,
            Type::F64,
        ],
        &[Some(other), None, None, None, None, None, None, None],
    );
    let (code, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
    b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 0, 8);
    let file = decode(&b.finalize().unwrap()).unwrap();

    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let other_cid = class_id_of(&m, "LOther;");
    let f = &m.functions[0];
    let sig = f.sig.as_ref().expect("api-9 proto carries a signature");
    assert_eq!(
        sig.return_ty,
        Some(Ty::Static(StaticTy::Reference(other_cid)))
    );
    assert_eq!(
        sig.param_tys,
        vec![
            Ty::Static(StaticTy::Reference(other_cid)),
            Ty::Static(StaticTy::I8),
            Ty::Static(StaticTy::I16),
            Ty::Static(StaticTy::U16),
            Ty::Static(StaticTy::I64),
            Ty::Static(StaticTy::U64),
            Ty::Static(StaticTy::F32),
            Ty::Static(StaticTy::F64),
        ]
    );
    // Entry params are typed from the same table (lib.rs:528-531).
    assert_eq!(f.params.len(), 8);
    assert_eq!(m.values[f.params[1].index()].ty, Ty::Static(StaticTy::I8));
}

#[test]
fn unresolvable_reference_type_degrades_to_any() {
    // metadata.rs:128-130 None arm: a Reference whose descriptor is not
    // even a pool string (hand-built) degrades to Ty::Any.
    let mut strings = abcd_file::StringPool::default();
    // A StringId from a DIFFERENT pool whose index is out of range here.
    let mut other_pool = abcd_file::StringPool::default();
    for i in 0..8 {
        other_pool.get_or_intern(format!("pad{i}"));
    }
    let dangling = other_pool.get_or_intern("LGhost;");
    let mut method = model_method(
        &mut strings,
        "f",
        AccessFlags::PUBLIC,
        FileFunctionKind::None,
    );
    method.arg_types = vec![Type::Reference(dangling)];
    let file = model_with_methods(strings, vec![method]);
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let sig = m.functions[0].sig.as_ref().expect("signature");
    assert_eq!(sig.param_tys, vec![Ty::Any], "dangling reference → Any");
}

// ── external_params(): body-less external (native) methods ───────────

#[test]
fn external_method_params_come_from_the_proto() {
    // metadata.rs:150-162 — called only for body-less external methods
    // (lib.rs:417). The Builder's add_foreign_method lands in the
    // foreign region and never surfaces as a class method at decode
    // (probe-verified), so the shape is a struct-literal model.
    let mut strings = abcd_file::StringPool::default();
    let mut method = model_method(
        &mut strings,
        "native",
        AccessFlags::PUBLIC,
        FileFunctionKind::None,
    );
    method.is_external = true;
    method.body = None;
    method.return_type = Some(Type::I32);
    method.arg_types = vec![Type::I8, Type::F64];
    let file = model_with_methods(strings, vec![method]);
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let f = &m.functions[0];
    assert!(f.is_external, "the external flag survives");
    assert_eq!(f.params.len(), 2, "one param per declared arg type");
    assert_eq!(m.values[f.params[0].index()].ty, Ty::Static(StaticTy::I8));
    assert_eq!(m.values[f.params[1].index()].ty, Ty::Static(StaticTy::F64));
    assert_eq!(
        m.values[f.params[0].index()].def,
        abcd_ir::ValueDef::Param(0)
    );
    let sig = f.sig.as_ref().expect("declared signature");
    assert_eq!(sig.return_ty, Some(Ty::Static(StaticTy::I32)));
    assert_eq!(
        sig.param_tys,
        vec![Ty::Static(StaticTy::I8), Ty::Static(StaticTy::F64)]
    );
}

// ── lift_field: I64/F32/F64 initial values + the no-value arm ────────

#[test]
fn field_initial_values_i64_f32_f64_and_none() {
    // metadata.rs:227-229,258 — es2abc-JS fields carry i32/string/none;
    // the I64/F32/F64 forms are ets2panda territory.
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_class("LF;");
    let fa = b.class_add_field(cls, "a", Type::I64, AccessFlags::PUBLIC);
    b.field_set_value_i64(fa, -7);
    let fb = b.class_add_field(cls, "b", Type::F32, AccessFlags::PUBLIC);
    b.field_set_value_f32(fb, 1.5);
    let fc = b.class_add_field(cls, "c", Type::F64, AccessFlags::PUBLIC);
    b.field_set_value_f64(fc, 2.5);
    let _fd = b.class_add_field(cls, "d", Type::I32, AccessFlags::PUBLIC); // no value
    let g = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
    b.class_add_method(g, "f", proto, AccessFlags::STATIC, &code, 0, 0);
    let file = decode(&b.finalize().unwrap()).unwrap();

    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let c = &m.classes[class_id_of(&m, "LF;").index()];
    let field = |name: &str| {
        c.fields
            .iter()
            .find(|f| resolve(&m, f.name) == name)
            .expect("field")
    };
    let init = |name: &str| {
        field(name)
            .initial_value
            .map(|cid| m.consts.get(cid).unwrap().clone())
    };
    assert_eq!(init("a"), Some(Const::number(-7.0)), "I64 → f64 const");
    assert_eq!(init("b"), Some(Const::number(1.5)), "F32 → f64 const");
    assert_eq!(init("c"), Some(Const::number(2.5)), "F64 → f64 const");
    assert_eq!(init("d"), None, "no initial value → None");
}

#[test]
fn type_summary_offset_field_yields_no_initial_value() {
    // metadata.rs:252-256: the nested-offset field model has no runtime
    // consumer; decode models it opaquely (encode hard-errors on it, so
    // only a hand-built model reaches the lift).
    let mut strings = abcd_file::StringPool::default();
    let field_name = strings.get_or_intern("typeSummaryOffset");
    let class = abcd_file::Class {
        descriptor: strings.get_or_intern("LModel;"),
        name: strings.get_or_intern("LModel;"),
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: vec![abcd_file::Field {
            name: field_name,
            offset: 0,
            field_type: Type::U32,
            access_flags: AccessFlags::PUBLIC,
            is_external: false,
            initial_value: Some(FieldValue::TypeSummaryOffset(0x40)),
            annotations: Default::default(),
        }],
        annotations: Default::default(),
    };
    let desc = class.descriptor;
    let file = abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(desc, class)].into_iter().collect(),
        literal_arrays: Vec::new(),
        entity_map: Default::default(),
        literal_array_offsets: Default::default(),
        literal_array_header_offsets: Vec::new(),
        string_raw_bytes: Default::default(),
    };
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let c = &m.classes[class_id_of(&m, "LModel;").index()];
    assert_eq!(
        c.fields[0].initial_value, None,
        "TypeSummaryOffset carries no liftable constant"
    );
}

// ── The annotation element matrix (Builder round-trip) ───────────────

#[test]
fn annotation_element_kinds_matrix() {
    // metadata.rs:311-393 (annotation_value) plus the Builder-expressible
    // half of :401-454 (annotation_value_as_const, reached through the
    // Array arm). Tags are the vendored AnnotationValueType bytes
    // (abcd-file-sys/src/lib.rs — C++ static_asserts pin them against
    // pandasm::Value).
    let mut b = Builder::new();
    b.set_api(12, "");
    let g = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
    let method = b.class_add_method(g, "m", proto, AccessFlags::STATIC, &code, 0, 0);
    let field = b.class_add_field(g, "fld", Type::I32, AccessFlags::PUBLIC);
    let ann_cls = b.add_class("LAnn;");
    let inner_cls = b.add_class("LInner;");
    let la = b.add_literal_array("annlit");
    b.literal_array_add_integer(la, 42);
    let inner_name = b.add_string("x");
    let inner = b.create_annotation_ex(
        inner_cls,
        &[AnnotationElemDefEx {
            name: inner_name,
            tag: b'7', // U32
            value: AnnotationElemValue::Scalar(3),
        }],
    );
    let mh = b.create_method_handle(4, method.as_raw()); // 4 = InvokeStatic
    let s_hello = b.add_string("hello");
    let s1 = b.add_string("s1");
    let s2 = b.add_string("s2");
    let mut elems: Vec<AnnotationElemDefEx> = Vec::new();
    {
        let mut push = |name: &str, tag: u8, value: AnnotationElemValue| {
            elems.push(AnnotationElemDefEx {
                name: b.add_string(name),
                tag,
                value,
            });
        };
        // Scalars (tags '1'..'9', 'A', 'B', 'I', '*').
        push("bool", b'1', AnnotationElemValue::Scalar(1));
        push("i8", b'2', AnnotationElemValue::Scalar(0xFB)); // -5 as i8
        push("u8", b'3', AnnotationElemValue::Scalar(200));
        push("i16", b'4', AnnotationElemValue::Scalar(0x8001)); // -32767
        push("u16", b'5', AnnotationElemValue::Scalar(60000));
        push("i32", b'6', AnnotationElemValue::Scalar((-16i32) as u32));
        push("u32", b'7', AnnotationElemValue::Scalar(77));
        push("void", b'I', AnnotationElemValue::Scalar(0));
        push("null", b'*', AnnotationElemValue::Scalar(0));
        push("i64", b'8', AnnotationElemValue::Scalar64(-5i64 as u64));
        push("u64", b'9', AnnotationElemValue::Scalar64(u64::MAX));
        push("f32", b'A', AnnotationElemValue::Scalar(2.5f32.to_bits()));
        push("f64", b'B', AnnotationElemValue::Scalar64(3.5f64.to_bits()));
        // Entity references (tags 'C', 'D', 'E', 'F', 'G', 'J', '#').
        push(
            "str",
            b'C',
            AnnotationElemValue::EntityRef(s_hello.as_raw()),
        );
        push(
            "record",
            b'D',
            AnnotationElemValue::EntityRef(inner_cls.as_raw()),
        );
        push(
            "method",
            b'E',
            AnnotationElemValue::EntityRef(method.as_raw()),
        );
        push("enum", b'F', AnnotationElemValue::EntityRef(field.as_raw()));
        push(
            "nested",
            b'G',
            AnnotationElemValue::EntityRef(inner.as_raw()),
        );
        push("mhandle", b'J', AnnotationElemValue::EntityRef(mh.as_raw()));
        push(
            "litarray",
            b'#',
            AnnotationElemValue::EntityRef(la.as_raw()),
        );
        // Scalar arrays (tags 'K'..'U').
        push("arrbool", b'K', AnnotationElemValue::Array(vec![1, 0]));
        push("arri8", b'L', AnnotationElemValue::Array(vec![0xF8])); // -8
        push("arru8", b'M', AnnotationElemValue::Array(vec![250]));
        push(
            "arri16",
            b'N',
            AnnotationElemValue::Array(vec![(-300i16) as u16 as u32]),
        );
        push("arru16", b'O', AnnotationElemValue::Array(vec![60000]));
        push(
            "arri32",
            b'P',
            AnnotationElemValue::Array(vec![(-70000i32) as u32]),
        );
        push("arru32", b'Q', AnnotationElemValue::Array(vec![7, 8]));
        push(
            "arrf32",
            b'T',
            AnnotationElemValue::Array(vec![6.25f32.to_bits()]),
        );
        // Entity arrays (tags 'V'..'Z', '@').
        push(
            "arrstr",
            b'V',
            AnnotationElemValue::EntityArray(vec![s1.as_raw(), s2.as_raw()]),
        );
        push(
            "arrrec",
            b'W',
            AnnotationElemValue::EntityArray(vec![inner_cls.as_raw()]),
        );
        push(
            "arrmeth",
            b'X',
            AnnotationElemValue::EntityArray(vec![method.as_raw()]),
        );
        push(
            "arrenum",
            b'Y',
            AnnotationElemValue::EntityArray(vec![field.as_raw()]),
        );
        push(
            "arrann",
            b'Z',
            AnnotationElemValue::EntityArray(vec![inner.as_raw()]),
        );
        push(
            "arrmh",
            b'@',
            AnnotationElemValue::EntityArray(vec![mh.as_raw()]),
        );
    }
    let ann = b.create_annotation_ex(ann_cls, &elems);
    b.class_add_annotation(g, ann);
    let file = decode(&b.finalize().unwrap()).unwrap();

    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let cid_global = class_id_of(&m, "L_GLOBAL;");
    let cid_inner = class_id_of(&m, "LInner;");
    let fid_m = abcd_ir::FuncId::new(
        m.functions
            .iter()
            .position(|f| resolve(&m, f.name) == "m")
            .expect("method m") as u32,
    );
    let fld_idx = m.classes[cid_global.index()]
        .fields
        .iter()
        .position(|f| resolve(&m, f.name) == "fld")
        .expect("field fld") as u32;
    let s_hello_sym = m.sym.intern("hello");
    let s1_sym = m.sym.intern("s1");
    let s2_sym = m.sym.intern("s2");
    let m_sym = m.sym.intern("m");
    let fld_sym = m.sym.intern("fld");
    let inner_desc_sym = m.sym.intern("LInner;");

    let class = &m.classes[cid_global.index()];
    assert_eq!(class.annotations.len(), 1, "one merged annotation");
    let ann0 = &class.annotations[0];
    let by_name: HashMap<&str, &AnnValue> = ann0
        .elements
        .iter()
        .map(|(n, v)| (resolve(&m, *n), v))
        .collect();
    let const_of = |v: &AnnValue| -> Const {
        let AnnValue::Const(c) = v else {
            panic!("expected AnnValue::Const, got {v:?}")
        };
        m.consts.get(*c).expect("const").clone()
    };

    // ── annotation_value scalar arms (metadata.rs:311-326) ──
    assert_eq!(const_of(by_name["bool"]), Const::Bool(true));
    assert_eq!(const_of(by_name["i8"]), Const::number(-5.0));
    assert_eq!(const_of(by_name["u8"]), Const::number(200.0));
    assert_eq!(const_of(by_name["i16"]), Const::number(-32767.0));
    assert_eq!(const_of(by_name["u16"]), Const::number(60000.0));
    assert_eq!(const_of(by_name["i32"]), Const::number(-16.0));
    assert_eq!(const_of(by_name["u32"]), Const::number(77.0));
    assert_eq!(const_of(by_name["i64"]), Const::number(-5.0));
    assert_eq!(const_of(by_name["u64"]), Const::number(u64::MAX as f64));
    assert_eq!(const_of(by_name["f32"]), Const::number(2.5));
    assert_eq!(const_of(by_name["f64"]), Const::number(3.5));
    assert_eq!(const_of(by_name["str"]), Const::String(s_hello_sym));
    assert_eq!(const_of(by_name["void"]), Const::Undefined);
    assert_eq!(const_of(by_name["null"]), Const::Null);

    // ── identity-carrying arms (metadata.rs:329-380) ──
    assert_eq!(by_name["record"], &AnnValue::Class(cid_inner));
    assert_eq!(
        const_of(by_name["method"]),
        Const::MethodRef(fid_m),
        "method element → MethodRef constant"
    );
    assert_eq!(
        by_name["enum"],
        &AnnValue::Field(cid_global, abcd_ir::FieldId::new(fld_idx)),
        "enum element resolves to the class-table field"
    );
    assert_eq!(
        by_name["nested"],
        &AnnValue::Class(cid_inner),
        "nested annotation → its CLASS (registered taxonomy gap)"
    );
    assert_eq!(
        by_name["mhandle"],
        &AnnValue::Name(m_sym),
        "method handle keeps the entity name (registered gap)"
    );
    assert_eq!(
        const_of(by_name["litarray"]),
        Const::ArrayLiteral(vec![Const::number(42.0)]),
        "literal-array element → its const tree"
    );

    // ── the Array arm + annotation_value_as_const (metadata.rs:384-454)
    assert_eq!(
        const_of(by_name["arrbool"]),
        Const::ArrayLiteral(vec![Const::Bool(true), Const::Bool(false)])
    );
    assert_eq!(
        const_of(by_name["arri8"]),
        Const::ArrayLiteral(vec![Const::number(-8.0)])
    );
    assert_eq!(
        const_of(by_name["arru8"]),
        Const::ArrayLiteral(vec![Const::number(250.0)])
    );
    assert_eq!(
        const_of(by_name["arri16"]),
        Const::ArrayLiteral(vec![Const::number(-300.0)])
    );
    assert_eq!(
        const_of(by_name["arru16"]),
        Const::ArrayLiteral(vec![Const::number(60000.0)])
    );
    assert_eq!(
        const_of(by_name["arri32"]),
        Const::ArrayLiteral(vec![Const::number(-70000.0)])
    );
    assert_eq!(
        const_of(by_name["arru32"]),
        Const::ArrayLiteral(vec![Const::number(7.0), Const::number(8.0)])
    );
    assert_eq!(
        const_of(by_name["arrf32"]),
        Const::ArrayLiteral(vec![Const::number(6.25)])
    );
    assert_eq!(
        const_of(by_name["arrstr"]),
        Const::ArrayLiteral(vec![Const::String(s1_sym), Const::String(s2_sym)])
    );
    assert_eq!(
        const_of(by_name["arrrec"]),
        Const::ArrayLiteral(vec![Const::String(inner_desc_sym)]),
        "record array elements become descriptor strings (documented)"
    );
    assert_eq!(
        const_of(by_name["arrmeth"]),
        Const::ArrayLiteral(vec![Const::MethodRef(fid_m)]),
        "method array elements keep MethodRef identity"
    );
    assert_eq!(
        const_of(by_name["arrenum"]),
        Const::ArrayLiteral(vec![Const::String(fld_sym)]),
        "enum array elements become name strings (documented)"
    );
    assert_eq!(
        const_of(by_name["arrann"]),
        Const::ArrayLiteral(vec![Const::String(inner_desc_sym)]),
        "nested-annotation array elements become descriptor strings"
    );
    assert_eq!(
        const_of(by_name["arrmh"]),
        Const::ArrayLiteral(vec![Const::String(m_sym)]),
        "method-handle array elements become name strings"
    );
}

// ── annotation degrade arms (hand-built: dangling identities) ────────

/// A StringId that never resolves in the file pool: interned in a
/// FRESH pool after more entries than the file pool's FINAL length, so
/// its raw index is out of range there. Intern everything the file
/// needs BEFORE calling this.
fn dangling_sid(pool_len: usize) -> abcd_file::StringId {
    let mut other = abcd_file::StringPool::default();
    for i in 0..=pool_len {
        other.get_or_intern(format!("pad{i}"));
    }
    other.get_or_intern("ghost")
}

#[test]
fn annotation_degrade_arms_for_dangling_identities() {
    use abcd_file::{Annotation as FileAnnotation, AnnotationElem, AnnotationValue};
    // metadata.rs:331 (Record miss), :340-343 (Method miss → Name),
    // :349-352 (Enum miss → Name), :361 (nested Annotation miss),
    // :366-370 (MethodHandle → Name), :377 (LiteralArray element failure
    // → Null inside the array).
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LModel;");
    let ann_desc = strings.get_or_intern("LAnn;");
    let zz_m = strings.get_or_intern("zz_m");
    let zz_e = strings.get_or_intern("zz_e");
    let handlee = strings.get_or_intern("handlee");
    let n = |strings: &mut abcd_file::StringPool, name: &str| strings.get_or_intern(name);
    let (n_rec, n_meth, n_enum, n_ann, n_mh, n_lit, n_str) = (
        n(&mut strings, "rec_miss"),
        n(&mut strings, "meth_miss"),
        n(&mut strings, "enum_miss"),
        n(&mut strings, "ann_miss"),
        n(&mut strings, "mh"),
        n(&mut strings, "lit"),
        n(&mut strings, "str_miss"),
    );
    let ghost = dangling_sid(strings.len());
    let elements = vec![
        AnnotationElem {
            name: n_rec,
            value: AnnotationValue::Record(ghost),
        },
        AnnotationElem {
            name: n_str,
            value: AnnotationValue::String(ghost), // :326 — dangling → Null
        },
        AnnotationElem {
            name: n_meth,
            value: AnnotationValue::Method {
                name: zz_m,
                offset: 0x777,
            },
        },
        AnnotationElem {
            name: n_enum,
            value: AnnotationValue::Enum {
                name: zz_e,
                offset: 0x888,
            },
        },
        AnnotationElem {
            name: n_ann,
            value: AnnotationValue::Annotation(Box::new(FileAnnotation {
                class_descriptor: ghost,
                elements: Vec::new(),
            })),
        },
        AnnotationElem {
            name: n_mh,
            value: AnnotationValue::MethodHandle(abcd_file::ResolvedMethodHandle {
                handle_type: abcd_file::MethodHandleType::InvokeStatic,
                entity: handlee,
                entity_offset: 0x999,
            }),
        },
        AnnotationElem {
            name: n_lit,
            value: AnnotationValue::LiteralArray(vec![
                abcd_file::LiteralValue::Integer(5),
                abcd_file::LiteralValue::String(ghost),
            ]),
        },
    ];
    let class = abcd_file::Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: Vec::new(),
        annotations: abcd_file::Annotations {
            compile_time: vec![FileAnnotation {
                class_descriptor: ann_desc,
                elements,
            }],
            ..Default::default()
        },
    };
    let file = abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(desc, class)].into_iter().collect(),
        literal_arrays: Vec::new(),
        entity_map: Default::default(),
        literal_array_offsets: Default::default(),
        literal_array_header_offsets: Vec::new(),
        string_raw_bytes: Default::default(),
    };
    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let zz_m = m.sym.intern("zz_m");
    let zz_e = m.sym.intern("zz_e");
    let handlee = m.sym.intern("handlee");
    let ann0 = m.classes[class_id_of(&m, "LModel;").index()].annotations[0].clone();
    let by_name: HashMap<String, AnnValue> = ann0
        .elements
        .iter()
        .map(|(n, v)| (resolve(&m, *n).to_owned(), v.clone()))
        .collect();
    let const_of = |v: &AnnValue| -> Const {
        let AnnValue::Const(c) = v else {
            panic!("expected AnnValue::Const, got {v:?}")
        };
        m.consts.get(*c).expect("const").clone()
    };
    assert_eq!(
        const_of(&by_name["rec_miss"]),
        Const::Null,
        "unresolvable record descriptor degrades to null"
    );
    assert_eq!(
        const_of(&by_name["str_miss"]),
        Const::Null,
        "dangling string element degrades to null"
    );
    assert_eq!(
        by_name["meth_miss"],
        AnnValue::Name(zz_m),
        "unresolvable method degrades to its display name"
    );
    assert_eq!(
        by_name["enum_miss"],
        AnnValue::Name(zz_e),
        "unresolvable enum field degrades to its display name"
    );
    assert_eq!(
        const_of(&by_name["ann_miss"]),
        Const::Null,
        "nested annotation with dangling descriptor degrades to null"
    );
    assert_eq!(
        by_name["mh"],
        AnnValue::Name(handlee),
        "method handle keeps the entity name"
    );
    assert_eq!(
        const_of(&by_name["lit"]),
        Const::ArrayLiteral(vec![Const::number(5.0), Const::Null]),
        "failing literal-array elements degrade to null inside the array"
    );
}

#[test]
fn annotation_value_as_const_exotic_array_elements() {
    use abcd_file::{Annotation as FileAnnotation, AnnotationElem, AnnotationValue};
    // metadata.rs:401-454 — annotation_value_as_const is only reachable
    // through the Array arm. The Builder cannot express 64-bit arrays
    // (Array(Vec<u32>) truncates) or arrays of void/literal-arrays
    // (not representable upstream), so these go through a hand-built
    // Array element.
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LModel;");
    let ann_desc = strings.get_or_intern("LAnn;");
    let zz_ok = strings.get_or_intern("zz_ok");
    let arr_name = strings.get_or_intern("arr");
    let ghost = dangling_sid(strings.len());
    let elements = vec![AnnotationElem {
        name: arr_name,
        value: AnnotationValue::Array {
            tag: b'H',
            values: vec![
                AnnotationValue::I64(-3),
                AnnotationValue::U64(9),
                AnnotationValue::F64(0.5),
                AnnotationValue::LiteralArray(vec![
                    abcd_file::LiteralValue::Integer(8),
                    abcd_file::LiteralValue::String(ghost), // :440 — Err → Null
                ]),
                AnnotationValue::Void,
                AnnotationValue::StringNullptr,
                AnnotationValue::Array {
                    tag: b'K',
                    values: vec![AnnotationValue::Bool(true)],
                },
                AnnotationValue::Method {
                    name: zz_ok,
                    offset: 0x777, // unresolvable → String(name)
                },
                AnnotationValue::Method {
                    name: ghost, // unresolvable AND dangling → Null
                    offset: 0x778,
                },
                AnnotationValue::Record(ghost), // dangling → Null
                AnnotationValue::Enum {
                    name: ghost, // dangling → Null
                    offset: 0x779,
                },
                AnnotationValue::MethodHandle(abcd_file::ResolvedMethodHandle {
                    handle_type: abcd_file::MethodHandleType::InvokeStatic,
                    entity: zz_ok, // → String("zz_ok")
                    entity_offset: 0x999,
                }),
                AnnotationValue::MethodHandle(abcd_file::ResolvedMethodHandle {
                    handle_type: abcd_file::MethodHandleType::InvokeStatic,
                    entity: ghost, // dangling → Null
                    entity_offset: 0x998,
                }),
                AnnotationValue::Annotation(Box::new(FileAnnotation {
                    class_descriptor: ann_desc, // → String("LAnn;")
                    elements: Vec::new(),
                })),
                AnnotationValue::Annotation(Box::new(FileAnnotation {
                    class_descriptor: ghost, // dangling → Null
                    elements: Vec::new(),
                })),
            ],
        },
    }];
    let class = abcd_file::Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: Vec::new(),
        annotations: abcd_file::Annotations {
            compile_time: vec![FileAnnotation {
                class_descriptor: ann_desc,
                elements,
            }],
            ..Default::default()
        },
    };
    let file = abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(desc, class)].into_iter().collect(),
        literal_arrays: Vec::new(),
        entity_map: Default::default(),
        literal_array_offsets: Default::default(),
        literal_array_header_offsets: Vec::new(),
        string_raw_bytes: Default::default(),
    };
    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let zz_ok_sym = m.sym.intern("zz_ok");
    let ann_desc_sym = m.sym.intern("LAnn;");
    let ann0 = m.classes[class_id_of(&m, "LModel;").index()].annotations[0].clone();
    let AnnValue::Const(arr_cid) = ann0.elements[0].1 else {
        panic!("expected Const, got {:?}", ann0.elements[0]);
    };
    assert_eq!(
        m.consts.get(arr_cid),
        Some(&Const::ArrayLiteral(vec![
            Const::number(-3.0), // I64
            Const::number(9.0),  // U64
            Const::number(0.5),  // F64
            // LiteralArray (one element fails → Null in place)
            Const::ArrayLiteral(vec![Const::number(8.0), Const::Null]),
            Const::Undefined,                             // Void
            Const::Null,                                  // StringNullptr
            Const::ArrayLiteral(vec![Const::Bool(true)]), // nested Array
            Const::String(zz_ok_sym),                     // Method miss, name ok
            Const::Null,                                  // Method miss, dangling name
            Const::Null,                                  // Record dangling
            Const::Null,                                  // Enum dangling name
            Const::String(zz_ok_sym),                     // MethodHandle, name ok
            Const::Null,                                  // MethodHandle dangling
            Const::String(ann_desc_sym),                  // nested Annotation, ok
            Const::Null,                                  // nested Annotation, dangling
        ])),
        "the full annotation_value_as_const matrix"
    );
}

#[test]
fn dangling_annotation_descriptor_and_element_name_are_skipped() {
    use abcd_file::{Annotation as FileAnnotation, AnnotationElem, AnnotationValue};
    // metadata.rs:277 (dangling class descriptor → the whole annotation
    // is skipped), :282 (dangling element name → the element is
    // skipped).
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LModel;");
    let ann_desc = strings.get_or_intern("LAnn;");
    let kept = strings.get_or_intern("kept");
    let ghost = dangling_sid(strings.len());
    let class = abcd_file::Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: Vec::new(),
        annotations: abcd_file::Annotations {
            compile_time: vec![
                FileAnnotation {
                    class_descriptor: ghost, // → skipped entirely
                    elements: Vec::new(),
                },
                FileAnnotation {
                    class_descriptor: ann_desc,
                    elements: vec![
                        AnnotationElem {
                            name: ghost, // → element skipped
                            value: AnnotationValue::U32(1),
                        },
                        AnnotationElem {
                            name: kept,
                            value: AnnotationValue::U32(2),
                        },
                    ],
                },
            ],
            ..Default::default()
        },
    };
    let file = abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(desc, class)].into_iter().collect(),
        literal_arrays: Vec::new(),
        entity_map: Default::default(),
        literal_array_offsets: Default::default(),
        literal_array_header_offsets: Vec::new(),
        string_raw_bytes: Default::default(),
    };
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let anns = &m.classes[class_id_of(&m, "LModel;").index()].annotations;
    assert_eq!(
        anns.len(),
        1,
        "the dangling-descriptor annotation is dropped"
    );
    assert_eq!(
        anns[0].elements.len(),
        1,
        "the dangling-name element is dropped"
    );
    assert_eq!(resolve(&m, anns[0].elements[0].0), "kept");
}

// ── lift_class identity-table errors (hand-built) ────────────────────

#[test]
fn class_descriptor_key_mismatch_is_an_unresolved_entity() {
    // metadata.rs:168: pass 1 keys class_to_id by the MAP key; a class
    // whose descriptor FIELD differs never resolves.
    let mut strings = abcd_file::StringPool::default();
    let key = strings.get_or_intern("LKey;");
    let other_desc = strings.get_or_intern("LOther;");
    let class = abcd_file::Class {
        descriptor: other_desc, // ≠ the map key
        name: other_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: Vec::new(),
        annotations: Default::default(),
    };
    let file = abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(key, class)].into_iter().collect(),
        literal_arrays: Vec::new(),
        entity_map: Default::default(),
        literal_array_offsets: Default::default(),
        literal_array_header_offsets: Vec::new(),
        string_raw_bytes: Default::default(),
    };
    let err = lift_file(&file).expect_err("descriptor/key mismatch");
    assert!(matches!(err, LiftError::UnresolvedEntity(0)), "got {err:?}");
}

#[test]
fn class_stubbed_by_super_reference_has_no_func_base() {
    // metadata.rs:171: a class whose descriptor was stub-appended via
    // class_of_descriptor (here: another class's super_class) is in
    // class_to_id but not in func_bases → UnresolvedEntity.
    let mut strings = abcd_file::StringPool::default();
    // Interning order fixes the BTreeMap iteration order: LA < LB.
    let desc_a = strings.get_or_intern("LA;");
    let shared = strings.get_or_intern("LShared;");
    let desc_b = strings.get_or_intern("LB;");
    let mk = |descriptor: abcd_file::StringId, super_class| abcd_file::Class {
        descriptor,
        name: descriptor,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: Vec::new(),
        annotations: Default::default(),
    };
    let class_a = mk(desc_a, Some(shared)); // stub-appends LShared; first
    let class_b = mk(shared, None); // keyed LB;, descriptor LShared;
    let file = abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(desc_a, class_a), (desc_b, class_b)].into_iter().collect(),
        literal_arrays: Vec::new(),
        entity_map: Default::default(),
        literal_array_offsets: Default::default(),
        literal_array_header_offsets: Vec::new(),
        string_raw_bytes: Default::default(),
    };
    let err = lift_file(&file).expect_err("stubbed class has no func base");
    assert!(matches!(err, LiftError::UnresolvedEntity(0)), "got {err:?}");
}

// ── Debug-record edge guards ─────────────────────────────────────────

#[test]
fn empty_debug_record_is_treated_as_no_debug_info() {
    // metadata.rs:467,471-475,487 (N55): a structurally-present but
    // contentless debug record (a degenerate line program) is dropped —
    // the function carries debug: None. The Builder path cannot produce
    // it (the vendored extractor always emits the initial row, and an
    // LNP that never SET_FILEs fails extraction outright — both
    // probe-verified), so this is a struct-literal model.
    let mut strings = abcd_file::StringPool::default();
    let mut method = model_method(
        &mut strings,
        "f",
        AccessFlags::PUBLIC,
        FileFunctionKind::None,
    );
    method.debug = Some(MethodDebugInfo {
        source_file: None, // :467 None arm
        source_code: None,
        line_table: Vec::new(),
        column_table: Vec::new(),
        local_vars: Vec::new(),
        params: Vec::new(),
    });
    let file = model_with_methods(strings, vec![method]);
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    assert!(
        m.functions[0].debug.is_none(),
        "an all-empty debug record is dropped (N55)"
    );

    // Variant: source_file present but EMPTY — same guard, :468 arm.
    let mut strings = abcd_file::StringPool::default();
    let mut method = model_method(
        &mut strings,
        "f",
        AccessFlags::PUBLIC,
        FileFunctionKind::None,
    );
    let empty = strings.get_or_intern("");
    method.debug = Some(MethodDebugInfo {
        source_file: Some(empty),
        source_code: None,
        line_table: Vec::new(),
        column_table: Vec::new(),
        local_vars: Vec::new(),
        params: Vec::new(),
    });
    let file = model_with_methods(strings, vec![method]);
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    assert!(
        m.functions[0].debug.is_none(),
        "an empty-string source file is not content"
    );
}

#[test]
fn debug_local_var_edge_ranges() {
    // metadata.rs:525 (dangling local name → skip), :541 (scope range
    // brackets no lifted instruction → None), :583 (empty type
    // signature → None).
    let mut strings = abcd_file::StringPool::default();
    let mut method = model_method(
        &mut strings,
        "f",
        AccessFlags::PUBLIC,
        FileFunctionKind::None,
    );
    let src = strings.get_or_intern("f.js");
    let empty_sig = strings.get_or_intern("");
    let i32_sig = strings.get_or_intern("i32");
    let nosig = strings.get_or_intern("nosig");
    let outofrange = strings.get_or_intern("outofrange");
    let ghost = dangling_sid(strings.len());
    method.debug = Some(MethodDebugInfo {
        source_file: Some(src),
        source_code: None,
        line_table: Vec::new(),
        column_table: Vec::new(),
        local_vars: vec![
            abcd_file::LocalVarInfo {
                name: ghost, // :525 — skipped
                type_name: i32_sig,
                type_signature: i32_sig,
                reg_number: 0,
                start: 0,
                end: 0,
            },
            abcd_file::LocalVarInfo {
                name: nosig,
                type_name: i32_sig,
                type_signature: empty_sig, // :583 — ty None
                reg_number: 0,
                start: 0,
                end: 0,
            },
            abcd_file::LocalVarInfo {
                name: outofrange,
                type_name: i32_sig,
                type_signature: i32_sig,
                reg_number: 0,
                start: 99, // :541 — no instruction at-or-after pc 99
                end: 100,
            },
        ],
        params: Vec::new(),
    });
    let file = model_with_methods(strings, vec![method]);
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let debug = m.functions[0].debug.as_ref().expect("debug present");
    let names: Vec<&str> = debug
        .local_names
        .iter()
        .map(|lv| resolve(&m, lv.name))
        .collect();
    assert_eq!(
        names,
        ["nosig", "outofrange"],
        "the dangling-name local is skipped"
    );
    assert_eq!(
        debug.local_names[0].ty, None,
        "empty type signature → no type"
    );
    assert!(
        debug.local_names[0].scope.is_some(),
        "in-range scope maps onto lifted instructions"
    );
    assert_eq!(
        debug.local_names[1].ty,
        Some(Ty::Static(StaticTy::I32)),
        "i32 descriptor parses"
    );
    assert_eq!(
        debug.local_names[1].scope, None,
        "a scope past the last instruction is None"
    );
}

// ── Module-record edge guards ────────────────────────────────────────

/// A file carrying one _ESModuleRecord class with the given module data.
fn module_record_file(md: abcd_file::ModuleData) -> abcd_file::File {
    let mut strings = abcd_file::StringPool::default();
    let rec_desc = strings.get_or_intern("L_ESModuleRecord;");
    let field_name = strings.get_or_intern("test.js");
    let class = abcd_file::Class {
        descriptor: rec_desc,
        name: rec_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: vec![abcd_file::Field {
            name: field_name,
            offset: 0,
            field_type: Type::U32,
            access_flags: AccessFlags::PUBLIC,
            is_external: false,
            initial_value: Some(FieldValue::ModuleData(md)),
            annotations: Default::default(),
        }],
        annotations: Default::default(),
    };
    abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(rec_desc, class)].into_iter().collect(),
        literal_arrays: Vec::new(),
        entity_map: Default::default(),
        literal_array_offsets: Default::default(),
        literal_array_header_offsets: Vec::new(),
        string_raw_bytes: Default::default(),
    }
}

#[test]
fn dangling_module_request_string_is_skipped() {
    // metadata.rs:600.
    let ghost = {
        let mut other = abcd_file::StringPool::default();
        for i in 0..8 {
            other.get_or_intern(format!("pad{i}"));
        }
        other.get_or_intern("ghost")
    };
    let file = module_record_file(abcd_file::ModuleData {
        source_offset: 0,
        requests: vec![ghost],
        records: Vec::new(),
    });
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    assert!(
        m.module_requests.is_empty(),
        "the dangling request sid is skipped"
    );
}

#[test]
fn out_of_range_module_request_idx_is_malformed() {
    // metadata.rs:622-625.
    let mut strings = abcd_file::StringPool::default();
    let dep = strings.get_or_intern("dep1");
    let local = strings.get_or_intern("local1");
    let imp = strings.get_or_intern("imp1");
    let rec_desc = strings.get_or_intern("L_ESModuleRecord;");
    let field_name = strings.get_or_intern("test.js");
    let class = abcd_file::Class {
        descriptor: rec_desc,
        name: rec_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: vec![abcd_file::Field {
            name: field_name,
            offset: 0,
            field_type: Type::U32,
            access_flags: AccessFlags::PUBLIC,
            is_external: false,
            initial_value: Some(FieldValue::ModuleData(abcd_file::ModuleData {
                source_offset: 0,
                requests: vec![dep],
                records: vec![abcd_file::ModuleRecord::RegularImport {
                    local_name: local,
                    import_name: imp,
                    module_request_idx: 7,
                }],
            })),
            annotations: Default::default(),
        }],
        annotations: Default::default(),
    };
    let file = abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(rec_desc, class)].into_iter().collect(),
        literal_arrays: Vec::new(),
        entity_map: Default::default(),
        literal_array_offsets: Default::default(),
        literal_array_header_offsets: Vec::new(),
        string_raw_bytes: Default::default(),
    };
    let err = lift_file(&file).expect_err("request idx 7 with one request");
    assert!(
        matches!(err, LiftError::MalformedModuleData { idx: 7, count: 1 }),
        "got {err:?}"
    );
}
