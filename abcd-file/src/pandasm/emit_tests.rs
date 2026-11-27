//! The no-panic rule: the emitter must render ANY File model, including
//! hand-built ones with dangling references (placeholders, never panic).
//!
//! The CI coverage job skips the asm corpus gates, so these tests also
//! carry the emitter's coverage: direct calls for the name/float
//! helpers, and synthetic File models for the emission arms no corpus
//! binary produces (external records/methods, module blobs, the ≤12
//! header-table fallback, …).
use super::*;
use crate::model::{Field, MethodBody, ModuleRequestPhase, ParamAnnotations};
use crate::types::AccessFlags;
use std::collections::BTreeMap;

fn empty_file() -> File {
    file_at(Version::new(12, 0, 6, 0))
}

fn file_at(version: Version) -> File {
    File {
        version,
        checksum: 0,
        size: 0,
        file_type: crate::FileType::Dynamic,
        strings: crate::StringPool::default(),
        classes: BTreeMap::new(),
        literal_arrays: Vec::new(),
        literal_array_header_offsets: Vec::new(),
    }
}

/// A minimal static method named `name`; `body` attaches a body.
fn bare_method(file: &mut File, name: &str, offset: u32, body: Option<MethodBody>) -> Method {
    Method {
        name: file.strings.get_or_intern(name),
        offset,
        access_flags: AccessFlags::STATIC,
        function_kind: crate::types::FunctionKind::None,
        source_lang: SourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body,
        annotations: crate::model::Annotations::default(),
        param_annotations: ParamAnnotations::default(),
        debug: None,
    }
}

fn body_of(bytecodes: Vec<Bytecode>) -> MethodBody {
    MethodBody {
        num_vregs: 0,
        num_args: 0,
        code: crate::MethodCode::Decoded(bytecodes),
        entities: crate::MethodEntities::new(),
        try_blocks: Vec::new(),
        ic_size: None,
    }
}

fn bare_field(
    file: &mut File,
    name: &str,
    field_type: Type,
    initial_value: Option<FieldValue>,
) -> Field {
    Field {
        name: file.strings.get_or_intern(name),
        offset: 0,
        field_type,
        access_flags: AccessFlags::empty(),
        is_external: false,
        initial_value,
        annotations: crate::model::Annotations::default(),
    }
}

fn add_class(
    file: &mut File,
    descriptor: &str,
    methods: Vec<Method>,
    fields: Vec<Field>,
) -> StringId {
    let sid = file.strings.get_or_intern(descriptor);
    file.classes.insert(
        sid,
        Class {
            descriptor: sid,
            name: sid,
            access_flags: AccessFlags::empty(),
            source_lang: SourceLang::EcmaScript,
            source_file: None,
            is_external: false,
            super_class: None,
            interfaces: Vec::new(),
            methods,
            fields,
            annotations: crate::model::Annotations::default(),
        },
    );
    sid
}

#[test]
fn empty_file_emits_sections() {
    let out = emit_file(&empty_file(), "empty.abc");
    let text = String::from_utf8(out).expect("empty file output is UTF-8");
    assert!(text.starts_with("# source binary: empty.abc\n\n# ====================\n# LITERALS\n"));
    assert!(text.contains("# RECORDS\n"));
    assert!(text.contains("# METHODS\n"));
    assert!(text.ends_with("# STRING\n\n"));
}

#[test]
fn dangling_references_render_placeholders() {
    let mut file = empty_file();
    let desc = file.strings.get_or_intern("L_GLOBAL;");
    let name = file.strings.get_or_intern("f");
    // A body whose entity references resolve to nothing.
    let mut body = MethodBody {
        num_vregs: 1,
        num_args: 0,
        code: crate::MethodCode::default(),
        entities: crate::MethodEntities::new(),
        try_blocks: Vec::new(),
        ic_size: None,
    };
    // Decode two real instructions via abcd-isa and add a dangling
    // entity offset by hand.
    let (bytes, _) = abcd_isa::encode(&[
        abcd_isa::insn::Ldai::new(abcd_isa::Imm(7)),
        abcd_isa::insn::Returnundefined::new(),
    ])
    .expect("encode smoke body");
    body.code = crate::MethodCode::Decoded(
        abcd_isa::decode(&bytes)
            .expect("decode smoke body")
            .into_iter()
            .map(|(bc, _)| bc)
            .collect(),
    );
    let method = Method {
        name,
        offset: 0x100,
        access_flags: AccessFlags::STATIC,
        function_kind: crate::types::FunctionKind::None,
        source_lang: SourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(body),
        annotations: crate::model::Annotations::default(),
        param_annotations: ParamAnnotations::default(),
        debug: None,
    };
    file.classes.insert(
        desc,
        Class {
            descriptor: desc,
            name: desc,
            access_flags: AccessFlags::empty(),
            source_lang: SourceLang::EcmaScript,
            source_file: None,
            is_external: false,
            super_class: None,
            interfaces: Vec::new(),
            methods: vec![method],
            fields: Vec::new(),
            annotations: crate::model::Annotations::default(),
        },
    );
    let out = emit_file(&file, "dangling.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(text.contains(".function any f() <static> {"), "{text}");
    assert!(text.contains("\tldai 0x7\n"), "{text}");
}

// -- Float formatting (direct calls; the corpus never prints these) ----

#[test]
fn float_formatting_special_values() {
    // std::scientific, precision 6.
    assert_eq!(format_scientific6(f64::NAN), "nan");
    assert_eq!(format_scientific6(-f64::NAN), "-nan");
    assert_eq!(format_scientific6(f64::INFINITY), "inf");
    assert_eq!(format_scientific6(f64::NEG_INFINITY), "-inf");
    assert_eq!(format_scientific6(1.0), "1.000000e+00");
    assert_eq!(format_scientific6(0.1), "1.000000e-01");
    assert_eq!(format_scientific6(4294967296.0), "4.294967e+09");
    assert_eq!(format_scientific6(-2.5), "-2.500000e+00");
    // iostream default (%g, precision 6).
    assert_eq!(format_g6(f64::NAN), "nan");
    assert_eq!(format_g6(-f64::NAN), "-nan");
    assert_eq!(format_g6(f64::INFINITY), "inf");
    assert_eq!(format_g6(f64::NEG_INFINITY), "-inf");
    assert_eq!(format_g6(0.0), "0");
    assert_eq!(format_g6(-0.0), "-0");
    assert_eq!(format_g6(1.25), "1.25");
    assert_eq!(format_g6(2.5), "2.5");
    assert_eq!(format_g6(42.0), "42");
    assert_eq!(format_g6(-0.25), "-0.25");
    // Outside [-4, 6): the %e branch (trailing zeros stripped).
    assert_eq!(format_g6(0.00001), "1e-05");
    assert_eq!(format_g6(1234567.0), "1.23457e+06");
    assert_eq!(format_g6(123456789.0), "1.23457e+08");
}

#[test]
fn float_formatting_g6_integer_trailing_zeros() {
    // %g drops the trailing zeros of the FRACTION only; integer digits
    // are never stripped. Reference: C `printf("%g", ...)` prints
    // 100000|100000|123400|999999|1e+06 for the values below; upstream
    // prints via plain iostream defaultfloat (precision 6), the same
    // semantics (disassembler.cpp SerializeFieldValue et al.).
    assert_eq!(format_g6(100000.0), "100000");
    assert_eq!(format_g6(-100000.0), "-100000");
    assert_eq!(format_g6(100000.5), "100000"); // rounds to 6 significant digits
    assert_eq!(format_g6(123400.0), "123400");
    assert_eq!(format_g6(999999.0), "999999");
    // %g switches to %e once the post-rounding exponent reaches P = 6.
    assert_eq!(format_g6(1000000.0), "1e+06");
    assert_eq!(format_g6(999999.9), "1e+06");
}

// -- Name helpers (direct calls) ----------------------------------------

#[test]
fn record_pandasm_name_all_forms() {
    // Reference descriptors: strip the wrapper, `/` → `.`.
    assert_eq!(record_pandasm_name(b"Lfoo/Bar;"), b"foo.Bar");
    assert_eq!(record_pandasm_name(b"Lx;"), b"x");
    assert_eq!(record_pandasm_name(b"L;"), b";");
    // Array rank: strip `[`s, re-append `[]`s.
    assert_eq!(record_pandasm_name(b"[I"), b"i32[]");
    assert_eq!(record_pandasm_name(b"[[I"), b"i32[][]");
    assert_eq!(record_pandasm_name(b"[Lfoo/Bar;"), b"foo.Bar[]");
    // Primitive letters.
    let letters: &[(&[u8], &[u8])] = &[
        (b"Z", b"u1"),
        (b"B", b"i8"),
        (b"H", b"u8"),
        (b"S", b"i16"),
        (b"C", b"u16"),
        (b"I", b"i32"),
        (b"U", b"u32"),
        (b"F", b"f32"),
        (b"D", b"f64"),
        (b"J", b"i64"),
        (b"Q", b"u64"),
        (b"V", b"void"),
        (b"A", b"any"),
    ];
    for &(desc, name) in letters {
        assert_eq!(record_pandasm_name(desc), name, "descriptor {desc:?}");
    }
    // Anything else passes through (e.g. the synthesized global).
    assert_eq!(record_pandasm_name(b"_GLOBAL"), b"_GLOBAL");
}

#[test]
fn language_str_all_variants() {
    assert_eq!(language_str(SourceLang::EcmaScript), "ECMAScript");
    assert_eq!(language_str(SourceLang::JavaScript), "JavaScript");
    assert_eq!(language_str(SourceLang::TypeScript), "TypeScript");
    assert_eq!(language_str(SourceLang::ArkTs), "ArkTS");
    assert_eq!(language_str(SourceLang::PandaAssembly), "PandaAssembly");
}

#[test]
fn mutf8_bytes_forms() {
    assert_eq!(mutf8_bytes("ab"), b"ab");
    // Embedded NUL → C0 80.
    assert_eq!(mutf8_bytes("a\0b"), [b'a', 0xC0, 0x80, b'b']);
    // Astral characters → CESU-8 surrogate pairs.
    assert_eq!(
        mutf8_bytes("\u{1F600}"),
        [0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80]
    );
    // BMP Private Use Area characters (e.g. HarmonyOS IconFont code points)
    // are preserved verbatim without truncation.
    assert_eq!(mutf8_bytes("ok\u{E000}dead"), "ok\u{E000}dead".as_bytes());
}

#[test]
fn replace_once_first_occurrence_only() {
    let mut v = b"a.ctor b.ctor".to_vec();
    replace_once(&mut v, b".ctor", b"_ctor_");
    assert_eq!(v, b"a_ctor_ b.ctor");
    // Missing needle: no-op. Empty needle: no-op.
    replace_once(&mut v, b"missing", b"x");
    assert_eq!(v, b"a_ctor_ b.ctor");
    replace_once(&mut v, b"", b"x");
    assert_eq!(v, b"a_ctor_ b.ctor");
}

// -- Synthetic models: emission arms no corpus binary produces ----------

#[test]
fn external_method_reference_falls_back_to_bare_signature() {
    // A MethodId operand referencing an external method (not in any class):
    // the signature falls back to `<name>:()`.
    let mut file = file_at(DEFAULT_VERSION);
    let orphan = file.strings.get_or_intern("orphan");
    let mut entities = crate::MethodEntities::new();
    entities.insert(
        (EntityKind::MethodId, 0),
        EntityRef::ExternalMethod {
            name: orphan,
            source_offset: 0x500,
        },
    );
    let body = MethodBody {
        entities,
        ..body_of(vec![
            abcd_isa::insn::Definefunc::new(
                abcd_isa::Imm(0),
                abcd_isa::EntityId(0),
                abcd_isa::Imm(0),
            ),
            abcd_isa::insn::Returnundefined::new(),
        ])
    };
    let m = bare_method(&mut file, "f", 0x100, Some(body));
    add_class(&mut file, "L_GLOBAL;", vec![m], vec![]);
    let out = emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(
        text.contains("\tdefinefunc 0x0, orphan:(), 0x0\n"),
        "{text}"
    );
}

#[test]
fn array_records_are_system_types() {
    // A class whose pandasm name contains `[`: never printed as a
    // record, its methods get no owner prefix.
    let mut file = file_at(DEFAULT_VERSION);
    let body = body_of(vec![abcd_isa::insn::Returnundefined::new()]);
    let m = bare_method(&mut file, "f", 0x100, Some(body));
    add_class(&mut file, "[I", vec![m], vec![]);
    let out = emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(text.contains(".function any f() <static> {"), "{text}");
    assert!(!text.contains(".record i32[]"), "{text}");
}

#[test]
fn field_value_offset_forms_and_unprintable_types() {
    let mut file = file_at(Version::new(12, 0, 6, 0));
    let fields = vec![
        bare_field(&mut file, "plain", Type::U32, Some(FieldValue::I32(0x2a))),
        bare_field(
            &mut file,
            crate::TYPE_SUMMARY_OFFSET_FIELD,
            Type::U32,
            Some(FieldValue::LiteralArrayRef {
                index: LiteralArrayIdx(0),
                source_offset: Some(0x123),
            }),
        ),
        // A u32 field whose value is not an offset: nothing prints.
        bare_field(&mut file, "odd", Type::U32, Some(FieldValue::F64(1.0))),
        // A value on a type the emitter never prints values for.
        bare_field(&mut file, "wide", Type::I64, Some(FieldValue::I64(9))),
    ];
    add_class(&mut file, "LR;", vec![], fields);
    let out = emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    // Upstream prints the typeSummaryOffset value (it is only excluded
    // from module-literal classification).
    assert!(text.contains("\tu32 plain = 0x2a\n"), "{text}");
    assert!(text.contains("\tu32 typeSummaryOffset = 0x123\n"), "{text}");
    assert!(text.contains("\tu32 odd\n"), "{text}");
    assert!(text.contains("\ti64 wide\n"), "{text}");
    assert!(!text.contains("odd ="), "{text}");
    assert!(!text.contains("wide ="), "{text}");
}

#[test]
fn header_less_12x_models_fall_back_to_decoded_order() {
    // Hand-built ≤12.0.6.0 model without the header table: regular
    // arrays in decoded order, then module blobs, then scope-names
    // arrays.
    let mut file = file_at(Version::new(12, 0, 6, 0));
    file.literal_arrays
        .push(crate::LiteralArray::with_source_offset(
            0x10,
            vec![LiteralValue::Integer(7)],
        ));
    file.literal_arrays
        .push(crate::LiteralArray::with_source_offset(0x50, Vec::new()));
    let req = file.strings.get_or_intern("r");
    let md = ModuleData {
        source_offset: 0x100,
        requests: vec![req],
        records: vec![ModuleRecord::StarExport {
            module_request_idx: 0,
        }],
    };
    let module_field = bare_field(
        &mut file,
        "moduleRecordIdx",
        Type::U32,
        Some(FieldValue::ModuleData(md)),
    );
    add_class(&mut file, "L_ESModuleRecord;", vec![], vec![module_field]);
    let scope_field = bare_field(
        &mut file,
        "scopeNames",
        Type::U32,
        Some(FieldValue::LiteralArrayRef {
            index: LiteralArrayIdx(1),
            source_offset: Some(0x50),
        }),
    );
    add_class(
        &mut file,
        "L_ESScopeNamesRecord;",
        vec![],
        vec![scope_field],
    );
    let out = emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(text.contains("0 0x10 { 1 [ i32:7, ]}\n"), "{text}");
    assert!(
        text.contains(
            "1 0x100 { 1 [\n\tMODULE_REQUEST_ARRAY: {\n\t\t0 : r,\n\t};\n\tModuleTag: STAR_EXPORT, module_request: r;\n]}\n"
        ),
        "{text}"
    );
    assert!(text.contains("2 0x50 \n"), "scope-names array last: {text}");
}

#[test]
fn header_table_skips_phase_slots_and_dangling_arrays() {
    // Decoded ≤12.0.6.0 shape: the header table is present, phase blobs
    // occupy slots but never list, and a slot whose array never decoded
    // prints key-only.
    let mut file = file_at(Version::new(12, 0, 6, 0));
    file.literal_arrays
        .push(crate::LiteralArray::with_source_offset(
            0x10,
            vec![LiteralValue::Integer(7)],
        ));
    file.literal_array_header_offsets = vec![0x10, 0x200, 0x99];
    let phase_field = bare_field(
        &mut file,
        crate::MODULE_REQUEST_PHASE_FIELD,
        Type::U32,
        Some(FieldValue::ModuleRequestPhase(ModuleRequestPhase {
            source_offset: 0x200,
            flags: vec![0],
        })),
    );
    add_class(
        &mut file,
        "L_ModuleRequestPhaseRecord;",
        vec![],
        vec![phase_field],
    );
    let out = emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(text.contains("0 0x10 { 1 [ i32:7, ]}\n"), "{text}");
    assert!(!text.contains("1 0x200"), "phase slot excluded: {text}");
    assert!(
        text.contains("2 0x99 \n"),
        "dangling array prints key-only: {text}"
    );
}

#[test]
fn overflowing_try_and_catch_spans_do_not_panic_on_emit() {
    let mut file = file_at(DEFAULT_VERSION);
    let mut body = body_of(vec![abcd_isa::insn::Returnundefined::new()]);
    body.try_blocks.push(crate::TryBlock {
        start: 1,
        len: u32::MAX,
        catches: vec![crate::CatchBlock {
            type_class: None,
            handler: 1,
            len: u32::MAX,
        }],
    });
    let m = bare_method(&mut file, "f", 0x100, Some(body));
    add_class(&mut file, "L_GLOBAL;", vec![m], vec![]);
    let out = emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(!text.contains(".catchall"), "{text}");
}

#[test]
fn duplicate_signature_still_registers_string_operands_and_streams_identically() {
    let mut file = file_at(DEFAULT_VERSION);
    let s1 = file.strings.get_or_intern("kept_str");
    let s2 = file.strings.get_or_intern("dropped_dup_str");

    let mut e1 = crate::MethodEntities::new();
    e1.insert(
        (EntityKind::StringId, 0),
        EntityRef::string_with_offset(s1, 0x200),
    );
    let b1 = MethodBody {
        entities: e1,
        ..body_of(vec![
            abcd_isa::insn::LdaStr::new(abcd_isa::EntityId(0)),
            abcd_isa::insn::Returnundefined::new(),
        ])
    };
    let mut e2 = crate::MethodEntities::new();
    e2.insert(
        (EntityKind::StringId, 0),
        EntityRef::string_with_offset(s2, 0x300),
    );
    let b2 = MethodBody {
        entities: e2,
        ..body_of(vec![
            abcd_isa::insn::LdaStr::new(abcd_isa::EntityId(0)),
            abcd_isa::insn::Returnundefined::new(),
        ])
    };
    let m1 = bare_method(&mut file, "dup", 0x100, Some(b1));
    let m2 = bare_method(&mut file, "dup", 0x104, Some(b2));
    add_class(&mut file, "L_GLOBAL;", vec![m1, m2], vec![]);

    let expected = emit_file(&file, "dup.abc");
    let mut streamed = Vec::new();
    emit_file_to_writer(&file, "dup.abc", &mut streamed).expect("stream to vec");
    assert_eq!(streamed, expected);

    let text = String::from_utf8_lossy(&expected);
    assert!(
        text.contains("[offset:0x200, name_value:kept_str]\n"),
        "{text}"
    );
    assert!(
        text.contains("[offset:0x300, name_value:dropped_dup_str]\n"),
        "duplicate-signature method must still register its string operands: {text}"
    );
    assert!(text.contains("\tlda.str \"kept_str\"\n"), "{text}");
    assert!(
        !text.contains("\tlda.str \"dropped_dup_str\"\n"),
        "second duplicate-signature method body must not emit: {text}"
    );

    struct FailingWriter;
    impl io::Write for FailingWriter {
        fn write(&mut self, _buf: &[u8]) -> io::Result<usize> {
            Err(io::Error::new(io::ErrorKind::BrokenPipe, "pipe closed"))
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    let err = emit_file_to_writer(&file, "dup.abc", &mut FailingWriter)
        .expect_err("broken writer must propagate io::Error");
    assert_eq!(err.kind(), io::ErrorKind::BrokenPipe);
}

#[test]
fn sim_primes_match_libstdcpp_and_cover_u32_space() {
    assert_eq!(sim::PRIMES.len(), 256);
    assert_eq!(sim::PRIMES[0], 2);
    assert_eq!(*sim::PRIMES.last().unwrap(), 4_294_967_291);
    for pair in sim::PRIMES.windows(2) {
        assert!(pair[0] < pair[1], "primes must be strictly increasing");
    }
    for &p in sim::PRIMES {
        assert!(p >= 2);
        if p > 3 {
            assert_ne!(p % 2, 0, "{p} is divisible by 2");
            let mut d = 3u64;
            let limit = u64::from(p);
            while d * d <= limit {
                assert_ne!(limit % d, 0, "{p} is composite (divisible by {d})");
                d += 2;
            }
        }
    }

    let mut set = sim::U32Set::default();
    for v in 0..1_110u32 {
        set.insert(v);
    }
    assert_eq!(
        set.bucket_count(),
        2_357,
        "libstdc++ _Prime_rehash_policy selects 2357 buckets at 1110 items"
    );

    let mut large = sim::U32Set::default();
    for v in 0..25_000u32 {
        large.insert(v);
    }
    assert_eq!(
        large.bucket_count(),
        42_043,
        "U32Set must rehash through primes above the old 23,957 ceiling"
    );
    assert_eq!(large.iter().len(), 25_000);
}

#[test]
fn static_dialect_does_not_treat_version_as_dynamic_12x_header_table() {
    let mut static_file = file_at(Version::new(0, 1, 0, 7));
    static_file.file_type = crate::FileType::Static;
    static_file
        .literal_arrays
        .push(crate::LiteralArray::with_source_offset(
            0x10,
            vec![LiteralValue::Integer(42)],
        ));
    assert_eq!(static_file.dialect(), Some(crate::Dialect::Static));

    let out = emit_file(&static_file, "static.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(
        !text.contains("0 0x10"),
        "Static 0.1.0.7 must not fall into <=12.0.6.0 dynamic header literal table: {text}"
    );
}
