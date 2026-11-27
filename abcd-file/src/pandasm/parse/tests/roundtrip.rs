//! Positive pandasm construct coverage and byte-exact `.pa` / `.abc` round-trip tests.

use abcd_isa::EntityKind;

use super::super::*;
use super::{doc, one_function};
use crate::types::HasAccessFlags as _;
use crate::{
    AnnotationValue, EntityRef, FieldValue, LiteralArrayIdx, LiteralValue, ModuleRecord, Type,
};

// -- Positive batch: handwritten-only constructs ------------------------

#[test]
fn record_owned_ctor_cctor_and_language_variants() {
    let input = doc(
        b"",
        b".language JavaScript\n.record RJs {\n}\n.language ArkTS\n.record R {\n}\n",
        b".language ECMAScript\n.function any R.f() <static> {\n\treturnundefined\n}\n.language JavaScript\n.function any R._ctor_() <ctor> {\n\treturnundefined\n}\n.language TypeScript\n.function any R._cctor_() <static, cctor> {\n\treturnundefined\n}\n.language ArkTS\n.function any RJs.g() <static> {\n\treturnundefined\n}\n",
        b"",
    );
    let file = parse_file(&input).expect("record-owned functions parse");
    let r = file.class_by_str("LR;").expect("record R");
    let names: Vec<&str> = r
        .methods
        .iter()
        .filter_map(|m| file.strings.resolve(m.name))
        .collect();
    assert!(names.contains(&"f"), "{names:?}");
    assert!(names.contains(&".ctor"), "ctor demangled: {names:?}");
    assert!(names.contains(&".cctor"), "cctor demangled: {names:?}");
    let ctor = r
        .methods
        .iter()
        .find(|m| file.strings.resolve(m.name) == Some(".ctor"))
        .unwrap();
    assert_eq!(ctor.source_lang, SourceLang::JavaScript);
    assert!(!ctor.is_static());
    let rjs = file.class_by_str("LRJs;").expect("record RJs");
    assert_eq!(rjs.source_lang, SourceLang::JavaScript);
    let g = &rjs.methods[0];
    assert_eq!(g.source_lang, SourceLang::ArkTs);
    // Emit side: non-system owner prefix, ctor/cctor renames, language
    // lines for the four non-default languages.
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(
        text.contains(".language JavaScript\n.record RJs {\n}\n"),
        "{text}"
    );
    assert!(text.contains(".language ArkTS\n.record R {\n}\n"), "{text}");
    assert!(text.contains(".function any R.f() <static> {"), "{text}");
    assert!(
        text.contains(".function any R._ctor_(R a0) <ctor> {"),
        "{text}"
    );
    assert!(
        text.contains(".function any R._cctor_() <static, cctor> {"),
        "{text}"
    );
    assert!(
        text.contains(".language ArkTS\n.function any RJs.g() <static> {"),
        "{text}"
    );
    crate::encode(&file).expect("encodes");
}

#[test]
fn external_record_and_codeless_external_function() {
    // `.record … <external>` (corpus-absent) plus an `external` method
    // on a NORMAL record (the emitter prints only those: external
    // classes skip method processing entirely).
    let input = doc(
        b"",
        b".record Ext.Thing <external>\n.record R {\n}\n",
        b".language ECMAScript\n.function  R.decl() <static, external> {\n}\n",
        b"",
    );
    let file = parse_file(&input).expect("external record parses");
    let class = file.class_by_str("LExt/Thing;").expect("external class");
    assert!(class.is_external);
    assert!(class.fields.is_empty());
    let r = file.class_by_str("LR;").expect("record R");
    let m = &r.methods[0];
    assert!(m.is_external);
    assert!(m.is_static());
    assert!(m.body.is_none(), "code-less method has no body");
    // 24.x: code-less protos carry no types.
    assert_eq!(m.return_type, None);
    assert!(m.arg_types.is_empty());
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(text.contains(".record Ext.Thing <external>\n\n"), "{text}");
    assert!(
        text.contains(".language ECMAScript\n.function  R.decl() <static, external> {\n}\n"),
        "{text}"
    );
    crate::encode(&file).expect("encodes");
}

#[test]
fn codeless_function_at_12x() {
    let input = doc(
        b"",
        b"",
        b".language ECMAScript\n.function  f() <static> {\n}\n",
        b"",
    );
    let file = parse_file_with_version(&input, Version::new(12, 0, 6, 0)).expect("12.x parses");
    let global = file.class_by_str("L_GLOBAL;").expect("global class");
    assert_eq!(global.methods.len(), 1);
    assert!(global.methods[0].body.is_none());
    assert_eq!(global.methods[0].return_type, None);
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(text.contains(".function  f() <static> {\n}\n"), "{text}");
}

#[test]
fn field_types_values_and_references() {
    let input = doc(
        b"",
        b".record Types {\n\tvoid v0\n\tu1 b0\n\ti8 i8f\n\tu8 u8f\n\ti16 i16f\n\tu16 u16f\n\ti32 i32f\n\tu32 u32f\n\ti64 i64f\n\tu64 u64f\n\tf32 f32f\n\tf64 f64f\n\tany anyf\n\tFoo.Bar ref\n\ti32[] arri\n\tFoo.Bar[][] arrr\n\tu1[] pa1\n\ti8[] pa2\n\tu8[] pa3\n\ti16[] pa4\n\tu16[] pa5\n\tu32[] pa6\n\tf32[] pa7\n\tf64[] pa8\n\ti64[] pa9\n\tu64[] pa10\n\tvoid[] pa11\n\tu32 valued = 0x2a\n\tu8 small = 0xf\n\tu1 flag = 1\n\tf64 fval = 1.25\n\tu32 path/name = 0x0\n}\n",
        b"",
        b"",
    );
    let file = parse_file(&input).expect("field zoo parses");
    let class = file.class_by_str("LTypes;").expect("record Types");
    let by_name = |n: &str| {
        class
            .fields
            .iter()
            .find(|f| file.strings.resolve(f.name) == Some(n))
            .unwrap_or_else(|| panic!("field {n}"))
    };
    assert_eq!(by_name("v0").field_type, Type::Void);
    assert_eq!(by_name("b0").field_type, Type::Bool);
    assert_eq!(by_name("i8f").field_type, Type::I8);
    assert_eq!(by_name("u16f").field_type, Type::U16);
    assert_eq!(by_name("i64f").field_type, Type::I64);
    assert_eq!(by_name("anyf").field_type, Type::Tagged);
    // Field without a value: no initial_value.
    assert_eq!(by_name("i32f").initial_value, None);
    // Reference/array types intern the descriptor.
    match by_name("ref").field_type {
        Type::Reference(sid) => assert_eq!(file.strings.resolve(sid), Some("LFoo/Bar;")),
        other => panic!("ref type: {other:?}"),
    }
    match by_name("arrr").field_type {
        Type::Reference(sid) => assert_eq!(file.strings.resolve(sid), Some("[[LFoo/Bar;")),
        other => panic!("arrr type: {other:?}"),
    }
    match by_name("arri").field_type {
        Type::Reference(sid) => assert_eq!(file.strings.resolve(sid), Some("[I")),
        other => panic!("arri type: {other:?}"),
    }
    assert_eq!(by_name("valued").initial_value, Some(FieldValue::I32(0x2a)));
    assert_eq!(by_name("flag").initial_value, Some(FieldValue::I32(1)));
    assert_eq!(by_name("fval").initial_value, Some(FieldValue::F64(1.25)));
    // Emit side: type names (all type_pandasm_name arms), the f64 field
    // value via format_g6, basename-stripped field names.
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    for line in [
        "\tvoid v0\n",
        "\tu1 b0\n",
        "\ti8 i8f\n",
        "\tu8 u8f\n",
        "\ti16 i16f\n",
        "\tu16 u16f\n",
        "\ti32 i32f\n",
        "\tu32 u32f\n",
        "\ti64 i64f\n",
        "\tu64 u64f\n",
        "\tf32 f32f\n",
        "\tf64 f64f\n",
        "\tany anyf\n",
        "\tFoo.Bar ref\n",
        "\ti32[] arri\n",
        "\tFoo.Bar[][] arrr\n",
        "\tu1[] pa1\n",
        "\ti8[] pa2\n",
        "\tu8[] pa3\n",
        "\ti16[] pa4\n",
        "\tu16[] pa5\n",
        "\tu32[] pa6\n",
        "\tf32[] pa7\n",
        "\tf64[] pa8\n",
        "\ti64[] pa9\n",
        "\tu64[] pa10\n",
        "\tvoid[] pa11\n",
        "\tu32 valued = 0x2a\n",
        "\tu8 small = 0xf\n",
        "\tu1 flag = 1\n",
        "\tf64 fval = 1.25\n",
        "\tu32 name = 0x0\n",
    ] {
        assert!(text.contains(line), "missing {line:?} in {text}");
    }
    // (No encode: the vendored writer rejects `void`-typed fields.)
}

#[test]
fn annotations_all_value_tags() {
    let input = doc(
        b"",
        b"",
        b"LMyAnno:\n\tu32 num { 0x2a }\n\tu1 flag { 1 }\n\tf64 score { 2.5 }\n\tpanda.String text { \"hello\" }\nLOther:\n\tu32 x { 0x1 }\nLMyAnno:\n\tu32 second { 0x2 }\n.language ECMAScript\n.function any f() <static> {\n\treturnundefined\n}\n",
        b"",
    );
    let file = parse_file(&input).expect("annotations parse");
    let global = file.class_by_str("L_GLOBAL;").unwrap();
    let m = &global.methods[0];
    let anns = &m.annotations.compile_time;
    assert_eq!(anns.len(), 3, "three annotation blocks (dup name kept)");
    let first = &anns[0];
    assert_eq!(
        file.strings.resolve(first.class_descriptor),
        Some("LMyAnno;")
    );
    let vals: Vec<&AnnotationValue> = first.elements.iter().map(|e| &e.value).collect();
    assert_eq!(
        vals,
        [
            &AnnotationValue::U32(0x2a),
            &AnnotationValue::Bool(true),
            &AnnotationValue::F64(2.5),
            &AnnotationValue::String(file.strings.get("hello").unwrap()),
        ]
    );
    // Emit side: same-name annotations merge into the first block, one
    // element per line.
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(
        text.contains(
            "LMyAnno:\n\tu32 num { 0x2a }\n\tu1 flag { 1 }\n\tf64 score { 2.5 }\n\tpanda.String text { \"hello\" }\n\tu32 second { 0x2 }\n"
        ),
        "{text}"
    );
    assert!(text.contains("LOther:\n\tu32 x { 0x1 }\n"), "{text}");
    crate::encode(&file).expect("encodes");
}

#[test]
fn instruction_operand_kinds_mainline() {
    let input = doc(
        b"",
        b"",
        b".language ECMAScript\n.function any g(any a0) <static> {\n\treturnundefined\n}\n.language PandaAssembly\n.function any f(any a0, any a1) <static> {\n\tldai 0x7\n\tldai 7\n\tsta a0\n\tmov v0, a1\n\tfldai 1.5\n\tfldai 0x0\n\tfldai inf\n\tfldai -nan\n\tjmp l_end\nl_end:\n\tdefinefunc 0x0, g:(any), 0x0\n\tlda.str \"hello\"\n\treturnundefined\n}\n",
        b"",
    );
    let file = parse_file(&input).expect("operand kinds parse");
    let global = file.class_by_str("L_GLOBAL;").unwrap();
    let f = global
        .methods
        .iter()
        .find(|m| file.strings.resolve(m.name) == Some("f"))
        .unwrap();
    assert_eq!(f.source_lang, SourceLang::PandaAssembly);
    let body = f.body.as_ref().unwrap();
    assert_eq!(body.num_vregs, 1, "max v-index + 1");
    assert_eq!(body.num_args, 2);
    assert_eq!(body.bytecodes().len(), 12);
    // a-regs are shifted past the vregs.
    assert_eq!(
        body.bytecodes()[2].operands(),
        [abcd_isa::Operand::Reg(1)],
        "sta a0"
    );
    assert_eq!(
        body.bytecodes()[3].operands(),
        [abcd_isa::Operand::Reg(0), abcd_isa::Operand::Reg(2)],
        "mov v0, a1"
    );
    // The unlisted string was interned with `source_offset: None`.
    let hello = file.strings.get("hello").unwrap();
    assert!(
        body.entities
            .values()
            .any(|&e| e == EntityRef::string(hello))
    );
    // Emit side: hex immediates, scientific floats (inf/-nan included),
    // jump label naming, method signature rendering, STRING section.
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    for line in [
        "\tldai 0x7\n",
        "\tsta a0\n",
        "\tmov v0, a1\n",
        "\tfldai 1.500000e+00\n",
        "\tfldai 0.000000e+00\n",
        "\tfldai inf\n",
        "\tfldai -nan\n",
        "\tjmp jump_label_0\n",
        "jump_label_0:\n",
        "\tdefinefunc 0x0, g:(any), 0x0\n",
        "\tlda.str \"hello\"\n",
        "name_value:hello]",
    ] {
        assert!(text.contains(line), "missing {line:?} in {text}");
    }
    crate::encode(&file).expect("encodes");
}

#[test]
fn out_of_bounds_jump_prints_raw_decimal() {
    let input = doc(b"", b"", &one_function(b"\tjmp 5\n"), b"");
    let file = parse_file(&input).expect("decimal jump parses");
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    // The upstream OOB-jump quirk round-trips the raw decimal index.
    assert!(text.contains("\tjmp 5\n"), "{text}");
}

#[test]
fn jump_to_trailing_empty_label() {
    let input = doc(b"", b"", &one_function(b"\tnop\n\tjmp l_missing\n:\n"), b"");
    let file = parse_file(&input).expect("trailing-label jump parses");
    let global = file.class_by_str("L_GLOBAL;").unwrap();
    let body = global.methods[0].body.as_ref().unwrap();
    assert_eq!(body.bytecodes().len(), 2);
    assert_eq!(
        body.bytecodes()[1].operands(),
        [abcd_isa::Operand::Label(2)],
        "one past the last instruction"
    );
}

#[test]
fn typed_and_catchall_catches_share_a_try_range() {
    let input = doc(
        b"",
        b".record R {\n}\n",
        b".language ECMAScript\n.function any R.f() <static> {\nt0:\n\tnop\nh0:\n\treturnundefined\nt1:\nh1:\n\n.catch R, t0, t1, h0, h1\n.catchall t0, t1, h0\n}\n",
        b"",
    );
    let file = parse_file(&input).expect("typed catch parses");
    let r = file.class_by_str("LR;").unwrap();
    let body = r.methods[0].body.as_ref().unwrap();
    assert_eq!(body.try_blocks.len(), 1, "same range groups");
    let tb = &body.try_blocks[0];
    assert_eq!((tb.start, tb.len), (0, 2));
    assert_eq!(tb.catches.len(), 2, "second catch joins the range");
    assert_eq!(
        tb.catches[0]
            .type_class
            .and_then(|sid| file.strings.resolve(sid)),
        Some("LR;"),
        "typed catch record"
    );
    assert_eq!(tb.catches[1].type_class, None, "catchall");
    // Emit side: `.catch <record>, …` rendering and the trailing `:`
    // (the try end binds one past the last instruction).
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(
        text.contains(
            ".catch R, try_begin_label_0, try_end_label_0, handler_begin_label_0_0, try_end_label_0\n"
        ),
        "{text}"
    );
    assert!(
        text.contains(".catchall try_begin_label_0, try_end_label_0, handler_begin_label_0_0\n"),
        "{text}"
    );
    assert!(text.contains("\treturnundefined\n:\n"), "{text}");
    crate::encode(&file).expect("encodes");
}

#[test]
fn literals_all_tags_at_12x_round_trip() {
    let input = doc(
        b"0 0x10 { 12 [ u1:1, i8:5, i32:-7, f32:1.5, f64:2.5, string:\"lit\", ets_implements:\"Iface\", method:foo, generator_method:gen, accessor:2, null_value:0, method_affiliate:9, ]}\n1 0x20 { 3 [ getter:getf, setter:setf, async_generator_method:agen, ]}\n2 0x30 { 2 [ lit_index:2, builtin_type:3, ]}\n3 0x40 \n4 0x50 { 1 [ lit_offset:0x20, ]}\n",
        b"",
        b".language ECMAScript\n.function any foo() <static> {\n\treturnundefined\n}\n.language ECMAScript\n.function any gen() <static> {\n\treturnundefined\n}\n.language ECMAScript\n.function any getf() <static> {\n\treturnundefined\n}\n.language ECMAScript\n.function any setf() <static> {\n\treturnundefined\n}\n.language ECMAScript\n.function any agen() <static> {\n\treturnundefined\n}\n",
        b"",
    );
    let file =
        parse_file_with_version(&input, Version::new(12, 0, 6, 0)).expect("12.x literals parse");
    // Header table is rebuilt from the keys.
    assert_eq!(
        file.literal_array_header_offsets,
        [0x10, 0x20, 0x30, 0x40, 0x50]
    );
    let idx = |off: u32| file.literal_array_by_offset(off).unwrap().0.index();
    let values = &file.literal_arrays[idx(0x10)].values;
    assert_eq!(values[0], LiteralValue::Bool(true));
    assert_eq!(values[1], LiteralValue::Integer8(5));
    assert_eq!(values[2], LiteralValue::Integer(-7i32 as u32));
    assert_eq!(values[3], LiteralValue::Float(1.5));
    assert_eq!(values[4], LiteralValue::Double(2.5));
    assert!(matches!(values[5], LiteralValue::String(_)));
    assert!(matches!(values[6], LiteralValue::EtsImplements(_)));
    assert!(matches!(values[7], LiteralValue::Method(_)));
    assert!(matches!(values[8], LiteralValue::GeneratorMethod(_)));
    assert_eq!(values[9], LiteralValue::Accessor(2));
    assert_eq!(values[10], LiteralValue::NullValue(0));
    assert_eq!(values[11], LiteralValue::MethodAffiliate(9));
    let accessors = &file.literal_arrays[idx(0x20)].values;
    assert!(matches!(accessors[0], LiteralValue::Getter(_)));
    assert!(matches!(accessors[1], LiteralValue::Setter(_)));
    assert!(matches!(
        accessors[2],
        LiteralValue::AsyncGeneratorMethod(_)
    ));
    let misc = &file.literal_arrays[idx(0x30)].values;
    assert_eq!(
        misc[0],
        LiteralValue::LiteralBufferIndex(LiteralArrayIdx(2))
    );
    assert_eq!(misc[1], LiteralValue::BuiltinTypeIndex(3));
    // The empty value stays empty.
    assert!(file.literal_arrays[idx(0x40)].values.is_empty());
    // lit_offset rewires to the target's table index.
    assert_eq!(
        file.literal_arrays[idx(0x50)].values[0],
        LiteralValue::LiteralArray(LiteralArrayIdx(idx(0x20) as u32))
    );
    // Emit side: all the non-corpus item tags print (Integer8 is the
    // upstream-dropped TAGVALUE).
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    for frag in [
        "u1:1",
        "i32:-7",
        "f32:1.5",
        "f64:2.5",
        "string:\"lit\"",
        "ets_implements:\"Iface\"",
        "method:foo",
        "generator_method:gen",
        "getter:getf",
        "setter:setf",
        "async_generator_method:agen",
        "accessor:2",
        "null_value:0",
        "method_affiliate:9",
        "lit_index:2",
        "builtin_type:3",
        "lit_offset:0x20",
    ] {
        assert!(text.contains(frag), "missing {frag:?} in {text}");
    }
    assert!(!text.contains("i8:"), "TAGVALUE items are dropped: {text}");
    // The empty array prints as nothing after the key's trailing space.
    assert!(text.contains("3 0x40 \n"), "{text}");
    crate::encode(&file).expect("encodes");
}

#[test]
fn header_table_gap_fills_with_phase_offsets() {
    let input = doc(
        b"0 0x10 { 1 [ i32:1, ]}\n2 0x30 { 1 [ i32:2, ]}\n",
        b".record _ModuleRequestPhaseRecord {\n\tu32 moduleRequestPhaseIdx = 0x200\n}\n",
        b"",
        b"",
    );
    let file = parse_file_with_version(&input, Version::new(12, 0, 6, 0)).expect("12.x gap parse");
    assert_eq!(
        file.literal_array_header_offsets,
        [0x10, 0x200, 0x30],
        "the gap slot takes the phase-blob offset"
    );
    let phase = &file
        .class_by_str("L_ModuleRequestPhaseRecord;")
        .unwrap()
        .fields[0];
    assert!(matches!(
        phase.initial_value,
        Some(FieldValue::ModuleRequestPhase(_))
    ));
    // Emit side: the phase slot is excluded from the LITERALS listing
    // (the FIELD value itself prints, upstream-style).
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(text.contains("0 0x10 { 1 [ i32:1, ]}"), "{text}");
    assert!(text.contains("2 0x30 { 1 [ i32:2, ]}"), "{text}");
    assert!(!text.contains("1 0x200"), "phase slots never list: {text}");
    assert!(
        text.contains("\tu32 moduleRequestPhaseIdx = 0x200\n"),
        "{text}"
    );
    crate::encode(&file).expect("encodes");
}

#[test]
fn strings_multiline_4byte_lossy_and_duplicates() {
    // STRING entries: a duplicate content (two offsets), an empty
    // content, a raw 4-byte UTF-8 content, and two lone-surrogate raw
    // forms whose lossy identities collide.
    let mut strings = b"[offset:0x40, name_value:dup]\n[offset:0x50, name_value:dup]\n[offset:0x80, name_value:]\n".to_vec();
    strings.extend_from_slice(b"[offset:0x60, name_value:");
    strings.extend_from_slice(&[0xF0, 0x9F, 0x98, 0x80]); // U+1F600, raw 4-byte
    strings.extend_from_slice(b"]\n[offset:0x70, name_value:");
    strings.extend_from_slice(&[0xED, 0xA0, 0xBD]); // lone high surrogate U+D83D
    strings.extend_from_slice(b"]\n[offset:0x78, name_value:");
    strings.extend_from_slice(&[0xED, 0xA0, 0xBE]); // lone high surrogate U+D83E
    strings.extend_from_slice(b"]\n");
    let mut methods =
        b".language ECMAScript\n.function any f() <static> {\n\tlda.str \"dup\"\n\tlda.str \"\"\n\tlda.str \"".to_vec();
    methods.extend_from_slice(&[0xF0, 0x9F, 0x98, 0x80]);
    methods.extend_from_slice(b"\"\n\tlda.str \"");
    methods.extend_from_slice(&[0xED, 0xA0, 0xBD]);
    methods.extend_from_slice(b"\"\n\tlda.str \"");
    // Same lossy raw form again: the duplicate-intern path.
    methods.extend_from_slice(&[0xED, 0xA0, 0xBD]);
    methods.extend_from_slice(b"\"\n\tlda.str \"");
    methods.extend_from_slice(&[0xED, 0xA0, 0xBE]);
    methods.extend_from_slice(b"\"\n\treturnundefined\n}\n");
    let input = doc(b"", b"", &methods, &strings);
    let file = parse_file(&input).expect("exotic strings parse");
    // The 4-byte form decoded to the astral character.
    assert!(file.strings.get("\u{1F600}").is_some());
    // Both lone-surrogate raw forms are registered losslessly (#30).
    assert_eq!(file.strings.lossy_count(), 2);
    // Emit side: the raw bytes are re-emitted verbatim at their listed
    // offsets (the 4-byte form goes out as CESU-8, so anchor the
    // surrogate checks on their STRING entry headers).
    let out = crate::pandasm::emit_file(&file, "t.abc");
    for (off, raw) in [(0x70u8, [0xED, 0xA0, 0xBD]), (0x78, [0xED, 0xA0, 0xBE])] {
        let mut needle = format!("[offset:0x{off:x}, name_value:").into_bytes();
        needle.extend_from_slice(&raw);
        needle.push(b']');
        assert!(
            out.windows(needle.len()).any(|w| w == needle),
            "raw surrogate bytes preserved at {off:#x}"
        );
    }
    let dup = b"[offset:0x40, name_value:dup]";
    assert!(
        out.windows(dup.len()).any(|w| w == dup),
        "dup entry prints at its first listed offset"
    );
    crate::encode(&file).expect("encodes");
}

#[test]
fn module_blob_13x_collects_and_round_trips() {
    let input = doc(
        b"0 0x100 { 5 [\n\tMODULE_REQUEST_ARRAY: {\n\t\t0 : req_a,\n\t\t1 : req_b,\n\t};\n\tModuleTag: REGULAR_IMPORT, local_name: la, import_name: ia, module_request: req_a;\n\tModuleTag: NAMESPACE_IMPORT, local_name: ln, module_request: req_b;\n\tModuleTag: LOCAL_EXPORT, local_name: ll, export_name: el;\n\tModuleTag: INDIRECT_EXPORT, export_name: ei, import_name: ii, module_request: req_a;\n\tModuleTag: STAR_EXPORT, module_request: req_b;\n\n]}\n",
        b".record _ESModuleRecord {\n\tu32 moduleRecordIdx = 0x100\n}\n.record _ESScopeNamesRecord {\n\tu32 scopeNames = 0x10\n}\n.record _ModuleRequestPhaseRecord {\n\tu32 moduleRequestPhaseIdx = 0x200\n}\n.record Ext <external>\n",
        b"",
        b"",
    );
    let file = parse_file(&input).expect("module blob parses");
    let class = file.class_by_str("L_ESModuleRecord;").unwrap();
    let Some(FieldValue::ModuleData(md)) = &class.fields[0].initial_value else {
        panic!("module field carries ModuleData");
    };
    assert_eq!(md.source_offset, 0x100);
    assert_eq!(md.requests.len(), 2);
    assert_eq!(md.records.len(), 5);
    assert!(matches!(md.records[0], ModuleRecord::RegularImport { .. }));
    assert!(matches!(
        md.records[1],
        ModuleRecord::NamespaceImport { .. }
    ));
    assert!(matches!(md.records[2], ModuleRecord::LocalExport { .. }));
    assert!(matches!(md.records[3], ModuleRecord::IndirectExport { .. }));
    assert!(matches!(md.records[4], ModuleRecord::StarExport { .. }));
    // The scope-names field references a synthesized empty array.
    let scope = &file.class_by_str("L_ESScopeNamesRecord;").unwrap().fields[0];
    let Some(FieldValue::LiteralArrayRef {
        index,
        source_offset: Some(0x10),
    }) = scope.initial_value
    else {
        panic!(
            "expected LiteralArrayRef at 0x10, got {:?}",
            scope.initial_value
        );
    };
    assert!(file.literal_arrays[index.index()].values.is_empty());
    // Emit side (13.x/24.x collector): the module blob routes to the
    // module table via the field-driven classification.
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    for frag in [
        "MODULE_REQUEST_ARRAY: {",
        "\t\t0 : req_a,",
        "ModuleTag: REGULAR_IMPORT, local_name: la, import_name: ia, module_request: req_a;",
        "ModuleTag: NAMESPACE_IMPORT, local_name: ln, module_request: req_b;",
        "ModuleTag: LOCAL_EXPORT, local_name: ll, export_name: el;",
        "ModuleTag: INDIRECT_EXPORT, export_name: ei, import_name: ii, module_request: req_a;",
        "ModuleTag: STAR_EXPORT, module_request: req_b;",
        ".record Ext <external>",
    ] {
        assert!(text.contains(frag), "missing {frag:?} in {text}");
    }
    crate::encode(&file).expect("encodes");
}

#[test]
fn module_blob_leading_junk_is_tolerated() {
    // Handwritten tolerance: the section path requires the value to
    // START with `{`, but lines before the `{ N [` line are skipped.
    let input = doc(
        b"0 0x100 {}\n{ 0 [\n\tMODULE_REQUEST_ARRAY: {\n\t};\n]}\n",
        b"",
        b"",
        b"",
    );
    parse_file(&input).expect("leading junk before `{ N [` is skipped");
}

#[test]
fn inline_literals_synthetic_registration_and_empty_operand() {
    let input = doc(
        b"0 0x10 { 1 [ i32:1, ]}\n",
        b"",
        b".language ECMAScript\n.function any f() <static> {\n\tcreatearraywithbuffer 0x0, { 1 [ i32:1, ]}\n\tcreatearraywithbuffer 0x1, { 2 [ i32:9, string:\"s\", ]}\n\tcreatearraywithbuffer 0x2\n\treturnundefined\n}\n.language ECMAScript\n.function  f.codeless() <static> {\n}\n",
        b"",
    );
    let file = parse_file(&input).expect("inline literals parse");
    let global = file.class_by_str("L_GLOBAL;").unwrap();
    let f = &global.methods[0];
    let body = f.body.as_ref().unwrap();
    assert_eq!(body.bytecodes().len(), 4);
    // The listed text resolves to its printed offset; the other two get
    // synthetic offsets.
    let offsets: Vec<u32> = body
        .entities
        .values()
        .filter_map(|e| match e {
            EntityRef::LiteralArray(la_idx) => file.literal_arrays[la_idx.index()].source_offset,
            _ => None,
        })
        .collect();
    assert!(
        offsets.contains(&0x10),
        "listed literal offset: {offsets:?}"
    );
    assert!(
        offsets
            .iter()
            .filter(|&&o| o >= SYNTHETIC_OFFSET_BASE)
            .count()
            == 2
    );
    // The implicit empty operand parsed as an empty array.
    let synth: Vec<u32> = offsets
        .iter()
        .copied()
        .filter(|&o| o >= SYNTHETIC_OFFSET_BASE)
        .collect();
    let mut saw_empty = false;
    for off in synth {
        let (_, la) = file.literal_array_by_offset(off).unwrap();
        if la.values.is_empty() {
            saw_empty = true;
        }
    }
    assert!(saw_empty, "omitted literal operand = empty array");
    // Emit side (24.x collector): referenced arrays print.
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(text.contains("{ 1 [ i32:1, ]}"), "{text}");
    assert!(text.contains("{ 2 [ i32:9, string:\"s\", ]}"), "{text}");
    crate::encode(&file).expect("encodes");
}

#[test]
fn nested_literal_arrays_via_lit_offset() {
    let input = doc(
        b"0 0x10 { 1 [ lit_offset:0x20, ]}\n1 0x20 { 1 [ i32:7, ]}\n",
        b"",
        b".language ECMAScript\n.function any f() <static> {\n\tcreatearraywithbuffer 0x0, { 1 [ lit_offset:0x20, ]}\n\treturnundefined\n}\n",
        b"",
    );
    let file = parse_file(&input).expect("nested literals parse");
    // 24.x emit: the nested array is collected transitively.
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(text.contains("{ 1 [ lit_offset:0x20, ]}"), "{text}");
    assert!(text.contains("{ 1 [ i32:7, ]}"), "{text}");
    crate::encode(&file).expect("encodes");
}

#[test]
fn duplicate_signature_is_dropped_on_emit() {
    let input = doc(
        b"",
        b".record R {\n}\n",
        b".language ECMAScript\n.function any R.f() <static> {\n\tlda.str \"dupsig\"\n\treturnundefined\n}\n.language ECMAScript\n.function any R.f() <static> {\n\treturnundefined\n}\n",
        b"",
    );
    let file = parse_file(&input).expect("duplicate signatures parse");
    let r = file.class_by_str("LR;").unwrap();
    assert_eq!(r.methods.len(), 2, "the model keeps both");
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert_eq!(
        text.matches(".function any R.f() <static> {").count(),
        1,
        "the second same-signature function is dropped: {text}"
    );
}

#[test]
fn non_static_method_gains_this_param() {
    let input = doc(
        b"",
        b".record R {\n}\n",
        b".language ECMAScript\n.function any R.m(R a0) {\n\treturnundefined\n}\n",
        b"",
    );
    let file = parse_file(&input).expect("non-static method parses");
    let r = file.class_by_str("LR;").unwrap();
    let m = &r.methods[0];
    assert!(!m.is_static());
    let body = m.body.as_ref().unwrap();
    assert_eq!(body.num_args, 0, "the printed param is `this`");
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(text.contains(".function any R.m(R a0) {"), "{text}");
    crate::encode(&file).expect("encodes");
}

#[test]
fn non_ascii_method_names_and_signatures() {
    let mut methods = b".language ECMAScript\n.function any ".to_vec();
    methods.push(0xE9); // non-ASCII bare name
    methods.extend_from_slice(b"() <static> {\n\treturnundefined\n}\n.language ECMAScript\n.function any f() <static> {\n\tdefinefunc 0x0, ");
    methods.push(0xE9);
    methods.extend_from_slice(b":(), 0x0\n\tjmp ");
    methods.push(0xE9);
    methods.push(b'\n');
    methods.push(0xE9);
    methods.extend_from_slice(b":\n\treturnundefined\n}\n");
    let input = doc(b"", b"", &methods, b"");
    let file = parse_file(&input).expect("non-ASCII method ref parses");
    let global = file.class_by_str("L_GLOBAL;").unwrap();
    assert_eq!(global.methods.len(), 2);
    let f = global
        .methods
        .iter()
        .find(|m| file.strings.resolve(m.name) == Some("f"))
        .unwrap();
    let body = f.body.as_ref().unwrap();
    assert_eq!(body.bytecodes()[0].mnemonic(), "definefunc");
    // The non-ASCII bare label resolved to the final instruction index.
    assert_eq!(
        body.bytecodes()[1].operands(),
        [abcd_isa::Operand::Label(2)],
        "non-ASCII label"
    );
}

#[test]
fn blank_lines_are_tolerated_in_record_bodies() {
    let input = doc(b"", b".record R {\n\n\tu32 x = 0x1\n\n}\n", b"", b"");
    let file = parse_file(&input).expect("blank lines in records parse");
    let r = file.class_by_str("LR;").unwrap();
    assert_eq!(r.fields.len(), 1);
}

#[test]
fn parse_error_display_and_error_trait() {
    let err = parse_file(b"garbage").expect_err("garbage rejected");
    assert_eq!(
        format!("{err}"),
        "pandasm parse error at line 0: expected exactly four section banners (LITERALS/RECORDS/METHODS/STRING)"
    );
    assert_eq!(err.line, 0);
    // The std::error::Error impl is usable as a trait object.
    let _: &dyn std::error::Error = &err;
}

#[test]
fn catch_may_target_the_trailing_empty_label() {
    // A catch label absent from the label table but covered by the
    // trailing `:` quirk binds one past the last instruction.
    let input = doc(
        b"",
        b"",
        b".language ECMAScript\n.function any f() <static> {\n\tnop\nl1:\nh:\n:\n.catchall l1, missing_end, h\n}\n",
        b"",
    );
    let file = parse_file(&input).expect("trailing-label catch parses");
    let global = file.class_by_str("L_GLOBAL;").unwrap();
    let body = global.methods[0].body.as_ref().unwrap();
    assert_eq!(body.try_blocks.len(), 1);
    let tb = &body.try_blocks[0];
    assert_eq!((tb.start, tb.len), (1, 0), "try end = insn_count");
    assert_eq!((tb.catches[0].handler, tb.catches[0].len), (1, 0));
}

#[test]
fn module_field_without_a_printed_blob_builds_empty() {
    // 13.x/24.x handwritten shape: the module blob offset the field
    // names was never printed, so the model gets an empty blob.
    let input = doc(
        b"",
        b".record _ESModuleRecord {\n\tu32 moduleRecordIdx = 0x999\n}\n",
        b"",
        b"",
    );
    let file = parse_file(&input).expect("blob-less module field parses");
    let class = file.class_by_str("L_ESModuleRecord;").unwrap();
    let Some(FieldValue::ModuleData(md)) = &class.fields[0].initial_value else {
        panic!("module field carries ModuleData");
    };
    assert_eq!(md.source_offset, 0x999);
    assert!(md.requests.is_empty());
    assert!(md.records.is_empty());
    // Emit side (24.x): the empty blob routes to the module table.
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(
        text.contains("0 0x999 { 0 [\n\tMODULE_REQUEST_ARRAY: {\n\t};\n]}\n"),
        "{text}"
    );
}

#[test]
fn module_blob_via_the_12x_header_table() {
    let input = doc(
        b"0 0x100 { 1 [\n\tMODULE_REQUEST_ARRAY: {\n\t\t0 : r,\n\t};\n\tModuleTag: STAR_EXPORT, module_request: r;\n]}\n",
        b".record _ESModuleRecord {\n\tu32 moduleRecordIdx = 0x100\n}\n",
        b"",
        b"",
    );
    let file = parse_file_with_version(&input, Version::new(12, 0, 6, 0))
        .expect("12.x module blob parses");
    assert_eq!(file.literal_array_header_offsets, [0x100]);
    // Emit side: the header-table walk routes the offset to the module
    // table (module_data_at hit).
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert!(
        text.contains("0 0x100 { 1 [\n\tMODULE_REQUEST_ARRAY: {\n\t\t0 : r,\n\t};\n\tModuleTag: STAR_EXPORT, module_request: r;\n]}\n"),
        "{text}"
    );
    crate::encode(&file).expect("encodes");
}

#[test]
fn multiline_literal_string_via_the_oracle() {
    // A literal-array string spanning physical lines whose content the
    // STRING section lists: the completeness scan closes it via the
    // oracle (not the same-line fallback).
    let input = doc(
        b"0 0x10 { 1 [ string:\"x\ny\", ]}\n",
        b"",
        b"",
        b"[offset:0x40, name_value:x\ny]",
    );
    let file = parse_file(&input).expect("multi-line literal string parses");
    let (_, la) = file.literal_array_by_offset(0x10).unwrap();
    let expected = file.strings.get("x\ny").unwrap();
    assert_eq!(la.values, [LiteralValue::String(expected)]);
}

#[test]
fn same_content_arrays_distribute_round_robin() {
    // Fourteen identical literal arrays: the build rank-orders the
    // same-content group by printed index, references bind round-robin,
    // and the 13.x collector's unordered_set simulation rehashes.
    let offsets: [u32; 14] = [
        0x10, 0x1d, 0x2d, 0x24, 0x28, 0x2c, 0x30, 0x34, 0x38, 0x3c, 0x40, 0x44, 0x48, 0x4c,
    ];
    let mut literals = Vec::new();
    for (i, off) in offsets.iter().enumerate() {
        literals.extend_from_slice(format!("{i} 0x{off:x} {{ 1 [ i32:0, ]}}\n").as_bytes());
    }
    let mut methods = b".language ECMAScript\n.function any f() <static> {\n".to_vec();
    for i in 0..14u8 {
        methods.extend_from_slice(
            format!("\tcreatearraywithbuffer 0x{i:x}, {{ 1 [ i32:0, ]}}\n").as_bytes(),
        );
    }
    methods.extend_from_slice(b"\treturnundefined\n}\n");
    let input = doc(&literals, b"", &methods, b"");
    let file = parse_file(&input).expect("same-content arrays parse");
    let global = file.class_by_str("L_GLOBAL;").unwrap();
    let body = global.methods[0].body.as_ref().unwrap();
    // Every printed offset is referenced exactly once, in rank order.
    let got: Vec<u32> = (0..14u32)
        .map(
            |id| match body.entities[&(EntityKind::LiteralarrayId, id)] {
                EntityRef::LiteralArray(la_idx) => {
                    file.literal_arrays[la_idx.index()].source_offset.unwrap()
                }
                other => panic!("expected EntityRef::LiteralArray, got {other:?}"),
            },
        )
        .collect();
    assert_eq!(got, offsets, "rank order = printed index order");
    // Emit side: all fourteen collect (rehash + same-bucket inserts) —
    // once each in the LITERALS listing and once per inline operand.
    let out = crate::pandasm::emit_file(&file, "t.abc");
    let text = String::from_utf8_lossy(&out);
    assert_eq!(text.matches("{ 1 [ i32:0, ]}").count(), 28, "{text}");
    crate::encode(&file).expect("encodes");
}

#[test]
fn multiline_operand_prefers_the_longest_oracle_match() {
    // Oracle: "ab" and "ab\"\nq". The one-line reading already parses,
    // but the tail after the close quote is still an oracle prefix, so
    // the lookahead extends and the two-line reading wins on matched
    // string bytes.
    let input = doc(
        b"",
        b"",
        b".language ECMAScript\n.function any f() <static> {\n\tlda.str \"ab\"\nq\"\n\treturnundefined\n}\n",
        b"[offset:0x40, name_value:ab]\n[offset:0x50, name_value:ab\"\nq]",
    );
    let file = parse_file(&input).expect("longest match parses");
    let global = file.class_by_str("L_GLOBAL;").unwrap();
    let body = global.methods[0].body.as_ref().unwrap();
    assert_eq!(body.bytecodes().len(), 2, "the insn spans two lines");
    // The operand is the two-line string at its listed offset.
    let sid = file
        .strings
        .get("ab\"\nq")
        .expect("two-line string interned");
    assert_eq!(
        body.entities[&(EntityKind::StringId, 0)],
        EntityRef::string_with_offset(sid, 0x50)
    );
}

// -- Mainline batch: a moderate document, byte-exact ---------------------

#[test]
fn moderate_document_round_trip_is_byte_exact() {
    let input: &[u8] = b"# source binary: t.abc\n\n# ====================\n# LITERALS\n\n0 0x10 { 1 [ i32:7, ]}\n\n# ====================\n# RECORDS\n\n.language ECMAScript\n.record R {\n\tu32 x = 0x2a\n}\n\n# ====================\n# METHODS\n\n.language ECMAScript\n.function any R.f() <static> {\n\tcreatearraywithbuffer 0x0, { 1 [ i32:7, ]}\n\treturnundefined\n}\n\n# ====================\n# STRING\n\n";
    let file =
        parse_file_with_version(input, Version::new(12, 0, 6, 0)).expect("moderate doc parses");
    let out = crate::pandasm::emit_file(&file, "t.abc");
    assert_eq!(out, input, "parse->emit must be byte-exact");
    // The emitted text is a parse fixpoint.
    let file2 = parse_file_with_version(&out, Version::new(12, 0, 6, 0)).expect("re-parse");
    assert_eq!(crate::pandasm::emit_file(&file2, "t.abc"), input);
    crate::encode(&file).expect("encodes");
}

#[test]
fn literals_12x_overflowing_header_index_is_parse_error() {
    for bad_idx in [0x4000_0001u32, u32::MAX] {
        let lit = format!("{bad_idx} 0x10 {{ 1 [ i32:1, ]}}\n");
        let input = doc(lit.as_bytes(), b"", b"", b"");
        let err = parse_file_with_version(&input, Version::new(12, 0, 6, 0))
            .expect_err("huge 12.x header index must fail cleanly");
        assert!(
            err.message.contains("LITERALS header index"),
            "unexpected error for {bad_idx:#x}: {err}"
        );
    }
}

#[test]
fn multiline_embedded_quotes_and_80_lines_round_trip() {
    let mut long_str = String::from("line0 \"alpha\" and \"beta\" \"unbalanced");
    for idx in 1..80 {
        if idx % 3 == 0 {
            long_str.push_str(&format!("\nline{idx} with \"embedded\" and ]}} tokens"));
        } else {
            long_str.push_str(&format!("\nline{idx} plain continuation"));
        }
    }
    let comma_str = "bar\", \"baz\nsecond line";

    let literals = format!("0 0x10 {{ 1 [ string:\"{long_str}\", ]}}\n");
    let methods = format!(
        ".language ECMAScript\n.function any f() <static> {{\n\tlda.str \"bar\"\n\tlda.str \"{comma_str}\"\n\tlda.str \"{long_str}\"\n\tcreatearraywithbuffer 0x0, {{ 1 [ string:\"{long_str}\", ]}}\n\treturnundefined\n}}\n"
    );
    let strings = format!(
        "[offset:0x40, name_value:bar]\n[offset:0x50, name_value:{comma_str}]\n[offset:0x80, name_value:{long_str}]\n"
    );
    let input = doc(
        literals.as_bytes(),
        b"",
        methods.as_bytes(),
        strings.as_bytes(),
    );

    let file = parse_file_with_version(&input, Version::new(12, 0, 6, 0))
        .expect("80-line embedded-quote string must parse");
    assert!(file.strings.get(&long_str).is_some());
    assert!(file.strings.get(comma_str).is_some());
    let global = file.class_by_str("L_GLOBAL;").expect("global record");
    let body = global.methods[0].body.as_ref().expect("body");
    assert_eq!(body.bytecodes().len(), 5);

    let emitted = crate::pandasm::emit_file(&file, "t.abc");
    let reparsed = parse_file_with_version(&emitted, Version::new(12, 0, 6, 0))
        .expect("canonical emitted pandasm must re-parse");
    let reemitted = crate::pandasm::emit_file(&reparsed, "t.abc");
    assert_eq!(
        reemitted, emitted,
        "emit -> parse -> emit must be byte-exact"
    );

    let encoded = crate::encode(&file).expect("encodes");
    let decoded = crate::decode(&encoded).expect("decodes");
    assert!(decoded.strings.get(&long_str).is_some());
    assert!(decoded.strings.get(comma_str).is_some());
    let bin_emitted = crate::pandasm::emit_file(&decoded, "t.abc");
    let bin_reparsed = parse_file_with_version(&bin_emitted, decoded.version)
        .expect("binary round-trip pandasm must re-parse");
    assert_eq!(
        crate::pandasm::emit_file(&bin_reparsed, "t.abc"),
        bin_emitted,
        "decode -> emit -> parse -> emit must be byte-exact"
    );
}
