//! Regression tests for Phase 0.5 worker F fixes (design/review-bridge-wrapper.md):
//! - #5  local-variable scopes must survive an encode roundtrip
//! - #8  nested literal-array references resolve through the handle table
//! - #9  embedded-NUL strings encode as MUTF-8 (C0 80) instead of panicking
//! - #18 64-bit annotation array elements return an error instead of panicking

use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationValue, Annotations, Builder, Error,
    LiteralArray, LiteralArrayIdx, LiteralValue, SourceLang, Type, decode, encode,
};

/// Build a method carrying debug info with a local variable whose scope
/// spans several instructions: start at pc 1, end at pc 3 (of 4 one-byte
/// instructions).
fn build_local_var_scope() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);

    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_with_local",
        proto,
        AccessFlags::PUBLIC,
        &[0x65, 0x65, 0x65, 0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);

    let lnp = b.create_lnp();
    let debug = b.create_debug_info(lnp, 10);
    // A line program with file/line content — without it the vendored writer
    // drops the method's debug info entirely (same shape as debug_info.rs).
    let src = b.add_string("main.js");
    b.lnp_emit_set_file(lnp, debug, src);
    b.lnp_emit_advance_pc(lnp, debug, 1);
    b.lnp_emit_advance_line(lnp, debug, 2);
    // Local variable "scoped_var" in register 1, live over pc 1..3.
    let vname = b.add_string("scoped_var");
    let vtype = b.add_string("I");
    b.lnp_emit_start_local(lnp, debug, 1, vname, vtype);
    b.lnp_emit_advance_pc(lnp, debug, 2);
    b.lnp_emit_end_local(lnp, 1);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m, debug);

    b.finalize().expect("finalize")
}

/// Finding #5: `lv.start`/`lv.end` were ignored on encode, collapsing every
/// local variable to a zero-length scope. decode→encode→decode must preserve
/// the scope's instruction-index range.
#[test]
fn local_var_scope_survives_encode_roundtrip() {
    let file1 = decode(&build_local_var_scope()).expect("decode #1");
    let g = file1.classes.values().find(|c| !c.is_external).unwrap();
    let lv1 = file1
        .strings
        .resolve(g.methods[0].debug.as_ref().unwrap().local_vars[0].name)
        .unwrap();
    assert_eq!(lv1, "scoped_var");
    let lv1 = &g.methods[0].debug.as_ref().unwrap().local_vars[0];
    assert_eq!((lv1.start, lv1.end), (1, 3), "scope built with pc 1..3");

    let bytes2 = encode(&file1).expect("encode");
    let file2 = decode(&bytes2).expect("decode #2");
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    let lv2 = &g2.methods[0].debug.as_ref().unwrap().local_vars[0];
    assert_eq!(
        (lv2.start, lv2.end),
        (lv1.start, lv1.end),
        "local variable scope must survive encode (was collapsed to end == start)"
    );
    assert_ne!(lv2.start, lv2.end);
}

/// Finding #8: `LiteralValue::LiteralArray(idx)` holds a model table index,
/// not a builder handle. With an annotation-embedded literal array present
/// (which consumes builder handles during class configuration), a nested
/// reference must still point at the right array after a roundtrip.
#[test]
fn nested_literal_array_resolves_to_model_table_index() {
    // Base file: just the global class. Pin a 12.x version so the literal
    // array table is enumerated from the header on decode (newer versions
    // only expose literal arrays through instruction index regions).
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    b.add_global_class();
    let file_bytes = b.finalize().expect("finalize");
    let mut file = decode(&file_bytes).expect("decode base");

    // Model literal arrays: [0] references [1]; [1] carries a marker value.
    file.literal_arrays.push(LiteralArray {
        values: vec![LiteralValue::LiteralArray(LiteralArrayIdx(1))],
    });
    file.literal_arrays.push(LiteralArray {
        values: vec![LiteralValue::Integer(7)],
    });

    // Annotation-embedded literal array on the global class: this creates an
    // `ann_la_0` builder array while classes are configured. It also nests a
    // reference to model array [1], exercising encode_literal_value_simple.
    let ann_desc = file.strings.get_or_intern("LAnno;");
    let elem_name = file.strings.get_or_intern("v");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.annotations.compile_time.push(Annotation {
        class_descriptor: ann_desc,
        elements: vec![AnnotationElem {
            name: elem_name,
            value: AnnotationValue::LiteralArray(vec![
                LiteralValue::Integer(42),
                LiteralValue::LiteralArray(LiteralArrayIdx(1)),
            ]),
        }],
    });

    let bytes2 = encode(&file).expect("encode");
    let file2 = decode(&bytes2).expect("decode #2");

    // Follow the nested reference and check the target's content. The writer
    // owns the final table order, so locate arrays by content.
    let (host_idx, target_idx) = file2
        .literal_arrays
        .iter()
        .enumerate()
        .find_map(|(i, la)| match la.values.as_slice() {
            [LiteralValue::LiteralArray(idx)] => Some((i, idx.0 as usize)),
            _ => None,
        })
        .expect("a literal array with a nested reference");
    assert_ne!(
        host_idx, target_idx,
        "nested reference must not point at its own array"
    );
    assert_eq!(
        file2.literal_arrays[target_idx].values,
        vec![LiteralValue::Integer(7)],
        "nested reference must resolve to the model-indexed array"
    );

    // The annotation-embedded array must survive the roundtrip.
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    assert_eq!(g2.annotations.compile_time.len(), 1);
}

/// Finding #9: MUTF-8 encodes U+0000 as C0 80, so re-encoding a file whose
/// method name contains an embedded NUL must succeed and roundtrip
/// losslessly (previously `CString::new` panicked on the data path).
#[test]
fn embedded_nul_method_name_roundtrips() {
    let mut b = Builder::new();
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    b.class_add_method(cls, "original", proto, AccessFlags::PUBLIC, &[], 0, 0);
    let file_bytes = b.finalize().expect("finalize");
    let mut file = decode(&file_bytes).expect("decode base");

    let nul_name = file.strings.get_or_intern("a\0b");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.methods[0].name = nul_name;

    let bytes2 = encode(&file).expect("encode must not panic on embedded NUL");
    let file2 = decode(&bytes2).expect("decode #2");
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    assert_eq!(
        file2.strings.resolve(g2.methods[0].name),
        Some("a\0b"),
        "embedded NUL must survive the MUTF-8 roundtrip"
    );
}

/// Finding #18: 64-bit annotation array elements are unsupported by the
/// builder ABI; encode must return `UnsupportedAnnotationArrayType` rather
/// than panic.
#[test]
fn i64_annotation_array_element_returns_error_not_panic() {
    let mut b = Builder::new();
    b.add_global_class();
    let file_bytes = b.finalize().expect("finalize");
    let mut file = decode(&file_bytes).expect("decode base");

    let ann_desc = file.strings.get_or_intern("LAnno;");
    let elem_name = file.strings.get_or_intern("v");
    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    cls.annotations = Annotations {
        compile_time: vec![Annotation {
            class_descriptor: ann_desc,
            elements: vec![AnnotationElem {
                name: elem_name,
                value: AnnotationValue::Array {
                    tag: b'S', // ArrayI64 (upstream pandasm array tag chars)
                    values: vec![AnnotationValue::I64(-1)],
                },
            }],
        }],
        ..Annotations::default()
    };

    let err = encode(&file).expect_err("encode must fail, not panic");
    assert_eq!(err, Error::UnsupportedAnnotationArrayType { tag: b'S' });
}
