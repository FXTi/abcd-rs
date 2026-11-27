//! Regression tests for GitHub Issue #91 (Part 3: `abcd-file` remediations):
//! - `256 KiB`-stack 5,000-deep nested `Annotation` & `ArrayAnnotation` decode,
//!   DAG diamond sharing, and `AVT::ArrayAnnotation` cycle rejection;
//! - `256 KiB`-stack 10,000-deep `AnnotationValue` `Clone`, `PartialEq`, `Debug`,
//!   and `Drop`;
//! - Lossless non-empty typed `LiteralValue::Array*` (all 12 variants) binary
//!   and `pandasm` round-trip;
//! - `LiteralValue::LiteralBufferIndex` index stability with annotation-embedded
//!   `AnnotationValue::LiteralArray` coexistence;
//! - Dual-bucket `ParamAnnotations` round-trip + invalid-handle seal error;
//! - `FieldValue::String` on `Type::Reference` and `Type::U32` fields;
//! - Checked `i32` enumerators (truncated try-block `Error::Malformed`) and
//!   bounded `LineNumberProgram` row cap;
//! - `pandasm` duplicate `.record` `ParseError`, `N20` deterministic ordering,
//!   per-method entity slot interning, and linear `O(N)` quote scanning.

use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationElemDefEx, AnnotationElemValue,
    AnnotationValue, Builder, CatchBlock, Error, FieldValue, LiteralArray, LiteralArrayIdx,
    LiteralValue, SourceLang, StringPool, TryBlock, Type, Version, decode, encode, inspect_summary,
    pandasm,
};

fn run_on_256k_stack<F, T>(name: &str, f: F) -> T
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    std::thread::Builder::new()
        .name(name.to_owned())
        .stack_size(256 * 1024)
        .spawn(f)
        .expect("spawn 256 KiB test thread")
        .join()
        .expect("256 KiB test thread must not overflow stack or panic")
}

#[test]
fn deep_5000_nested_annotation_and_array_annotation_decode_on_256k_stack() {
    const DEPTH: usize = 5_000;

    run_on_256k_stack("ann-decode-5000", || {
        let mut b = Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let leaf_key = b.add_string("leaf");
        let step_key = b.add_string("next");

        let mut cur = b.create_annotation_ex(
            cls,
            &[AnnotationElemDefEx {
                name: leaf_key,
                tag: b'7', // U32
                value: AnnotationElemValue::Scalar(0xCAFE_BABE),
            }],
        );
        for level in 0..DEPTH {
            cur = if level % 2 == 0 {
                // AVT::ArrayAnnotation ('Z')
                b.create_annotation_ex(
                    cls,
                    &[AnnotationElemDefEx {
                        name: step_key,
                        tag: b'Z',
                        value: AnnotationElemValue::EntityArray(vec![cur.as_raw()]),
                    }],
                )
            } else {
                // AVT::Annotation ('G')
                b.create_annotation_ex(
                    cls,
                    &[AnnotationElemDefEx {
                        name: step_key,
                        tag: b'G',
                        value: AnnotationElemValue::EntityRef(cur.as_raw()),
                    }],
                )
            };
        }
        b.class_add_annotation(cls, cur);

        let proto = b.create_proto(Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            AccessFlags::PUBLIC | AccessFlags::STATIC,
            &[0x65],
            0,
            0,
        );
        b.method_set_source_lang(m, SourceLang::EcmaScript);
        let bytes = b.finalize().expect("finalize 5000-deep annotation file");

        let summary = inspect_summary(&bytes, true).expect("inspect_summary 5000-deep");
        assert_eq!(summary.classes, 1);

        let file = decode(&bytes).expect("decode 5000-deep annotation chain");
        let global = file.class_by_str("L_GLOBAL;").expect("global class");
        let mut cursor = &global.annotations.compile_time[0];
        let mut depth_seen = 0usize;
        loop {
            match &cursor.elements[0].value {
                AnnotationValue::Annotation(inner) => {
                    cursor = inner;
                    depth_seen += 1;
                }
                AnnotationValue::Array { tag, values } => {
                    assert_eq!(*tag, b'Z');
                    assert_eq!(values.len(), 1);
                    let AnnotationValue::Annotation(inner) = &values[0] else {
                        panic!("expected nested Annotation inside ArrayAnnotation");
                    };
                    cursor = inner;
                    depth_seen += 1;
                }
                AnnotationValue::U32(v) => {
                    assert_eq!(*v, 0xCAFE_BABE);
                    break;
                }
                other => panic!("unexpected element at depth {depth_seen}: {other:?}"),
            }
        }
        assert_eq!(depth_seen, DEPTH);

        // Re-encode and re-decode inside the same 256 KiB stack budget.
        let rewritten = encode(&file).expect("encode 5000-deep annotation chain");
        let file2 = decode(&rewritten).expect("re-decode 5000-deep annotation chain");
        assert_eq!(
            file.class_by_str("L_GLOBAL;")
                .unwrap()
                .annotations
                .compile_time,
            file2
                .class_by_str("L_GLOBAL;")
                .unwrap()
                .annotations
                .compile_time
        );
        drop(file);
        drop(file2);
    });
}

#[test]
fn array_annotation_cycle_rejected_while_diamond_dag_succeeds() {
    // 1. Diamond DAG: `[leaf, leaf]` inside `ArrayAnnotation` must succeed
    // because `visiting` pops on frame exit.
    {
        let mut b = Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let k = b.add_string("k");
        let leaf = b.create_annotation_ex(
            cls,
            &[AnnotationElemDefEx {
                name: k,
                tag: b'7',
                value: AnnotationElemValue::Scalar(99),
            }],
        );
        let diamond = b.create_annotation_ex(
            cls,
            &[AnnotationElemDefEx {
                name: k,
                tag: b'Z',
                value: AnnotationElemValue::EntityArray(vec![leaf.as_raw(), leaf.as_raw()]),
            }],
        );
        b.class_add_annotation(cls, diamond);
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
        let bytes = b.finalize().expect("finalize diamond");
        inspect_summary(&bytes, false).expect("diamond summary ok");
        let decoded = decode(&bytes).expect("diamond decode ok");
        let g = decoded.class_by_str("L_GLOBAL;").unwrap();
        match &g.annotations.compile_time[0].elements[0].value {
            AnnotationValue::Array { tag: b'Z', values } => assert_eq!(values.len(), 2),
            other => panic!("expected 2-element ArrayAnnotation, got {other:?}"),
        }
    }

    // 2. Cycle through `AVT::ArrayAnnotation`: `outer ('Z' -> [inner])` where
    // `inner ('G' -> decoy)` is patched to point back to `outer`.
    run_on_256k_stack("ann-array-cycle", || {
        let mut b = Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let k_leaf = b.add_string("leaf_decoy");
        let k_back = b.add_string("back_edge");
        let k_arr = b.add_string("arr_edge");
        let decoy = b.create_annotation_ex(
            cls,
            &[AnnotationElemDefEx {
                name: k_leaf,
                tag: b'7',
                value: AnnotationElemValue::Scalar(1),
            }],
        );
        let inner = b.create_annotation_ex(
            cls,
            &[AnnotationElemDefEx {
                name: k_back,
                tag: b'G',
                value: AnnotationElemValue::EntityRef(decoy.as_raw()),
            }],
        );
        let outer = b.create_annotation_ex(
            cls,
            &[AnnotationElemDefEx {
                name: k_arr,
                tag: b'Z',
                value: AnnotationElemValue::EntityArray(vec![inner.as_raw()]),
            }],
        );
        b.class_add_annotation(cls, outer);
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
        let mut data = b.finalize().expect("finalize");

        // Locate `outer` and `inner`'s `back_edge` value slot and patch `back_edge` -> `outer_off`.
        let find_elem = |bytes: &[u8], elem_name: &str, tag: u8| -> (usize, usize) {
            let mut pat = vec![((elem_name.len() as u8) << 1) | 1];
            pat.extend_from_slice(elem_name.as_bytes());
            pat.push(0);
            let str_off = bytes
                .windows(pat.len())
                .position(|w| w == pat)
                .expect("string item") as u32;
            let needle = str_off.to_le_bytes();
            for pos in 4..bytes.len().saturating_sub(9) {
                if bytes[pos..pos + 4] == needle {
                    let ann_off = pos - 4;
                    let cnt =
                        u16::from_le_bytes(bytes[ann_off + 2..ann_off + 4].try_into().unwrap());
                    if cnt == 1 && bytes[pos + 8] == tag {
                        return (ann_off, pos + 4);
                    }
                }
            }
            panic!("annotation element {elem_name} not found");
        };
        let (outer_off, _) = find_elem(&data, "arr_edge", b'Z');
        let (_, back_val_pos) = find_elem(&data, "back_edge", b'G');
        data[back_val_pos..back_val_pos + 4].copy_from_slice(&(outer_off as u32).to_le_bytes());

        let err = decode(&data).expect_err("ArrayAnnotation cycle must fail decode");
        assert!(
            matches!(
                err,
                Error::Malformed {
                    field: "nested annotation",
                    ..
                }
            ),
            "expected Malformed/nested annotation, got: {err:?}"
        );
        let sum_err =
            inspect_summary(&data, false).expect_err("ArrayAnnotation cycle must fail summary");
        assert!(matches!(
            sum_err,
            Error::Malformed {
                field: "nested annotation",
                ..
            }
        ));
    });
}

#[test]
fn deep_10000_annotation_value_traits_on_256k_stack() {
    const DEPTH: usize = 10_000;

    run_on_256k_stack("ann-traits-10000", || {
        let mut pool = StringPool::new();
        let desc = pool.get_or_intern("LDeepAnn;");
        let elem_name = pool.get_or_intern("child");

        let build_chain = |leaf_u32: u32| -> AnnotationValue {
            let mut cur = AnnotationValue::U32(leaf_u32);
            for level in 0..DEPTH {
                cur = if level % 2 == 0 {
                    AnnotationValue::Annotation(Box::new(Annotation {
                        class_descriptor: desc,
                        elements: vec![AnnotationElem {
                            name: elem_name,
                            value: cur,
                        }],
                    }))
                } else {
                    AnnotationValue::Array {
                        tag: b'Z',
                        values: vec![cur],
                    }
                };
            }
            cur
        };

        let tree_a = build_chain(42);
        let tree_b = tree_a.clone();
        let tree_diff = build_chain(43);

        assert_eq!(tree_a, tree_b, "10,000-deep clone must compare equal");
        assert_ne!(
            tree_a, tree_diff,
            "10,000-deep PartialEq must reach leaf difference"
        );

        let formatted = format!("{tree_a:?}");
        assert!(formatted.contains("U32(42)"));
        assert!(formatted.contains("Annotation("));
        assert!(formatted.contains("Array { tag: 90, values: ["));

        drop(tree_a);
        drop(tree_b);
        drop(tree_diff);
    });
}

#[test]
fn typed_literal_arrays_all_12_variants_lossless_binary_and_pandasm_roundtrip() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &[0x65],
        0,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let seed = b.finalize().expect("seed finalize");
    let mut file = decode(&seed).expect("seed decode");

    let s1 = file.strings.get_or_intern("hello, world");
    let s2 = file.strings.get_or_intern("second_elem");
    let nan32 = f32::from_bits(0x7fc0_1234);
    let nan64 = f64::from_bits(0x7ff8_0000_1234_5678);

    let variants = vec![
        LiteralValue::ArrayU1(vec![true, false, true, true]),
        LiteralValue::ArrayU8(vec![0, 1, 127, 255]),
        LiteralValue::ArrayI8(vec![i8::MIN, -1, 0, i8::MAX]),
        LiteralValue::ArrayU16(vec![0, 258, u16::MAX]),
        LiteralValue::ArrayI16(vec![i16::MIN, -258, i16::MAX]),
        LiteralValue::ArrayU32(vec![0, 0x89AB_CDEF, u32::MAX]),
        LiteralValue::ArrayI32(vec![i32::MIN, -123_456, i32::MAX]),
        LiteralValue::ArrayU64(vec![0, 0x0123_4567_89AB_CDEF, u64::MAX]),
        LiteralValue::ArrayI64(vec![i64::MIN, -9_876_543_210, i64::MAX]),
        LiteralValue::ArrayF32(vec![-0.0, 1.25, f32::INFINITY, f32::NEG_INFINITY, nan32]),
        LiteralValue::ArrayF64(vec![
            -0.0,
            std::f64::consts::PI,
            f64::INFINITY,
            f64::NEG_INFINITY,
            nan64,
        ]),
        LiteralValue::ArrayString(vec![s1, s2]),
    ];

    for v in &variants {
        assert_eq!(
            v.literal_array_idx(),
            None,
            "typed array variants must not report a LiteralArrayIdx"
        );
    }
    assert_eq!(
        LiteralValue::LiteralArray(LiteralArrayIdx(3)).literal_array_idx(),
        Some(LiteralArrayIdx(3))
    );
    assert_eq!(
        LiteralValue::LiteralBufferIndex(LiteralArrayIdx(5)).literal_array_idx(),
        Some(LiteralArrayIdx(5))
    );

    file.literal_arrays = variants
        .into_iter()
        .map(|v| LiteralArray::new(vec![v]))
        .collect();

    let bin1 = encode(&file).expect("encode #1");
    let sum1 = inspect_summary(&bin1, true).expect("summary #1");
    let dec1 = decode(&bin1).expect("decode #1");
    assert_eq!(sum1.strings, dec1.strings.len());
    assert_eq!(dec1.literal_arrays.len(), 12);

    // Binary encode -> decode preserves exact creation order in `header.literalarray_idx`.
    assert_eq!(
        dec1.literal_arrays[0].values,
        vec![LiteralValue::ArrayU1(vec![true, false, true, true])]
    );
    assert_eq!(
        dec1.literal_arrays[1].values,
        vec![LiteralValue::ArrayU8(vec![0, 1, 127, 255])]
    );

    let pa_bytes = pandasm::emit_file(&dec1, "typed.abc");
    let pa_parsed =
        pandasm::parse_file_with_version(&pa_bytes, dec1.version).expect("parse_pandasm");
    let bin2 = encode(&pa_parsed).expect("encode #2");
    let dec2 = decode(&bin2).expect("decode #2");

    // `pandasm::emit_file` sorts `# LITERALS` keys lexicographically ("0 ...", "1 ...",
    // "10 ...", "11 ...", "2 ..."), so locate each variant by discriminant in `dec2`.
    assert_eq!(dec2.literal_arrays.len(), 12);
    let vals2: Vec<&LiteralValue> = dec2
        .literal_arrays
        .iter()
        .map(|la| {
            assert_eq!(la.values.len(), 1);
            &la.values[0]
        })
        .collect();

    assert!(vals2.contains(&&LiteralValue::ArrayU1(vec![true, false, true, true])));
    assert!(vals2.contains(&&LiteralValue::ArrayU8(vec![0, 1, 127, 255])));
    assert!(vals2.contains(&&LiteralValue::ArrayI8(vec![i8::MIN, -1, 0, i8::MAX])));
    assert!(vals2.contains(&&LiteralValue::ArrayU16(vec![0, 258, u16::MAX])));
    assert!(vals2.contains(&&LiteralValue::ArrayI16(vec![i16::MIN, -258, i16::MAX])));
    assert!(vals2.contains(&&LiteralValue::ArrayU32(vec![0, 0x89AB_CDEF, u32::MAX])));
    assert!(vals2.contains(&&LiteralValue::ArrayI32(vec![i32::MIN, -123_456, i32::MAX])));
    assert!(vals2.contains(&&LiteralValue::ArrayU64(vec![
        0,
        0x0123_4567_89AB_CDEF,
        u64::MAX
    ])));
    assert!(vals2.contains(&&LiteralValue::ArrayI64(vec![
        i64::MIN,
        -9_876_543_210,
        i64::MAX
    ])));

    let got_f32 = vals2
        .iter()
        .find_map(|v| match v {
            LiteralValue::ArrayF32(got) => Some(got),
            _ => None,
        })
        .expect("ArrayF32 present");
    let got_f32_bits: Vec<u32> = got_f32.iter().map(|x| x.to_bits()).collect();
    assert_eq!(
        got_f32_bits,
        vec![
            (-0.0f32).to_bits(),
            1.25f32.to_bits(),
            f32::INFINITY.to_bits(),
            f32::NEG_INFINITY.to_bits(),
            nan32.to_bits(),
        ]
    );

    let got_f64 = vals2
        .iter()
        .find_map(|v| match v {
            LiteralValue::ArrayF64(got) => Some(got),
            _ => None,
        })
        .expect("ArrayF64 present");
    let got_f64_bits: Vec<u64> = got_f64.iter().map(|x| x.to_bits()).collect();
    assert_eq!(
        got_f64_bits,
        vec![
            (-0.0f64).to_bits(),
            std::f64::consts::PI.to_bits(),
            f64::INFINITY.to_bits(),
            f64::NEG_INFINITY.to_bits(),
            nan64.to_bits(),
        ]
    );

    let got_str = vals2
        .iter()
        .find_map(|v| match v {
            LiteralValue::ArrayString(got) => Some(got),
            _ => None,
        })
        .expect("ArrayString present");
    let resolved: Vec<&str> = got_str
        .iter()
        .map(|&sid| dec2.strings.resolve(sid).expect("resolved string"))
        .collect();
    assert_eq!(resolved, vec!["hello, world", "second_elem"]);
}

#[test]
fn literal_buffer_index_coexists_with_annotation_literal_arrays() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &[0x65],
        0,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let mut file = decode(&b.finalize().expect("finalize")).expect("decode");
    assert!(file.version <= Version::new(12, 0, 6, 0));

    let ann_desc = file.strings.get_or_intern("L_GLOBAL;");
    let ann_elem = file.strings.get_or_intern("embedded_la");

    // Attach annotation-embedded `LiteralArray`s BEFORE model literal arrays are populated.
    let g = file.classes.get_mut(&ann_desc).expect("global class");
    g.annotations.compile_time.push(Annotation {
        class_descriptor: ann_desc,
        elements: vec![AnnotationElem {
            name: ann_elem,
            value: AnnotationValue::LiteralArray(vec![LiteralValue::Integer(111)]),
        }],
    });
    g.methods[0].annotations.compile_time.push(Annotation {
        class_descriptor: ann_desc,
        elements: vec![AnnotationElem {
            name: ann_elem,
            value: AnnotationValue::LiteralArray(vec![LiteralValue::Integer(222)]),
        }],
    });

    // Model literal arrays: slot 0 references slot 1 via `LiteralBufferIndex(1)`.
    file.literal_arrays = vec![
        LiteralArray::new(vec![LiteralValue::LiteralBufferIndex(LiteralArrayIdx(1))]),
        LiteralArray::new(vec![LiteralValue::Integer(999)]),
    ];

    let bytes = encode(&file).expect("encode with annotation literal arrays + LiteralBufferIndex");
    let decoded = decode(&bytes).expect("decode");

    // Model literal arrays occupy header indices 0 and 1, so `LiteralBufferIndex(1)`
    // continues to point at the array carrying `Integer(999)`.
    assert!(decoded.literal_arrays.len() >= 2);
    assert_eq!(
        decoded.literal_arrays[0].values,
        vec![LiteralValue::LiteralBufferIndex(LiteralArrayIdx(1))]
    );
    assert_eq!(
        decoded.literal_arrays[1].values,
        vec![LiteralValue::Integer(999)]
    );
}

#[test]
fn reference_and_u32_string_field_initializers_roundtrip() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let str_cls = b.add_foreign_class("Ljava/lang/String;");
    let cls = b.add_class("LConstants;");
    b.class_set_source_lang(cls, SourceLang::ArkTs);

    let dummy_sid = StringPool::new().get_or_intern("Ljava/lang/String;");
    let f_ref = b.class_add_field_ex(
        cls,
        "GREETING",
        Type::Reference(dummy_sid),
        str_cls,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
    );
    let s_ref = b.add_string("hello from reference field");
    b.field_set_value_string(f_ref, s_ref)
        .expect("set string on reference field");

    let f_u32_str = b.class_add_field(
        cls,
        "U32_STR",
        Type::U32,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
    );
    let s_u32 = b.add_string("hello from u32 field");
    b.field_set_value_string(f_u32_str, s_u32)
        .expect("set string on u32 field");

    let f_u32_int = b.class_add_field(
        cls,
        "U32_INT",
        Type::U32,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
    );
    b.field_set_value_i32(f_u32_int, 123);

    let global = b.add_global_class();
    b.class_set_source_lang(global, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        global,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);

    let bytes1 = b.finalize().expect("finalize");
    let summary = inspect_summary(&bytes1, true).expect("summary");
    let file1 = decode(&bytes1).expect("decode #1");
    assert_eq!(summary.strings, file1.strings.len());

    let check = |file: &abcd_file::File| {
        let c = file.class_by_str("LConstants;").expect("LConstants;");
        let by_name = |name: &str| {
            c.fields
                .iter()
                .find(|f| file.strings.resolve(f.name) == Some(name))
                .expect(name)
        };
        match by_name("GREETING").initial_value {
            Some(FieldValue::String(sid)) => {
                assert_eq!(
                    file.strings.resolve(sid),
                    Some("hello from reference field")
                );
            }
            ref other => panic!("expected FieldValue::String on GREETING, got {other:?}"),
        }
        match by_name("U32_STR").initial_value {
            Some(FieldValue::String(sid)) => {
                assert_eq!(file.strings.resolve(sid), Some("hello from u32 field"));
            }
            ref other => panic!("expected FieldValue::String on U32_STR, got {other:?}"),
        }
        assert_eq!(by_name("U32_INT").initial_value, Some(FieldValue::I32(123)));
    };
    check(&file1);

    let bytes2 = encode(&file1).expect("encode");
    let file2 = decode(&bytes2).expect("decode #2");
    check(&file2);
}

#[test]
fn seal_param_annotations_invalid_handle_returns_error() {
    let mut b1 = Builder::new();
    let cls1 = b1.add_global_class();
    let p1 = b1.create_proto(Type::Void, &[]);
    let _m0 = b1.class_add_method(cls1, "m0", p1, AccessFlags::PUBLIC, &[0x65], 0, 0);
    let foreign_handle = b1.class_add_method(cls1, "m1", p1, AccessFlags::PUBLIC, &[0x65], 0, 0);

    let mut b2 = Builder::new();
    let err = b2
        .method_seal_param_annotations(foreign_handle, false)
        .expect_err("out-of-bounds method handle must fail");
    assert!(matches!(
        err,
        Error::Malformed {
            field: "param_annotations",
            ..
        }
    ));
}

#[test]
fn truncated_try_block_returns_malformed_error() {
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
        &[0x65, 0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let mut model = decode(&b.finalize().expect("seed")).expect("decode seed");
    model.classes.values_mut().next().unwrap().methods[0]
        .body
        .as_mut()
        .unwrap()
        .try_blocks
        .push(TryBlock {
            start: 0,
            len: 1,
            catches: vec![CatchBlock {
                type_class: None,
                handler: 1,
                len: 1,
            }],
        });
    let mut data = encode(&model).expect("encode with try block");

    let baseline = decode(&data).expect("baseline decode");
    assert_eq!(
        baseline.class_by_str("L_GLOBAL;").unwrap().methods[0]
            .body
            .as_ref()
            .unwrap()
            .try_blocks
            .len(),
        1
    );

    // Locate the original `CodeItem` (`num_vregs=0, num_args=1, code_size=2, tries_size=1,
    // insns=[0x65, 0x65]` or `num_vregs=1`) via the method's `MethodTag::CODE` (`0x01`) u32
    // pointer, and repoint it to a tail-appended `CodeItem` whose `tries_size = 1` table is
    // truncated at EOF while all header index tables stay intact.
    let method_off = baseline.class_by_str("L_GLOBAL;").unwrap().methods[0].offset as usize;
    // `MethodItem` header: `[u16 class_idx][u16 proto_idx][u32 name_off][uleb128 index_data]`,
    // followed immediately by `[u8 tag = 0x01 (CODE)][u32 code_off]`.
    let mut scan = method_off + 8;
    while data[scan] & 0x80 != 0 {
        scan += 1;
    }
    scan += 1; // past final ULEB128 byte of `index_data`
    assert_eq!(data[scan], 0x01, "expected MethodTag::CODE (0x01)");
    let code_ptr_pos = scan + 1;

    let tail_code_off = data.len() as u32;
    // `[num_vregs=1, num_args=1, code_size=2, tries_size=1, insn0=0x65, insn1=0x65, truncated_try=0x00]`
    data.extend_from_slice(&[0x01, 0x01, 0x02, 0x01, 0x65, 0x65, 0x00]);
    data[code_ptr_pos..code_ptr_pos + 4].copy_from_slice(&tail_code_off.to_le_bytes());
    let new_file_size = data.len() as u32;
    data[16..20].copy_from_slice(&new_file_size.to_le_bytes());
    // Recompute Adler-32 over bytes 12..EOF (`header.checksum` sits at 8..12).
    let adler = {
        const MOD: u32 = 65_521;
        let (mut a, mut b_acc) = (1u32, 0u32);
        for &byte in &data[12..] {
            a = (a + u32::from(byte)) % MOD;
            b_acc = (b_acc + a) % MOD;
        }
        (b_acc << 16) | a
    };
    data[8..12].copy_from_slice(&adler.to_le_bytes());

    let err = decode(&data).expect_err("truncated try block must fail decode");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "try_block",
                ..
            }
        ),
        "expected Malformed/try_block, got: {err:?}"
    );
    let sum_err =
        inspect_summary(&data, true).expect_err("truncated try block must fail verify summary");
    assert!(matches!(
        sum_err,
        Error::Malformed {
            field: "try_block",
            ..
        }
    ));
}

#[test]
fn runaway_lnp_stream_exceeding_row_cap_is_rejected() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let sf = b.add_string("test.js");
    b.class_set_source_file(cls, sf);
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
    let lnp = b.create_lnp();
    let dbg = b.create_debug_info(lnp, 1);
    b.lnp_emit_special_opcode(lnp, dbg, 0, 1);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m, dbg);
    let mut data = b.finalize().expect("finalize");

    // Locate `lnp_off` from header (`lnp_idx_off` at header 40..44) and append a
    // synthetic 1,000,005-byte stream of 1-byte special opcodes (`0x10`) + `0x00`
    // at the tail of the buffer, updating `lnp_idx[0]`, `file_size`, and Adler-32.
    let lnp_idx_off = u32::from_le_bytes(data[40..44].try_into().unwrap()) as usize;
    let new_lnp_off = data.len() as u32;
    data.resize(data.len() + 1_000_005, 0x10);
    data.push(0x00);
    let new_size = data.len() as u32;
    data[lnp_idx_off..lnp_idx_off + 4].copy_from_slice(&new_lnp_off.to_le_bytes());
    data[16..20].copy_from_slice(&new_size.to_le_bytes());
    let adler = {
        const MOD: u32 = 65_521;
        let (mut a, mut b_acc) = (1u32, 0u32);
        for &byte in &data[12..] {
            a = (a + u32::from(byte)) % MOD;
            b_acc = (b_acc + a) % MOD;
        }
        (b_acc << 16) | a
    };
    data[8..12].copy_from_slice(&adler.to_le_bytes());

    let err = decode(&data).expect_err("runaway LNP must hit row cap");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "line_number_program",
                ..
            }
        ),
        "expected Malformed/line_number_program, got: {err:?}"
    );
    let sum_err = inspect_summary(&data, false).expect_err("runaway LNP must fail summary");
    assert!(matches!(
        sum_err,
        Error::Malformed {
            field: "line_number_program",
            ..
        }
    ));
}

#[test]
fn pandasm_duplicate_record_per_method_slot_interning_and_linear_quote_scan() {
    // 1. Duplicate `.record` must return typed `ParseError`.
    let dup_pa = b"# source binary: t.abc\n\n# ====================\n# LITERALS\n\n# ====================\n# RECORDS\n\n.language ECMAScript\n.record Dup {\n}\n.record Dup {\n}\n\n# ====================\n# METHODS\n\n# ====================\n# STRING\n\n";
    let err = pandasm::parse_file(dup_pa).expect_err("duplicate .record must fail");
    assert!(
        err.message.contains("duplicate .record `Dup`"),
        "got: {err}"
    );

    // 2. Per-method entity slot interning: repeated identical string/method
    // operands inside one method share a single slot, while a second method
    // gets its own independent slot table.
    let intern_pa = b"# source binary: t.abc\n\n# ====================\n# LITERALS\n\n# ====================\n# RECORDS\n\n# ====================\n# METHODS\n\n.language ECMAScript\n.function any helper() <static> {\n\tlda.str \"shared\"\n\treturnundefined\n}\n.language ECMAScript\n.function any main_fn() <static> {\n\tlda.str \"shared\"\n\tlda.str \"shared\"\n\tlda.str \"shared\"\n\tdefinefunc 0x0, helper:(), 0x0\n\tdefinefunc 0x1, helper:(), 0x0\n\treturnundefined\n}\n\n# ====================\n# STRING\n\n[offset:0x40, name_value:shared]\n";
    let parsed = pandasm::parse_file(intern_pa).expect("parse intern_pa");
    let g = parsed.class_by_str("L_GLOBAL;").expect("global");
    let m_main = g
        .methods
        .iter()
        .find(|m| parsed.strings.resolve(m.name) == Some("main_fn"))
        .unwrap();
    let m_helper = g
        .methods
        .iter()
        .find(|m| parsed.strings.resolve(m.name) == Some("helper"))
        .unwrap();
    let main_entities = &m_main.body.as_ref().unwrap().entities;
    let helper_entities = &m_helper.body.as_ref().unwrap().entities;
    assert_eq!(
        main_entities
            .keys()
            .filter(|(k, _)| *k == abcd_isa::EntityKind::StringId)
            .count(),
        1,
        "three identical string operands in main_fn must share 1 slot"
    );
    assert_eq!(
        main_entities
            .keys()
            .filter(|(k, _)| *k == abcd_isa::EntityKind::MethodId)
            .count(),
        1,
        "two identical method operands in main_fn must share 1 slot"
    );
    assert_eq!(
        helper_entities
            .keys()
            .filter(|(k, _)| *k == abcd_isa::EntityKind::StringId)
            .count(),
        1,
        "helper has its own independent slot 0"
    );

    // 3. Linear O(N) quote scanning on a 2,500-line multiline string with
    // embedded quotes on every line + a 1,000-string literal array.
    let mut big_multiline = String::from("head \"q0\"");
    for line_idx in 1..2_500 {
        big_multiline.push_str(&format!("\nline {line_idx} \"embedded\" middle"));
    }
    let mut many_items = String::from("0 0x10 { 1000 [ ");
    for idx in 0..1_000 {
        many_items.push_str(&format!("string:\"item_{idx}\", "));
    }
    many_items.push_str("]}\n");

    let pa_doc = format!(
        "# source binary: perf.abc\n\n# ====================\n# LITERALS\n\n{many_items}\n# ====================\n# RECORDS\n\n# ====================\n# METHODS\n\n.language ECMAScript\n.function any f() <static> {{\n\tlda.str \"{big_multiline}\"\n\treturnundefined\n}}\n\n# ====================\n# STRING\n\n[offset:0x80, name_value:{big_multiline}]\n"
    );
    let f = pandasm::parse_file(pa_doc.as_bytes()).expect("large O(N) pandasm must parse");
    assert!(f.strings.get(&big_multiline).is_some());
    assert_eq!(f.literal_arrays[0].values.len(), 1_000);
}
