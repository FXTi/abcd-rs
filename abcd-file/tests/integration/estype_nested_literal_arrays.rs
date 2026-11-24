//! Integration tests for `#32-File`: `L_ESTypeAnnotation;` (`_TypeOfInstruction`)
//! and general `AnnotationValue::LiteralArray` containing nested
//! `LiteralValue::LiteralArray` references across `decode -> encode -> decode`,
//! explicit iterative workstacks (deep nesting without stack growth), and cycle /
//! dangling-offset loud errors.

use std::path::Path;
use std::process::Command;

use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationElemDefEx, AnnotationElemValue,
    AnnotationValue, Builder, Error, LiteralArray, LiteralArrayIdx, LiteralValue, SourceLang, Type,
    Version, decode, encode,
};

/// Canonicalize a literal array iteratively by content (resolving `StringId`s,
/// method names, and nested `LiteralArrayIdx` indices, while breaking
/// active-path cycles via `<cycle:depth>`) so two decoded `File`s with
/// different layout offsets can be compared structurally even on cyclic ArkTS
/// recursive type graphs.
fn canon_lit_values(file: &abcd_file::File, values: &[LiteralValue]) -> String {
    enum Step<'a> {
        Enter(&'a [LiteralValue], Option<u32>),
        Item(&'a LiteralValue),
        Sep,
        Leave(Option<u32>),
    }

    let mut out = String::new();
    let mut active_path: Vec<u32> = Vec::new();
    let mut stack: Vec<Step<'_>> = vec![Step::Enter(values, None)];

    while let Some(step) = stack.pop() {
        match step {
            Step::Enter(slice, entered_idx) => {
                if let Some(idx) = entered_idx {
                    active_path.push(idx);
                    out.push('[');
                }
                stack.push(Step::Leave(entered_idx));
                for (i, item) in slice.iter().enumerate().rev() {
                    if i + 1 < slice.len() {
                        stack.push(Step::Sep);
                    }
                    stack.push(Step::Item(item));
                }
            }
            Step::Sep => out.push_str(", "),
            Step::Leave(entered_idx) => {
                if entered_idx.is_some() {
                    active_path.pop();
                    out.push(']');
                }
            }
            Step::Item(v) => match v {
                LiteralValue::String(sid) => {
                    out.push_str(&format!(
                        "str({:?})",
                        file.strings.resolve(*sid).unwrap_or("<?>")
                    ));
                }
                LiteralValue::EtsImplements(sid) => {
                    out.push_str(&format!(
                        "impl({:?})",
                        file.strings.resolve(*sid).unwrap_or("<?>")
                    ));
                }
                LiteralValue::Method(off) => {
                    let mname = file
                        .all_methods()
                        .find(|(_, m)| m.offset == *off)
                        .and_then(|(_, m)| file.strings.resolve(m.name))
                        .unwrap_or("<unresolved>");
                    out.push_str(&format!("method({mname})"));
                }
                LiteralValue::LiteralArray(idx) => {
                    if let Some(depth) = active_path.iter().position(|&p| p == idx.0) {
                        out.push_str(&format!("<cycle:{depth}>"));
                    } else {
                        let target = file
                            .literal_arrays
                            .get(idx.0 as usize)
                            .unwrap_or_else(|| panic!("dangling LiteralArrayIdx({})", idx.0));
                        stack.push(Step::Enter(&target.values, Some(idx.0)));
                    }
                }
                other => out.push_str(&format!("{other:?}")),
            },
        }
    }
    out
}

/// Build an `.abc` file at `version` modeling OpenHarmony's
/// `Lcom.ohos.settings/phone/ets/Application/AbilityStage;::onCreate` carrying
/// `L_ESTypeAnnotation;` -> `_TypeOfInstruction` with multi-level nested
/// `LiteralTag::LiteralArray` (`0x18`) entries, a shared DAG target, a method
/// reference, and trailing scalar items after each nested reference.
fn build_estype_fixture(version: Version) -> Vec<u8> {
    let mut b = Builder::new();
    b.set_file_version(version).expect("set_file_version");

    let global = b.add_global_class();
    b.class_set_source_lang(global, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let entry = b.class_add_method(
        global,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(entry, SourceLang::EcmaScript);

    let estype_cls = b.add_class("L_ESTypeAnnotation;");
    b.class_set_source_lang(estype_cls, SourceLang::EcmaScript);

    let stage_cls = b.add_class("Lcom/ohos/settings/phone/ets/Application/AbilityStage;");
    b.class_set_source_lang(stage_cls, SourceLang::EcmaScript);
    let helper = b.class_add_method(
        stage_cls,
        "helper",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(helper, SourceLang::EcmaScript);

    let on_create = b.class_add_method(
        stage_cls,
        "onCreate",
        proto,
        AccessFlags::PUBLIC,
        &[0x65, 0x65],
        1,
        0,
    );
    b.method_set_source_lang(on_create, SourceLang::EcmaScript);

    // Depth-3 leaf type descriptor literal array (shared DAG node referenced twice).
    let leaf_la = b.add_literal_array("type_leaf");
    b.literal_array_add_u8(leaf_la, 0x00); // TAGVALUE / Integer8
    b.literal_array_add_u8(leaf_la, 1);
    b.literal_array_add_integer(leaf_la, 99);
    let leaf_str = b.add_string("ohos.app.ability.Want");
    b.literal_array_add_string(leaf_la, leaf_str);
    b.literal_array_add_u8(leaf_la, 0xFF); // NULLVALUE (0xFF)
    b.literal_array_add_u8(leaf_la, 0);

    // Depth-2 class type descriptor literal array (matches Settings.hap 0x72098 shape).
    let mid_la = b.add_literal_array("type_mid");
    b.literal_array_add_integer(mid_la, 3);
    b.literal_array_add_integer(mid_la, 0);
    let stage_name = b.add_string("AbilityStage");
    b.literal_array_add_string(mid_la, stage_name);
    b.literal_array_add_literalarray(mid_la, leaf_la);
    b.literal_array_add_method(mid_la, helper);
    b.literal_array_add_u8(mid_la, 0x19); // BUILTINTYPEINDEX (25 = 0x19)
    b.literal_array_add_u8(mid_la, 7);
    b.literal_array_add_u8(mid_la, 0xFF); // NULLVALUE (0xFF)
    b.literal_array_add_u8(mid_la, 0);

    // Depth-1 `_TypeOfInstruction` embedded literal array.
    let typeof_la = b.add_literal_array("typeof_insn");
    b.literal_array_add_integer(typeof_la, 0);
    b.literal_array_add_literalarray(typeof_la, mid_la);
    b.literal_array_add_integer(typeof_la, 1);
    b.literal_array_add_literalarray(typeof_la, leaf_la); // shared DAG reference
    b.literal_array_add_bool(typeof_la, true);
    let tail_str = b.add_string("tail_sentinel");
    b.literal_array_add_string(typeof_la, tail_str);

    let elem_name = b.add_string("_TypeOfInstruction");
    let ann = b.create_annotation_ex(
        estype_cls,
        &[AnnotationElemDefEx {
            name: elem_name,
            tag: b'#',
            value: AnnotationElemValue::EntityRef(typeof_la.as_raw()),
        }],
    );
    b.method_add_annotation(on_create, ann);

    b.finalize().expect("finalize estype fixture")
}

/// Core `#32-File` regression test: `L_ESTypeAnnotation;` `_TypeOfInstruction`
/// carrying multi-level nested `LiteralArray`s, shared DAG nodes, method refs,
/// and trailing elements survives `decode -> encode -> decode -> encode -> decode`
/// on `9.0.0.0`, `12.0.2.0`, and headerless `24.0.0.0`.
#[test]
fn estype_typeofinstruction_builder_roundtrip_v9_v12_v24() {
    for version in [
        Version::new(9, 0, 0, 0),
        Version::new(12, 0, 2, 0),
        Version::new(24, 0, 0, 0),
    ] {
        let bytes0 = build_estype_fixture(version);
        let file1 = decode(&bytes0).unwrap_or_else(|e| panic!("{version}: decode #1 failed: {e}"));
        let bytes1 = encode(&file1).unwrap_or_else(|e| panic!("{version}: encode #1 failed: {e}"));
        let file2 = decode(&bytes1).unwrap_or_else(|e| panic!("{version}: decode #2 failed: {e}"));
        let bytes2 = encode(&file2).unwrap_or_else(|e| panic!("{version}: encode #2 failed: {e}"));
        let file3 = decode(&bytes2).unwrap_or_else(|e| panic!("{version}: decode #3 failed: {e}"));

        let extract = |file: &abcd_file::File| -> String {
            let cls = file
                .classes
                .values()
                .find(|c| {
                    file.strings.resolve(c.descriptor)
                        == Some("Lcom/ohos/settings/phone/ets/Application/AbilityStage;")
                })
                .expect("AbilityStage class");
            let m = cls
                .methods
                .iter()
                .find(|m| file.strings.resolve(m.name) == Some("onCreate"))
                .expect("onCreate method");
            let ann = m
                .annotations
                .compile_time
                .iter()
                .chain(m.annotations.runtime.iter())
                .find(|a| file.strings.resolve(a.class_descriptor) == Some("L_ESTypeAnnotation;"))
                .expect("L_ESTypeAnnotation;");
            assert_eq!(
                file.strings.resolve(ann.elements[0].name),
                Some("_TypeOfInstruction")
            );
            let AnnotationValue::LiteralArray(values) = &ann.elements[0].value else {
                panic!(
                    "expected AnnotationValue::LiteralArray, got {:?}",
                    ann.elements[0].value
                );
            };
            canon_lit_values(file, values)
        };

        let c1 = extract(&file1);
        let c2 = extract(&file2);
        let c3 = extract(&file3);
        assert_eq!(c1, c2, "{version}: decode #1 vs decode #2 mismatch");
        assert_eq!(c2, c3, "{version}: decode #2 vs decode #3 mismatch");
        assert!(
            c1.contains("AbilityStage")
                && c1.contains("ohos.app.ability.Want")
                && c1.contains("method(helper)")
                && c1.contains("tail_sentinel"),
            "{version}: unexpected canonical payload: {c1}"
        );
    }
}

/// Even on `<= 12.x`, if a nested literal array is NOT listed in the header
/// `literalarray_idx` table and is reachable ONLY via `_TypeOfInstruction`'s
/// `0x18` slot, `decode` recovers it transitively and `encode` relocates it.
#[test]
fn estype_unregistered_nested_literal_array_recovered_and_relocated() {
    let mut data = build_estype_fixture(Version::new(12, 0, 2, 0));
    data[44..48].copy_from_slice(&0u32.to_le_bytes());
    data[48..52].copy_from_slice(&0xFFFF_FFFFu32.to_le_bytes());

    let file1 = decode(&data).expect("decode header-stripped 12.x fixture");
    assert!(
        file1.literal_arrays.len() >= 2,
        "both nested literal arrays must be transitively recovered from _TypeOfInstruction, got {}",
        file1.literal_arrays.len()
    );

    let reencoded = encode(&file1).expect("encode recovered fixture");
    let file2 = decode(&reencoded).expect("decode reencoded fixture");

    let find_typeof = |file: &abcd_file::File| -> String {
        let (_, m) = file
            .all_methods()
            .find(|(_, m)| file.strings.resolve(m.name) == Some("onCreate"))
            .expect("onCreate");
        let ann = &m.annotations.compile_time[0];
        let AnnotationValue::LiteralArray(vals) = &ann.elements[0].value else {
            panic!("expected LiteralArray");
        };
        canon_lit_values(file, vals)
    };
    assert_eq!(find_typeof(&file1), find_typeof(&file2));
}

/// Deeply nested literal-array chains (depth 256) and deeply nested annotation
/// trees (depth 128) round-trip cleanly on a constrained 512 KiB thread stack,
/// proving all traversals use explicit heap workstacks instead of native
/// recursion.
#[test]
fn deep_nested_literal_arrays_and_annotations_use_iterative_workstacks() {
    let handle = std::thread::Builder::new()
        .name("small_stack_estype".into())
        .stack_size(512 * 1024)
        .spawn(|| {
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
                &[0x65],
                1,
                0,
            );
            b.method_set_source_lang(m, SourceLang::EcmaScript);
            let base = b.finalize().expect("finalize base");
            let mut file = decode(&base).expect("decode base");

            const LA_DEPTH: usize = 256;
            for i in 0..LA_DEPTH {
                let values = if i + 1 < LA_DEPTH {
                    vec![
                        LiteralValue::Integer(i as u32),
                        LiteralValue::LiteralArray(LiteralArrayIdx((i + 1) as u32)),
                    ]
                } else {
                    vec![LiteralValue::Integer(0xCAFE_u32)]
                };
                file.literal_arrays.push(LiteralArray { values });
            }

            let ann_desc = file.strings.get_or_intern("L_ESTypeAnnotation;");
            let elem_name = file.strings.get_or_intern("_TypeOfInstruction");
            let mut current = Annotation {
                class_descriptor: ann_desc,
                elements: vec![AnnotationElem {
                    name: elem_name,
                    value: AnnotationValue::LiteralArray(vec![LiteralValue::LiteralArray(
                        LiteralArrayIdx(0),
                    )]),
                }],
            };
            for _ in 0..128 {
                current = Annotation {
                    class_descriptor: ann_desc,
                    elements: vec![AnnotationElem {
                        name: elem_name,
                        value: AnnotationValue::Annotation(Box::new(current)),
                    }],
                };
            }

            let g = file.classes.values_mut().find(|c| !c.is_external).unwrap();
            g.methods[0].annotations.compile_time.push(current);

            let encoded = encode(&file).expect("encode deep fixture");
            let file2 = decode(&encoded).expect("decode deep fixture");
            // 12.x header table records the 256 model arrays + 1 annotation-embedded array.
            assert_eq!(file2.literal_arrays.len(), LA_DEPTH + 1);
        })
        .expect("spawn thread");
    handle.join().expect("small-stack thread must not overflow");
}

/// Binary-mutated dangling `0x18` nested literal-array offsets inside
/// `_TypeOfInstruction` — both past EOF (`0xFFFF_FF00`) and inside the 60-byte
/// header (`0x04` when `literal_arrays.len() > 4`, guarding against header-offset
/// aliasing) — decode without panicking and fail loudly on `encode` with
/// `Error::CodeRelocation`.
#[test]
fn dangling_nested_offset_in_estype_fails_encode_loudly() {
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
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);

    let mut target_la = None;
    for i in 0..6u32 {
        let la = b.add_literal_array(&format!("m_{i}"));
        b.literal_array_add_integer(la, 1000 + i);
        if i == 0 {
            target_la = Some(la);
        }
    }
    let target_la = target_la.expect("target_la");

    let emb = b.add_literal_array("emb");
    b.literal_array_add_integer(emb, 0x1357_2468);
    b.literal_array_add_literalarray(emb, target_la);
    let ename = b.add_string("_TypeOfInstruction");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name: ename,
            tag: b'#',
            value: AnnotationElemValue::EntityRef(emb.as_raw()),
        }],
    );
    b.method_add_annotation(m, ann);
    let base_bytes = b.finalize().expect("finalize");

    let mut marker = vec![0x02u8];
    marker.extend_from_slice(&0x1357_2468u32.to_le_bytes());
    marker.push(0x18u8);
    let pos = base_bytes
        .windows(marker.len())
        .position(|w| w == marker.as_slice())
        .expect("embedded literal-array pattern");
    let nested_off_pos = pos + marker.len();

    for bogus in [0xFFFF_FF00u32, 0x0000_0004u32] {
        let mut mutated = base_bytes.clone();
        mutated[nested_off_pos..nested_off_pos + 4].copy_from_slice(&bogus.to_le_bytes());

        let decoded = decode(&mutated).expect("decode must tolerate dangling nested 0x18 offset");
        assert!(
            decoded.literal_arrays.len() >= 6,
            "fixture must have >= 6 literal arrays"
        );
        let err = encode(&decoded)
            .expect_err("encode must reject unrecoverable nested 0x18 offset instead of aliasing");
        assert!(
            matches!(err, Error::CodeRelocation(ref msg) if msg.contains("out of bounds")),
            "bogus {bogus:#x}: expected CodeRelocation out of bounds, got {err:?}"
        );
    }
}

/// Binary-crafted cyclic `AVT::Annotation` (`'G'`) references fail `decode`
/// cleanly with `Error::Malformed` (never a stack overflow), while shared
/// sibling DAG references (`[inner, inner]`) decode and round-trip cleanly.
#[test]
fn cyclic_binary_nested_annotation_fails_decode_cleanly_while_dag_succeeds() {
    // 1. Shared sibling DAG `[inner, inner]`.
    {
        let mut b = Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let k = b.add_string("k");
        let inner = b.create_annotation_ex(
            cls,
            &[AnnotationElemDefEx {
                name: k,
                tag: b'7',
                value: AnnotationElemValue::Scalar(42),
            }],
        );
        let arr_name = b.add_string("dagArr");
        let outer = b.create_annotation_ex(
            cls,
            &[AnnotationElemDefEx {
                name: arr_name,
                tag: b'Z',
                value: AnnotationElemValue::EntityArray(vec![inner.as_raw(), inner.as_raw()]),
            }],
        );
        b.class_add_runtime_annotation(cls, outer);
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
        let bytes = b.finalize().expect("finalize dag");
        let file = decode(&bytes).expect("DAG annotation sharing must decode");
        let bytes2 = encode(&file).expect("DAG annotation sharing must encode");
        decode(&bytes2).expect("decode reencoded DAG");
    }

    // 2. Direct binary cycle: outer 'G' element patched to point to `outer`'s own offset.
    {
        let mut b = Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let inner_k = b.add_string("innerK");
        let inner = b.create_annotation_ex(
            cls,
            &[AnnotationElemDefEx {
                name: inner_k,
                tag: b'7',
                value: AnnotationElemValue::Scalar(9),
            }],
        );
        let cyc_name_str = "cycElemG";
        let cyc_name = b.add_string(cyc_name_str);
        let outer = b.create_annotation_ex(
            cls,
            &[AnnotationElemDefEx {
                name: cyc_name,
                tag: b'G',
                value: AnnotationElemValue::EntityRef(inner.as_raw()),
            }],
        );
        b.class_add_runtime_annotation(cls, outer);
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
        let mut data = b.finalize().expect("finalize cycle base");

        let mut str_pat = vec![((cyc_name_str.len() as u8) << 1) | 1];
        str_pat.extend_from_slice(cyc_name_str.as_bytes());
        str_pat.push(0);
        let str_off = data
            .windows(str_pat.len())
            .position(|w| w == str_pat.as_slice())
            .expect("cycElemG string") as u32;
        let name_pos = data
            .windows(4)
            .enumerate()
            .find_map(|(pos, w)| {
                if w == str_off.to_le_bytes() && pos >= 6 && pos + 9 <= data.len() {
                    let count = u16::from_le_bytes(data[pos - 2..pos].try_into().unwrap());
                    if count == 1 && data[pos + 8] == b'G' {
                        return Some(pos);
                    }
                }
                None
            })
            .expect("outer annotation item");
        // AnnotationItem layout: `[u16 class_idx][u16 count][u32 name_off, u32 value][u8 tag]`.
        let outer_off = (name_pos - 4) as u32;
        data[name_pos + 4..name_pos + 8].copy_from_slice(&outer_off.to_le_bytes());

        let err = decode(&data).expect_err("self-referential annotation must fail decode");
        assert!(
            matches!(
                err,
                Error::Malformed {
                    field: "nested annotation",
                    ref context,
                } if context.contains("cyclic")
            ),
            "expected cyclic nested annotation error, got: {err:?}"
        );
    }
}

/// `pandasm::emit_file` renders nested `LiteralValue::LiteralArray` elements
/// inside `L_ESTypeAnnotation;` as `lit_offset:0x<source_offset>` both before
/// and after `encode`.
#[test]
fn estype_pandasm_emit_preserves_lit_offset() {
    let bytes1 = build_estype_fixture(Version::new(12, 0, 2, 0));
    let file1 = decode(&bytes1).expect("decode #1");
    let pa1 = String::from_utf8(abcd_file::pandasm::emit_file(&file1, "test.abc")).expect("utf8");
    assert!(
        pa1.contains("_ESTypeAnnotation") && pa1.contains("lit_offset:0x"),
        "pandasm output must render _ESTypeAnnotation with lit_offset:0x...: {pa1}"
    );
    assert!(
        !pa1.contains("lit_offset:0x0,") && !pa1.contains("lit_offset:0x1,"),
        "lit_offset must reverse table index to real file offset (>= 60): {pa1}"
    );

    let bytes2 = encode(&file1).expect("encode");
    let file2 = decode(&bytes2).expect("decode #2");
    let pa2 = String::from_utf8(abcd_file::pandasm::emit_file(&file2, "test2.abc")).expect("utf8");
    assert!(
        pa2.contains("_ESTypeAnnotation") && pa2.contains("lit_offset:0x"),
        "re-encoded pandasm output must also render lit_offset:0x...: {pa2}"
    );
    assert!(
        !pa2.contains("lit_offset:0x0,") && !pa2.contains("lit_offset:0x1,"),
        "re-encoded lit_offset must reverse table index to real file offset: {pa2}"
    );
}

/// Read-only empirical verification against the wild OpenHarmony 4.0 Release
/// `Settings.hap` (`ets/modules.abc`, 3.8 MB) reported in `#32-File`.
/// Ignored by default so `cargo test` stays fast and hermetic when the local
/// wild corpus is absent; run explicitly with `-- --ignored`.
#[test]
#[ignore = "local wild corpus verification; run with --ignored"]
fn wild_ohos40_settings_hap_estype_roundtrip() {
    let hap_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace root")
        .join("exports/corpus/wild/wild-haps/OpenHarmony-4.0-Release/Settings.hap");
    assert!(
        hap_path.exists(),
        "Settings.hap not found at {}",
        hap_path.display()
    );

    let out = Command::new("/usr/bin/unzip")
        .arg("-p")
        .arg(&hap_path)
        .arg("ets/modules.abc")
        .output()
        .expect("spawn unzip -p");
    assert!(out.status.success(), "unzip -p failed");
    let abc_bytes = out.stdout;

    let file1 = decode(&abc_bytes).expect("decode Settings.hap ets/modules.abc");

    let find_on_create_typeof = |file: &abcd_file::File| -> String {
        let cls = file
            .classes
            .values()
            .find(|c| {
                file.strings.resolve(c.descriptor)
                    == Some("Lcom.ohos.settings/phone/ets/Application/AbilityStage;")
            })
            .expect("AbilityStage class in Settings.hap");
        let m = cls
            .methods
            .iter()
            .find(|m| file.strings.resolve(m.name) == Some("onCreate"))
            .expect("onCreate method in AbilityStage");
        let ann = m
            .annotations
            .compile_time
            .iter()
            .chain(m.annotations.runtime.iter())
            .find(|a| file.strings.resolve(a.class_descriptor) == Some("L_ESTypeAnnotation;"))
            .expect("L_ESTypeAnnotation; on AbilityStage::onCreate");
        let elem = ann
            .elements
            .iter()
            .find(|e| file.strings.resolve(e.name) == Some("_TypeOfInstruction"))
            .expect("_TypeOfInstruction element");
        let AnnotationValue::LiteralArray(vals) = &elem.value else {
            panic!("expected AnnotationValue::LiteralArray");
        };
        canon_lit_values(file, vals)
    };

    let before_on_create = find_on_create_typeof(&file1);
    assert!(!before_on_create.is_empty());

    let count_typeof = |file: &abcd_file::File| -> usize {
        file.all_methods()
            .flat_map(|(_, m)| {
                m.annotations
                    .compile_time
                    .iter()
                    .chain(m.annotations.runtime.iter())
            })
            .filter(|a| file.strings.resolve(a.class_descriptor) == Some("L_ESTypeAnnotation;"))
            .count()
    };
    let estype_count_1 = count_typeof(&file1);
    assert!(estype_count_1 > 0);

    let reencoded = encode(&file1).expect("encode unmodified Settings.hap directly");
    let file2 = decode(&reencoded).expect("decode reencoded Settings.hap");
    assert_eq!(count_typeof(&file2), estype_count_1);
    assert_eq!(find_on_create_typeof(&file2), before_on_create);
}
