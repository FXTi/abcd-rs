//! F-new-1 (design/review-bridge-wrapper.md): the bridge baked staged
//! line-number-program operands (SET_FILE / START_LOCAL encode `StringItem`
//! file offsets into the debug constant pool at flush time) against a layout
//! computed BEFORE the staged literal-array items were applied to their
//! `LiteralArrayItem`s (that only happened at finalize). The arrays then
//! grew, shifting every item laid out *after* them in the container's
//! creation-ordered item list and leaving the baked string offsets stale —
//! the P3-era "main.js" -> "n_0" corruption seen when literal arrays were
//! created before classes. The bridge now applies the literal staging before
//! any offset-baking layout pass, so creation order no longer matters.
//!
//! These tests drive the constraint through `abcd_file::encode`: an
//! annotation-embedded literal array is created mid-class-configuration
//! (before the second method's debug strings in the writer's item list), and
//! the second method's SET_FILE must still read its own source-file string
//! after the rewrite.
//!
//! The control additionally pins a companion fix: decode used to
//! surface methods without a debug info item as `source_file:
//! Some("")` (vendored DebugInfoExtractor::GetSourceFile returns ""
//! for missing entries — the N55 invention, since fixed at decode:
//! such methods now get `debug: None`), and counting that invented
//! empty string as content used to emit a degenerate END-only debug
//! item; the vendored extractor then read string offset 0 and threw
//! (file.h GetSpanFromId INVALID_FILE_OFFSET), killing the ENTIRE
//! file's debug region on rewrite. Encode now treats empty debug
//! strings as no content.

use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationValue, Builder, LineEntry, LiteralValue,
    MethodDebugInfo, SourceLang, Type, decode, encode,
};

/// Build the two-method file and rewrite it. With `with_annotation`, m1
/// carries an annotation-embedded literal array that is created
/// mid-class-configuration — before m2's debug strings in the writer's
/// creation-ordered item list — and grows when the staged literal items are
/// applied. m1 deliberately carries no debug info, exercising the
/// decode-invented empty debug guard at the same time.
fn build_and_rewrite(with_annotation: bool) -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    b.class_add_method(cls, "m1", proto, AccessFlags::PUBLIC, &[0x65, 0x65], 1, 0);
    b.class_add_method(cls, "m2", proto, AccessFlags::PUBLIC, &[0x65, 0x65], 1, 0);
    let base = b.finalize().expect("finalize");
    let mut file = decode(&base).expect("decode base");

    let ann_desc = file.strings.get_or_intern("LAnno;");
    let elem_name = file.strings.get_or_intern("v");
    let late_file = file.strings.get_or_intern("late.js");

    let cls = file.classes.values_mut().find(|c| !c.is_external).unwrap();
    let m1_pos = cls
        .methods
        .iter()
        .position(|m| file.strings.resolve(m.name) == Some("m1"))
        .expect("m1 present");
    let m2_pos = cls
        .methods
        .iter()
        .position(|m| file.strings.resolve(m.name) == Some("m2"))
        .expect("m2 present");
    // The hazard requires m1's annotation-embedded array to be created BEFORE
    // m2's debug strings; encode follows cls.methods order, so pin it.
    if m2_pos < m1_pos {
        cls.methods.swap(m1_pos, m2_pos);
    }
    let (m1_pos, m2_pos) = (m1_pos.min(m2_pos), m1_pos.max(m2_pos));
    if with_annotation {
        cls.methods[m1_pos]
            .annotations
            .compile_time
            .push(Annotation {
                class_descriptor: ann_desc,
                elements: vec![AnnotationElem {
                    name: elem_name,
                    value: AnnotationValue::LiteralArray(vec![
                        LiteralValue::Integer(1),
                        LiteralValue::Integer(2),
                        LiteralValue::Integer(3),
                        LiteralValue::Integer(4),
                        LiteralValue::Integer(5),
                        LiteralValue::Integer(6),
                        LiteralValue::Integer(7),
                        LiteralValue::Integer(8),
                    ]),
                }],
            });
    }
    // m2 gets debug info whose source-file string is created only now —
    // after m1's annotation-embedded array in the item list.
    cls.methods[m2_pos].debug = Some(MethodDebugInfo {
        source_file: Some(late_file),
        source_code: None,
        line_table: vec![
            LineEntry { index: 0, line: 7 },
            LineEntry { index: 1, line: 9 },
        ],
        column_table: Vec::new(),
        local_vars: Vec::new(),
        params: Vec::new(),
    });

    let bytes = encode(&file).expect("encode");
    decode(&bytes).expect("decode rewritten")
}

fn source_file_of(file: &abcd_file::File, method: &str) -> Option<String> {
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let m = g
        .methods
        .iter()
        .find(|m| file.strings.resolve(m.name) == Some(method))
        .unwrap_or_else(|| panic!("{method} present"));
    let dbg = m
        .debug
        .as_ref()
        .unwrap_or_else(|| panic!("{method} debug info preserved"));
    dbg.source_file
        .and_then(|sf| file.strings.resolve(sf))
        .map(str::to_owned)
}

/// Control: without the annotation-embedded array, m2's SET_FILE roundtrips
/// (and m1's debug-less state must not poison the file's debug region).
#[test]
fn set_file_roundtrips_without_literal_array() {
    let file2 = build_and_rewrite(false);
    assert_eq!(source_file_of(&file2, "m2").as_deref(), Some("late.js"));
    let g = file2.classes.values().find(|c| !c.is_external).unwrap();
    let m1 = g
        .methods
        .iter()
        .find(|m| file2.strings.resolve(m.name) == Some("m1"))
        .expect("m1 present");
    assert!(
        m1.debug.is_none(),
        "m1 never had debug info; since the N55 decode fix, rewrite must \
         surface it as debug: None (no invented record), got {:?}",
        m1.debug.as_ref().map(|d| d.source_file)
    );
}

/// F-new-1: with an annotation-embedded array created before m2's debug
/// strings, the baked SET_FILE operand must still track "late.js" after the
/// literal array grows.
#[test]
fn set_file_offset_survives_literal_array_growth() {
    assert_eq!(
        source_file_of(&build_and_rewrite(true), "m2").as_deref(),
        Some("late.js")
    );
}
