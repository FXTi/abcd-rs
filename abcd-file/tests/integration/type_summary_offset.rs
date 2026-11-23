//! typeSummaryOffset field handling (N8, revised after the wild-OHOS sweep).
//!
//! Vendor facts:
//! - `TYPE_SUMMARY_FIELD_NAME = "typeSummaryOffset"`
//!   (abcd-file-sys/arkcompiler_runtime_core/libpandabase/include/libpandabase/utils/const_value.h:25).
//! - Its value is a NESTED file offset (it points to a literal array
//!   whose elements are themselves offsets) — arkcompiler_runtime_core
//!   docs/changelogs/2022-08-18-isa-changelog.md item 5 ("The literalarray
//!   which is referenced by TypeSummary contains the offsets of all
//!   type-literalarray").
//! - The 2026-09-20 "no upstream producer" assumption is WILD-DISPROVED:
//!   4.x–5.x-era es2abc emits the field on AbilityStage/Application
//!   classes (219/512 wild OpenHarmony haps carry it, 94 distinct offset
//!   variants across 4.0→5.1).
//!
//! Contract (decode unlocked, write side stays honest):
//! - Decode reads the u32 value as a fact and models it as
//!   `FieldValue::TypeSummaryOffset` — an opaque source-file offset, never
//!   a mis-routed module-data decode, never a bare `FieldValue::I32` that
//!   would look like a scalar constant.
//! - Encode/rewrite still HARD-ERRORS: the value is a nested file offset
//!   and the rewriter has no relocation support for the indirection, so a
//!   rewrite must not silently emit a dangling offset.

use abcd_file::{AccessFlags, Builder, FieldValue, SourceLang, Type, decode, encode};

/// Build a minimal well-formed file (global class + entry method) and
/// let `configure` add the class under test.
fn build(configure: impl FnOnce(&mut Builder)) -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    configure(&mut b);
    let global = b.add_global_class();
    b.class_set_source_lang(global, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        global,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65], // returnundefined
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.finalize().expect("finalize")
}

/// A u32 field named `typeSummaryOffset` on an ordinary record (the wild
/// shape: es2abc hangs it on AbilityStage/Application classes) decodes to
/// the opaque source-file offset.
#[test]
fn type_summary_offset_decodes_as_opaque_offset() {
    let data = build(|b| {
        let cls = b.add_class("LTest;");
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let f = b.class_add_field(cls, "typeSummaryOffset", Type::U32, AccessFlags::PUBLIC);
        b.field_set_value_i32(f, 0x40);
    });
    let file = decode(&data).expect("typeSummaryOffset must decode");
    let cls = file
        .classes
        .values()
        .find(|c| file.strings.resolve(c.descriptor) == Some("LTest;"))
        .expect("LTest; class");
    let field = cls
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("typeSummaryOffset"))
        .expect("typeSummaryOffset field");
    assert!(
        matches!(
            &field.initial_value,
            Some(FieldValue::TypeSummaryOffset(0x40))
        ),
        "value must surface as the opaque-offset model, got {:?}",
        field.initial_value
    );
}

/// Upstream attaches the field to the module record itself in some
/// producers; the name guard must win over the `_ESModuleRecord` catch-all
/// u32 arm so the value is not mis-routed into the module-data blob
/// decoder.
#[test]
fn type_summary_offset_on_module_record_class_decodes() {
    let data = build(|b| {
        let cls = b.add_class("L_ESModuleRecord;");
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let f = b.class_add_field(cls, "typeSummaryOffset", Type::U32, AccessFlags::PUBLIC);
        b.field_set_value_i32(f, 0x40);
    });
    let file = decode(&data).expect("typeSummaryOffset on _ESModuleRecord must decode");
    let cls = file
        .classes
        .values()
        .find(|c| file.strings.resolve(c.descriptor) == Some("L_ESModuleRecord;"))
        .expect("_ESModuleRecord class");
    let field = cls
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("typeSummaryOffset"))
        .expect("typeSummaryOffset field");
    assert!(
        matches!(
            &field.initial_value,
            Some(FieldValue::TypeSummaryOffset(0x40))
        ),
        "name guard must win over the module-data catch-all, got {:?}",
        field.initial_value
    );
}

/// A valueless field of that name carries no offset, so nothing can
/// dangle: decode keeps it with no initial value.
#[test]
fn type_summary_offset_without_value_decodes() {
    let data = build(|b| {
        let cls = b.add_class("LTest;");
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        b.class_add_field(cls, "typeSummaryOffset", Type::U32, AccessFlags::PUBLIC);
    });
    let file = decode(&data).expect("valueless typeSummaryOffset must decode");
    let cls = file
        .classes
        .values()
        .find(|c| file.strings.resolve(c.descriptor) == Some("LTest;"))
        .expect("LTest; class");
    let field = cls
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("typeSummaryOffset"))
        .expect("typeSummaryOffset field");
    assert_eq!(field.initial_value, None, "valueless field stays valueless");
}

/// Write side stays honest: a decoded file carrying the field cannot be
/// rewritten (the nested offset would dangle), so encode fails loudly
/// instead of emitting bad bytes.
#[test]
fn type_summary_offset_rewrite_is_hard_error() {
    let data = build(|b| {
        let cls = b.add_class("LTest;");
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let f = b.class_add_field(cls, "typeSummaryOffset", Type::U32, AccessFlags::PUBLIC);
        b.field_set_value_i32(f, 0x40);
    });
    let file = decode(&data).expect("decode must succeed before rewrite is attempted");
    let err = encode(&file).expect_err("rewrite of typeSummaryOffset must fail (write side)");
    assert!(
        matches!(err, abcd_file::Error::TypeSummaryOffset { .. }),
        "dedicated variant, got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("typeSummaryOffset"),
        "error must name the field: {msg}"
    );
    assert!(
        msg.contains("2022-08-18"),
        "error must cite the ISA changelog: {msg}"
    );
}
