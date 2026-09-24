//! N8 regression: a field named `typeSummaryOffset` must FAIL decode
//! with a dedicated hard error — never a silent `FieldValue::I32`
//! pass-through, never a mis-routed module-data decode.
//!
//! Vendor facts:
//! - `TYPE_SUMMARY_FIELD_NAME = "typeSummaryOffset"`
//!   (abcd-file-sys/arkcompiler_runtime_core/libpandabase/include/libpandabase/utils/const_value.h:25) sits
//!   beside `SCOPE_NAME_RECORD` / `MODULE_REQUEST_PAHSE_IDX` — it is a
//!   module-record field name.
//! - Its value is a NESTED file offset (it points to a literal array
//!   whose elements are themselves offsets) — arkcompiler_runtime_core
//!   docs/changelogs/2022-08-18-isa-changelog.md item 5.
//! - No producer (es2panda never emits it), no runtime consumer
//!   (`TYPE_SUMMARY_OFFSET_NOT_FOUND` is a dead constant), the
//!   disassembler excludes it (disassembler.cpp:1009), and the corpus
//!   has zero occurrences.
//!
//! The rewriter has no relocation support for the nested indirection,
//! so decode must refuse loudly instead of landing a raw scalar that a
//! rewrite would leave dangling (maintainer ruling 2026-09-20, N8:
//! hard error, never a warning, never silent pass-through).

use abcd_file::{AccessFlags, Builder, SourceLang, Type, decode};

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

/// The silent pass-through the ruling forbids: a u32 field named
/// `typeSummaryOffset` on an ordinary record decodes today as a raw
/// `FieldValue::I32` — a rewrite would leave the nested offset
/// dangling.
#[test]
fn type_summary_offset_scalar_is_hard_error() {
    let data = build(|b| {
        let cls = b.add_class("LTest;");
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let f = b.class_add_field(cls, "typeSummaryOffset", Type::U32, AccessFlags::PUBLIC);
        b.field_set_value_i32(f, 0x40);
    });
    let err = decode(&data).expect_err("typeSummaryOffset must fail decode (N8)");
    assert!(
        matches!(err, abcd_file::Error::TypeSummaryOffset { .. }),
        "dedicated N8 variant, got: {err:?}"
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

/// Upstream attaches the field to the module record itself, where the
/// `_ESModuleRecord` catch-all u32 arm would otherwise mis-route the
/// value into the module-data blob decoder. The name guard must win.
#[test]
fn type_summary_offset_on_module_record_class_is_hard_error() {
    let data = build(|b| {
        let cls = b.add_class("L_ESModuleRecord;");
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let f = b.class_add_field(cls, "typeSummaryOffset", Type::U32, AccessFlags::PUBLIC);
        b.field_set_value_i32(f, 0x40);
    });
    let err = decode(&data)
        .expect_err("typeSummaryOffset on _ESModuleRecord must fail decode with the N8 error");
    assert!(
        matches!(err, abcd_file::Error::TypeSummaryOffset { .. }),
        "dedicated N8 variant, got: {err:?}"
    );
    assert!(
        err.to_string().contains("typeSummaryOffset"),
        "must be the dedicated N8 error, not a module-data mis-decode: {err}"
    );
}

/// The name alone is enough — a valueless field of that name still
/// names a payload layout we cannot relocate.
#[test]
fn type_summary_offset_without_value_is_hard_error() {
    let data = build(|b| {
        let cls = b.add_class("LTest;");
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        b.class_add_field(cls, "typeSummaryOffset", Type::U32, AccessFlags::PUBLIC);
    });
    let err = decode(&data).expect_err("valueless typeSummaryOffset must fail decode (N8)");
    assert!(
        matches!(err, abcd_file::Error::TypeSummaryOffset { .. }),
        "dedicated N8 variant, got: {err:?}"
    );
    assert!(
        err.to_string().contains("typeSummaryOffset"),
        "error must name the field: {err}"
    );
}
