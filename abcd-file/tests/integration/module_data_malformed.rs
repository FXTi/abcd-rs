//! Malformed module-data literal streams: the `ModuleData` cursor helpers
//! must fail loudly with `Error::Malformed` on truncated input and on
//! wrong-typed elements (the tagged pandasm-level representation is parsed
//! by `ModuleData::from_literal_values`; on-disk blobs are untagged).

use abcd_file::{Error, LiteralValue, ModuleData};

fn sid() -> abcd_file::StringId {
    let mut pool = abcd_file::StringPool::default();
    pool.get_or_intern("x")
}

/// Truncated stream: the cursor runs out of values mid-header and
/// mid-record.
#[test]
fn truncated_module_data_is_hard_error() {
    // Empty: no module_requests_count.
    let err = ModuleData::from_literal_values(&[]).expect_err("empty stream must fail");
    assert!(
        matches!(err, Error::Malformed { field: "module_data", ref context } if context.contains("unexpected end at module_requests_count")),
        "unexpected error: {err:?}"
    );

    // One request declared but absent.
    let err = ModuleData::from_literal_values(&[LiteralValue::Integer(1)])
        .expect_err("truncated request must fail");
    assert!(
        matches!(err, Error::Malformed { field: "module_data", ref context } if context.contains("unexpected end at module_request")),
        "unexpected error: {err:?}"
    );

    // Truncated inside a regular-import record (missing module_idx).
    let s = sid();
    let err = ModuleData::from_literal_values(&[
        LiteralValue::Integer(0), // 0 requests
        LiteralValue::Integer(1), // 1 regular import
        LiteralValue::String(s),  // local_name
        LiteralValue::String(s),  // import_name
    ])
    .expect_err("truncated regular import must fail");
    assert!(
        matches!(err, Error::Malformed { field: "module_data", ref context } if context.contains("unexpected end at regular_import.module_idx")),
        "unexpected error: {err:?}"
    );
}

/// Wrong-typed elements: each cursor helper rejects the wrong literal kind
/// with a Malformed error naming the context.
#[test]
fn wrong_typed_module_data_is_hard_error() {
    let s = sid();

    // read_u32: String where Integer is expected.
    let err = ModuleData::from_literal_values(&[LiteralValue::String(s)])
        .expect_err("non-Integer count must fail");
    assert!(
        matches!(err, Error::Malformed { field: "module_data", ref context } if context.contains("expected Integer for module_requests_count")),
        "unexpected error: {err:?}"
    );

    // read_string_id: Integer where String is expected.
    let err = ModuleData::from_literal_values(&[
        LiteralValue::Integer(0), // 0 requests
        LiteralValue::Integer(1), // 1 regular import
        LiteralValue::Integer(5), // local_name: not a String
    ])
    .expect_err("non-String name must fail");
    assert!(
        matches!(err, Error::Malformed { field: "module_data", ref context } if context.contains("expected String for regular_import.local_name")),
        "unexpected error: {err:?}"
    );

    // read_u16: Integer where MethodAffiliate is expected.
    let err = ModuleData::from_literal_values(&[
        LiteralValue::Integer(0), // 0 requests
        LiteralValue::Integer(1), // 1 regular import
        LiteralValue::String(s),  // local_name
        LiteralValue::String(s),  // import_name
        LiteralValue::Integer(0), // module_idx: not a MethodAffiliate
    ])
    .expect_err("non-MethodAffiliate index must fail");
    assert!(
        matches!(err, Error::Malformed { field: "module_data", ref context } if context.contains("expected MethodAffiliate for regular_import.module_idx")),
        "unexpected error: {err:?}"
    );
}
