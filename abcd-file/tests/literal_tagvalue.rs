//! Regression tests for audit finding #A1: the vendor literal-array
//! enumerator aborts (`UNREACHABLE`) on tag 0x00 (TAGVALUE / INTEGER_8),
//! which real 12.x files contain. The bridge now walks [tag][value] pairs
//! tolerantly: tag 0x00 is a one-byte integer, reads are bounded, and
//! unknown tags stop the walk instead of aborting.

use abcd_file::{AccessFlags, Builder, LiteralValue, SourceLang, Type, decode};

/// Build a minimal file with one literal array and return (bytes, array_offset).
fn build_with_literal_array() -> (Vec<u8>, usize) {
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

    let la = b.add_literal_array("s");
    b.literal_array_add_u8(la, 0x2a); // placeholder, patched below

    let data = b.finalize().expect("finalize");
    // Header layout: magic(8) checksum(4) version(4) file_size(4)
    // foreign_off(4) foreign_size(4) num_classes(4) class_idx_off(4)
    // num_lnps(4) lnp_idx_off(4) num_literalarrays(4) literalarray_idx_off(4)
    let literalarray_idx_off = u32::from_le_bytes(data[48..52].try_into().unwrap()) as usize;
    let array_off = u32::from_le_bytes(
        data[literalarray_idx_off..literalarray_idx_off + 4]
            .try_into()
            .unwrap(),
    ) as usize;
    (data, array_off)
}

#[test]
fn tagvalue_integer8_literal_decodes() {
    let (mut data, array_off) = build_with_literal_array();
    // Rewrite the array as: count=2, tag=0x00 (TAGVALUE), value=0x2a.
    data[array_off..array_off + 6].copy_from_slice(&[2, 0, 0, 0, 0x00, 0x2a]);

    let file = decode(&data).expect("decode with TAGVALUE literal");
    let la = &file.literal_arrays[0];
    assert_eq!(la.values, vec![LiteralValue::Integer8(0x2a)]);
}

#[test]
fn unknown_literal_tag_stops_without_abort() {
    let (mut data, array_off) = build_with_literal_array();
    // count=2, unknown tag 0xee, value 0x01: must not abort, walk stops.
    data[array_off..array_off + 6].copy_from_slice(&[2, 0, 0, 0, 0xee, 0x01]);

    let file = decode(&data).expect("decode with unknown literal tag");
    assert!(file.literal_arrays[0].values.is_empty());
}

#[test]
fn truncated_literal_pair_stops_without_abort() {
    let (mut data, array_off) = build_with_literal_array();
    // count=4 claims two pairs but only one tag byte exists.
    data[array_off..array_off + 5].copy_from_slice(&[4, 0, 0, 0, 0x00]);

    // The array has no length field: the walk cannot detect truncation by
    // itself, it can only stay in bounds and stop. Assert the decode
    // succeeds and never yields more values than the claimed pair count.
    let file = decode(&data).expect("decode with truncated literal pair");
    assert!(file.literal_arrays[0].values.len() <= 2);
}
