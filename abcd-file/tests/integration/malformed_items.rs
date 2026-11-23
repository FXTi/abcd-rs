//! Test group H — malformed input per item kind: pointers into the class
//! index table, the literal-array table, and the LNP index table are
//! redirected or corrupted; decode must return Ok/Err without aborting.

use abcd_file::{AccessFlags, Builder, SourceLang, Type, decode};

fn build() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let f = b.class_add_field(cls, "fx", Type::I32, AccessFlags::PUBLIC);
    b.field_set_value_i32(f, 42);
    let la = b.add_literal_array("s");
    b.literal_array_add_integer(la, 7);
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

    // Debug info so the LNP table is non-empty.
    let lnp = b.create_lnp();
    let debug = b.create_debug_info(lnp, 1);
    let src = b.add_string("m.js");
    b.lnp_emit_set_file(lnp, debug, src);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m, debug);

    b.finalize().expect("finalize")
}

fn header_field(data: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(data[offset..offset + 4].try_into().unwrap())
}

#[test]
fn class_index_pointing_past_end_does_not_abort() {
    let mut data = build();
    let class_idx_off = header_field(&data, 32) as usize;
    let big = data.len() as u32 - 2; // inside the file, past any item
    data[class_idx_off..class_idx_off + 4].copy_from_slice(&big.to_le_bytes());
    let _ = decode(&data); // Ok or Err, never abort
}

#[test]
fn class_index_pointing_into_header_does_not_abort() {
    let mut data = build();
    let class_idx_off = header_field(&data, 32) as usize;
    data[class_idx_off..class_idx_off + 4].copy_from_slice(&4u32.to_le_bytes());
    let _ = decode(&data);
}

#[test]
fn literal_array_count_huge_does_not_abort() {
    let mut data = build();
    let lit_idx_off = header_field(&data, 48) as usize;
    let array_off = header_field(&data, lit_idx_off) as usize;
    data[array_off..array_off + 4].copy_from_slice(&0xFFFF_FFF0u32.to_le_bytes());
    let result = decode(&data);
    assert!(
        result.is_ok(),
        "huge count must stop the walk, decode succeeds"
    );
}

#[test]
fn lnp_index_pointing_past_end_does_not_abort() {
    let mut data = build();
    let lnp_idx_off = header_field(&data, 40) as usize;
    let big = (data.len() - 2) as u32;
    data[lnp_idx_off..lnp_idx_off + 4].copy_from_slice(&big.to_le_bytes());
    let _ = decode(&data);
}

#[test]
fn corrupted_method_tag_stream_does_not_abort() {
    // Overwrite a byte run inside the file body (after the index tables)
    // with 0xFF tags — walks must stop, not crash.
    let mut data = build();
    let class_idx_off = header_field(&data, 32) as usize;
    let class_off = header_field(&data, class_idx_off) as usize;
    for i in class_off..(class_off + 16).min(data.len()) {
        data[i] = 0xFF;
    }
    let _ = decode(&data);
}

#[test]
fn foreign_region_garbage_does_not_abort() {
    let mut data = build();
    // Corrupt foreign_off/size to overlap the header.
    let len = data.len() as u32;
    data[20..24].copy_from_slice(&0u32.to_le_bytes());
    data[24..28].copy_from_slice(&len.to_le_bytes());
    let _ = decode(&data);
}
