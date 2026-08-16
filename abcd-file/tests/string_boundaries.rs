//! Test group G — string boundaries: empty strings, long strings (multi-
//! byte ULEB length), the ASCII fast-path flag, astral characters, and the
//! MUTF-8 C0 80 encoding of embedded NUL (patched into the file, since the
//! builder API takes C strings and cannot express embedded NUL).

use abcd_file::{AccessFlags, Builder, SourceLang, Type, decode};

#[test]
fn empty_and_long_strings_roundtrip() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);

    let empty = b.add_string("");
    let long_ascii = b.add_string(&"a".repeat(300)); // multi-byte ULEB length
    let long_unicode = b.add_string(&"中".repeat(200));
    let mixed = b.add_string("ascii + 中文 + 😀");

    let la = b.add_literal_array("s");
    b.literal_array_add_string(la, empty);
    b.literal_array_add_string(la, long_ascii);
    b.literal_array_add_string(la, long_unicode);
    b.literal_array_add_string(la, mixed);

    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(cls, "f", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);

    let data = b.finalize().expect("finalize");
    let file = decode(&data).expect("decode");
    let values = &file.literal_arrays[0].values;
    assert_eq!(values.len(), 4);
    let resolve = |i: usize| -> String {
        match &values[i] {
            abcd_file::LiteralValue::String(sid) => file.strings.resolve(*sid).unwrap().to_string(),
            other => panic!("expected String, got {other:?}"),
        }
    };
    assert_eq!(resolve(0), "");
    assert_eq!(resolve(1), "a".repeat(300));
    assert_eq!(resolve(2), "中".repeat(200));
    assert_eq!(resolve(3), "ascii + 中文 + 😀");
}

#[test]
fn embedded_nul_decodes_via_c0_80() {
    // The MUTF-8 encoding of U+0000 is the two-byte sequence C0 80, so a
    // string can contain a NUL without terminating the C view. The builder
    // cannot express it (C-string API), so patch the method-name string
    // item in place: "a\0b" -> 'a' C0 80 'b'.
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(cls, "f", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let data = b.finalize().expect("finalize");

    // Locate the method item via the class's method stream: class offset
    // from the class index table, then method is inline after the class
    // header. Easier: the method name string offset is a u32 at
    // (method_off + 4); find the method offset through the index section
    // is complex — instead, scan for the method name string "f\0" pattern
    // is fragile. Use the bridge's static accessor through decode-side
    // knowledge: the only string containing exactly "f" at offset > header
    // is the method name; we locate it by scanning for the ULEB tag
    // (2<<1|1 = 5) followed by 'f' 0x00.
    let mut patched: Vec<u8> = Vec::new();
    let mut i = 60usize;
    let mut found = false;
    while i + 4 < data.len() {
        // candidate string item: tag = (1<<1)|0 or ascii flag variants
        let tag = data[i];
        let utf16_len = tag >> 1;
        let is_ascii = tag & 1;
        if is_ascii == 1 && utf16_len == 1 && data[i + 1] == b'f' && data[i + 2] == 0 {
            // rewrite: 'a' C0 80 'b' — utf16 len 3, not ascii: tag = 3<<1 = 6
            let new_item = vec![6u8, b'a', 0xC0, 0x80, b'b', 0x00];
            let mut tmp: Vec<u8> = Vec::new();
            tmp.extend_from_slice(&data[..i]);
            tmp.extend_from_slice(&new_item);
            tmp.extend_from_slice(&data[i + 4..]);
            patched = tmp;
            found = true;
            break;
        }
        i += 1;
    }
    assert!(found, "method name string item not found");

    let file = decode(&patched).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let name = file.strings.resolve(g.methods[0].name).unwrap();
    assert_eq!(name, "a\0b", "embedded NUL must decode via C0 80");
}
