//! Regression tests for review finding #5 (MUTF-8 strings were converted
//! lossily; NUL, surrogate pairs, and astral characters corrupted to U+FFFD)
//! and for the literal-array `[tag][value]` pair layout they exposed.

use abcd_file::{AccessFlags, Builder, LiteralValue, SourceLang, Type, decode};

#[test]
fn non_ascii_strings_decode_losslessly() {
    let zh = "中文测试";
    let astral = "emoji \u{1F600} and \u{1D11E}"; // 😀 and 𝄞 (astral plane)
    let mixed = "caf\u{E9} \u{2603}"; // é and ☃ (BMP beyond ASCII)

    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);

    // Strings travel through the builder's UTF-8 → MUTF-8 conversion and
    // must come back out through MUTF-8 → UTF-16 losslessly. The literal
    // array mixes strings with scalar literals to also pin down the
    // `[tag][value]` pair layout of the section.
    let la = b.add_literal_array("s");
    let zh_h = b.add_string(zh);
    b.literal_array_add_string(la, zh_h);
    let astral_h = b.add_string(astral);
    b.literal_array_add_string(la, astral_h);
    let mixed_h = b.add_string(mixed);
    b.literal_array_add_string(la, mixed_h);
    b.literal_array_add_bool(la, true);
    b.literal_array_add_integer(la, 7);

    // A method with a non-ASCII name.
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(cls, zh, proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);

    let data = b.finalize().expect("finalize");
    let file = decode(&data).expect("decode");

    let values = &file.literal_arrays.first().unwrap().values;
    assert_eq!(
        values[0..3]
            .iter()
            .map(|v| match v {
                LiteralValue::String(sid) => Some(file.strings.resolve(*sid).unwrap()),
                _ => None,
            })
            .collect::<Vec<_>>(),
        vec![Some(zh), Some(astral), Some(mixed)]
    );
    assert_eq!(values[3], LiteralValue::Bool(true));
    assert_eq!(values[4], LiteralValue::Integer(7));

    // Method name round-trips as well.
    let global = file.classes.values().find(|c| !c.is_external).unwrap();
    let method_name = file.strings.resolve(global.methods[0].name).unwrap();
    assert_eq!(method_name, zh);
}
