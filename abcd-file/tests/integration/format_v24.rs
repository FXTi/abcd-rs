//! Regression tests for audit finding #A2: 24.0.0.0 files store
//! INVALID_INDEX in the header's literal-array fields (the array table
//! moved out of the header); the bridge must report zero arrays instead of
//! 0xFFFFFFFF so decode never iterates a bogus table.

use abcd_file::{AccessFlags, Builder, SourceLang, Type, decode};

#[test]
fn v24_file_decodes_without_bogus_literal_table() {
    let mut b = Builder::new();
    b.set_api(24, "beta1");
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
    b.literal_array_add_integer(la, 42);

    let data = b.finalize().expect("finalize");
    assert_eq!(&data[12..16], &[24, 0, 0, 0], "builder must write 24.0.0.0");

    // Must decode (pre-fix this ran a 4-billion-iteration loop), and the
    // global literal-array list is empty by format design.
    let file = decode(&data).expect("decode v24 file");
    assert!(file.literal_arrays.is_empty());
    assert_eq!(file.classes.len(), 1);
    let cls_dec = file.classes.values().find(|c| !c.is_external).unwrap();
    assert!(cls_dec.methods[0].body.is_some());
}
