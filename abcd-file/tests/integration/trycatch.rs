//! Test group B — try/catch blocks: multi-catch, catch-all, nested try
//! regions, and handler ranges surviving the round-trip.

use abcd_file::{AccessFlags, Builder, CatchBlockDef, SourceLang, Type, decode};

fn build(
    code: &[u8],
    configure: impl FnOnce(&mut Builder, abcd_file::CodeHandle, abcd_file::ClassHandle),
) -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let err = b.add_foreign_class("LError;");

    let code_h = b.create_code(code, 4, 1);
    configure(&mut b, code_h, err);

    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(cls, "func_main_0", proto, AccessFlags::PUBLIC, code, 4, 1);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.method_set_code(m, code_h);
    b.finalize().expect("finalize")
}

#[test]
fn multi_catch_and_catch_all_roundtrip() {
    let code = [0x65, 0x65, 0x65, 0x65]; // returnundefined x4
    let data = build(&code, |b, code_h, err| {
        b.code_add_try_block(
            code_h,
            0,
            2,
            &[
                CatchBlockDef {
                    type_class: Some(err),
                    handler_pc: 2,
                    code_size: 1,
                },
                CatchBlockDef {
                    type_class: None, // catch-all
                    handler_pc: 3,
                    code_size: 1,
                },
            ],
        );
    });

    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let body = g.methods[0].body.as_ref().expect("body");
    assert_eq!(body.try_blocks.len(), 1);

    let tb = &body.try_blocks[0];
    assert_eq!((tb.start, tb.len), (0, 2));
    assert_eq!(tb.catches.len(), 2);

    let typed = &tb.catches[0];
    assert_ne!(
        typed.type_idx,
        u32::MAX,
        "typed catch must reference a class"
    );
    assert_eq!((typed.handler, typed.len), (2, 1));

    let catch_all = &tb.catches[1];
    assert_eq!(
        catch_all.type_idx,
        u32::MAX,
        "catch-all decodes as type index UINT32_MAX (stored 0 minus 1)"
    );
    assert_eq!((catch_all.handler, catch_all.len), (3, 1));
}

#[test]
fn nested_try_regions_roundtrip() {
    let code = [0x65, 0x65, 0x65, 0x65, 0x65, 0x65];
    let data = build(&code, |b, code_h, err| {
        b.code_add_try_block(
            code_h,
            0,
            5,
            &[CatchBlockDef {
                type_class: Some(err),
                handler_pc: 5,
                code_size: 1,
            }],
        );
        b.code_add_try_block(
            code_h,
            1,
            2,
            &[CatchBlockDef {
                type_class: None,
                handler_pc: 4,
                code_size: 1,
            }],
        );
    });

    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let body = g.methods[0].body.as_ref().expect("body");
    assert_eq!(body.try_blocks.len(), 2, "nested regions must both survive");

    let outer = &body.try_blocks[0];
    assert_eq!((outer.start, outer.len), (0, 5));
    assert_eq!(outer.catches.len(), 1);
    assert_eq!((outer.catches[0].handler, outer.catches[0].len), (5, 1));

    let inner = &body.try_blocks[1];
    assert_eq!((inner.start, inner.len), (1, 2));
    assert_eq!(inner.catches.len(), 1);
    assert_eq!(
        inner.catches[0].type_idx,
        u32::MAX,
        "inner catch is catch-all"
    );
    assert_eq!((inner.catches[0].handler, inner.catches[0].len), (4, 1));
}

#[test]
fn try_blocks_survive_encode_roundtrip() {
    let code = [0x65, 0x65, 0x65, 0x65];
    let data = build(&code, |b, code_h, err| {
        b.code_add_try_block(
            code_h,
            0,
            2,
            &[
                CatchBlockDef {
                    type_class: Some(err),
                    handler_pc: 2,
                    code_size: 1,
                },
                CatchBlockDef {
                    type_class: None,
                    handler_pc: 3,
                    code_size: 1,
                },
            ],
        );
    });

    let file1 = decode(&data).expect("first decode");
    let encoded = abcd_file::encode(&file1).expect("encode");
    let file2 = decode(&encoded).expect("second decode");
    let g2 = file2.classes.values().find(|c| !c.is_external).unwrap();
    let body2 = g2.methods[0].body.as_ref().expect("body after round-trip");

    assert_eq!(body2.try_blocks.len(), 1);
    let tb = &body2.try_blocks[0];
    assert_eq!((tb.start, tb.len), (0, 2));
    assert_eq!(tb.catches.len(), 2);
    assert_ne!(tb.catches[0].type_idx, u32::MAX);
    assert_eq!((tb.catches[0].handler, tb.catches[0].len), (2, 1));
    assert_eq!(tb.catches[1].type_idx, u32::MAX);
    assert_eq!((tb.catches[1].handler, tb.catches[1].len), (3, 1));
}
