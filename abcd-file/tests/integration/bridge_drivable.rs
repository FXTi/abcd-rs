//! Safe-layer drivers for the remaining drivable bridge arms (c-COV W11):
//! the direct (post-`method_set_code`) try-block path and the pending-block
//! skip, method-handle field-op/foreign-entity arms, the foreign-field
//! relocation arm, the `GetFileType` short/bad-magic branches, the
//! `abc_class_get_descriptor` raw fallback, and the runtime/type
//! annotation-bucket decode callbacks (reached by patching the vendored
//! single-bucket writer output into the other buckets' tag positions).

use abcd_file::{
    AccessFlags, AnnotationElemDefEx, AnnotationElemValue, AnnotationValue, Builder, CatchBlockDef,
    CodeEntity, Error, MethodHandleType, SourceLang, Type, decode, file_type,
};
use abcd_file_sys::FileType;

/// Build a file whose global class carries one method with inline code and
/// returns the builder handles needed by the try-block tests.
fn base_builder(code: &[u8]) -> (Builder, abcd_file::ClassHandle) {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(cls, "func_main_0", proto, AccessFlags::PUBLIC, code, 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    (b, cls)
}

/// The direct `code_add_try_block` path: the try block is staged AFTER
/// `method_set_code`, so the bridge builds the CatchBlocks immediately
/// (owner known) instead of deferring through the pending queue.
#[test]
fn try_block_added_after_set_code_roundtrip() {
    let code = [0x65, 0x65, 0x65, 0x65]; // returnundefined x4
    let (mut b, cls) = base_builder(&code);
    let err = b.add_foreign_class("LError;");
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(cls, "direct", proto, AccessFlags::PUBLIC, &code, 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);

    let code_h = b.create_code(&code, 1, 0);
    b.method_set_code(m, code_h);
    // Owner attached: this takes the direct construction arm.
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
    let data = b.finalize().expect("finalize");
    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let m = g
        .methods
        .iter()
        .find(|m| file.strings.resolve(m.name) == Some("direct"))
        .expect("method direct");
    let body = m.body.as_ref().expect("body");
    assert_eq!(body.try_blocks.len(), 1);
    let tb = &body.try_blocks[0];
    assert_eq!((tb.start, tb.len), (0, 2));
    assert_eq!(tb.catches.len(), 2);
    assert_ne!(tb.catches[0].type_idx, u32::MAX, "typed catch got an index");
    assert_eq!((tb.catches[0].handler, tb.catches[0].len), (2, 1));
    assert_eq!(tb.catches[1].type_idx, u32::MAX, "catch-all");
}

/// The pending-queue skip arm: a try block staged on code item A is NOT
/// flushed when an unrelated code item B is attached first; it flushes when
/// A's owner is attached.
#[test]
fn pending_try_block_flushes_only_for_owning_code() {
    let code = [0x65, 0x65];
    let (mut b, cls) = base_builder(&code);
    let err = b.add_foreign_class("LError;");
    let proto = b.create_proto(Type::Tagged, &[]);
    let m1 = b.class_add_method(cls, "m_one", proto, AccessFlags::PUBLIC, &code, 1, 0);
    b.method_set_source_lang(m1, SourceLang::EcmaScript);
    let m2 = b.class_add_method(cls, "m_two", proto, AccessFlags::PUBLIC, &code, 1, 0);
    b.method_set_source_lang(m2, SourceLang::EcmaScript);

    let code_a = b.create_code(&code, 1, 0);
    let code_b = b.create_code(&code, 1, 0);
    // Stage the try block on A while A has no owner (pending queue).
    b.code_add_try_block(
        code_a,
        0,
        1,
        &[CatchBlockDef {
            type_class: Some(err),
            handler_pc: 1,
            code_size: 1,
        }],
    );
    // Attaching B first must skip A's pending entry (the skip arm).
    b.method_set_code(m1, code_b);
    b.method_set_code(m2, code_a);

    let data = b.finalize().expect("finalize");
    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let by_name = |name: &str| {
        g.methods
            .iter()
            .find(|m| file.strings.resolve(m.name) == Some(name))
            .unwrap_or_else(|| panic!("method {name}"))
            .body
            .as_ref()
            .expect("body")
            .try_blocks
            .len()
    };
    assert_eq!(by_name("m_one"), 0, "code B carries no try block");
    assert_eq!(by_name("m_two"), 1, "the pending block flushed onto A");
}

/// Method handles of every operation type over regular AND foreign
/// entities: field ops 0-3 (two over a regular field, two over a foreign
/// field) and method ops 4-8 (two over a regular method, three over a
/// foreign method). Drives the bridge's foreign-entity resolution arms and
/// round-trips through decode.
#[test]
fn method_handle_field_ops_and_foreign_entities_roundtrip() {
    let (mut b, cls) = base_builder(&[0x65]);
    let fld = b.class_add_field(cls, "f0field", Type::I32, AccessFlags::PUBLIC);
    let proto = b.create_proto(Type::Tagged, &[]);
    let target = b.class_add_method(cls, "mmethod", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(target, SourceLang::EcmaScript);
    let fcls = b.add_foreign_class("LForeign;");
    let ff = b.add_foreign_field(fcls, "ff", Type::I32);
    let fm = b.add_foreign_method(fcls, "fm", proto, AccessFlags::PUBLIC);

    let defs: [(u8, u32, &str); 9] = [
        (MethodHandleType::PutStatic as u8, fld.as_raw(), "f0field"),
        (MethodHandleType::GetStatic as u8, fld.as_raw(), "f0field"),
        (MethodHandleType::PutInstance as u8, ff.as_raw(), "ff"),
        (MethodHandleType::GetInstance as u8, ff.as_raw(), "ff"),
        (
            MethodHandleType::InvokeStatic as u8,
            target.as_raw(),
            "mmethod",
        ),
        (
            MethodHandleType::InvokeInstance as u8,
            target.as_raw(),
            "mmethod",
        ),
        (MethodHandleType::InvokeConstructor as u8, fm.as_raw(), "fm"),
        (MethodHandleType::InvokeDirect as u8, fm.as_raw(), "fm"),
        (MethodHandleType::InvokeInterface as u8, fm.as_raw(), "fm"),
    ];
    let elems: Vec<AnnotationElemDefEx> = defs
        .iter()
        .map(|(ty, entity, _)| {
            let mh = b.create_method_handle(*ty, *entity);
            AnnotationElemDefEx {
                name: b.add_string("mh"),
                tag: b'J',
                value: AnnotationElemValue::EntityRef(mh.as_raw()),
            }
        })
        .collect();
    let ann = b.create_annotation_ex(cls, &elems);
    b.class_add_runtime_annotation(cls, ann);

    let data = b.finalize().expect("finalize");
    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let ann = &g.annotations.compile_time[0];
    assert_eq!(ann.elements.len(), 9);
    for (i, (want_ty, _, want_name)) in defs.iter().enumerate() {
        match &ann.elements[i].value {
            AnnotationValue::MethodHandle(mh) => {
                assert_eq!(mh.handle_type as u8, *want_ty, "handle type of element {i}");
                assert_ne!(mh.entity_offset, 0, "entity offset of element {i}");
                // Foreign members never enter the entity_map (decode.rs
                // resolve_foreign_entity_name doc): the method-handle path
                // resolves through the map only, so foreign entities decode
                // to the empty-name fallback. Regular members resolve by name.
                if *want_name == "ff" || *want_name == "fm" {
                    assert_eq!(file.strings.resolve(mh.entity), Some(""));
                } else {
                    assert_eq!(
                        file.strings.resolve(mh.entity),
                        Some(*want_name),
                        "entity of element {i}"
                    );
                }
            }
            other => panic!("expected MethodHandle at element {i}, got {other:?}"),
        }
    }
}

/// `relocate_code_id` accepts a FOREIGN field entity: the bridge resolves
/// the tagged handle through the foreign-field table (the arm no other test
/// drives). As with the Class/Field arms, no bytecode operand is ISA-typed
/// as a field reference, so this drives registration only.
#[test]
fn relocate_code_id_foreign_field_entity() {
    use abcd_isa::{Bytecode, EntityId, Imm};

    let (mut b, cls) = base_builder(&[0x65]);
    let fcls = b.add_foreign_class("LForeign;");
    let ff = b.add_foreign_field(fcls, "ff", Type::I32);
    let proto = b.create_proto(Type::Tagged, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = abcd_isa::encode(&[
        Bytecode::Definefunc(Imm(0), placeholder, Imm(0)),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let owner = b.class_add_method(cls, "caller", proto, AccessFlags::STATIC, &code, 0, 0);
    b.method_set_source_lang(owner, SourceLang::EcmaScript);
    b.relocate_code_id(owner, offsets[0], 0, CodeEntity::Field(ff))
        .expect("foreign field relocation must register");
}

/// `GetFileType` early branches: buffers at least 8 but smaller than the
/// file header are Invalid (the short branch), and a header-sized buffer
/// whose file_size matches but whose magic is wrong is Invalid via the
/// magic branch (the size-mismatch branch is already pinned in
/// file_type.rs).
#[test]
fn file_type_short_header_and_bad_magic() {
    // Short: magic present, but smaller than sizeof(Header) (60).
    for len in [8usize, 16, 59] {
        let mut data = vec![0u8; len];
        data[..8].copy_from_slice(b"PANDA\0\0\0");
        assert_eq!(
            file_type(&data),
            FileType::Invalid,
            "{len}-byte buffer must be Invalid"
        );
    }
    // Header-sized, file_size field consistent, magic wrong.
    let mut data = vec![0u8; 60];
    data[..8].copy_from_slice(b"PANDX\0\0\0");
    data[16..20].copy_from_slice(&60u32.to_le_bytes());
    assert_eq!(file_type(&data), FileType::Invalid);
    // Positive control: same shape with the right magic is Dynamic.
    data[..8].copy_from_slice(b"PANDA\0\0\0");
    data[12..16].copy_from_slice(&[12, 0, 2, 0]);
    assert_eq!(file_type(&data), FileType::Dynamic);
}

/// The `abc_class_get_descriptor` raw fallback: when the class name string
/// item fails the bounded lossless read (its tag claims more units than the
/// payload decodes to), decode falls back to the raw-byte descriptor view
/// and reports the later name failure against THAT string — the error's
/// context is the fallback-produced descriptor.
#[test]
fn class_descriptor_raw_fallback_on_corrupt_name() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_class("LCorrupt;");
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let global = b.add_global_class();
    b.class_set_source_lang(global, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        global,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let mut data = b.finalize().expect("finalize");

    // The LCorrupt class item starts with its inline descriptor string item
    // [uleb (9 << 1) | 1]["LCorrupt;"][NUL]. Locate it via the class index
    // table and inflate the tag's declared unit count: the payload still
    // decodes to 9 units, so the bounded conversion's exact-count rule
    // (`out_pos == sd.utf16_length`) fails while the vendored class-item
    // parse (a raw scan to NUL) is unaffected. (Corrupting the NUL itself
    // would shift that parse and trip the N55 extractor guard first.)
    let class_idx_off = u32_at(&data, 32) as usize;
    let num_classes = u32_at(&data, 28) as usize;
    let mut tag_pos = None;
    for i in 0..num_classes {
        let off = u32_at(&data, class_idx_off + 4 * i) as usize;
        if data[off] == 0x13 && &data[off + 1..off + 10] == b"LCorrupt;" {
            tag_pos = Some(off);
        }
    }
    let tag_pos = tag_pos.expect("LCorrupt class item must exist");
    data[tag_pos] = 20 << 1 | 1; // claims 20 units; the payload holds 9

    let err = decode(&data).expect_err("the corrupted name must fail decode");
    match err {
        Error::Malformed { field, context } => {
            assert_eq!(field, "name");
            assert_eq!(
                context, "class LCorrupt;",
                "the context embeds the raw-fallback descriptor"
            );
        }
        other => panic!("expected Malformed/name, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Annotation-bucket decode via tag patching
// ---------------------------------------------------------------------------

fn u32_at(data: &[u8], pos: usize) -> u32 {
    u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap())
}

fn uleb128(data: &[u8], mut pos: usize) -> (u32, usize) {
    let mut result = 0u32;
    let mut shift = 0;
    loop {
        let byte = data[pos];
        pos += 1;
        result |= u32::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            break;
        }
        shift += 7;
    }
    (result, pos)
}

/// Positions of the ANNOTATION tag byte on the class, method, and field
/// items of the bucket fixture, plus the DEBUG_INFO tag position on the
/// method (needed for the runtime-bucket pair swap).
struct TagPositions {
    class_ann: usize,
    method_ann: usize,
    method_debug: usize,
    field_ann: usize,
}

/// Build a fixture whose class, method, and field each carry one
/// compile-time annotation (a single U32(111) element). The vendored writer
/// emits every staged annotation into the single ANNOTATION bucket, so the
/// runtime/type/runtime-type decode callbacks only fire when the tag byte
/// is patched into those buckets' positions.
fn build_bucket_fixture() -> (Vec<u8>, TagPositions) {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let name = b.add_string("value");
    let elem = AnnotationElemDefEx {
        name,
        tag: b'7',
        value: AnnotationElemValue::Scalar(111),
    };
    let mk = |b: &mut Builder| b.create_annotation_ex(cls, std::slice::from_ref(&elem));
    let class_ann = mk(&mut b);
    b.class_add_annotation(cls, class_ann);
    let fld = b.class_add_field(cls, "fx", Type::I32, AccessFlags::PUBLIC);
    let field_ann = mk(&mut b);
    b.field_add_annotation(fld, field_ann);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(cls, "m", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let method_ann = mk(&mut b);
    b.method_add_annotation(m, method_ann);
    let lnp = b.create_lnp();
    let debug = b.create_debug_info(lnp, 1);
    // A debug item without a SET_FILE op is the exact N55 extractor trap;
    // emit one so decode's extractor guard stays quiet.
    let sf = b.add_string("m.js");
    b.lnp_emit_set_file(lnp, debug, sf);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m, debug);
    let data = b.finalize().expect("finalize");

    // Walk the class item: [uleb name tag][MUTF-8][NUL][u32 super]
    // [uleb flags][uleb num_fields][uleb num_methods][tagged][0x00]
    // then the INLINE field items, then the INLINE method items
    // (class_data_accessor-inl.h EnumerateClassElements — no offset table).
    let class_idx_off = u32_at(&data, 32) as usize;
    let class_off = u32_at(&data, class_idx_off) as usize;
    let mut pos = class_off;
    let (_, p) = uleb128(&data, pos);
    pos = p;
    while data[pos] != 0 {
        pos += 1;
    }
    pos += 1 + 4; // NUL + super_class_off
    let (_, p) = uleb128(&data, pos);
    pos = p; // access_flags
    let (num_fields, p) = uleb128(&data, pos);
    pos = p;
    let (num_methods, p) = uleb128(&data, pos);
    pos = p;
    // Class tagged section: [0x02 SOURCE_LANG u8]? then [0x04 ANNOTATION u32].
    let class_ann = loop {
        let tag = data[pos];
        pos += 1;
        assert_ne!(tag, 0, "class ANNOTATION tag not found");
        if tag == 0x04 {
            pos += 4;
            break pos - 5;
        }
        pos += if tag == 0x02 { 1 } else { 4 };
    };
    assert_eq!(data[pos], 0, "class tags end with NOTHING");
    pos += 1;
    assert_eq!(num_fields, 1, "one field in the fixture");
    assert_eq!(num_methods, 1, "one method in the fixture");

    // The inline field item starts here: `[u16 class_idx][u16 type_idx]
    // [u32 name_off][uleb flags][tagged][0x00]`; the method item follows it.
    let field_off = pos;
    let (_, p) = uleb128(&data, field_off + 8); // access_flags
    let f0 = p;
    assert_eq!(data[f0], 0x04, "field ANNOTATION");
    assert_eq!(data[f0 + 5], 0x00, "field tags end with NOTHING");
    let method_off = f0 + 6; // past the ANNOTATION record and NOTHING

    // Method tagged section: [0x01 CODE u32][0x02 SOURCE_LANG u8]
    // [0x05 DEBUG_INFO u32][0x06 ANNOTATION u32][0x00].
    let (_, p) = uleb128(&data, method_off + 8); // access_flags
    let m0 = p;
    assert_eq!(data[m0], 0x01, "CODE");
    assert_eq!(data[m0 + 5], 0x02, "SOURCE_LANG");
    assert_eq!(data[m0 + 7], 0x05, "DEBUG_INFO");
    assert_eq!(data[m0 + 12], 0x06, "ANNOTATION");
    assert_eq!(data[m0 + 17], 0x00, "NOTHING");

    (
        data,
        TagPositions {
            class_ann,
            method_ann: m0 + 12,
            method_debug: m0 + 7,
            field_ann: f0,
        },
    )
}

/// The value of the single annotation element found in `bucket`.
fn bucket_u32s(bucket: &[abcd_file::Annotation]) -> Vec<u32> {
    bucket
        .iter()
        .flat_map(|a| a.elements.iter())
        .filter_map(|e| match e.value {
            AnnotationValue::U32(v) => Some(v),
            _ => None,
        })
        .collect()
}

/// Decode one patched variant and assert the annotation landed in exactly
/// the wanted bucket on each patched target. `field_patched` is false for
/// the type/runtime-type variants: the vendored FieldDataAccessor matches
/// `FieldTag::ANNOTATION` (0x04) for ALL four bucket enumerations
/// (field_data_accessor-inl.h:171,186 — an upstream quirk), so the field
/// type buckets can never receive items; the field record stays unpatched
/// (compile-time) in those variants.
fn assert_bucket(data: &[u8], which: &str, field_patched: bool) {
    let file = decode(data).unwrap_or_else(|e| panic!("decode {which} variant: {e}"));
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let m = g
        .methods
        .iter()
        .find(|m| file.strings.resolve(m.name) == Some("m"))
        .expect("method m");
    let want: &[u32] = &[111];
    let empty: &[u32] = &[];
    let idx = match which {
        "runtime" => 1,
        "type" => 2,
        "runtime_type" => 3,
        other => panic!("unknown bucket {other}"),
    };
    for (target, anns, patched) in [
        ("class", &g.annotations, true),
        ("method", &m.annotations, true),
        ("field", &g.fields[0].annotations, field_patched),
    ] {
        let got = [
            bucket_u32s(&anns.compile_time),
            bucket_u32s(&anns.runtime),
            bucket_u32s(&anns.compile_time_type),
            bucket_u32s(&anns.runtime_type),
        ];
        let mut expect = [empty, empty, empty, empty];
        if patched {
            expect[idx] = want;
        } else {
            expect[0] = want; // the field record stays compile-time
        }
        assert_eq!(got, expect, "{target} buckets for the {which} variant");
    }
}

/// Runtime/type annotation decode callbacks fire for class, method, and
/// field targets when the file carries those buckets. The vendored builder
/// has only the single ANNOTATION list per item, so the variants are made
/// by patching the tag byte (same 5-byte `[tag][u32 offset]` record): the
/// accessor chains check each bucket's tag at the position it occupies in
/// the vendored emission order.
#[test]
fn annotation_buckets_decode_via_tag_patch() {
    let (data, pos) = build_bucket_fixture();

    // Runtime: the method's RUNTIME_ANNOTATION chain position is BEFORE
    // DEBUG_INFO, so the method's annotation record swaps places with the
    // (same-sized) debug record; class and field patch in place.
    let mut runtime = data.clone();
    runtime[pos.class_ann] = 0x03;
    runtime[pos.field_ann] = 0x03;
    let d = pos.method_debug;
    let dbg_rec: [u8; 5] = runtime[d..d + 5].try_into().unwrap();
    let ann_rec: [u8; 5] = runtime[d + 5..d + 10].try_into().unwrap();
    runtime[d] = 0x03; // [0x03][ann u32] takes the debug record's slot
    runtime[d + 1..d + 5].copy_from_slice(&ann_rec[1..]);
    runtime[d + 5..d + 10].copy_from_slice(&dbg_rec); // [0x05][debug u32] follows
    assert_bucket(&runtime, "runtime", true);
    // The debug record survived the swap: method debug info still decodes.
    let file = decode(&runtime).expect("decode runtime variant");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let m = g
        .methods
        .iter()
        .find(|m| file.strings.resolve(m.name) == Some("m"))
        .expect("method m");
    assert!(m.debug.is_some(), "the swapped debug record still reads");

    // Type annotations: class and method patch in place; the field record
    // stays compile-time (the vendored field reader has no type buckets —
    // see assert_bucket's doc).
    let mut typed = data.clone();
    typed[pos.class_ann] = 0x06;
    typed[pos.method_ann] = 0x08;
    assert_bucket(&typed, "type", false);

    // Runtime-type annotations: same target set.
    let mut rtype = data;
    rtype[pos.class_ann] = 0x05;
    rtype[pos.method_ann] = 0x09;
    assert_bucket(&rtype, "runtime_type", false);
}
