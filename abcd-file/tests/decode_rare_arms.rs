//! Decode-side rare arms the corpus never exercises: the modern and legacy
//! foreign-method operand fallbacks (foreign members never enter the
//! pre-registered entity map, so the operand resolver falls back to opening
//! the item directly), the empty/unknown/64-bit annotation-array arms, and
//! the `AVT::Unknown` scalar fallback.

use abcd_file::{
    AccessFlags, AnnotationElemDefEx, AnnotationElemValue, AnnotationValue, Builder, CodeEntity,
    SourceLang, Type, Version, decode,
};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm};

/// File::Header layout (unchanged since 3.1): magic(8) checksum(4)
/// version(4) file_size(4) ... — the fields the legacy crafts touch.
const CHECKSUM_OFF: usize = 8;
const VERSION_OFF: usize = 12;

/// The legacy header version under test.
const LEGACY_VERSION: [u8; 4] = [0, 0, 0, 2];

/// adler32 with initial 1, matching the vendored writer's checksum backfill
/// (zlib adler32 over the file content after the checksum field).
fn adler32(data: &[u8]) -> u32 {
    const MOD: u32 = 65521;
    let mut a = 1u32;
    let mut b = 0u32;
    for &byte in data {
        a = (a + byte as u32) % MOD;
        b = (b + a) % MOD;
    }
    (b << 16) | a
}

/// Find the unique occurrence of `needle` in `haystack`.
fn locate_unique(haystack: &[u8], needle: &[u8]) -> usize {
    assert!(needle.len() <= haystack.len());
    let mut hits =
        (0..=haystack.len() - needle.len()).filter(|&i| haystack[i..i + needle.len()] == *needle);
    let pos = hits.next().expect("code bytes not found in file");
    assert!(hits.next().is_none(), "code bytes occur more than once");
    pos
}

/// Read a method's final (post-relocation) code bytes through the sys
/// layer (same walk as legacy_decode.rs).
fn method_code(data: &[u8], method_offset: u32) -> Vec<u8> {
    let f = unsafe { abcd_file_sys::abc_file_open(data.as_ptr(), data.len()) };
    assert!(!f.is_null(), "abc_file_open failed");
    let mr = unsafe { abcd_file_sys::abc_method_open(f, method_offset) };
    assert!(!mr.is_null(), "abc_method_open failed");
    let code_off = unsafe { abcd_file_sys::abc_method_code_off(mr) };
    unsafe { abcd_file_sys::abc_method_close(mr) };
    assert_ne!(code_off, u32::MAX, "method has no code item");
    let cr = unsafe { abcd_file_sys::abc_code_open(f, code_off) };
    assert!(!cr.is_null(), "abc_code_open failed");
    let ptr = unsafe { abcd_file_sys::abc_code_instructions(cr) };
    let len = unsafe { abcd_file_sys::abc_code_code_size(cr) } as usize;
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) }.to_vec();
    unsafe { abcd_file_sys::abc_code_close(cr) };
    unsafe { abcd_file_sys::abc_file_close(f) };
    bytes
}

/// Build a file whose `caller` method references a FOREIGN method through
/// its index region (definefunc's method operand, relocated after layout).
fn build_with_foreign_method_operand() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Void, &[]);
    let foreign = b.add_foreign_method(cls, "foreign_fn", proto, AccessFlags::PUBLIC);

    let placeholder = EntityId(u16::MAX as u32);
    let mut insns = vec![
        Bytecode::Definefunc(Imm(0), placeholder, Imm(0)),
        Bytecode::Returnundefined,
    ];
    // Legroom for the longer legacy stream rewrite below.
    insns.extend(std::iter::repeat_n(Bytecode::Nop, 32));
    let (code, offsets) = abcd_isa::encode(&insns).unwrap();
    let caller = b.class_add_method(cls, "caller", proto, AccessFlags::STATIC, &code, 1, 0);
    b.method_set_source_lang(caller, SourceLang::EcmaScript);
    b.relocate_code_id(caller, offsets[0], 0, CodeEntity::Method(foreign))
        .expect("relocate to foreign method");
    // One literal array: the API-12 writer emits the header literal-array
    // table that the legacy global-index blob pass reads.
    let lit = b.add_literal_array("lit");
    b.literal_array_add_integer(lit, 42);
    b.deduplicate();
    b.finalize().expect("finalize")
}

/// Modern decode: a method operand resolving to a FOREIGN method is not in
/// the pre-registered entity map (foreign members are not class members),
/// so decode falls back to opening the method item for its name.
#[test]
fn foreign_method_operand_resolves_through_fallback() {
    let data = build_with_foreign_method_operand();
    let file = decode(&data).expect("decode");
    let caller = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("caller"))
        .expect("caller")
        .1;
    let body = caller.body.as_ref().unwrap();
    let (kind, id) = body.bytecodes[0].entity_operands()[0];
    assert_eq!(kind, EntityKind::MethodId);
    let off = body.entity_offsets[&(kind, id.0)];
    assert_eq!(
        file.resolve_entity_str(off),
        Some("foreign_fn"),
        "the foreign method operand must resolve to the foreign name"
    );
}

/// Legacy (0.0.0.2) decode of the same shape: the legacy method-operand
/// rule (16-bit index into the same index region) hits the same foreign
/// fallback on the legacy branch.
#[test]
fn legacy_foreign_method_operand_resolves_through_fallback() {
    let mut data = build_with_foreign_method_operand();

    // Learn the method-local index of the foreign method from a modern
    // decode (legacy method operands are 16-bit indices into the same
    // index region).
    let modern = decode(&data).expect("modern decode");
    let caller = modern
        .all_methods()
        .find(|(_, m)| modern.strings.resolve(m.name) == Some("caller"))
        .expect("caller")
        .1;
    let caller_off = caller.offset;
    let body = caller.body.as_ref().unwrap();
    let (kind, id) = body.bytecodes[0].entity_operands()[0];
    assert_eq!(kind, EntityKind::MethodId);
    let method_index = u16::try_from(id.0).unwrap();

    // Rewrite caller's code stream as legacy: definefuncdyn id16, imm16, v0;
    // the create*withbuffer family carrying imm16 global literal-table
    // indices; return.dyn. 0x00 is the legacy nop, padding the tail.
    let mut legacy = vec![0xff, 0x5f];
    legacy.extend_from_slice(&method_index.to_le_bytes());
    legacy.extend_from_slice(&[0x00, 0x00, 0x00]);
    for op in [0x66u8, 0x67, 0x69] {
        // createarraywithbuffer / createobjecthavingmethod /
        // createobjectwithbuffer: imm16 global litidx 0.
        legacy.extend_from_slice(&[0xff, op, 0x00, 0x00]);
    }
    legacy.push(0xa6);
    let modern_bytes = method_code(&data, caller_off);
    assert!(legacy.len() <= modern_bytes.len());
    let pos = locate_unique(&data, &modern_bytes);
    data[pos..pos + legacy.len()].copy_from_slice(&legacy);
    data[pos + legacy.len()..pos + modern_bytes.len()].fill(0x00);

    // Header: version 0.0.0.2 + honest checksum (the decoder never
    // validates it, but a stale checksum would be malformed in a way real
    // legacy files are not).
    data[VERSION_OFF..VERSION_OFF + 4].copy_from_slice(&LEGACY_VERSION);
    let checksum = adler32(&data[VERSION_OFF..]);
    data[CHECKSUM_OFF..CHECKSUM_OFF + 4].copy_from_slice(&checksum.to_le_bytes());

    let literal_offset = {
        let table_off = u32::from_le_bytes(data[48..52].try_into().unwrap()) as usize;
        u32::from_le_bytes(data[table_off..table_off + 4].try_into().unwrap())
    };

    let file = decode(&data).expect("legacy decode");
    assert_eq!(file.version, Version::new(0, 0, 0, 2));
    let caller = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("caller"))
        .expect("caller (legacy)")
        .1;
    let body = caller.body.as_ref().unwrap();
    // Legacy definefuncdyn maps to modern Definefunc.
    let (kind, id) = body.bytecodes[0].entity_operands()[0];
    assert_eq!(kind, EntityKind::MethodId);
    let off = body.entity_offsets[&(kind, id.0)];
    assert_eq!(
        file.resolve_entity_str(off),
        Some("foreign_fn"),
        "the legacy foreign method operand must resolve to the foreign name"
    );
    // The create*withbuffer imm16 references resolved through the header's
    // global literal-array table (the legacy blob pass).
    assert_eq!(
        body.entity_offsets[&(EntityKind::LiteralarrayId, 0)],
        literal_offset,
        "the legacy global literal-table index must resolve to the array"
    );
}

// ---------------------------------------------------------------------------
// Annotation array tag arms (crafted by patching the element tag byte)
// ---------------------------------------------------------------------------

/// Build a file whose global class carries one annotation with a single
/// element `(name, tag, value)`.
fn build_single_elem(name: &str, tag: u8, value: AnnotationElemValue) -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let n = b.add_string(name);
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name: n,
            tag,
            value,
        }],
    );
    b.class_add_runtime_annotation(cls, ann);
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
    b.finalize().expect("finalize")
}

fn find_all(data: &[u8], pat: &[u8]) -> Vec<usize> {
    data.windows(pat.len())
        .enumerate()
        .filter(|(_, w)| *w == pat)
        .map(|(i, _)| i)
        .collect()
}

/// Position of the single element's tag byte, located via its name string
/// (annotation item: `[u32 class_idx][u16 count][(u32 name_off, u32
/// value)][u8 tag]` — vendored annotation_data_accessor.cpp).
fn locate_tag_byte(data: &[u8], elem_name: &str, tag: u8) -> usize {
    let mut pat = vec![((elem_name.len() as u8) << 1) | 1];
    pat.extend_from_slice(elem_name.as_bytes());
    pat.push(0);
    let str_offs = find_all(data, &pat);
    assert_eq!(str_offs.len(), 1, "string item for {elem_name}");
    let str_off = str_offs[0] as u32;
    for name_pos in find_all(data, &str_off.to_le_bytes()) {
        if name_pos < 6 || name_pos + 9 > data.len() {
            continue;
        }
        let ann_off = name_pos - 6;
        let count = u16::from_le_bytes(data[ann_off + 4..ann_off + 6].try_into().unwrap());
        if count == 1 && data[name_pos + 8] == tag {
            return name_pos + 8;
        }
    }
    panic!("annotation element for {elem_name} not found");
}

/// Extract the single annotation element of the global class.
fn single_element_value(file: &abcd_file::File) -> &AnnotationValue {
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    &g.annotations.compile_time[0].elements[0].value
}

/// An empty annotation array (count 0) decodes to an empty value list.
#[test]
fn empty_annotation_array_decodes() {
    let data = build_single_elem("empty_arr", b'Q', AnnotationElemValue::Array(vec![]));
    let file = decode(&data).expect("decode");
    assert_eq!(
        single_element_value(&file),
        &AnnotationValue::Array {
            tag: b'Q',
            values: vec![]
        },
        "empty array must decode to an empty value list"
    );
}

/// 64-bit annotation arrays (tags 'R'/'S'/'U' = ArrayI64/U64/F64) decode
/// through the 8-byte element path. The builder's array ABI is 32-bit, so
/// the tag byte is patched post-build; the two u32 payload words then read
/// back as the first 64-bit element, exactly.
#[test]
fn array_i64_u64_f64_decode() {
    for (tag, expect) in [
        (b'R', AnnotationValue::I64(0x0506_0708_0102_0304u64 as i64)),
        (b'S', AnnotationValue::U64(0x0506_0708_0102_0304)),
        (
            b'U',
            AnnotationValue::F64(f64::from_bits(0x0506_0708_0102_0304)),
        ),
    ] {
        let mut data = build_single_elem(
            "arr64",
            b'Q',
            AnnotationElemValue::Array(vec![0x0102_0304, 0x0506_0708]),
        );
        let tag_pos = locate_tag_byte(&data, "arr64", b'Q');
        data[tag_pos] = tag;
        let file = decode(&data).unwrap_or_else(|e| panic!("decode tag {}: {e}", tag as char));
        match single_element_value(&file) {
            AnnotationValue::Array {
                tag: got_tag,
                values,
            } => {
                assert_eq!(*got_tag, tag);
                assert_eq!(values.len(), 2, "count is payload elements / 8 bytes");
                assert_eq!(values[0], expect, "tag {}", tag as char);
            }
            other => panic!("expected array for tag {}, got {other:?}", tag as char),
        }
    }
}

/// An unknown scalar tag byte ('0' = AVT::Unknown) decodes as a raw U32
/// (the vendored fallback).
#[test]
fn unknown_scalar_tag_decodes_as_u32() {
    let mut data = build_single_elem("unk", b'7', AnnotationElemValue::Scalar(42));
    let tag_pos = locate_tag_byte(&data, "unk", b'7');
    data[tag_pos] = b'0';
    let file = decode(&data).expect("decode");
    assert_eq!(
        single_element_value(&file),
        &AnnotationValue::U32(42),
        "unknown tag falls back to the raw u32 value"
    );
}

/// A method without an index-section entry decodes with
/// `FunctionKind::None` (edge fallback in the function-kind read).
#[test]
fn method_without_index_entry_gets_no_function_kind() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Void, &[]);
    // No entity operands, no explicit function kind.
    b.class_add_method(cls, "bare", proto, AccessFlags::STATIC, &[0x65], 0, 0);
    let data = b.finalize().expect("finalize");
    let file = decode(&data).expect("decode");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("bare"))
        .expect("bare method")
        .1;
    assert_eq!(m.function_kind, abcd_file::FunctionKind::None);
}

/// A method with a debug item but no bytecode: the byte-offset table is
/// empty, so debug offsets map by identity (the codeless fallback). The
/// LNP must SET_FILE (a fileless program in a class without a source-file
/// record is the N55 throw — a hard error, not this arm).
#[test]
fn codeless_method_debug_offsets_map_by_identity() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Void, &[]);
    let m = b.class_add_method(cls, "nocode", proto, AccessFlags::STATIC, &[], 0, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let lnp = b.create_lnp();
    let debug = b.create_debug_info(lnp, 7);
    let sf = b.add_string("x.ets");
    b.lnp_emit_set_file(lnp, debug, sf);
    b.lnp_emit_advance_line(lnp, debug, 3); // a line-table entry at pc 0
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m, debug);
    let data = b.finalize().expect("finalize");
    let file = decode(&data).expect("decode");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("nocode"))
        .expect("nocode method")
        .1;
    let dbg = m.debug.as_ref().expect("debug record present");
    assert!(
        m.body.as_ref().is_none_or(|b| b.bytecodes.is_empty()),
        "test setup: the method must be codeless"
    );
    // The extractor's initial row carries the debug item's start line at
    // pc 0; with no bytecode the offset maps to index 0 by identity.
    assert_eq!(
        dbg.line_table.first().map(|e| (e.index, e.line)),
        Some((0, 7)),
        "the debug line table must decode through the identity fallback"
    );
}

/// A debug item whose source file is the EMPTY string maps to `None`
/// (N55: "" is the vendor's "no value" answer, not a value).
#[test]
fn debug_empty_source_file_maps_to_none() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Void, &[]);
    let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &[0x65], 0, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let lnp = b.create_lnp();
    let debug = b.create_debug_info(lnp, 1);
    let empty = b.add_string("");
    b.lnp_emit_set_file(lnp, debug, empty);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m, debug);
    let data = b.finalize().expect("finalize");
    let file = decode(&data).expect("decode");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("f"))
        .expect("method f")
        .1;
    let dbg = m.debug.as_ref().expect("debug record present");
    assert_eq!(
        dbg.source_file, None,
        "an empty source file must map to None, not Some(\"\")"
    );
}

/// The legacy foreign-method fallback fails loudly when the foreign
/// method's name is unreadable (name field at item+4 per the vendored
/// foreign-item layout).
#[test]
fn legacy_foreign_method_name_unreadable_is_hard_error() {
    let mut data = build_with_foreign_method_operand();

    // Learn the foreign method's entity offset and the method-local index
    // from a modern decode.
    let modern = decode(&data).expect("modern decode");
    let caller = modern
        .all_methods()
        .find(|(_, m)| modern.strings.resolve(m.name) == Some("caller"))
        .expect("caller")
        .1;
    let caller_off = caller.offset;
    let body = caller.body.as_ref().unwrap();
    let (kind, id) = body.bytecodes[0].entity_operands()[0];
    let method_index = u16::try_from(id.0).unwrap();
    let foreign_off = body.entity_offsets[&(kind, id.0)];

    // Legacy rewrite of caller's stream (definefuncdyn id16).
    let mut legacy = vec![0xff, 0x5f];
    legacy.extend_from_slice(&method_index.to_le_bytes());
    legacy.extend_from_slice(&[0x00, 0x00, 0x00]);
    legacy.push(0xa6);
    let modern_bytes = method_code(&data, caller_off);
    let pos = locate_unique(&data, &modern_bytes);
    data[pos..pos + legacy.len()].copy_from_slice(&legacy);
    data[pos + legacy.len()..pos + modern_bytes.len()].fill(0x00);

    // Corrupt the foreign method's name field (item+4) to dangle.
    let name_field = foreign_off as usize + 4;
    data[name_field..name_field + 4].copy_from_slice(&u32::MAX.to_le_bytes());

    data[VERSION_OFF..VERSION_OFF + 4].copy_from_slice(&LEGACY_VERSION);
    let checksum = adler32(&data[VERSION_OFF..]);
    data[CHECKSUM_OFF..CHECKSUM_OFF + 4].copy_from_slice(&checksum.to_le_bytes());

    let err = decode(&data).expect_err("unreadable foreign method name must fail");
    assert!(
        matches!(
            err,
            abcd_file::Error::Malformed {
                field: "bytecode entity reference",
                ..
            }
        ),
        "unexpected error: {err:?}"
    );
}

/// The modern foreign-method fallback fails loudly when the foreign
/// method's name is unreadable (same craft as the legacy variant, no
/// version rewrite).
#[test]
fn foreign_method_name_unreadable_is_hard_error() {
    let mut data = build_with_foreign_method_operand();
    let modern = decode(&data).expect("modern decode");
    let caller = modern
        .all_methods()
        .find(|(_, m)| modern.strings.resolve(m.name) == Some("caller"))
        .expect("caller")
        .1;
    let body = caller.body.as_ref().unwrap();
    let (kind, id) = body.bytecodes[0].entity_operands()[0];
    let foreign_off = body.entity_offsets[&(kind, id.0)];

    // Corrupt the foreign method's name field (item+4) to dangle.
    let name_field = foreign_off as usize + 4;
    data[name_field..name_field + 4].copy_from_slice(&u32::MAX.to_le_bytes());

    let err = decode(&data).expect_err("unreadable foreign method name must fail");
    assert!(
        matches!(
            err,
            abcd_file::Error::Malformed {
                field: "bytecode entity reference",
                ..
            }
        ),
        "unexpected error: {err:?}"
    );
}
