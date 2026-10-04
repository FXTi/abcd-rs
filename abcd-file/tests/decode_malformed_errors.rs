//! Decode-side malformed-input ERROR-PATH battery (the decode.rs arms the
//! corpus never trips): every test builds a valid file via [`Builder`],
//! byte-mutates one field so a specific bridge read fails, and asserts the
//! exact [`Error`] variant + message fragment. Companion to
//! `malformed_items.rs` (never-abort fuzzing) and `annotation_loud_errors.rs`
//! (annotation payload reads): this file owns the remaining dec-malformed /
//! dec-module-errors / dec-ann-errors / dec-legacy-errors arms.
//!
//! Byte-layout references (vendored libpandafile):
//! - `File::Header` (file.h): magic(0,8) checksum(8) version(12)
//!   file_size(16) foreign_off(20) foreign_size(24) num_classes(28)
//!   class_idx_off(32) num_lnps(36) lnp_idx_off(40) num_literalarrays(44)
//!   literalarray_idx_off(48) num_indexes(52) index_section_off(56).
//! - `File::IndexHeader` (file.h): start(+0) end(+4) class_idx_size(+8)
//!   class_idx_off(+12) method_idx_size(+16) method_idx_off(+20)
//!   field_idx_size(+24) field_idx_off(+28) proto_idx_size(+32)
//!   proto_idx_off(+36) — 40 bytes.
//! - Class item (class_data_accessor.cpp ctor): inline descriptor string
//!   item `[uleb (utf16_len<<1)|is_ascii][MUTF-8][NUL]`, then
//!   `[u32 super_class][uleb access_flags][uleb num_fields]
//!   [uleb num_methods]`, the tagged stream (INTERFACES=0x01: uleb count +
//!   count×u16; SOURCE_LANG=0x02: u8; 0x03..=0x07: u32), a NOTHING(0) byte,
//!   then the INLINE field and method items (no offset table — see the
//!   uncraftable list below).
//! - Method item (method_data_accessor.cpp ctor): `[u16 class_idx]
//!   [u16 proto_idx][u32 name_off][uleb access_flags]`, then the tagged
//!   stream (CODE=0x01: u32; SOURCE_LANG=0x02: u8; 0x03..=0x09: u32),
//!   NOTHING(0) terminator.
//! - Field item (field_data_accessor.cpp ctor): `[u16 class_idx]
//!   [u16 type_idx][u32 name_off][uleb access_flags]`, tagged stream
//!   (INT_VALUE=0x01: uleb; VALUE=0x02: u32; 0x03..=0x06: u32), NOTHING(0).
//! - Annotation item (annotation_data_accessor.cpp ctor):
//!   `[u16 class_idx][u16 count][count × (u32 name_off, u32 value)]
//!   [count × u8 tag]`.
//! - ParamAnnotationsItem (file_bridge.cpp abc_param_annotations_enumerate):
//!   `[u32 num_params][per param: u32 count, count × u32 annotation offs]`.
//! - Proto item (proto_data_accessor-inl.h): 4-bit shorty nibbles packed
//!   into u16 words (0-terminated), then `num_ref × u16` class-index-table
//!   indices.
//! - Module blob (module_data_accessor.cpp): `[u32 item count]
//!   [u32 num_requests][num × u32 request offsets][tag sections]`.
//! - Module-request-phase blob: `[u32 count][count × u8 flags]`.
//!
//! ## Documented accepts (arms proven uncraftable from the public input)
//!
//! - **decode.rs class-index ABSENT / class-open-null skip arms (both
//!   passes)**: any class-table entry that would trip them is non-external
//!   garbage, and the vendored DebugInfoExtractor constructor walks EVERY
//!   non-external class (debug_info_extractor.cpp Extract: GetClasses loop)
//!   before decode's class passes run — its throw becomes the hard
//!   `Error::DebugInfoExtraction` at decode open (N55). The skip arms never
//!   execute first. (malformed_items.rs's never-abort pins cover the crash
//!   surface.)
//! - **decode.rs `abc_method_open` null after enumeration (entity-map pass
//!   skip and `decode_method_at`'s `InvalidOffset`)**: methods are INLINE
//!   items inside the class item — `EnumerateClassElements` constructs the
//!   accessor to learn the offset, so an offset is yielded only when the
//!   ctor already succeeded; the deterministic re-open cannot fail. A ctor
//!   throw mid-enumeration aborts the enumeration instead (bridge catch →
//!   truncated list). Same for the field-open arms (`abc_field_open`).
//! - **decode.rs class-descriptor `None → skip` and the raw-pointer
//!   fallback's null arm** (`read_class_descriptor`): `GetDescriptor()`
//!   returns `name_.data`, which a successful ctor always sets — so once
//!   `abc_class_open` succeeds the descriptor is always `Some` (via the raw
//!   fallback if the lossless read fails). The `None` arm would need the
//!   ctor to succeed AND the getter to throw — impossible.
//! - **decode.rs `abc_index_open` null → `FunctionKind::None` fallback**:
//!   the bridge's `AbcIndexAccessor` is a deliberately thin wrapper whose
//!   constructor cannot throw (file_bridge.cpp — it does NOT wrap the
//!   vendored IndexAccessor because that ctor's unchecked header-index read
//!   is UB on malformed input, audit #B2). The open never returns null.
//! - **decode.rs `abc_proto_open` null → `InvalidOffset`**: the vendored
//!   ProtoDataAccessor ctor is trivial (no validation; accessors throw
//!   lazily on field reads), so the open never returns null. A bogus proto
//!   offset instead surfaces as `Error::UnknownTypeId` from the return-type
//!   read (pinned below).
//! - **decode.rs field type/runtime-type annotation bucket `?` arms**: the
//!   vendored FieldDataAccessor's `EnumerateTypeAnnotations` and
//!   `EnumerateRuntimeTypeAnnotations` both match `FieldTag::ANNOTATION`
//!   (field_data_accessor-inl.h — upstream quirk), i.e. they enumerate the
//!   SAME entries the compile-time bucket already read; a corrupt entry
//!   fails the compile-time read first (pinned below), and an intact one
//!   leaves the type buckets empty. The error propagation at those two
//!   call sites cannot fire.
//! - **decode.rs legacy `LiteralarrayId` entity-operand arm** (incl. the
//!   no-header-table and OOB errors inside it): unreachable by
//!   construction — no legacy-decoded bytecode variant carries a
//!   `LiteralarrayId` entity operand (abcd-isa legacy_table.rs maps the
//!   create*withbuffer family to the Imm-only `Deprecated*` variants; the
//!   generated `entity_operands` lists no `LiteralarrayId` for any
//!   `Deprecated*` variant). The in-code comment says the same.
//! - **decode.rs legacy method-index `u16::try_from` failure**: legacy
//!   method operands are decoded from 16-bit fields, so the conversion
//!   cannot fail.
//! - **decode.rs legacy create*withbuffer negative-immediate error**
//!   (`u32::try_from`): the legacy decoder zero-extends the imm16 field
//!   (legacy_table.rs `mk_ecma_66/67/69` read `u16`), so the immediate is
//!   never negative.
//! - **decode.rs unknown module-record tag**: the vendored
//!   `ModuleDataAccessor::EnumerateModuleRecord` hardcodes the five tag
//!   values per section loop — no input byte reaches the callback as a
//!   tag, so the `_ =>` arm cannot fire.
//! - **decode.rs annotation-array converter `_` fallback**: every tag byte
//!   that passes the element-size match has a converter arm; an
//!   unparsable tag (`AVT::try_from` Err) takes the early
//!   `return Ok(Vec::new())` — the `_` arm is defense-in-depth against a
//!   future AVT variant with a size but no converter.
//! - **decode.rs legacy blob-pass table-entry read past the buffer**
//!   (`data.get(entry..entry + 4)` returning `None`): the table's end is
//!   prevalidated against the buffer length by `legacy_literalarray_table`,
//!   so every entry read is in bounds.
//! - **decode.rs legacy header table read failure** (`read(44)`/`read(48)`
//!   returning `None`): `abc_file_open` rejects buffers smaller than
//!   `sizeof(File::Header)` (60 bytes), so both header fields always exist.
//! - **decode.rs field `TypeId::try_from` and non-Reference
//!   `Type::from_raw` error paths**: the vendored `GetTypeFromFieldEncoding`
//!   is total over u32 (every encoding maps to a valid TypeId), and
//!   `Type::from_raw` only fails for `TypeId::Reference`, which that branch
//!   excludes.
//! - **decode.rs nested-annotation empty-list defensive arm**: a one-offset
//!   input slice to `decode_annotation_list` yields exactly one annotation
//!   on `Ok` by construction (the map is per-offset), so the `list.pop()`
//!   None case cannot fire.
//! - **decode.rs annotation-array converter error propagation through the
//!   public element path**: the only `Err` sources inside
//!   `decode_annotation_array_elements` are the bridge array re-read (the
//!   caller has already read the same span successfully — exercised
//!   directly by decode.rs's in-crate test) and the '#' array-element arm
//!   (upstream-unrepresentable — also exercised in-crate); neither is
//!   reachable from `decode()`.
//! - **decode.rs per-method `abc_debug_get_source_file` /
//!   `abc_debug_get_source_code` null arms**: the vendored extractor's
//!   getters are pure map lookups that answer `""` for missing entries
//!   (debug_info_extractor.cpp GetSourceFile/GetSourceCode); only the
//!   constructor throws (N55 — the hard `Error::DebugInfoExtraction` at
//!   open, pinned by debug_n55_decode.rs). The per-method nulls are FFI
//!   defense, unreachable for immutable bytes.

use abcd_file::{
    AccessFlags, AnnotationElemDef, AnnotationElemDefEx, AnnotationElemValue, AnnotationValue,
    Builder, CodeEntity, Error, FieldValue, SourceLang, Type, decode,
};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm};

// ---------------------------------------------------------------------------
// Byte utilities
// ---------------------------------------------------------------------------

const CHECKSUM_OFF: usize = 8;
const VERSION_OFF: usize = 12;
const FILE_SIZE_OFF: usize = 16;
const NUM_CLASSES_OFF: usize = 28;
const CLASS_IDX_OFF: usize = 32;
const NUM_LITERALARRAYS_OFF: usize = 44;
const LITERALARRAY_IDX_OFF: usize = 48;
const NUM_INDEXES_OFF: usize = 52;
const INDEX_SECTION_OFF: usize = 56;

const LEGACY_VERSION: [u8; 4] = [0, 0, 0, 2];
/// Past any declared file size: `GetSpanFromId` throws on it (offset >=
/// header file_size), so bridge constructors return null.
const BOGUS: u32 = 0xFFFF_F000;

fn header_field(data: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(data[offset..offset + 4].try_into().unwrap())
}

fn write_u32(data: &mut [u8], pos: usize, v: u32) {
    data[pos..pos + 4].copy_from_slice(&v.to_le_bytes());
}

fn find_all(data: &[u8], pat: &[u8]) -> Vec<usize> {
    data.windows(pat.len())
        .enumerate()
        .filter(|(_, w)| *w == pat)
        .map(|(i, _)| i)
        .collect()
}

/// Find the unique occurrence of `needle` in `haystack`.
fn locate_unique(haystack: &[u8], needle: &[u8]) -> usize {
    assert!(needle.len() <= haystack.len());
    let mut hits =
        (0..=haystack.len() - needle.len()).filter(|&i| haystack[i..i + needle.len()] == *needle);
    let pos = hits.next().expect("needle not found in file");
    assert!(hits.next().is_none(), "needle occurs more than once");
    pos
}

/// Read a uleb128 at `pos`; return `(value, byte length)`.
fn read_uleb(data: &[u8], pos: usize) -> (u32, usize) {
    let mut value = 0u32;
    let mut shift = 0;
    let mut i = pos;
    loop {
        let b = data[i];
        value |= ((b & 0x7f) as u32) << shift;
        i += 1;
        if b & 0x80 == 0 {
            return (value, i - pos);
        }
        shift += 7;
    }
}

/// adler32 with initial 1, matching the vendored writer's checksum
/// backfill (same as legacy_decode.rs / decode_rare_arms.rs).
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

/// Rewrite the header version to 0.0.0.2 (legacy) and refresh the checksum.
fn set_legacy_version(data: &mut [u8]) {
    data[VERSION_OFF..VERSION_OFF + 4].copy_from_slice(&LEGACY_VERSION);
    let checksum = adler32(&data[VERSION_OFF..]);
    data[CHECKSUM_OFF..CHECKSUM_OFF + 4].copy_from_slice(&checksum.to_le_bytes());
}

/// Read a method's final (post-relocation) code bytes through the sys
/// layer (same walk as legacy_decode.rs / decode_rare_arms.rs).
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

/// A method's proto item offset, learned through the sys layer.
fn method_proto_offset(data: &[u8], method_offset: u32) -> u32 {
    let f = unsafe { abcd_file_sys::abc_file_open(data.as_ptr(), data.len()) };
    assert!(!f.is_null(), "abc_file_open failed");
    let mr = unsafe { abcd_file_sys::abc_method_open(f, method_offset) };
    assert!(!mr.is_null(), "abc_method_open failed");
    let proto = unsafe { abcd_file_sys::abc_method_get_proto_id(mr) };
    unsafe { abcd_file_sys::abc_method_close(mr) };
    unsafe { abcd_file_sys::abc_file_close(f) };
    assert_ne!(proto, u32::MAX, "method has no proto");
    proto
}

// ---------------------------------------------------------------------------
// Item walkers (tagged streams)
// ---------------------------------------------------------------------------

/// Walk a method item's tagged stream. Returns `(tag, tag_pos, value_pos)`
/// per entry; u32-valued tags only appear in the result (SOURCE_LANG's u8
/// value is skipped silently).
fn walk_method_tags(data: &[u8], method_off: usize) -> Vec<(u8, usize, usize)> {
    // [u16 class_idx][u16 proto_idx][u32 name_off][uleb access_flags]
    let (_, flags_len) = read_uleb(data, method_off + 8);
    let mut pos = method_off + 8 + flags_len;
    let mut out = Vec::new();
    loop {
        let tag = data[pos];
        if tag == 0 {
            return out; // NOTHING
        }
        match tag {
            0x02 => pos += 2, // SOURCE_LANG: u8 value
            0x01..=0x09 => {
                // CODE / annotations / debug: u32 value
                out.push((tag, pos, pos + 1));
                pos += 5;
            }
            other => panic!("unexpected method tag {other:#x} at {pos:#x}"),
        }
    }
}

/// Walk a field item's tagged stream (same triple shape as methods).
/// INT_VALUE's uleb value is skipped silently.
fn walk_field_tags(data: &[u8], field_off: usize) -> Vec<(u8, usize, usize)> {
    // [u16 class_idx][u16 type_idx][u32 name_off][uleb access_flags]
    let (_, flags_len) = read_uleb(data, field_off + 8);
    let mut pos = field_off + 8 + flags_len;
    let mut out = Vec::new();
    loop {
        let tag = data[pos];
        if tag == 0 {
            return out;
        }
        match tag {
            0x01 => {
                // INT_VALUE: uleb scalar.
                let (_, len) = read_uleb(data, pos + 1);
                pos += 1 + len;
            }
            0x02..=0x06 => {
                out.push((tag, pos, pos + 1));
                pos += 5;
            }
            other => panic!("unexpected field tag {other:#x} at {pos:#x}"),
        }
    }
}

/// Walk a class item's tagged stream (same triple shape). The walker parses
/// the inline descriptor string item first.
fn walk_class_tags(data: &[u8], class_off: usize) -> Vec<(u8, usize, usize)> {
    // Inline descriptor string item: [uleb tag][bytes][NUL].
    let (tag_byte, tag_len) = read_uleb(data, class_off);
    let utf16_len = (tag_byte >> 1) as usize;
    let is_ascii = tag_byte & 1 == 1;
    // MUTF-8 bytes: ASCII strings are 1 byte/unit; the fixtures here only
    // ever carry ASCII descriptors, so the byte count is the unit count.
    assert!(
        is_ascii,
        "craft walker only supports ASCII class descriptors"
    );
    let mut pos = class_off + tag_len + utf16_len + 1; // + NUL
    pos += 4; // super_class
    let (_, l1) = read_uleb(data, pos); // access_flags
    pos += l1;
    let (_, l2) = read_uleb(data, pos); // num_fields
    pos += l2;
    let (_, l3) = read_uleb(data, pos); // num_methods
    pos += l3;
    let mut out = Vec::new();
    loop {
        let tag = data[pos];
        if tag == 0 {
            return out;
        }
        match tag {
            0x01 => {
                // INTERFACES: uleb count + count × u16.
                let (count, len) = read_uleb(data, pos + 1);
                pos += 1 + len + count as usize * 2;
            }
            0x02 => pos += 2, // SOURCE_LANG: u8
            0x03..=0x07 => {
                out.push((tag, pos, pos + 1));
                pos += 5;
            }
            other => panic!("unexpected class tag {other:#x} at {pos:#x}"),
        }
    }
}

/// The single index region's header offset (the writer emits exactly one).
fn index_header_off(data: &[u8]) -> usize {
    let num = header_field(data, NUM_INDEXES_OFF);
    assert_eq!(num, 1, "craft assumes a single index region, got {num}");
    header_field(data, INDEX_SECTION_OFF) as usize
}

/// Locate a single-element annotation item via its element-name string.
/// Layout: `[u16 class_idx][u16 count][(u32 name_off, u32 value)][u8 tag]`.
/// Returns `(item_off, value_pos, tag_pos)`.
fn locate_annotation(data: &[u8], elem_name: &str, tag: u8) -> (usize, usize, usize) {
    let mut pat = vec![((elem_name.len() as u8) << 1) | 1];
    pat.extend_from_slice(elem_name.as_bytes());
    pat.push(0);
    let str_offs = find_all(data, &pat);
    assert_eq!(
        str_offs.len(),
        1,
        "string item for {elem_name}: {str_offs:?}"
    );
    let str_off = str_offs[0] as u32;
    for name_pos in find_all(data, &str_off.to_le_bytes()) {
        if name_pos < 4 || name_pos + 9 > data.len() {
            continue;
        }
        let ann_off = name_pos - 4;
        let count = u16::from_le_bytes(data[ann_off + 2..ann_off + 4].try_into().unwrap());
        if count == 1 && data[name_pos + 8] == tag {
            return (ann_off, name_pos + 4, name_pos + 8);
        }
    }
    panic!("annotation element for {elem_name} not found");
}

/// Locate an ASCII string item `[uleb (len<<1)|1][bytes][NUL]`; returns the
/// item offset (the uleb byte).
fn locate_string_item(data: &[u8], s: &str) -> usize {
    let mut pat = vec![(((s.len() as u8) << 1) | 1)];
    pat.extend_from_slice(s.as_bytes());
    pat.push(0);
    let hits = find_all(data, &pat);
    assert_eq!(hits.len(), 1, "string item for {s}: {hits:?}");
    hits[0]
}

/// Inflate a single-byte-uleb ASCII string item's declared utf16 length by
/// one: the payload then decodes to FEWER units than declared, so the
/// bridge's bounded UTF-16 validation fails (`convert_string_utf16_bounded`
/// requires exact agreement) and the lossless read returns None.
fn inflate_string_item_len(data: &mut [u8], item_off: usize) {
    let tag = data[item_off];
    assert_eq!(tag & 0x80, 0, "craft requires a single-byte uleb tag");
    assert_eq!(tag & 1, 1, "craft requires an ASCII string item");
    data[item_off] = tag + 2; // utf16_len + 1
}

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// Minimal file: global class + one `returnundefined` method (no debug
/// items, no annotations, no literal arrays).
fn build_minimal() -> Vec<u8> {
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
    b.finalize().expect("finalize")
}

/// The decoded offset of the sole method named `name`.
fn method_offset_of(file: &abcd_file::File, name: &str) -> u32 {
    file.all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some(name))
        .unwrap_or_else(|| panic!("method {name} missing"))
        .1
        .offset
}

/// The header class-index entry `i` (a class item offset).
fn class_item_off(data: &[u8], i: usize) -> u32 {
    let table = header_field(data, CLASS_IDX_OFF) as usize;
    header_field(data, table + i * 4)
}

// ---------------------------------------------------------------------------
// Class index / open arms
// ---------------------------------------------------------------------------

/// Corrupt class-index entries never reach decode's class passes: the
/// vendored debug extractor walks every non-external class first and its
/// throw is the hard `Error::DebugInfoExtraction` (N55). This pins the
/// shadowing that makes the entity-map/main-pass skip arms uncraftable.
#[test]
fn corrupt_class_index_entry_trips_debug_extractor_first() {
    let mut data = build_minimal();
    let num_classes = header_field(&data, NUM_CLASSES_OFF);
    assert_eq!(num_classes, 1, "fixture has exactly one class");
    let table = header_field(&data, CLASS_IDX_OFF) as usize;
    write_u32(&mut data, table, u32::MAX);
    let err = decode(&data).expect_err("the extractor dies before the class passes");
    assert!(
        matches!(err, Error::DebugInfoExtraction),
        "expected DebugInfoExtraction, got: {err:?}"
    );
}

/// Class descriptor whose declared utf16 length disagrees with the payload:
/// the lossless read fails, the raw-pointer fallback answers the lossy form
/// (decode.rs read_class_descriptor), and then the class NAME read — which
/// has no fallback — fails loudly.
#[test]
fn class_name_unreadable_is_hard_error() {
    let mut data = build_minimal();
    let class_off = class_item_off(&data, 0) as usize;
    // Sanity: "L_GLOBAL;" — 9 ASCII chars, tag byte (9 << 1) | 1 = 0x13.
    assert_eq!(data[class_off], 0x13, "global class descriptor tag byte");
    inflate_string_item_len(&mut data, class_off);
    let err = decode(&data).expect_err("unreadable class name must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "name",
                context,
            } if context.starts_with("class L_GLOBAL;")
        ),
        "expected Malformed/name for the class, got: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Method item arms
// ---------------------------------------------------------------------------

/// A method whose tagged stream has no CODE entry (tag byte flipped to
/// NOTHING) decodes bodiless: `code_off == ABSENT`.
#[test]
fn method_code_tag_absent_decodes_bodiless() {
    let mut data = build_minimal();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let tags = walk_method_tags(&data, m_off);
    let code_tag = tags
        .iter()
        .find(|(tag, _, _)| *tag == 0x01)
        .expect("CODE tag present");
    data[code_tag.1] = 0x00; // NOTHING: ends the tagged stream before CODE
    let file = decode(&data).expect("a codeless method decodes fine");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert!(m.body.is_none(), "the method must decode without a body");
}

/// The legacy (0.0.0.2) blob pass skips bodiless methods: the same codeless
/// craft under the legacy version gate.
#[test]
fn legacy_bodiless_method_skips_blob_pass() {
    let mut data = build_minimal();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let code_tag = walk_method_tags(&data, m_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x01)
        .expect("CODE tag present");
    data[code_tag.1] = 0x00;
    set_legacy_version(&mut data);
    let file = decode(&data).expect("legacy decode of a bodiless method");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert!(m.body.is_none(), "the method must decode without a body");
}

/// A CODE tag value pointing past the declared file size fails the code
/// accessor open loudly.
#[test]
fn method_code_offset_bogus_is_hard_error() {
    let mut data = build_minimal();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let (_, _, value_pos) = walk_method_tags(&data, m_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x01)
        .expect("CODE tag present");
    write_u32(&mut data, value_pos, BOGUS);
    let err = decode(&data).expect_err("a dangling code item must fail");
    assert!(
        matches!(err, Error::InvalidOffset(o) if o == BOGUS),
        "expected InvalidOffset({BOGUS:#x}), got: {err:?}"
    );
}

/// Minimal file at API 9: the proto-index wiring the proto crafts need is
/// only emitted there (the 12.x writer leaves proto_idx invalid — the
/// "empty proto" quirk proto_queries.rs / param_annotations.rs pin).
fn build_minimal_api9() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(9, "");
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
    let data = b.finalize().expect("finalize");
    // Fixture guard: the method must decode WITH a signature.
    let file = decode(&data).expect("control decode");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert_eq!(
        m.return_type,
        Some(Type::Tagged),
        "API-9 output must carry the proto"
    );
    data
}

/// The method's proto index resolves to a table entry of `u32::MAX`:
/// `has_valid_proto` holds (the 16-bit proto_idx is valid) but the resolved
/// proto offset is ABSENT, so the method decodes with no signature.
#[test]
fn method_proto_table_entry_absent_decodes_protoidless() {
    let mut data = build_minimal_api9();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    // The method item's proto_idx (u16 at +2) selects the region proto
    // table entry; corrupt that entry to ABSENT.
    let proto_idx = u16::from_le_bytes(data[m_off + 2..m_off + 4].try_into().unwrap()) as usize;
    let ih = index_header_off(&data);
    let proto_idx_off = header_field(&data, ih + 36) as usize;
    write_u32(&mut data, proto_idx_off + proto_idx * 4, u32::MAX);
    let file = decode(&data).expect("an ABSENT proto id decodes to no signature");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert_eq!(m.return_type, None, "no signature must be decoded");
    assert!(m.arg_types.is_empty());
}

/// The method's proto index resolves to a proto offset past the declared
/// file size: the proto item's shorty read throws in the bridge, which
/// answers `UINT8_MAX` — an unknown type id. (The proto OPEN cannot fail:
/// the vendored ProtoDataAccessor ctor performs no validation.)
#[test]
fn method_proto_offset_bogus_is_hard_error() {
    let mut data = build_minimal_api9();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let proto_idx = u16::from_le_bytes(data[m_off + 2..m_off + 4].try_into().unwrap()) as usize;
    let ih = index_header_off(&data);
    let proto_idx_off = header_field(&data, ih + 36) as usize;
    write_u32(&mut data, proto_idx_off + proto_idx * 4, BOGUS);
    let err = decode(&data).expect_err("a dangling proto item must fail");
    assert!(
        matches!(err, Error::UnknownTypeId(0xFF)),
        "expected UnknownTypeId(0xff), got: {err:?}"
    );
}

/// A method whose access-flags function-kind bits are not a known
/// discriminant decodes with `FunctionKind::None` (the `unwrap_or`
/// fallback on `FunctionKind::try_from`). The bridge derives the kind from
/// the method item's access flags.
#[test]
fn method_unknown_function_kind_decodes_none() {
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
    b.method_set_function_kind(m, abcd_file::FunctionKind::Function);
    let mut data = b.finalize().expect("finalize");

    // Control: the kind round-trips while the flags are intact.
    let file = decode(&data).expect("control decode");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert_eq!(m.function_kind, abcd_file::FunctionKind::Function);

    // access_flags = PUBLIC | Function << 8 = 0x101 (uleb [0x81, 0x02]);
    // rewrite the kind nibble to 0xF (no such FunctionKind): uleb
    // [0x81, 0x1E] = 0xF01.
    let m_off = m.offset as usize;
    assert_eq!(&data[m_off + 8..m_off + 10], &[0x81, 0x02]);
    data[m_off + 9] = 0x1E;
    let file = decode(&data).expect("an unknown function kind is not fatal");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert_eq!(
        m.function_kind,
        abcd_file::FunctionKind::None,
        "an unknown kind byte must degrade to None"
    );
}

// ---------------------------------------------------------------------------
// Annotation list `?` arms (method ×4, field ×4, class ×4)
// ---------------------------------------------------------------------------

/// Build a file whose single method carries one compile-time annotation
/// (tag 0x06 in the method item's tagged stream).
fn build_method_with_annotation() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let name = b.add_string("level");
    let ann = b.create_annotation(
        cls,
        &[AnnotationElemDef {
            name,
            tag: b'7',
            value: 1,
        }],
    );
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
    b.method_add_annotation(m, ann);
    b.finalize().expect("finalize")
}

/// Each method annotation category's decode bucket propagates a dangling
/// annotation offset loudly. The API-12 writer emits every category as the
/// compile-time (ANNOTATION) tag; the craft rewrites the tag byte to the
/// target category and corrupts the offset.
#[test]
fn method_annotation_offset_bogus_is_hard_error() {
    // (target tag in the method item, bucket name)
    for (tag, bucket) in [
        (0x06u8, "compile-time"),
        (0x03, "runtime"),
        (0x08, "type"),
        (0x09, "runtime-type"),
    ] {
        let mut data = build_method_with_annotation();
        let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
        let entries = walk_method_tags(&data, m_off);
        let entry = entries
            .iter()
            .find(|(t, _, _)| *t == 0x06)
            .expect("ANNOTATION tag present");
        data[entry.1] = tag; // reassign the category
        write_u32(&mut data, entry.2, BOGUS);
        let err = decode(&data).expect_err("a dangling annotation offset must fail");
        assert!(
            matches!(err, Error::InvalidOffset(o) if o == BOGUS),
            "expected InvalidOffset({BOGUS:#x}) for the {bucket} bucket, got: {err:?}"
        );
    }
}

/// Build a file whose global class's field carries one compile-time
/// annotation (tag 0x04 in the field item's tagged stream).
fn build_field_with_annotation() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let name = b.add_string("level");
    let ann = b.create_annotation(
        cls,
        &[AnnotationElemDef {
            name,
            tag: b'7',
            value: 1,
        }],
    );
    let f = b.class_add_field(cls, "fx", Type::I32, AccessFlags::PUBLIC);
    b.field_add_annotation(f, ann);
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

/// The field compile-time and runtime annotation buckets propagate a
/// dangling annotation offset loudly (same tag-rewrite craft as the method
/// buckets). The field type/runtime-type buckets are NOT craftable: the
/// vendored field accessor enumerates them via `FieldTag::ANNOTATION`
/// (upstream quirk), so the compile-time read of the same entries always
/// fails first — see the module docs.
#[test]
fn field_annotation_offset_bogus_is_hard_error() {
    for (tag, bucket) in [(0x04u8, "compile-time"), (0x03, "runtime")] {
        let mut data = build_field_with_annotation();
        let file = decode(&data).expect("decode");
        let g = file.classes.values().find(|c| !c.is_external).unwrap();
        let f_off = g
            .fields
            .iter()
            .find(|f| file.strings.resolve(f.name) == Some("fx"))
            .expect("field fx")
            .offset as usize;
        let entries = walk_field_tags(&data, f_off);
        let entry = entries
            .iter()
            .find(|(t, _, _)| *t == 0x04)
            .expect("ANNOTATION tag present");
        data[entry.1] = tag;
        write_u32(&mut data, entry.2, BOGUS);
        let err = decode(&data).expect_err("a dangling annotation offset must fail");
        assert!(
            matches!(err, Error::InvalidOffset(o) if o == BOGUS),
            "expected InvalidOffset({BOGUS:#x}) for the {bucket} bucket, got: {err:?}"
        );
    }
}

/// Build a file whose global class carries one compile-time annotation
/// (tag 0x04 in the class item's tagged stream).
fn build_class_with_annotation() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let name = b.add_string("level");
    let ann = b.create_annotation(
        cls,
        &[AnnotationElemDef {
            name,
            tag: b'7',
            value: 1,
        }],
    );
    b.class_add_annotation(cls, ann);
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

/// Each class annotation category's decode bucket propagates a dangling
/// annotation offset loudly (same tag-rewrite craft).
#[test]
fn class_annotation_offset_bogus_is_hard_error() {
    for (tag, bucket) in [
        (0x04u8, "compile-time"),
        (0x03, "runtime"),
        (0x06, "type"),
        (0x05, "runtime-type"),
    ] {
        let mut data = build_class_with_annotation();
        let class_off = class_item_off(&data, 0) as usize;
        let entries = walk_class_tags(&data, class_off);
        let entry = entries
            .iter()
            .find(|(t, _, _)| *t == 0x04)
            .expect("ANNOTATION tag present");
        data[entry.1] = tag;
        write_u32(&mut data, entry.2, BOGUS);
        let err = decode(&data).expect_err("a dangling annotation offset must fail");
        assert!(
            matches!(err, Error::InvalidOffset(o) if o == BOGUS),
            "expected InvalidOffset({BOGUS:#x}) for the {bucket} bucket, got: {err:?}"
        );
    }
}

/// An annotation item whose class index is out of the region class table
/// resolves to offset 0, which is never in the entity map: hard error.
#[test]
fn annotation_class_index_oob_is_hard_error() {
    let mut data = build_class_with_annotation();
    let (ann_off, _, _) = locate_annotation(&data, "level", b'7');
    data[ann_off..ann_off + 2].copy_from_slice(&0x7FFFu16.to_le_bytes());
    let err = decode(&data).expect_err("an unresolvable annotation class must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "class_descriptor",
                context,
            } if context.starts_with("annotation at offset")
        ),
        "expected Malformed/class_descriptor, got: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Foreign-entity name fallbacks (decode.rs resolve_foreign_entity_name)
// ---------------------------------------------------------------------------

/// Build a file whose global class carries an annotation with a METHOD
/// element (tag 'E') referencing a FOREIGN method.
fn build_foreign_method_annotation() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let foreign = b.add_foreign_method(cls, "foreign_fn", proto, AccessFlags::PUBLIC);
    let name = b.add_string("mref");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name,
            tag: b'E', // Method
            value: AnnotationElemValue::EntityRef(foreign.as_raw()),
        }],
    );
    b.class_add_runtime_annotation(cls, ann);
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

/// The foreign method's decoded entity offset (learned from the annotation
/// element), so the crafts can patch its item's name field (item+4).
fn foreign_method_offset(data: &[u8]) -> usize {
    let file = decode(data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let ann = &g.annotations.compile_time[0];
    match &ann.elements[0].value {
        AnnotationValue::Method { offset, .. } => *offset as usize,
        other => panic!("expected Method element, got {other:?}"),
    }
}

/// A foreign method item whose name field reads ABSENT falls back to the
/// empty string (edge fallback, not an error).
#[test]
fn foreign_method_name_absent_falls_back_to_empty() {
    let mut data = build_foreign_method_annotation();
    let f_off = foreign_method_offset(&data);
    write_u32(&mut data, f_off + 4, u32::MAX); // name_off = ABSENT
    let file = decode(&data).expect("an ABSENT foreign name is not an error");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    match &g.annotations.compile_time[0].elements[0].value {
        AnnotationValue::Method { name, .. } => {
            assert_eq!(file.strings.resolve(*name), Some(""));
        }
        other => panic!("expected Method element, got {other:?}"),
    }
}

/// A foreign method item whose name string is unreadable falls back to the
/// empty string (edge fallback, not an error).
#[test]
fn foreign_method_name_unreadable_falls_back_to_empty() {
    let mut data = build_foreign_method_annotation();
    let decoy = locate_string_item(&data, "foreign_fn");
    inflate_string_item_len(&mut data, decoy);
    let file = decode(&data).expect("an unreadable foreign name is not an error");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    match &g.annotations.compile_time[0].elements[0].value {
        AnnotationValue::Method { name, .. } => {
            assert_eq!(file.strings.resolve(*name), Some(""));
        }
        other => panic!("expected Method element, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Param-annotations item arms
// ---------------------------------------------------------------------------

/// Build a file whose method carries one sealed compile-time param
/// annotation (param_annotations.rs fixture shape).
fn build_param_annotation() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(9, "");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[Type::Tagged]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        2,
        1,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let p0 = b.method_add_param(m, Type::Tagged);
    let name = b.add_string("value");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name,
            tag: b'7',
            value: AnnotationElemValue::Scalar(7),
        }],
    );
    b.method_param_add_annotation(m, p0, ann);
    b.method_seal_param_annotations(m, false);
    b.finalize().expect("finalize")
}

/// A param-annotations item offset pointing at a span too short for the
/// num_params header fails the enumeration loudly (bridge rc != 0).
#[test]
fn param_annotations_item_truncated_is_hard_error() {
    let mut data = build_param_annotation();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let entry = walk_method_tags(&data, m_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x07) // PARAM_ANNOTATION
        .expect("PARAM_ANNOTATION tag present");
    let file_size = header_field(&data, FILE_SIZE_OFF);
    let short = file_size - 2; // in-span but shorter than the u32 header
    write_u32(&mut data, entry.2, short);
    let err = decode(&data).expect_err("a truncated param-annotations item must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "param_annotations",
                context,
            } if context.starts_with("param annotations item at offset")
        ),
        "expected Malformed/param_annotations, got: {err:?}"
    );
}

/// A param-annotations item whose embedded ANNOTATION offset dangles fails
/// loudly through the param-annotation decode (`decode_annotation_list`
/// inside the pair loop).
#[test]
fn param_annotation_entry_dangling_is_hard_error() {
    let mut data = build_param_annotation();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let entry = walk_method_tags(&data, m_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x07)
        .expect("PARAM_ANNOTATION tag present");
    let item_off = header_field(&data, entry.2) as usize;
    // [u32 num_params=1][u32 count=1][u32 annotation_off]
    assert_eq!(header_field(&data, item_off), 1, "fixture: one param");
    assert_eq!(
        header_field(&data, item_off + 4),
        1,
        "fixture: one annotation"
    );
    write_u32(&mut data, item_off + 8, BOGUS);
    let err = decode(&data).expect_err("a dangling param annotation must fail");
    assert!(
        matches!(err, Error::InvalidOffset(o) if o == BOGUS),
        "expected InvalidOffset({BOGUS:#x}), got: {err:?}"
    );
}

/// A param-annotations item declaring zero params enumerates no pairs: the
/// method's buckets stay empty (edge, not an error).
#[test]
fn param_annotations_zero_params_is_empty() {
    let mut data = build_param_annotation();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let entry = walk_method_tags(&data, m_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x07)
        .expect("PARAM_ANNOTATION tag present");
    let item_off = header_field(&data, entry.2) as usize;
    write_u32(&mut data, item_off, 0); // num_params = 0
    let file = decode(&data).expect("a zero-param item decodes fine");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert!(
        m.param_annotations.compile_time.is_empty() && m.param_annotations.runtime.is_empty(),
        "no buckets must be created for a zero-pair item"
    );
}

// ---------------------------------------------------------------------------
// Field arms
// ---------------------------------------------------------------------------

/// A field whose name offset is ABSENT fails loudly.
#[test]
fn field_name_absent_is_hard_error() {
    let mut data = build_field_with_annotation();
    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let f_off = g
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("fx"))
        .expect("field fx")
        .offset as usize;
    write_u32(&mut data, f_off + 4, u32::MAX); // name_off = ABSENT
    let err = decode(&data).expect_err("an ABSENT field name must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "name",
                context,
            } if context.starts_with("field at offset")
        ),
        "expected Malformed/name for the field, got: {err:?}"
    );
}

/// A field whose name string is unreadable fails loudly.
#[test]
fn field_name_unreadable_is_hard_error() {
    let mut data = build_field_with_annotation();
    let item = locate_string_item(&data, "fx");
    inflate_string_item_len(&mut data, item);
    let err = decode(&data).expect_err("an unreadable field name must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "name",
                context,
            } if context.starts_with("field at offset")
        ),
        "expected Malformed/name for the field, got: {err:?}"
    );
}

/// A reference-typed field whose type entity offset is in no class table
/// entry's payload fails loudly (entity_map miss).
#[test]
fn field_reference_type_unresolvable_is_hard_error() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let ext = b.add_foreign_class("LExternal;");
    let mut pool = abcd_file::StringPool::default();
    let desc = pool.get_or_intern("LExternal;");
    let _f = b.class_add_field_ex(cls, "obj", Type::Reference(desc), ext, AccessFlags::PUBLIC);
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
    let mut data = b.finalize().expect("finalize");

    // The field item's type_idx (u16 at +2) selects a region class-table
    // entry; corrupt that entry so the resolved type offset is in no
    // entity map (BOGUS is past the file: certainly no class item).
    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let f_off = g
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("obj"))
        .expect("field obj")
        .offset as usize;
    let type_idx = u16::from_le_bytes(data[f_off + 2..f_off + 4].try_into().unwrap()) as usize;
    let ih = index_header_off(&data);
    let class_idx_off = header_field(&data, ih + 12) as usize;
    write_u32(&mut data, class_idx_off + type_idx * 4, BOGUS);
    let err = decode(&data).expect_err("an unresolvable field type must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "field_type",
                ..
            }
        ),
        "expected Malformed/field_type, got: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Module blob arms
// ---------------------------------------------------------------------------

/// Build a file with an `_ESModuleRecord` class (one request + one record)
/// and a minimal global class. Returns the bytes; the blob offset is
/// learnable from the decoded field value.
fn build_module_blob() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let rec_cls = b.add_class("L_ESModuleRecord;");
    b.class_set_source_lang(rec_cls, SourceLang::EcmaScript);
    let field = b.class_add_field(rec_cls, "test.js", Type::U32, AccessFlags::PUBLIC);
    let dep = b.add_string("dep1");
    let records = vec![abcd_file::ModuleRecordDef::RegularImport {
        local_name: b.add_string("local1"),
        import_name: b.add_string("imp1"),
        module_request_idx: 0,
    }];
    let module_la = b.add_literal_array("module");
    b.literal_array_add_module_data(module_la, &[dep], &records)
        .expect("stage module data");
    b.field_set_value_literalarray(field, module_la)
        .expect("wire module field");

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
    b.finalize().expect("finalize")
}

/// The module blob's source offset, learned from a decode.
fn module_blob_off(data: &[u8]) -> usize {
    let file = decode(data).expect("decode");
    let rec = file
        .class_by_str("L_ESModuleRecord;")
        .expect("record class");
    let field = &rec.fields[0];
    match &field.initial_value {
        Some(FieldValue::ModuleData(md)) => md.source_offset as usize,
        other => panic!("expected ModuleData field value, got {other:?}"),
    }
}

/// A module request whose string offset is ABSENT fails loudly. The field
/// decode wraps the module-data error with the field's identity.
#[test]
fn module_request_offset_absent_is_hard_error() {
    let mut data = build_module_blob();
    let blob = module_blob_off(&data);
    // [u32 item count][u32 num_requests][request 0 offset]
    write_u32(&mut data, blob + 8, u32::MAX);
    let err = decode(&data).expect_err("an ABSENT module request offset must fail");
    assert!(
        matches!(&err, Error::ModuleData(msg) if msg.contains("string at offset 0xffffffff is invalid")),
        "expected ModuleData wrapping InvalidString(u32::MAX), got: {err:?}"
    );
}

/// A module request whose string item is unreadable fails loudly.
#[test]
fn module_request_string_unreadable_is_hard_error() {
    let mut data = build_module_blob();
    let blob = module_blob_off(&data);
    let short = header_field(&data, FILE_SIZE_OFF) - 2;
    write_u32(&mut data, blob + 8, short);
    let err = decode(&data).expect_err("an unreadable module request string must fail");
    let want = format!("string at offset {short:#x} is invalid");
    assert!(
        matches!(&err, Error::ModuleData(msg) if msg.contains(&want)),
        "expected ModuleData wrapping InvalidString({short:#x}), got: {err:?}"
    );
}

/// Build a module blob with one request and one record of EACH kind
/// (regular import, namespace import, local export, indirect export, star
/// export), so the section-walking crafts can corrupt any name field.
fn build_module_blob_all_records() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let rec_cls = b.add_class("L_ESModuleRecord;");
    b.class_set_source_lang(rec_cls, SourceLang::EcmaScript);
    let field = b.class_add_field(rec_cls, "test.js", Type::U32, AccessFlags::PUBLIC);
    let dep = b.add_string("dep1");
    let records = vec![
        abcd_file::ModuleRecordDef::RegularImport {
            local_name: b.add_string("ri_local"),
            import_name: b.add_string("ri_imp"),
            module_request_idx: 0,
        },
        abcd_file::ModuleRecordDef::NamespaceImport {
            local_name: b.add_string("ns_local"),
            module_request_idx: 0,
        },
        abcd_file::ModuleRecordDef::LocalExport {
            local_name: b.add_string("le_local"),
            export_name: b.add_string("le_exp"),
        },
        abcd_file::ModuleRecordDef::IndirectExport {
            export_name: b.add_string("ie_exp"),
            import_name: b.add_string("ie_imp"),
            module_request_idx: 0,
        },
        abcd_file::ModuleRecordDef::StarExport {
            module_request_idx: 0,
        },
    ];
    let module_la = b.add_literal_array("module");
    b.literal_array_add_module_data(module_la, &[dep], &records)
        .expect("stage module data");
    b.field_set_value_literalarray(field, module_la)
        .expect("wire module field");

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
    b.finalize().expect("finalize")
}

/// Walk the module blob's section layout (module_data_accessor-inl.h
/// EnumerateModuleRecord) and return the byte position of the given
/// section's first entry's `field_index`-th u32 name field. Sections in
/// vendored order: RegularImport (local, import, u16 idx),
/// NamespaceImport (local, u16 idx), LocalExport (local, export),
/// IndirectExport (export, import, u16 idx), StarExport (u16 idx).
fn module_record_name_pos(data: &[u8], blob: usize, section: usize, field_index: usize) -> usize {
    let num_requests = header_field(data, blob + 4) as usize;
    let mut pos = blob + 8 + 4 * num_requests; // entry_data_sp_
    let section_layouts: [&[usize]; 5] = [
        &[4, 4, 2], // RegularImport: local u32, import u32, idx u16
        &[4, 2],    // NamespaceImport: local u32, idx u16
        &[4, 4],    // LocalExport: local u32, export u32
        &[4, 4, 2], // IndirectExport: export u32, import u32, idx u16
        &[2],       // StarExport: idx u16
    ];
    for (i, layout) in section_layouts.iter().enumerate() {
        let count = header_field(data, pos) as usize;
        pos += 4;
        let entry_size: usize = layout.iter().sum();
        if i == section {
            assert_eq!(count, 1, "fixture: one record in section {section}");
            // Position of the field_index-th u32 field inside entry 0.
            let mut field_pos = pos;
            for (j, width) in layout.iter().enumerate() {
                if j == field_index {
                    return field_pos;
                }
                field_pos += width;
            }
            panic!("section {section} has no u32 field {field_index}");
        }
        pos += count * entry_size;
    }
    panic!("section {section} not found");
}

/// Every module-record name field fails loudly when its offset dangles
/// (the per-record-kind `intern_string_at` arms).
#[test]
fn module_record_name_dangling_is_hard_error() {
    // (section, field_index, record-kind name, field name)
    for (section, field_index, kind, field) in [
        (0, 0, "RegularImport", "local_name"),
        (0, 1, "RegularImport", "import_name"),
        (1, 0, "NamespaceImport", "local_name"),
        (2, 0, "LocalExport", "local_name"),
        (2, 1, "LocalExport", "export_name"),
        (3, 0, "IndirectExport", "export_name"),
        (3, 1, "IndirectExport", "import_name"),
    ] {
        let mut data = build_module_blob_all_records();
        let blob = module_blob_off(&data);
        let pos = module_record_name_pos(&data, blob, section, field_index);
        write_u32(&mut data, pos, BOGUS);
        let err = decode(&data).expect_err("a dangling module-record name must fail");
        let want = format!("string at offset {BOGUS:#x} is invalid");
        assert!(
            matches!(&err, Error::ModuleData(msg) if msg.contains(&want)),
            "expected ModuleData wrapping InvalidString({BOGUS:#x}) for {kind}.{field}, got: {err:?}"
        );
    }
}

/// An `_ESModuleRecord` u32 field value with the sign bit set is a negative
/// blob offset: hard error, never a misread.
#[test]
fn module_record_negative_blob_offset_is_hard_error() {
    let mut data = build_module_blob();
    negate_field_value(&mut data, "L_ESModuleRecord;", "test.js");
    let err = decode(&data).expect_err("a negative blob offset must fail");
    assert!(
        matches!(&err, Error::ModuleData(msg) if msg.contains("negative blob offset")),
        "expected ModuleData/negative blob offset, got: {err:?}"
    );
}

/// Flip the named class's named u32 field value to `i32::MIN` (the field
/// item's VALUE tag payload).
fn negate_field_value(data: &mut [u8], class: &str, field: &str) {
    let file = decode(data).expect("decode");
    let cls = file.class_by_str(class).expect("class present");
    let f = cls
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some(field))
        .expect("field present");
    let f_off = f.offset as usize;
    let entry = walk_field_tags(data, f_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x02) // VALUE: u32 inline offset
        .expect("VALUE tag present");
    write_u32(data, entry.2, 0x8000_0000);
}

/// Build a file with an `_ESScopeNamesRecord` class carrying one u32 field
/// wired to a tagged literal array.
fn build_scope_names() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let scope_cls = b.add_class("L_ESScopeNamesRecord;");
    b.class_set_source_lang(scope_cls, SourceLang::EcmaScript);
    let scope_field = b.class_add_field(scope_cls, "test.js", Type::U32, AccessFlags::PUBLIC);
    let scope_la = b.add_literal_array("scope");
    let box_name = b.add_string("Box");
    b.literal_array_add_string(scope_la, box_name);
    b.field_set_value_literalarray(scope_field, scope_la)
        .expect("wire scope field");

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
    b.finalize().expect("finalize")
}

/// An `_ESScopeNamesRecord` u32 field value with the sign bit set is a
/// negative blob offset: hard error.
#[test]
fn scope_names_negative_blob_offset_is_hard_error() {
    let mut data = build_scope_names();
    negate_field_value(&mut data, "L_ESScopeNamesRecord;", "test.js");
    let err = decode(&data).expect_err("a negative blob offset must fail");
    assert!(
        matches!(&err, Error::ModuleData(msg) if msg.contains("negative blob offset")),
        "expected ModuleData/negative blob offset, got: {err:?}"
    );
}

/// Build a file with a `moduleRequestPhaseIdx` field on the module record
/// (the merge-abc layout, module_record_phase_field.rs).
fn build_phase_field() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_class("L_ESModuleRecord;");
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let phase_field =
        b.class_add_field(cls, "moduleRequestPhaseIdx", Type::U32, AccessFlags::PUBLIC);
    let phase_la = b.add_literal_array("phase");
    b.literal_array_add_module_request_phase(phase_la, &[1, 0, 1])
        .expect("stage phase blob");
    b.field_set_value_literalarray(phase_field, phase_la)
        .expect("wire phase field");

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
    b.finalize().expect("finalize")
}

/// A `moduleRequestPhaseIdx` field value with the sign bit set is a
/// negative blob offset: hard error.
#[test]
fn phase_field_negative_blob_offset_is_hard_error() {
    let mut data = build_phase_field();
    negate_field_value(&mut data, "L_ESModuleRecord;", "moduleRequestPhaseIdx");
    let err = decode(&data).expect_err("a negative phase blob offset must fail");
    assert!(
        matches!(&err, Error::ModuleData(msg) if msg.contains("negative blob offset")),
        "expected ModuleData/negative blob offset, got: {err:?}"
    );
}

/// A phase blob that does not parse (too short for its u32 count) fails the
/// structural read; the field-level wrapper propagates the message.
#[test]
fn phase_blob_unreadable_is_hard_error() {
    let mut data = build_phase_field();
    // Point the field value at a 2-byte tail span.
    let file = decode(&data).expect("decode");
    let cls = file.class_by_str("L_ESModuleRecord;").expect("class");
    let f = cls
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("moduleRequestPhaseIdx"))
        .expect("phase field");
    let f_off = f.offset as usize;
    let entry = walk_field_tags(&data, f_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x02)
        .expect("VALUE tag present");
    let short = header_field(&data, FILE_SIZE_OFF) - 2;
    write_u32(&mut data, entry.2, short);
    let err = decode(&data).expect_err("an unreadable phase blob must fail");
    assert!(
        matches!(&err, Error::ModuleData(msg) if msg.contains("module-request-phase blob") && msg.contains("unreadable")),
        "expected ModuleData/module-request-phase blob unreadable, got: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Literal-array string interning arms (N72)
// ---------------------------------------------------------------------------

/// Two literal-array string elements with DIFFERENT raw MUTF-8 forms but
/// the SAME lossy content collide; when the disambiguated identity of the
/// second collides with a GENUINE pool string, interning fails loudly and
/// the error rides the collection context out of the C callback
/// (literal.rs error capture + decode.rs propagation). A THIRD lossy form
/// colliding the same way exercises the capture's "first error wins"
/// branch (the second error is dropped).
#[test]
fn literal_array_lossy_identity_collision_is_hard_error() {
    // ED A0 B4 = U+D834, ED B4 86 = U+DF06, ED B4 87 = U+DF07 — all
    // lossy-decode to three U+FFFD (see abcd-file/src/file.rs N72 tests).
    const RAW_A: [u8; 3] = [0xED, 0xA0, 0xB4];
    const RAW_B: [u8; 3] = [0xED, 0xB4, 0x86];
    const RAW_C: [u8; 3] = [0xED, 0xB4, 0x87];
    const LOSSY: &str = "\u{FFFD}\u{FFFD}\u{FFFD}";
    // The disambiguated identities RAW_B / RAW_C would get:
    // content + U+E000 + lowercase hex(raw).
    let genuine_b = format!("{LOSSY}\u{E000}edb486");
    let genuine_c = format!("{LOSSY}\u{E000}edb487");

    let mut b = Builder::new();
    b.set_api(12, "beta1");
    b.set_raw_strings(
        [
            ("key_a".to_string(), Box::from(&RAW_A[..])),
            ("key_b".to_string(), Box::from(&RAW_B[..])),
            ("key_c".to_string(), Box::from(&RAW_C[..])),
        ]
        .into_iter()
        .collect(),
    );
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let la = b.add_literal_array("s");
    // Order matters: the first lossy form records RAW_A; each genuine
    // string interns the exact disambiguated identity of the lossy form
    // that follows it, so both collisions fail loudly.
    let s_a = b.add_string("key_a");
    b.literal_array_add_string(la, s_a);
    let s_gb = b.add_string(&genuine_b);
    b.literal_array_add_string(la, s_gb);
    let s_b = b.add_string("key_b");
    b.literal_array_add_string(la, s_b);
    let s_gc = b.add_string(&genuine_c);
    b.literal_array_add_string(la, s_gc);
    let s_c = b.add_string("key_c");
    b.literal_array_add_string(la, s_c);
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
    let data = b.finalize().expect("finalize");

    let err = decode(&data).expect_err("a genuine identity collision must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "string",
                context,
            } if context.contains("genuine string collides with a disambiguated")
        ),
        "expected Malformed/string genuine-collision, got: {err:?}"
    );
}

/// A literal-array string element whose item is unreadable interns the
/// empty string (literal.rs `Ok(None)` fallback), never an error.
#[test]
fn literal_array_unreadable_string_interns_empty() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let la = b.add_literal_array("s");
    let victim = b.add_string("victimstr");
    b.literal_array_add_string(la, victim);
    b.literal_array_add_integer(la, 42);
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
    let mut data = b.finalize().expect("finalize");

    let item = locate_string_item(&data, "victimstr");
    inflate_string_item_len(&mut data, item);
    let file = decode(&data).expect("an unreadable literal string is not an error");
    let values = &file.literal_arrays[0].values;
    assert_eq!(values.len(), 2);
    match &values[0] {
        abcd_file::LiteralValue::String(sid) => {
            assert_eq!(file.strings.resolve(*sid), Some(""));
        }
        other => panic!("expected String element, got {other:?}"),
    }
}

/// Build a file with an ArrayMethodHandle ('@') annotation element holding
/// two method handles (to distinct targets). Returns the bytes; the payload
/// layout is `[uleb count=2][u32 mh1][u32 mh2]`.
fn build_method_handle_array() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let t1 = b.class_add_method(cls, "target1", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(t1, SourceLang::EcmaScript);
    let t2 = b.class_add_method(cls, "target2", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(t2, SourceLang::EcmaScript);
    let mh1 = b.create_method_handle(4, t1.as_raw()); // INVOKE_STATIC
    let mh2 = b.create_method_handle(4, t2.as_raw());
    let name = b.add_string("mhArr");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name,
            tag: b'@', // ArrayMethodHandle
            value: AnnotationElemValue::EntityArray(vec![mh1.as_raw(), mh2.as_raw()]),
        }],
    );
    b.class_add_runtime_annotation(cls, ann);
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

// ---------------------------------------------------------------------------
// Entity-operand resolution arms (modern + legacy)
// ---------------------------------------------------------------------------

/// A modern method operand index beyond the method's index region resolves
/// to ABSENT: hard error.
#[test]
fn modern_method_operand_index_oob_is_hard_error() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Void, &[]);
    // definefunc with a huge method-index operand, never relocated: the
    // method's index region has no such entry.
    let (code, _) = abcd_isa::encode(&[
        Bytecode::Definefunc(Imm(0), EntityId(0x7FFF), Imm(0)),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let m = b.class_add_method(cls, "caller", proto, AccessFlags::STATIC, &code, 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let data = b.finalize().expect("finalize");
    let err = decode(&data).expect_err("an out-of-range method operand must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "bytecode entity reference",
                context,
            } if context.contains("definefunc")
        ),
        "expected Malformed/bytecode entity reference, got: {err:?}"
    );
}

/// Build a file whose `caller` references a FOREIGN method through its
/// index region (decode_rare_arms.rs's fixture shape).
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
    insns.extend(std::iter::repeat_n(Bytecode::Nop, 32));
    let (code, offsets) = abcd_isa::encode(&insns).unwrap();
    let caller = b.class_add_method(cls, "caller", proto, AccessFlags::STATIC, &code, 1, 0);
    b.method_set_source_lang(caller, SourceLang::EcmaScript);
    b.relocate_code_id(caller, offsets[0], 0, CodeEntity::Method(foreign))
        .expect("relocate to foreign method");
    b.deduplicate();
    b.finalize().expect("finalize")
}

/// The caller's method-local index of the foreign method operand, learned
/// from a decode.
fn foreign_operand_index(data: &[u8]) -> u16 {
    let file = decode(data).expect("decode");
    let caller = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("caller"))
        .expect("caller")
        .1;
    let body = caller.body.as_ref().unwrap();
    let (kind, id) = body.bytecodes[0].entity_operands()[0];
    assert_eq!(kind, EntityKind::MethodId);
    u16::try_from(id.0).unwrap()
}

/// A method operand whose index-region entry points past the declared file
/// size: the direct open of the item fails loudly (modern path).
#[test]
fn modern_foreign_method_open_failure_is_hard_error() {
    let mut data = build_with_foreign_method_operand();
    let idx = foreign_operand_index(&data);
    let ih = index_header_off(&data);
    let method_idx_off = header_field(&data, ih + 20) as usize;
    write_u32(&mut data, method_idx_off + idx as usize * 4, BOGUS);
    let err = decode(&data).expect_err("an unopenable method operand must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "bytecode entity reference",
                context,
            } if context.contains("definefunc")
        ),
        "expected Malformed/bytecode entity reference, got: {err:?}"
    );
}

/// Legacy fixture: `caller`'s code stream rewritten to legacy encodings
/// (definefuncdyn id16 + return.dyn), version 0.0.0.2.
fn make_legacy(data: &mut [u8], legacy_stream: &[u8]) {
    let caller_off = method_offset_of(&decode(data).expect("modern decode"), "caller");
    let modern_bytes = method_code(data, caller_off);
    assert!(legacy_stream.len() <= modern_bytes.len());
    let pos = locate_unique(data, &modern_bytes);
    data[pos..pos + legacy_stream.len()].copy_from_slice(legacy_stream);
    data[pos + legacy_stream.len()..pos + modern_bytes.len()].fill(0x00);
    set_legacy_version(data);
}

/// Legacy: a method operand index with no index-region entry resolves to
/// ABSENT: hard error (legacy operand rule).
#[test]
fn legacy_method_operand_index_oob_is_hard_error() {
    let mut data = build_minimal_with_room();
    // definefuncdyn id16=0x7FFF, imm16=0, v0; return.dyn
    let stream = [0xff, 0x5f, 0xFF, 0x7F, 0x00, 0x00, 0x00, 0xa6];
    make_legacy(&mut data, &stream);
    let err = decode(&data).expect_err("a legacy out-of-range method operand must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "bytecode entity reference",
                ..
            }
        ),
        "expected Malformed/bytecode entity reference, got: {err:?}"
    );
}

/// Legacy: the foreign fallback's direct open fails when the index-region
/// entry points past the declared file size.
#[test]
fn legacy_foreign_method_open_failure_is_hard_error() {
    let mut data = build_with_foreign_method_operand();
    let idx = foreign_operand_index(&data);
    // Legacy stream: definefuncdyn id16, imm16, v0; return.dyn.
    let mut stream = vec![0xff, 0x5f];
    stream.extend_from_slice(&idx.to_le_bytes());
    stream.extend_from_slice(&[0x00, 0x00, 0x00]);
    stream.push(0xa6);
    make_legacy(&mut data, &stream);
    // Now corrupt the index-region entry the operand resolves through.
    let ih = index_header_off(&data);
    let method_idx_off = header_field(&data, ih + 20) as usize;
    write_u32(&mut data, method_idx_off + idx as usize * 4, BOGUS);
    let err = decode(&data).expect_err("an unopenable legacy method operand must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "bytecode entity reference",
                ..
            }
        ),
        "expected Malformed/bytecode entity reference, got: {err:?}"
    );
}

/// Minimal fixture with legroom for a legacy stream rewrite (a `caller`
/// method with 34 nop-padded instructions and one header literal array).
fn build_minimal_with_room() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Void, &[]);
    let mut insns = vec![Bytecode::Returnundefined];
    insns.extend(std::iter::repeat_n(Bytecode::Nop, 32));
    let (code, _) = abcd_isa::encode(&insns).unwrap();
    let caller = b.class_add_method(cls, "caller", proto, AccessFlags::STATIC, &code, 1, 0);
    b.method_set_source_lang(caller, SourceLang::EcmaScript);
    let lit = b.add_literal_array("lit");
    b.literal_array_add_integer(lit, 42);
    b.deduplicate();
    b.finalize().expect("finalize")
}

/// Legacy: a string operand of 0 (no string item lives at offset 0) fails
/// the direct-offset bounds check loudly.
#[test]
fn legacy_string_operand_zero_offset_is_hard_error() {
    let mut data = build_minimal_with_room();
    // lda.str id32 = 0; return.dyn
    let stream = [0x18, 0x00, 0x00, 0x00, 0x00, 0xa6];
    make_legacy(&mut data, &stream);
    let err = decode(&data).expect_err("a zero legacy string operand must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "bytecode entity reference",
                ..
            }
        ),
        "expected Malformed/bytecode entity reference, got: {err:?}"
    );
}

/// Legacy: a string operand pointing at an unreadable string item fails the
/// intern loudly (the decoy is referenced by nothing else, so it is not in
/// the entity map and the operand path reads it directly).
#[test]
fn legacy_string_operand_unreadable_is_hard_error() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Void, &[]);
    let mut insns = vec![Bytecode::Returnundefined];
    insns.extend(std::iter::repeat_n(Bytecode::Nop, 32));
    let (code, _) = abcd_isa::encode(&insns).unwrap();
    let caller = b.class_add_method(cls, "caller", proto, AccessFlags::STATIC, &code, 1, 0);
    b.method_set_source_lang(caller, SourceLang::EcmaScript);
    let _decoy = b.add_string("decoystr");
    let lit = b.add_literal_array("lit");
    b.literal_array_add_integer(lit, 42);
    b.deduplicate();
    let mut data = b.finalize().expect("finalize");

    let item = locate_string_item(&data, "decoystr");
    let off = item as u32;
    // lda.str id32 = the decoy string's offset; return.dyn
    let mut stream = vec![0x18];
    stream.extend_from_slice(&off.to_le_bytes());
    stream.push(0xa6);
    inflate_string_item_len(&mut data, item);
    make_legacy(&mut data, &stream);
    let err = decode(&data).expect_err("an unreadable legacy string operand must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "bytecode entity reference",
                ..
            }
        ),
        "expected Malformed/bytecode entity reference, got: {err:?}"
    );
}

/// Legacy: a create*withbuffer immediate with NO legacy header table (the
/// header table overruns the file) fails loudly.
#[test]
fn legacy_buffer_imm_without_header_table_is_hard_error() {
    let mut data = build_minimal_with_room();
    // createobjectwithbuffer imm16 = 0; return.dyn
    let stream = [0xff, 0x69, 0x00, 0x00, 0xa6];
    make_legacy(&mut data, &stream);
    // Corrupt the header literal-array table geometry so the table read
    // overruns the file and yields None.
    write_u32(&mut data, NUM_LITERALARRAYS_OFF, 0x4000_0000);
    let err = decode(&data).expect_err("a buffer reference without a table must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "legacy literal-array reference",
                ..
            }
        ),
        "expected Malformed/legacy literal-array reference, got: {err:?}"
    );
}

/// Legacy: a header literal-array table entry of 0 (no literal array lives
/// at offset 0) fails the blob-pass bounds check loudly.
#[test]
fn legacy_buffer_table_entry_zero_is_hard_error() {
    let mut data = build_minimal_with_room();
    let stream = [0xff, 0x69, 0x00, 0x00, 0xa6];
    make_legacy(&mut data, &stream);
    let table_off = header_field(&data, LITERALARRAY_IDX_OFF) as usize;
    write_u32(&mut data, table_off, 0); // entry 0 -> offset 0
    let err = decode(&data).expect_err("a zero legacy table entry must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "legacy literal-array reference",
                ..
            }
        ),
        "expected Malformed/legacy literal-array reference, got: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Typed-proto reference arms
// ---------------------------------------------------------------------------

/// Build a file whose method has a REFERENCE return type (one ref-list
/// entry in the proto item). API 9 for the proto wiring (see
/// build_minimal_api9).
fn build_reference_proto() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(9, "");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let ext = b.add_foreign_class("LExternal;");
    let mut pool = abcd_file::StringPool::default();
    let desc = pool.get_or_intern("LExternal;");
    let proto = b.create_proto_ex(&Type::Reference(desc), Some(ext), &[], &[]);
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
    let data = b.finalize().expect("finalize");
    // Fixture guard: the reference return type must decode.
    let file = decode(&data).expect("control decode");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert!(
        matches!(m.return_type, Some(Type::Reference(_))),
        "API-9 output must carry the reference proto: {:?}",
        m.return_type
    );
    data
}

/// A proto item outside every index region: the ref-list slot read throws
/// in the bridge (GetIndexHeader null), the slot decodes as ABSENT/None,
/// and the Reference return type then fails the resolve loudly.
#[test]
fn proto_reference_slot_absent_is_hard_error() {
    let mut data = build_reference_proto();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0");
    let proto_off = method_proto_offset(&data, m_off);
    let ih = index_header_off(&data);
    let start = header_field(&data, ih) as usize;
    let end = header_field(&data, ih + 4) as usize;
    assert!(
        start <= m_off as usize && (m_off as usize) < end,
        "the method must start inside the region"
    );
    // Narrow the region to keep the method but exclude the proto item.
    assert_ne!(m_off, proto_off);
    if proto_off < m_off {
        write_u32(&mut data, ih, m_off); // start = method offset
    } else {
        write_u32(&mut data, ih + 4, proto_off); // end = proto offset
    }
    let err = decode(&data).expect_err("an unreadable proto ref slot must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "reference_type",
                context,
            } if context == "return type"
        ),
        "expected Malformed/reference_type, got: {err:?}"
    );
}

/// A proto ref-list slot indexing past the region class table resolves to
/// offset 0, which no entity map contains: the Reference return type fails
/// the resolve loudly.
#[test]
fn proto_reference_slot_oob_is_hard_error() {
    let mut data = build_reference_proto();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0");
    let proto_off = method_proto_offset(&data, m_off) as usize;
    // Shorty word 0 holds the return-type nibble; the ref list follows.
    let shorty0 = u16::from_le_bytes(data[proto_off..proto_off + 2].try_into().unwrap());
    assert_eq!(
        shorty0 & 0xF,
        abcd_file_sys::Type_TypeId_REFERENCE as u16,
        "the return-type nibble must be REFERENCE"
    );
    assert_eq!(shorty0 >> 4, 0, "fixture proto has a single shorty nibble");
    data[proto_off + 2..proto_off + 4].copy_from_slice(&0x7FFFu16.to_le_bytes()); // ref slot u16 OOB
    let err = decode(&data).expect_err("an unresolvable proto ref slot must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "reference_type",
                context,
            } if context == "return type"
        ),
        "expected Malformed/reference_type, got: {err:?}"
    );
}

/// A proto argument-type nibble that is not a known TypeId fails the
/// conversion loudly (the arg-loop `TypeId::try_from`).
#[test]
fn proto_arg_type_nibble_unknown_is_hard_error() {
    let mut b = Builder::new();
    b.set_api(9, "");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[Type::Tagged, Type::Tagged]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        2,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let mut data = b.finalize().expect("finalize");
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0");
    let proto_off = method_proto_offset(&data, m_off) as usize;
    // Shorty word 0 = [ret, arg1, arg2, 0] nibbles; arg2 is bits 8-11.
    let shorty0 = u16::from_le_bytes(data[proto_off..proto_off + 2].try_into().unwrap());
    let tagged = abcd_file_sys::Type_TypeId_TAGGED as u16;
    assert_eq!(
        shorty0,
        tagged | (tagged << 4) | (tagged << 8),
        "fixture shorty must be a Tagged triple: {shorty0:#x}"
    );
    // Set arg2's nibble to 0xF (no such TypeId), leaving the count intact.
    data[proto_off + 1] = (data[proto_off + 1] & 0xF0) | 0x0F;
    let err = decode(&data).expect_err("an unknown arg-type nibble must fail");
    assert!(
        matches!(err, Error::UnknownTypeId(0x0F)),
        "expected UnknownTypeId(0x0f), got: {err:?}"
    );
}

/// An annotation element whose NAME offset dangles fails loudly.
#[test]
fn annotation_element_name_unreadable_is_hard_error() {
    let mut data = build_class_with_annotation();
    let (ann_off, _, _) = locate_annotation(&data, "level", b'7');
    // The element's name_off is the first u32 after [u16 class][u16 count].
    write_u32(&mut data, ann_off + 4, BOGUS);
    let err = decode(&data).expect_err("a dangling annotation element name must fail");
    assert!(
        matches!(err, Error::InvalidString(o) if o == BOGUS),
        "expected InvalidString({BOGUS:#x}), got: {err:?}"
    );
}

/// An ArrayMethodHandle element whose entity offset is in no entity map
/// decodes with an empty entity name. PINNED TOLERANCE (format evidence):
/// a method handle may legally target a FOREIGN method/field (the vendored
/// MethodHandleItem holds any BaseItem); foreign members live in the
/// foreign region and never enter the entity map, so a miss is format-legal
/// and must NOT become a hard error (see
/// annotation_loud_errors.rs::method_handle_foreign_entity_decodes_with_empty_name).
#[test]
fn annotation_array_method_handle_unknown_entity_decodes_empty() {
    let mut data = build_method_handle_array();
    let (_, value_pos, _) = locate_annotation(&data, "mhArr", b'@');
    let payload = header_field(&data, value_pos) as usize;
    let mh1_off = header_field(&data, payload + 1) as usize;
    // Method-handle item: [u8 type][uleb entity_off]. Point the entity at
    // 128 (in no entity map; nothing else reads it) — a two-byte uleb like
    // the fixture's own (the method items sit past offset 127).
    let (_entity, len) = read_uleb(&data, mh1_off + 1);
    assert_eq!(
        len, 2,
        "craft requires a two-byte entity uleb; got {_entity:#x}"
    );
    data[mh1_off + 1..mh1_off + 3].copy_from_slice(&[0x80, 0x01]); // uleb 128
    let file = decode(&data).expect("an unknown handle entity is not an error");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    match &g.annotations.compile_time[0].elements[0].value {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'@');
            match &values[0] {
                AnnotationValue::MethodHandle(mh) => {
                    assert_eq!(file.strings.resolve(mh.entity), Some(""));
                    assert_eq!(mh.entity_offset, 128);
                }
                other => panic!("expected MethodHandle element, got {other:?}"),
            }
        }
        other => panic!("expected Array element, got {other:?}"),
    }
}

/// A header literal-array table entry of ABSENT is skipped from both the
/// decoded table and the raw header-offset list (byte-identity metadata).
#[test]
fn literal_array_header_entry_absent_is_skipped() {
    let mut data = build_minimal_with_room();
    let table_off = header_field(&data, LITERALARRAY_IDX_OFF) as usize;
    write_u32(&mut data, table_off, u32::MAX);
    let file = decode(&data).expect("an ABSENT header entry is skipped");
    assert!(
        file.literal_arrays.is_empty() && file.literal_array_offsets.is_empty(),
        "the ABSENT entry must not decode"
    );
    assert!(
        file.literal_array_header_offsets.is_empty(),
        "the ABSENT entry is excluded from the raw header list"
    );
}

// ---------------------------------------------------------------------------
// N72 collision propagation through method string operands
// ---------------------------------------------------------------------------

/// Build a file whose `caller` has two ldstr operands (relocated to the two
/// raw-form strings) and a second method NAMED with the exact disambiguated
/// identity of the second form — so the pool carries it before the operand
/// pass runs. `(data,)` — offsets are learnable by string pattern.
fn build_operand_collision() -> Vec<u8> {
    const RAW_A: [u8; 3] = [0xED, 0xA0, 0xB4];
    const RAW_B: [u8; 3] = [0xED, 0xB4, 0x86];
    const LOSSY: &str = "\u{FFFD}\u{FFFD}\u{FFFD}";
    let genuine = format!("{LOSSY}\u{E000}edb486");

    let mut b = Builder::new();
    b.set_api(12, "beta1");
    b.set_raw_strings(
        [
            ("key_a".to_string(), Box::from(&RAW_A[..])),
            ("key_b".to_string(), Box::from(&RAW_B[..])),
        ]
        .into_iter()
        .collect(),
    );
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Void, &[]);
    // The second method's NAME is the genuine string carrying the
    // disambiguated identity of key_b.
    let m2 = b.class_add_method(cls, &genuine, proto, AccessFlags::STATIC, &[0x65], 1, 0);
    b.method_set_source_lang(m2, SourceLang::EcmaScript);
    // caller: ldstr key_a; ldstr key_b; returnundefined.
    let placeholder = EntityId(u16::MAX as u32);
    let mut insns = vec![
        Bytecode::LdaStr(placeholder),
        Bytecode::LdaStr(placeholder),
        Bytecode::Returnundefined,
    ];
    insns.extend(std::iter::repeat_n(Bytecode::Nop, 32));
    let (code, offsets) = abcd_isa::encode(&insns).unwrap();
    let caller = b.class_add_method(cls, "caller", proto, AccessFlags::STATIC, &code, 1, 0);
    b.method_set_source_lang(caller, SourceLang::EcmaScript);
    let s_a = b.add_string("key_a");
    let s_b = b.add_string("key_b");
    b.relocate_code_id(caller, offsets[0], 0, CodeEntity::String(s_a))
        .expect("relocate first string operand");
    b.relocate_code_id(caller, offsets[1], 0, CodeEntity::String(s_b))
        .expect("relocate second string operand");
    b.deduplicate();
    b.finalize().expect("finalize")
}

/// Modern: the N72 genuine-collision guard propagates through the method
/// string-operand intern (`intern_string(...) ?`), not just the literal
/// array pass.
#[test]
fn modern_string_operand_identity_collision_is_hard_error() {
    let data = build_operand_collision();
    let err = decode(&data).expect_err("the genuine identity collision must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "string",
                context,
            } if context.contains("genuine string collides with a disambiguated")
        ),
        "expected Malformed/string genuine-collision, got: {err:?}"
    );
}

/// Legacy: the same propagation through the legacy direct-offset string
/// operand rule.
#[test]
fn legacy_string_operand_identity_collision_is_hard_error() {
    // Same collision as the modern variant, but the file must stay clean
    // until the legacy rewrite: start from a fixture with NO string
    // operands (the collision would otherwise fire in the modern decode
    // that make_legacy performs to learn the code location).
    const RAW_A: [u8; 3] = [0xED, 0xA0, 0xB4];
    const RAW_B: [u8; 3] = [0xED, 0xB4, 0x86];
    const LOSSY: &str = "\u{FFFD}\u{FFFD}\u{FFFD}";
    let genuine = format!("{LOSSY}\u{E000}edb486");
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    b.set_raw_strings(
        [
            ("key_a".to_string(), Box::from(&RAW_A[..])),
            ("key_b".to_string(), Box::from(&RAW_B[..])),
        ]
        .into_iter()
        .collect(),
    );
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Void, &[]);
    // The second method's NAME carries the disambiguated identity of key_b.
    // Bodiless (empty code emits no code item): the legacy rewrite below
    // only rewrites `caller`, and a modern-encoded second stream would be
    // undecodable legacy bytecode.
    let m2 = b.class_add_method(cls, &genuine, proto, AccessFlags::STATIC, &[], 0, 0);
    b.method_set_source_lang(m2, SourceLang::EcmaScript);
    let mut insns = vec![Bytecode::Returnundefined];
    insns.extend(std::iter::repeat_n(Bytecode::Nop, 32));
    let (code, _) = abcd_isa::encode(&insns).unwrap();
    let caller = b.class_add_method(cls, "caller", proto, AccessFlags::STATIC, &code, 1, 0);
    b.method_set_source_lang(caller, SourceLang::EcmaScript);
    let _a = b.add_string("key_a");
    let _b = b.add_string("key_b");
    let lit = b.add_literal_array("lit");
    b.literal_array_add_integer(lit, 42);
    b.deduplicate();
    let mut data = b.finalize().expect("finalize");
    // The two raw string items: [uleb (1<<1)|0 = 0x02][3 raw bytes][NUL].
    let item_a = locate_unique(&data, &[0x02, 0xED, 0xA0, 0xB4, 0x00]) as u32;
    let item_b = locate_unique(&data, &[0x02, 0xED, 0xB4, 0x86, 0x00]) as u32;
    // Legacy stream: lda.str id32 (item_a); lda.str id32 (item_b); return.dyn.
    let mut stream = vec![0x18];
    stream.extend_from_slice(&item_a.to_le_bytes());
    stream.push(0x18);
    stream.extend_from_slice(&item_b.to_le_bytes());
    stream.push(0xa6);
    make_legacy(&mut data, &stream);
    let err = decode(&data).expect_err("the genuine identity collision must fail (legacy)");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "string",
                context,
            } if context.contains("genuine string collides with a disambiguated")
        ),
        "expected Malformed/string genuine-collision, got: {err:?}"
    );
}

/// Legacy: a defineclasswithbuffer immediate with no legacy header table
/// fails loudly through the blob pass (the fourth create*withbuffer match
/// arm).
#[test]
fn legacy_defineclasswithbuffer_without_table_is_hard_error() {
    let mut data = build_with_foreign_method_operand();
    // defineclasswithbuffer id16=0 (the region's entry 0), imm16 litidx=0,
    // imm16=0, v0, v0; return.dyn
    let stream = [
        0xff, 0x70, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa6,
    ];
    make_legacy(&mut data, &stream);
    // Corrupt the header literal-array table geometry so the table read
    // overruns the file and yields None.
    write_u32(&mut data, NUM_LITERALARRAYS_OFF, 0x4000_0000);
    let err = decode(&data).expect_err("a class buffer reference without a table must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "legacy literal-array reference",
                ..
            }
        ),
        "expected Malformed/legacy literal-array reference, got: {err:?}"
    );
}

/// A foreign class whose descriptor string is unreadable is skipped from
/// both class passes (the `if let Some` skip in the external branches) —
/// never an error. The debug extractor skips external classes, so nothing
/// trips first (contrast corrupt_class_index_entry_trips_debug_extractor_first).
#[test]
fn foreign_class_descriptor_unreadable_is_skipped() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let _ext = b.add_foreign_class("LExternal;");
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
    let mut data = b.finalize().expect("finalize");
    let item = locate_string_item(&data, "LExternal;");
    inflate_string_item_len(&mut data, item);
    let file = decode(&data).expect("an unreadable foreign descriptor is skipped");
    assert!(
        file.classes.values().all(|c| !c.is_external),
        "the unreadable foreign class must not appear: {:?}",
        file.classes.keys().collect::<Vec<_>>()
    );
}
