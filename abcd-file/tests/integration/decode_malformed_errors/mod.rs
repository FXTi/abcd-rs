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
    // SAFETY: `data` outlives `f`; all handles are checked for null and closed
    // in reverse open order.
    unsafe {
        let f = abcd_file_sys::abc_file_open(data.as_ptr(), data.len());
        assert!(!f.is_null(), "abc_file_open failed");
        let mr = abcd_file_sys::abc_method_open(f, method_offset);
        assert!(!mr.is_null(), "abc_method_open failed");
        let code_off = abcd_file_sys::abc_method_code_off(mr);
        abcd_file_sys::abc_method_close(mr);
        assert_ne!(code_off, u32::MAX, "method has no code item");
        let cr = abcd_file_sys::abc_code_open(f, code_off);
        assert!(!cr.is_null(), "abc_code_open failed");
        let ptr = abcd_file_sys::abc_code_instructions(cr);
        let len = abcd_file_sys::abc_code_code_size(cr) as usize;
        let bytes = if ptr.is_null() || len == 0 {
            Vec::new()
        } else {
            std::slice::from_raw_parts(ptr, len).to_vec()
        };
        abcd_file_sys::abc_code_close(cr);
        abcd_file_sys::abc_file_close(f);
        bytes
    }
}

/// A method's proto item offset, learned through the sys layer.
fn method_proto_offset(data: &[u8], method_offset: u32) -> u32 {
    // SAFETY: `data` outlives `f`; handles are checked for null and closed.
    unsafe {
        let f = abcd_file_sys::abc_file_open(data.as_ptr(), data.len());
        assert!(!f.is_null(), "abc_file_open failed");
        let mr = abcd_file_sys::abc_method_open(f, method_offset);
        assert!(!mr.is_null(), "abc_method_open failed");
        let proto = abcd_file_sys::abc_method_get_proto_id(mr);
        abcd_file_sys::abc_method_close(mr);
        abcd_file_sys::abc_file_close(f);
        assert_ne!(proto, u32::MAX, "method has no proto");
        proto
    }
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

mod items_and_annotations;
mod modules_and_literals;
mod operands_and_legacy;
