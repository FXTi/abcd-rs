//! Legacy (file format 0.0.0.2) ABC decode — fully synthetic, zero binary
//! fixtures.
//!
//! A legacy file is synthesized at runtime: the Builder emits a modern file
//! whose `caller` method references a string and a sibling method through
//! its index region, then the test patches the header version to 0.0.0.2 and
//! rewrites both method bodies with hand-assembled legacy (pre-2022-08-18)
//! instruction streams. The legacy operand encodings under test:
//!
//! - `lda.str` id32: a direct 32-bit string FILE OFFSET (the string index
//!   region did not exist yet)
//! - `deprecated.ldobjbyname` id32: same direct-offset string semantics
//! - `definefuncdyn` id16: a 16-bit index into the method's index region
//!   (same layout as today)
//! - `createobjectwithbuffer` imm16: a 16-bit index into the header's
//!   global literal-array table (deprecated by the 2022-08-18 refactoring)
//!
//! The build uses API 12 (12.0.2.0, at or below the vendored
//! LAST_CONTAINS_LITERAL_IN_HEADER_VERSION 12.0.6.0), so the writer emits a
//! real header literal-array table — mandatory for the legacy global-index
//! path. The header checksum is recomputed after patching: the decoder never
//! validates it, but a stale checksum would make the file malformed in a way
//! real 0.0.0.2 files are not.
//!
//! Pins: decode succeeds end to end on the patched file, the legacy IR
//! carries the expected variants with correctly resolved entity offsets,
//! encode refuses to silently emit a modern file from a legacy model, and
//! the decoder never panics on random or legacy-shaped mutated input.

use abcd_file::{
    AccessFlags, Builder, CodeEntity, Error, LiteralValue, Type, Version, decode, encode,
};
use abcd_file_sys as sys;
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm};

/// File::Header layout (unchanged since 3.1): magic(8) checksum(4)
/// version(4) file_size(4) foreign_off(4) foreign_size(4) num_classes(4)
/// class_idx_off(4) num_lnps(4) lnp_idx_off(4) num_literalarrays(4)
/// literalarray_idx_off(4) num_index_regions(4) index_section_off(4).
const CHECKSUM_OFF: usize = 8;
const VERSION_OFF: usize = 12;
const NUM_LITERALARRAYS_OFF: usize = 44;
const LITERALARRAY_IDX_OFF: usize = 48;

/// The legacy header version under test.
const LEGACY_VERSION: [u8; 4] = [0, 0, 0, 2];

/// String the legacy id32 operands reference, by direct file offset.
const NEEDLE: &str = "legacy-synthetic-needle";

/// A synthetic 0.0.0.2 file plus the layout facts its streams reference.
struct SyntheticLegacy {
    data: Vec<u8>,
    string_offset: u32,
    method_index: u16,
    target_offset: u32,
    literal_offset: u32,
    /// Byte range of `caller`'s code stream inside `data`.
    caller_code: (usize, usize),
}

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

/// Read a method's final (post-relocation) code bytes through the sys layer,
/// the same walk the archaeology probe uses.
fn method_code(data: &[u8], method_offset: u32) -> Vec<u8> {
    let f = unsafe { sys::abc_file_open(data.as_ptr(), data.len()) };
    assert!(!f.is_null(), "abc_file_open failed");
    let mr = unsafe { sys::abc_method_open(f, method_offset) };
    assert!(!mr.is_null(), "abc_method_open failed");
    let code_off = unsafe { sys::abc_method_code_off(mr) };
    unsafe { sys::abc_method_close(mr) };
    assert_ne!(code_off, u32::MAX, "method has no code item");
    let cr = unsafe { sys::abc_code_open(f, code_off) };
    assert!(!cr.is_null(), "abc_code_open failed");
    let ptr = unsafe { sys::abc_code_instructions(cr) };
    let len = unsafe { sys::abc_code_code_size(cr) } as usize;
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) }.to_vec();
    unsafe { sys::abc_code_close(cr) };
    unsafe { sys::abc_file_close(f) };
    bytes
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

fn build_synthetic_legacy() -> SyntheticLegacy {
    // --- Modern file: `caller` references the `target` method and NEEDLE
    // through its index region; nop legroom lets the longer legacy stream
    // reuse the same code item. One literal array populates the header's
    // global literal-array table (read as the legacy 16-bit global index
    // table below).
    let mut builder = Builder::new();
    builder.set_api(12, "beta1");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let mut caller_insns = vec![
        Bytecode::Definefunc(Imm(0), placeholder, Imm(0)),
        Bytecode::LdaStr(placeholder),
        Bytecode::Returnundefined,
    ];
    caller_insns.extend(std::iter::repeat_n(Bytecode::Nop, 32));
    let (caller_code, caller_offsets) = abcd_isa::encode(&caller_insns).unwrap();
    let caller = builder.class_add_method(
        class,
        "caller",
        proto,
        AccessFlags::STATIC,
        &caller_code,
        1,
        0,
    );
    let (target_code, _) = abcd_isa::encode(&[
        Bytecode::Ldai(Imm(0x0bad_f00d)), // distinctive marker for the byte search
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let target = builder.class_add_method(
        class,
        "target",
        proto,
        AccessFlags::STATIC,
        &target_code,
        0,
        0,
    );
    let needle = builder.add_string(NEEDLE);
    let lit = builder.add_literal_array("lit");
    builder.literal_array_add_integer(lit, 0x2a);
    builder
        .relocate_code_id(caller, caller_offsets[0], 0, CodeEntity::Method(target))
        .unwrap();
    builder
        .relocate_code_id(caller, caller_offsets[1], 0, CodeEntity::String(needle))
        .unwrap();
    builder.deduplicate();
    let mut data = builder.finalize().unwrap();

    // --- Learn the layout facts from a modern decode ---
    let modern = decode(&data).unwrap();
    let find_method = |name: &str| {
        modern
            .all_methods()
            .find(|(_, m)| modern.strings.resolve(m.name) == Some(name))
            .unwrap_or_else(|| panic!("method {name} missing"))
            .1
    };
    let caller_model = find_method("caller");
    let target_offset = find_method("target").offset;
    let body = caller_model.body.as_ref().unwrap();
    let (kind, mid) = body.bytecodes[0].entity_operands()[0];
    assert_eq!(kind, EntityKind::MethodId);
    assert_eq!(body.entity_offsets[&(kind, mid.0)], target_offset);
    let method_index = u16::try_from(mid.0).unwrap();
    let (kind, sid) = body.bytecodes[1].entity_operands()[0];
    assert_eq!(kind, EntityKind::StringId);
    let string_offset = body.entity_offsets[&(kind, sid.0)];
    assert_eq!(modern.resolve_entity_str(string_offset), Some(NEEDLE));
    // The header's global literal-array table holds the array's file offset;
    // table index 0 is the legacy 16-bit global index the stream references.
    let lit_count = u32::from_le_bytes(
        data[NUM_LITERALARRAYS_OFF..NUM_LITERALARRAYS_OFF + 4]
            .try_into()
            .unwrap(),
    );
    let table_off = u32::from_le_bytes(
        data[LITERALARRAY_IDX_OFF..LITERALARRAY_IDX_OFF + 4]
            .try_into()
            .unwrap(),
    ) as usize;
    assert_eq!(
        lit_count, 1,
        "writer must emit one header literal-array entry"
    );
    let literal_offset = u32::from_le_bytes(data[table_off..table_off + 4].try_into().unwrap());

    // --- Rewrite both code streams as legacy (pre-2022-08-18) encodings ---
    let mut legacy_caller = Vec::new();
    legacy_caller.push(0x18); // lda.str id32: direct string FILE OFFSET
    legacy_caller.extend_from_slice(&string_offset.to_le_bytes());
    legacy_caller.extend_from_slice(&[0xff, 0x77]); // deprecated.ldobjbyname id32, v0
    legacy_caller.extend_from_slice(&string_offset.to_le_bytes());
    legacy_caller.push(0x00);
    legacy_caller.extend_from_slice(&[0xff, 0x5f]); // definefuncdyn id16, imm16, v0
    legacy_caller.extend_from_slice(&method_index.to_le_bytes());
    legacy_caller.extend_from_slice(&[0x00, 0x00, 0x00]);
    legacy_caller.extend_from_slice(&[0xff, 0x69]); // createobjectwithbuffer imm16: global litidx
    legacy_caller.extend_from_slice(&0u16.to_le_bytes());
    legacy_caller.push(0xa6); // return.dyn
    // ldai.dyn imm32 (the same marker value); return.dyn
    let legacy_target = [0xa4, 0x0d, 0xf0, 0xad, 0x0b, 0xa6];

    let mut caller_code = (0, 0);
    for (method_offset, legacy) in [
        (caller_model.offset, &legacy_caller[..]),
        (target_offset, &legacy_target[..]),
    ] {
        let modern_bytes = method_code(&data, method_offset);
        assert!(
            legacy.len() <= modern_bytes.len(),
            "legacy stream must fit the existing code item"
        );
        let pos = locate_unique(&data, &modern_bytes);
        data[pos..pos + legacy.len()].copy_from_slice(legacy);
        // 0x00 is the legacy nop: pad the tail of the code item.
        data[pos + legacy.len()..pos + modern_bytes.len()].fill(0x00);
        if method_offset == caller_model.offset {
            caller_code = (pos, modern_bytes.len());
        }
    }

    // --- Header: version 0.0.0.2 + an honest checksum over the patched
    // content (the decoder never validates it; a lying checksum would make
    // the file malformed in a way real legacy files are not).
    data[VERSION_OFF..VERSION_OFF + 4].copy_from_slice(&LEGACY_VERSION);
    let checksum = adler32(&data[VERSION_OFF..]);
    data[CHECKSUM_OFF..CHECKSUM_OFF + 4].copy_from_slice(&checksum.to_le_bytes());

    SyntheticLegacy {
        data,
        string_offset,
        method_index,
        target_offset,
        literal_offset,
        caller_code,
    }
}

#[test]
fn legacy_file_decodes() {
    let syn = build_synthetic_legacy();
    let file = decode(&syn.data).expect("legacy decode");
    assert_eq!(file.version, Version::new(0, 0, 0, 2));
    assert_eq!(file.classes.len(), 1);
    let methods: usize = file.classes.values().map(|c| c.methods.len()).sum();
    assert_eq!(methods, 2);
    // Every method decoded its (legacy) bytecode.
    for method in file.classes.values().flat_map(|c| &c.methods) {
        let body = method.body.as_ref().expect("method body");
        assert!(!body.bytecodes.is_empty());
    }
}

#[test]
fn legacy_ir_contents() {
    let syn = build_synthetic_legacy();
    let file = decode(&syn.data).expect("legacy decode");
    let caller = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("caller"))
        .expect("caller")
        .1;
    let body = caller.body.as_ref().unwrap();

    // Legacy `lda.str` keeps the direct 32-bit file offset as its operand.
    assert!(
        body.bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::LdaStr(id) if id.0 == syn.string_offset)),
        "expected lda.str with a direct string offset"
    );
    // Legacy `ecma.ldobjbyname` keeps its legacy layout via the deprecated
    // variant.
    assert!(
        body.bytecodes.iter().any(
            |bc| matches!(bc, Bytecode::DeprecatedLdobjbyname(id, _) if id.0 == syn.string_offset)
        ),
        "expected deprecated.ldobjbyname"
    );
    // Legacy `definefuncdyn` maps to modern Definefunc with a synthesized
    // IC-slot immediate of 0.
    assert!(
        body.bytecodes.iter().any(
            |bc| matches!(bc, Bytecode::Definefunc(Imm(0), id, Imm(0)) if id.0 == syn.method_index as u32)
        ),
        "expected legacy definefuncdyn -> definefunc"
    );
    // Legacy `createobjectwithbuffer` carries the literal array as a plain
    // 16-bit immediate: a global index into the header table.
    assert!(
        body.bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::DeprecatedCreateobjectwithbuffer(Imm(0)))),
        "expected deprecated.createobjectwithbuffer with global index 0"
    );

    // Entity resolution: the string operand resolved as a direct file
    // offset, the method operand through the index region, the literal
    // array through the header's global table.
    assert_eq!(
        body.entity_offsets[&(EntityKind::StringId, syn.string_offset)],
        syn.string_offset
    );
    assert_eq!(
        body.entity_offsets[&(EntityKind::MethodId, syn.method_index as u32)],
        syn.target_offset
    );
    assert_eq!(
        body.entity_offsets[&(EntityKind::LiteralarrayId, 0)],
        syn.literal_offset
    );
    assert_eq!(file.resolve_entity_str(syn.string_offset), Some(NEEDLE));
    let array = &file.literal_arrays[file.literal_array_offsets[&syn.literal_offset] as usize];
    assert!(
        matches!(array.values.as_slice(), [LiteralValue::Integer(0x2a)]),
        "expected the header-table literal array to decode"
    );
}

#[test]
fn legacy_encode_refused() {
    // A legacy-decoded model carries legacy entity operands (direct offsets,
    // global literal-array indices); encoding it as a modern file would be
    // lossy. Encode must fail loudly, never silently.
    let syn = build_synthetic_legacy();
    let file = decode(&syn.data).expect("legacy decode");
    let err = encode(&file).expect_err("encode must fail");
    assert!(
        matches!(err, Error::UnsupportedOutputVersion(v) if v == Version::new(0, 0, 0, 2)),
        "unexpected error: {err}"
    );
    assert!(
        err.to_string().contains("unsupported ABC output version"),
        "unexpected error: {err}"
    );
}

/// Append a randomly chosen legacy instruction (deterministic seed via
/// `next`) to `out`. The pool deliberately excludes every form whose operand
/// is a 32-bit string offset or a 16-bit method index into the index region:
/// those resolve to bridge string reads (`abc_file_get_string_utf16`,
/// `abc_method_get_name_utf16`) that size the destination buffer from the
/// StringData length prefix but convert `strlen(payload)` bytes — with a
/// garbage offset that is a heap write overflow in the bridge
/// (pre-existing, reported separately). `createobjectwithbuffer` stays: its
/// 16-bit global table index is bounds-checked in pure Rust.
fn gen_legacy_insn(next: &mut impl FnMut() -> u32, out: &mut Vec<u8>) {
    match next() % 12 {
        0 => out.push(0x00), // nop
        1 => out.push(0xa6), // return.dyn
        2 => {
            out.push(0xa4); // ldai.dyn imm32
            out.extend_from_slice(&next().to_le_bytes());
        }
        3 => out.extend_from_slice(&[0xa0, next() as u8, next() as u8]), // mov.dyn v8, v8
        4 => out.extend_from_slice(&[0xff, 0x07]),                       // ldtrue
        5 => out.extend_from_slice(&[0xff, 0x08]),                       // ldfalse
        6 => out.extend_from_slice(&[0xff, 0x09]),                       // throw.dyn
        7 => out.extend_from_slice(&[0xff, 0x0a]),                       // typeofdyn
        8 => out.extend_from_slice(&[0xff, 0x11]),                       // returnundefined
        9 => out.extend_from_slice(&[0xff, 0x0b]),                       // deprecated.ldlexenv
        10 => out.extend_from_slice(&[0xff, 0x1a, next() as u8]),        // add2dyn v8
        _ => {
            // createobjectwithbuffer imm16: global literal-array index
            out.extend_from_slice(&[0xff, 0x69]);
            out.extend_from_slice(&(next() as u16).to_le_bytes());
        }
    }
}

#[test]
fn legacy_decode_never_panics_on_fuzz() {
    let syn = build_synthetic_legacy();
    // Deterministic xorshift32.
    let mut state = 0x9e37_79b9u32;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        state
    };

    // Fully random buffers: rejected at open (bad magic / too small),
    // never a panic.
    let mut buf = vec![0u8; 128];
    for _ in 0..256 {
        for b in buf.iter_mut() {
            *b = next() as u8;
        }
        let _ = decode(&buf);
    }

    // Truncation sweep: every strict prefix of the legacy file (the bridge
    // rejects them all through the declared-file_size gate; the pin is
    // process survival).
    for cut in 0..syn.data.len() {
        let _ = decode(&syn.data[..cut]);
    }

    // Legacy-shaped mutations: replace the caller's code stream with a
    // deterministically generated legacy stream of equal length. All
    // structural items (strings, index region, header tables) stay intact,
    // so the decode can only fail through the legacy bytecode dispatch and
    // the legacy operand-resolution bounds checks — the paths under test.
    // (File-level byte fuzz of string/structure items is excluded: it hits
    // the pre-existing bridge heap overflow documented on `gen_legacy_insn`
    // before it can prove anything about the legacy paths.)
    let (pos, len) = syn.caller_code;
    for _ in 0..256 {
        let mut stream = Vec::new();
        while stream.len() < len {
            gen_legacy_insn(&mut next, &mut stream);
        }
        stream.truncate(len);
        let mut mutated = syn.data.clone();
        mutated[pos..pos + len].copy_from_slice(&stream);
        let _ = decode(&mutated);
    }
}
