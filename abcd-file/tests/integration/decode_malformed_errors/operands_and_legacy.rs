//! Malformed-input tests for modern and legacy (`0.0.0.2`) bytecode entity,
//! string, method, and literal-buffer operands and 32-bit header overflow guards.

use super::*;

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
    let (kind, id) = body.bytecodes()[0].entity_operands()[0];
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
    // Mark the header literal-array table as absent (`INVALID_INDEX = u32::MAX`)
    // so header validation passes and `legacy_literalarray_table` yields `None`.
    write_u32(&mut data, NUM_LITERALARRAYS_OFF, u32::MAX);
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
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Void, &[]);
    let m2 = b.class_add_method(cls, &genuine, proto, AccessFlags::STATIC, &[0x65], 1, 0);
    b.method_set_source_lang(m2, SourceLang::EcmaScript);
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
    let s_a = b.add_string_mutf8(&RAW_A).unwrap();
    let s_b = b.add_string_mutf8(&RAW_B).unwrap();
    b.relocate_code_id(caller, offsets[0], 0, CodeEntity::String(s_a))
        .expect("relocate first string operand");
    b.relocate_code_id(caller, offsets[1], 0, CodeEntity::String(s_b))
        .expect("relocate second string operand");
    b.deduplicate();
    b.finalize().expect("finalize")
}

/// Modern (#30): PUA method names and colliding lone-surrogate string
/// operands coexist losslessly without sentinel collisions.
#[test]
fn modern_string_operand_pua_and_lone_surrogates_coexist() {
    const RAW_A: [u8; 3] = [0xED, 0xA0, 0xB4];
    const RAW_B: [u8; 3] = [0xED, 0xB4, 0x86];
    let data = build_operand_collision();
    let file = decode(&data).expect("coexisting PUA + lone surrogates must decode");
    let reencoded = abcd_file::encode(&file).expect("re-encode");
    let rt = decode(&reencoded).expect("re-decode");
    assert_eq!(rt.strings.lossy_count(), 2);
    assert!(rt.strings.get_raw_mutf8(&RAW_A).is_some());
    assert!(rt.strings.get_raw_mutf8(&RAW_B).is_some());
    assert!(
        rt.strings
            .get("\u{FFFD}\u{FFFD}\u{FFFD}\u{E000}edb486")
            .is_some()
    );
}

/// Legacy (#30): direct-offset lone-surrogate string operands and PUA method
/// names coexist losslessly without sentinel collisions.
#[test]
fn legacy_string_operand_pua_and_lone_surrogates_coexist() {
    const RAW_A: [u8; 3] = [0xED, 0xA0, 0xB4];
    const RAW_B: [u8; 3] = [0xED, 0xB4, 0x86];
    const LOSSY: &str = "\u{FFFD}\u{FFFD}\u{FFFD}";
    let genuine = format!("{LOSSY}\u{E000}edb486");
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Void, &[]);
    let m2 = b.class_add_method(cls, &genuine, proto, AccessFlags::STATIC, &[], 0, 0);
    b.method_set_source_lang(m2, SourceLang::EcmaScript);
    let mut insns = vec![Bytecode::Returnundefined];
    insns.extend(std::iter::repeat_n(Bytecode::Nop, 32));
    let (code, _) = abcd_isa::encode(&insns).unwrap();
    let caller = b.class_add_method(cls, "caller", proto, AccessFlags::STATIC, &code, 1, 0);
    b.method_set_source_lang(caller, SourceLang::EcmaScript);
    let _a = b.add_string_mutf8(&RAW_A).unwrap();
    let _b = b.add_string_mutf8(&RAW_B).unwrap();
    let lit = b.add_literal_array("lit");
    b.literal_array_add_integer(lit, 42);
    b.deduplicate();
    let mut data = b.finalize().expect("finalize");
    let item_a = locate_unique(&data, &[0x02, 0xED, 0xA0, 0xB4, 0x00]) as u32;
    let item_b = locate_unique(&data, &[0x02, 0xED, 0xB4, 0x86, 0x00]) as u32;
    let mut stream = vec![0x18];
    stream.extend_from_slice(&item_a.to_le_bytes());
    stream.push(0x18);
    stream.extend_from_slice(&item_b.to_le_bytes());
    stream.push(0xa6);
    make_legacy(&mut data, &stream);
    let file = decode(&data).expect("legacy PUA + lone surrogates must decode");
    assert_eq!(file.strings.lossy_count(), 2);
    assert!(file.strings.get_raw_mutf8(&RAW_A).is_some());
    assert!(file.strings.get_raw_mutf8(&RAW_B).is_some());
    assert!(file.strings.get(&genuine).is_some());
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
    // Mark the header literal-array table as absent (`INVALID_INDEX = u32::MAX`)
    // so header validation passes and `legacy_literalarray_table` yields `None`.
    write_u32(&mut data, NUM_LITERALARRAYS_OFF, u32::MAX);
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

/// Legacy header literal-array table counts and offsets that would overflow
/// 32-bit `usize` (`u32::MAX`, `0x4000_0001`, wrapping `table_off + count * 4`)
/// must never panic and must reject dangling buffer references cleanly.
#[test]
fn legacy_header_table_32bit_overflow_counts_and_offsets_are_hard_errors() {
    let mut base = build_minimal_with_room();
    // createobjectwithbuffer imm16 = 0; return.dyn
    let stream = [0xff, 0x69, 0x00, 0x00, 0xa6];
    make_legacy(&mut base, &stream);

    for (count, table_off) in [
        (0xffff_ffffu32, 0xffff_ffffu32),
        (0xffff_ffff, 60),
        (0x4000_0001, 60),
        (0x4000_0000, 0),
        (1, 0xffff_ffff),
        (1, 0xffff_fffe),
        (0, 0xffff_ffff),
        (0x2000_0001, 0x8000_0000),
    ] {
        let mut data = base.clone();
        write_u32(&mut data, NUM_LITERALARRAYS_OFF, count);
        write_u32(&mut data, LITERALARRAY_IDX_OFF, table_off);
        let err = decode(&data).expect_err("overflowing legacy header table must fail");
        assert!(
            matches!(
                &err,
                Error::Open(_)
                    | Error::Malformed {
                        field: "legacy literal-array reference",
                        ..
                    }
            ),
            "expected Open or Malformed/legacy literal-array reference for ({count:#x}, {table_off:#x}), got: {err:?}"
        );
    }
}
