//! Legacy (file format 0.0.0.2, pre-2022-08-18 ISA) bytecode decoding.
//!
//! The translation table is generated from the OpenHarmony 3.1-era ISA
//! definition (see abcd-isa/tools/gen_legacy_table.py); these tests pin the
//! byte-level behavior with hand-built legacy streams.

use abcd_isa::{Bytecode, DecodeError, EntityId, Imm, Label, Reg, decode_legacy};

fn decode_one(bytes: &[u8]) -> Bytecode {
    let v = decode_legacy(bytes).unwrap();
    assert_eq!(v.len(), 1);
    v[0].0
}

#[test]
fn legacy_core_dynamic_subset() {
    // mov.dyn v8_v8
    assert!(matches!(
        decode_one(&[0xa0, 0x03, 0x07]),
        Bytecode::Mov(Reg(3), Reg(7))
    ));
    // lda.dyn / sta.dyn
    assert!(matches!(decode_one(&[0xa2, 0x2a]), Bytecode::Lda(Reg(42))));
    assert!(matches!(decode_one(&[0xa3, 0x2a]), Bytecode::Sta(Reg(42))));
    // ldai.dyn imm32 (signed)
    assert!(matches!(
        decode_one(&[0xa4, 0xff, 0xff, 0xff, 0xff]),
        Bytecode::Ldai(Imm(-1))
    ));
    // fldai.dyn imm64 (f64 bits)
    assert!(matches!(
        decode_one(&[0xa5, 0, 0, 0, 0, 0, 0, 0xf0, 0x3f]),
        Bytecode::Fldai(Imm(bits)) if f64::from_bits(bits as u64) == 1.0
    ));
    // return.dyn / nop
    assert!(matches!(decode_one(&[0xa6]), Bytecode::Return));
    assert!(matches!(decode_one(&[0x00]), Bytecode::Nop));
    // lda.str id32: legacy string operand is a direct 32-bit file offset
    assert!(matches!(
        decode_one(&[0x18, 0x78, 0x56, 0x34, 0x12]),
        Bytecode::LdaStr(EntityId(0x12345678))
    ));
}

#[test]
fn legacy_ecma_prefixed_none_format() {
    assert!(matches!(decode_one(&[0xff, 0x07]), Bytecode::Ldtrue));
    assert!(matches!(decode_one(&[0xff, 0x08]), Bytecode::Ldfalse));
    assert!(matches!(
        decode_one(&[0xff, 0x11]),
        Bytecode::Returnundefined
    ));
    assert!(matches!(
        decode_one(&[0xff, 0x0b]),
        Bytecode::DeprecatedLdlexenv
    ));
    // throwdyn -> throw
    assert!(matches!(decode_one(&[0xff, 0x09]), Bytecode::Throw));
    // typeofdyn: modern gained an IC-slot immediate, synthesized as 0
    assert!(matches!(
        decode_one(&[0xff, 0x0a]),
        Bytecode::Typeof(Imm(0))
    ));
}

#[test]
fn legacy_ecma_ic_slot_synthesis() {
    // add2dyn pref_v8 -> Add2(Imm(0), Reg)
    assert!(matches!(
        decode_one(&[0xff, 0x1a, 0x09]),
        Bytecode::Add2(Imm(0), Reg(9))
    ));
    // stobjbyname pref_id32_v8 -> Stobjbyname(Imm(0), EntityId, Reg)
    assert!(matches!(
        decode_one(&[0xff, 0x78, 0xef, 0xbe, 0x00, 0x00, 0x05]),
        Bytecode::Stobjbyname(Imm(0), EntityId(0xbeef), Reg(5))
    ));
    // ldobjbyname keeps its legacy layout via the deprecated variant
    assert!(matches!(
        decode_one(&[0xff, 0x77, 0xef, 0xbe, 0x00, 0x00, 0x05]),
        Bytecode::DeprecatedLdobjbyname(EntityId(0xbeef), Reg(5))
    ));
}

#[test]
fn legacy_ecma_deprecated_layouts() {
    // callarg1dyn pref_v8_v8: keeps the explicit func register (modern
    // callarg1 moved it to the accumulator)
    assert!(matches!(
        decode_one(&[0xff, 0x47, 0x01, 0x02]),
        Bytecode::DeprecatedCallarg1(Reg(1), Reg(2))
    ));
    // callithisrangedyn pref_imm16_v8 -> Callthisrange(ic=0, argc, v0)
    assert!(matches!(
        decode_one(&[0xff, 0x5c, 0x03, 0x00, 0x07]),
        Bytecode::Callthisrange(Imm(0), Imm(3), Reg(7))
    ));
    // ldlexvardyn imm4_imm4: nibble-packed operands
    assert!(matches!(
        decode_one(&[0xff, 0x6a, 0x21]),
        Bytecode::Ldlexvar(Imm(1), Imm(2))
    ));
    // definefuncdyn pref_id16_imm16_v8 -> Definefunc(ic=0, method idx, length)
    assert!(matches!(
        decode_one(&[0xff, 0x5f, 0x34, 0x12, 0x05, 0x00, 0x09]),
        Bytecode::Definefunc(Imm(0), EntityId(0x1234), Imm(5))
    ));
    // createobjectwithbuffer: 16-bit global literal-array index
    assert!(matches!(
        decode_one(&[0xff, 0x69, 0x2a, 0x00]),
        Bytecode::DeprecatedCreateobjectwithbuffer(Imm(42))
    ));
}

#[test]
fn legacy_jump_resolution() {
    // jmp +6 over `mov v0, v0` (3 bytes) and `nop` -> lands on return.dyn
    let code = [0x22u8, 0x06, 0xa0, 0x00, 0x00, 0x00, 0xa6];
    let v = decode_legacy(&code).unwrap();
    assert_eq!(v.len(), 4);
    // target = insn index 3 (return.dyn at byte offset 6)
    assert!(matches!(v[0].0, Bytecode::Jmp(Label(3))));
    // jeqz -1 at offset 1: back-jump to the nop at offset 0 (legacy jump
    // offsets are relative to the jump instruction start — validated against
    // the wild corpus, where every jump lands on an instruction boundary)
    let code = [0x00u8, 0x2d, 0xff];
    let v = decode_legacy(&code).unwrap();
    assert!(matches!(v[1].0, Bytecode::Jeqz(Label(0))));
}

#[test]
fn legacy_errors() {
    // unmapped legacy core opcode (call.acc.short, Java-era)
    assert_eq!(
        decode_legacy(&[0x99]).unwrap_err(),
        DecodeError::InvalidOpcode(0)
    );
    // unmapped legacy ecma opcode (newobjspreaddyn: no modern counterpart)
    assert_eq!(
        decode_legacy(&[0xff, 0x42]).unwrap_err(),
        DecodeError::InvalidOpcode(0)
    );
    // truncated prefix
    assert_eq!(
        decode_legacy(&[0xff]).unwrap_err(),
        DecodeError::Truncated(0)
    );
    // truncated instruction body
    assert_eq!(
        decode_legacy(&[0xa4, 0x00]).unwrap_err(),
        DecodeError::Truncated(0)
    );
    // jump past the end of the stream
    assert!(matches!(
        decode_legacy(&[0x22, 0x10]).unwrap_err(),
        DecodeError::InvalidJumpTarget { offset: 0, .. }
    ));
    // jump into the middle of an instruction
    assert!(matches!(
        decode_legacy(&[0x22, 0x01, 0xa6]).unwrap_err(),
        DecodeError::InvalidJumpTarget { offset: 0, .. }
    ));
}

#[test]
fn legacy_decode_never_panics_on_random_bytes() {
    // Deterministic xorshift fuzz: arbitrary bytes must produce Ok or Err,
    // never a panic.
    let mut state = 0x12345678u32;
    let mut buf = vec![0u8; 64];
    for _ in 0..2000 {
        for b in buf.iter_mut() {
            state ^= state << 13;
            state ^= state >> 17;
            state ^= state << 5;
            *b = state as u8;
        }
        let _ = decode_legacy(&buf);
    }
}

/// Full-stream sweep over the dumped method bodies of the 11 wild 0.0.0.2
/// packages (archaeology probe output). Ignored by default: run with
///
/// ```text
/// ANCIENT_PROBE_DIR=/tmp/ancient-probe \
///   cargo test -p abcd-isa --test legacy -- --ignored --nocapture
/// ```
#[test]
#[ignore = "requires the archaeology probe dumps (ANCIENT_PROBE_DIR)"]
fn legacy_wild_stream_sweep() {
    let dir = std::env::var("ANCIENT_PROBE_DIR").unwrap_or_else(|_| "/tmp/ancient-probe".into());
    let dump = std::path::Path::new(&dir).join("dump");
    // Local archaeology instrument: skip (never fail) without the probe
    // dump — the coverage job runs #[ignore]d tests on runners that have
    // none.
    if !dump.is_dir() {
        eprintln!("legacy sweep: no dump at {dump:?}, skipping (local-only instrument)");
        return;
    }
    let mut total = 0usize;
    let mut insns = 0usize;
    let mut failures = Vec::new();
    let mut entries: Vec<_> = std::fs::read_dir(&dump)
        .expect("dump dir present but unreadable")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .collect();
    entries.sort();
    if entries.is_empty() {
        // An EMPTY dump is another instrument's leftover scaffold (the probe
        // creates the dir before it has anything to write); there is no
        // corpus to sweep, so skip rather than fail the volume assertion.
        eprintln!("legacy sweep: empty dump at {dump:?}, skipping (local-only instrument)");
        return;
    }
    for path in entries {
        let code = std::fs::read(&path).unwrap();
        total += 1;
        match decode_legacy(&code) {
            Ok(v) => insns += v.len(),
            Err(e) => failures.push(format!("{}: {e}", path.display())),
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {total} legacy streams failed:\n{}",
        failures.len(),
        failures[..failures.len().min(20)].join("\n")
    );
    eprintln!("legacy sweep: {total} streams, {insns} instructions, all decoded");
    assert!(insns > 100_000, "expected the full wild corpus volume");
}
