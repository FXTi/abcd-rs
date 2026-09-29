//! `abcd asm` tests: pandasm text → .abc assembly. The parser's corpus-level
//! fidelity is gated by tests/file-isa/pandasm_asm.rs; here we pin the CLI
//! plumbing: dis→asm round-trip shape, --check, version flag, error mapping.

mod common;

use abcd_cli::asm;

#[test]
fn dis_asm_roundtrip_preserves_shape() {
    let abc = common::tiny_abc();
    let file = abcd_file::decode(&abc).expect("decode fixture");
    let pa = abcd_file::pandasm::emit_file(&file, "tiny.abc");

    let reassembled = asm::assemble(&pa, "tiny.pa", None, true).expect("assemble");
    let reparsed = abcd_file::decode(&reassembled).expect("decode assembled");

    let shape = |f: &abcd_file::File| {
        f.all_methods()
            .map(|(_, m)| {
                (
                    m.body.as_ref().map(|b| b.bytecodes.len()),
                    m.body.as_ref().map(|b| {
                        b.bytecodes
                            .iter()
                            .map(|bc| bc.mnemonic())
                            .collect::<Vec<_>>()
                    }),
                )
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(shape(&file), shape(&reparsed));
}

#[test]
fn assemble_with_explicit_version() {
    let abc = common::tiny_abc();
    let file = abcd_file::decode(&abc).expect("decode fixture");
    let pa = abcd_file::pandasm::emit_file(&file, "tiny.abc");
    let out = asm::assemble(
        &pa,
        "tiny.pa",
        Some(abcd_file::Version::new(12, 0, 6, 0)),
        true,
    )
    .expect("assemble with version");
    let f = abcd_file::decode(&out).expect("decode");
    assert_eq!(f.version.major(), 12);
}

#[test]
fn unparsable_text_is_a_user_error() {
    let err = asm::assemble(b"this is not pandasm at all", "junk.pa", None, false).unwrap_err();
    assert_eq!(err.exit_code(), 1, "parse failures are user errors");
}
