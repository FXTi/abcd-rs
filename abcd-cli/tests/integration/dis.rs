//! `abcd dis` tests: disassembly of synthesized fixtures through the shared
//! input layer. Byte-identity against upstream ark_disasm is gated by the
//! corpus (tests/file-isa/pandasm_dis.rs); here we pin the CLI plumbing:
//! structure, determinism, source-name convention, module selection.

use crate::common;
use abcd_cli::dis;
use abcd_cli::input::{self, ModuleSelection};

#[test]
fn dis_bare_abc_emits_pandasm_structure() {
    let modules =
        input::load_bytes(&common::tiny_abc(), "tiny.abc", ModuleSelection::Single).expect("load");
    let pa = dis::disassemble(&modules[0]).expect("disassemble");
    let text = String::from_utf8_lossy(&pa);
    assert!(text.contains("# source binary: tiny.abc"), "text: {text}");
    assert!(text.contains("# METHODS"), "text: {text}");
    assert!(text.contains(".function"), "text: {text}");
    assert!(text.contains("func_main_0"), "text: {text}");
}

#[test]
fn dis_is_deterministic() {
    let modules =
        input::load_bytes(&common::tiny_abc(), "tiny.abc", ModuleSelection::Single).expect("load");
    let a = dis::disassemble(&modules[0]).expect("first");
    let b = dis::disassemble(&modules[0]).expect("second");
    assert_eq!(a, b);
}

#[test]
fn dis_container_module_uses_entry_basename_in_header() {
    let hap = common::hap("entry", &common::tiny_abc());
    let modules = input::load_bytes(&hap, "demo.hap", ModuleSelection::Single).expect("load");
    let pa = dis::disassemble(&modules[0]).expect("disassemble");
    let text = String::from_utf8_lossy(&pa);
    // ark_disasm prints the disassembled file's own name; for a module read
    // out of a container that is the entry basename, not the container name.
    assert!(
        text.contains("# source binary: modules.abc"),
        "text: {text}"
    );
}

#[test]
fn dis_corrupt_abc_is_a_tool_error() {
    let modules =
        input::load_bytes(b"not an abc at all", "bad.abc", ModuleSelection::Single).expect("load");
    let err = dis::disassemble(&modules[0]).unwrap_err();
    assert_eq!(err.exit_code(), 2, "decode failure is a tool error");
}

#[test]
fn write_all_out_dir_occupied_by_a_file_is_a_tool_error() {
    let modules =
        input::load_bytes(&common::tiny_abc(), "tiny.abc", ModuleSelection::Single).expect("load");
    let dir = common::tempdir("dis-io-err");
    let occupied = dir.join("occupied");
    std::fs::write(&occupied, b"x").unwrap();
    let err = dis::write_all(&modules, &occupied).unwrap_err();
    assert_eq!(err.exit_code(), 2);
    assert!(
        err.to_string().contains("cannot create output directory"),
        "{err}"
    );
}

#[test]
fn write_all_write_failure_is_a_tool_error() {
    // A directory squatting the <name>.pa output path fails the write.
    let modules =
        input::load_bytes(&common::tiny_abc(), "tiny.abc", ModuleSelection::Single).expect("load");
    let dir = common::tempdir("dis-write-err");
    std::fs::create_dir_all(dir.join("tiny.pa")).unwrap();
    let err = dis::write_all(&modules, &dir).unwrap_err();
    assert_eq!(err.exit_code(), 2);
    assert!(err.to_string().contains("cannot write"), "{err}");
}

#[test]
fn write_all_aborts_the_batch_on_a_bad_module() {
    // [good, corrupt]: the first module lands, the second fails the
    // disassembly and the error aborts the batch.
    let mut modules =
        input::load_bytes(&common::tiny_abc(), "tiny.abc", ModuleSelection::Single).expect("load");
    let mut bad = input::load_bytes(b"junk", "bad.abc", ModuleSelection::Single).expect("load");
    modules.append(&mut bad);
    let dir = common::tempdir("dis-batch-err");
    let err = dis::write_all(&modules, &dir).unwrap_err();
    assert_eq!(err.exit_code(), 2);
    assert!(err.to_string().contains("failed to decode"), "{err}");
    assert!(dir.join("tiny.pa").exists(), "the good module was written");
    assert!(!dir.join("bad.pa").exists(), "the bad module was not");
}

#[test]
fn streaming_disassemble_matches_in_memory_and_preserves_target_on_decode_error() {
    let modules =
        input::load_bytes(&common::tiny_abc(), "tiny.abc", ModuleSelection::Single).expect("load");
    let expected = dis::disassemble(&modules[0]).expect("disassemble");

    let mut streamed = Vec::new();
    let n_writer = dis::disassemble_to_writer(&modules[0], &mut streamed).expect("to_writer");
    assert_eq!(n_writer, expected.len());
    assert_eq!(streamed, expected);

    let dir = common::tempdir("dis-stream");
    let out_path = dir.join("tiny.pa");
    let n_path = dis::disassemble_to_path(&modules[0], &out_path).expect("to_path");
    assert_eq!(n_path, expected.len());
    assert_eq!(std::fs::read(&out_path).unwrap(), expected);

    let bad = input::load_bytes(b"corrupt", "bad.abc", ModuleSelection::Single).expect("load");
    let missing_path = dir.join("never_created.pa");
    assert!(dis::disassemble_to_path(&bad[0], &missing_path).is_err());
    assert!(
        !missing_path.exists(),
        "decode failure must not create an empty output file"
    );
    assert!(dis::disassemble_to_path(&bad[0], &out_path).is_err());
    assert_eq!(
        std::fs::read(&out_path).unwrap(),
        expected,
        "decode failure must not truncate an existing output file"
    );
}
