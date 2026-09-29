//! `abcd dis` tests: disassembly of synthesized fixtures through the shared
//! input layer. Byte-identity against upstream ark_disasm is gated by the
//! corpus (tests/file-isa/pandasm_dis.rs); here we pin the CLI plumbing:
//! structure, determinism, source-name convention, module selection.

mod common;

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
