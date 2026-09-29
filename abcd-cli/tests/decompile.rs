//! `decompile` tests over a synthesized .abc (through the full
//! decode → lift → emit pipeline).

mod common;

use abcd_cli::decompile::{self, DecompileOptions};
use abcd_cli::input::{self, ModuleSelection};

fn module(bytes: &[u8], name: &str) -> abcd_cli::input::InputModule {
    input::load_bytes(bytes, name, ModuleSelection::Single)
        .unwrap()
        .into_iter()
        .next()
        .unwrap()
}

#[test]
fn decompiles_a_bare_abc() {
    let m = module(&common::tiny_abc(), "modules.abc");
    let out = decompile::decompile(&m, DecompileOptions::default()).unwrap();
    assert!(
        out.text.contains("function func_main_0("),
        "expected the synthesized entry function in:\n{}",
        out.text
    );
    assert!(out.stats.functions >= 1);
}

#[test]
fn call_entry_flag_appends_the_entry_call() {
    let m = module(&common::tiny_abc(), "modules.abc");
    let plain = decompile::decompile(&m, DecompileOptions::default()).unwrap();
    let with_entry = decompile::decompile(
        &m,
        DecompileOptions {
            call_entry: true,
            ..Default::default()
        },
    )
    .unwrap();
    assert!(!plain.text.contains(".call(this)"));
    assert!(
        with_entry.text.contains(".call(this)"),
        "expected entry call in:\n{}",
        with_entry.text
    );
}

#[test]
fn decompiles_through_a_hap_container() {
    let hap = common::hap("entry", &common::tiny_abc());
    let m = module(&hap, "entry.hap");
    let out = decompile::decompile(&m, DecompileOptions::default()).unwrap();
    assert!(out.text.contains("function func_main_0("), "{}", out.text);
}

#[test]
fn write_all_lays_down_one_js_per_module() {
    let app = common::app(&[
        ("entry.hap", common::hap("entry", &common::tiny_abc())),
        ("phone.hap", common::hap("phone", &common::tiny_abc())),
    ]);
    let modules = input::load_bytes(&app, "bundle.app", ModuleSelection::All).unwrap();
    let dir = common::tempdir("decompile-all");
    let written = decompile::write_all(&modules, &dir, DecompileOptions::default()).unwrap();
    let names: Vec<&str> = written.iter().map(|(n, _, _)| n.as_str()).collect();
    assert_eq!(names, ["entry", "phone"]);
    for name in names {
        let path = dir.join(format!("{name}.js"));
        let text = std::fs::read_to_string(&path).unwrap();
        assert!(text.contains("function func_main_0("), "{name}.js:\n{text}");
    }
}

#[test]
fn corrupt_abc_is_a_tool_error() {
    let bad = vec![0u8; 32];
    let m = module(&bad, "bad.abc");
    let err = decompile::decompile(&m, DecompileOptions::default()).unwrap_err();
    assert_eq!(err.exit_code(), 2);
}
