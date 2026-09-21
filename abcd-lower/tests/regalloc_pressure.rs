//! v0.2 port of `abcd-ir/tests/regalloc_pressure.rs`: the wide-register
//! corpus fixture must lower without nontermination.

use abcd_file::decode;
use abcd_ir::{FuncId, verify_module};
use abcd_lift::lift_file;
use abcd_lower::lower_function;

#[test]
#[ignore = "requires exported GHCR corpus"]
fn wide_register_fixture_lowers_without_nontermination() {
    let path = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        })
        .join("9.0.0.0/upstream/bytecode/ts/ic/ic-slot-16-overflow/baseline/input.abc");
    let file = decode(&std::fs::read(path).expect("wide fixture")).expect("decode");
    let module = lift_file(&file).expect("lift");
    assert!(verify_module(&module).is_ok());
    for index in 0..module.functions.len() {
        let func_id = FuncId::new(index as u32);
        if module.functions[index].blocks.is_empty() {
            continue;
        }
        lower_function(&module, func_id).unwrap_or_else(|e| panic!("function {index}: {e}"));
    }
}
