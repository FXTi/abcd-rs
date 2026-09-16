use abcd_file::decode;
use abcd_ir::{lift::lift_file, lower::lower_function, verify::verify_module};

#[test]
#[ignore = "requires exported GHCR corpus"]
fn wide_register_fixture_lowers_without_nontermination() {
    let path = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::path::PathBuf::from("../exports/corpus"))
        .join("9.0.0.0/upstream/bytecode/ts/ic/ic-slot-16-overflow/baseline/input.abc");
    let file = decode(&std::fs::read(path).expect("wide fixture")).expect("decode");
    let module = lift_file(&file).expect("lift");
    assert!(verify_module(&module).is_empty());
    for index in 0..module.functions.len() {
        lower_function(&module, abcd_ir::entity::FuncId::from_index(index))
            .unwrap_or_else(|e| panic!("function {index}: {e}"));
    }
}
