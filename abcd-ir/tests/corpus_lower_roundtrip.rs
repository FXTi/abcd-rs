use abcd_file::decode;
use abcd_ir::{lift::lift_file, lower::lower_function, verify::verify_module};

#[test]
#[ignore = "requires exported GHCR corpus"]
fn arithmetic_corpus_lower_output_roundtrips_through_isa() {
    let root = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        });
    let manifest = std::fs::read_to_string(root.join("index.jsonl")).expect("corpus manifest");
    let mut fixtures = 0usize;
    for line in manifest.lines() {
        if !line.contains("\"case\": \"local/arithmetic\"") {
            continue;
        }
        let marker = "\"abc\": \"";
        let start = line.find(marker).expect("abc path") + marker.len();
        let end = start + line[start..].find('"').expect("abc path terminator");
        let relative = &line[start..end];
        let file = decode(&std::fs::read(root.join(relative)).expect("fixture"))
            .unwrap_or_else(|e| panic!("decode {relative}: {e}"));
        let module = lift_file(&file).unwrap_or_else(|e| panic!("lift {relative}: {e}"));
        assert!(verify_module(&module).is_empty());
        for index in 0..module.functions.len() {
            let result = lower_function(&module, abcd_ir::entity::FuncId::from_index(index))
                .unwrap_or_else(|e| panic!("lower {relative} function {index}: {e}"));
            let (bytes, _) = abcd_isa::encode(&result.bytecodes).expect("encode lowered bytecode");
            let decoded = abcd_isa::decode(&bytes).expect("decode lowered bytecode");
            assert_eq!(
                decoded.len(),
                result.bytecodes.len(),
                "{relative} function {index}"
            );
        }
        fixtures += 1;
    }
    assert_eq!(fixtures, 18);
}
