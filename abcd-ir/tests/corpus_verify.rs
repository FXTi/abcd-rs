use abcd_file::decode;
use abcd_ir::{lift::lift_file, verify::verify_module};

#[test]
#[ignore = "requires exported GHCR corpus"]
fn exported_corpus_lifts_and_verifies_every_fixture() {
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
    for (line_no, line) in manifest.lines().enumerate() {
        let marker = "\"abc\": \"";
        let start = line
            .find(marker)
            .unwrap_or_else(|| panic!("manifest line {} has no abc path", line_no + 1))
            + marker.len();
        let end = start
            + line[start..]
                .find('"')
                .unwrap_or_else(|| panic!("manifest line {} has no path terminator", line_no + 1));
        let relative = &line[start..end];
        let data = std::fs::read(root.join(relative)).expect("fixture");
        let file = decode(&data).unwrap_or_else(|e| panic!("decode {relative}: {e}"));
        let module = lift_file(&file).unwrap_or_else(|e| panic!("lift {relative}: {e}"));
        let errors = verify_module(&module);
        assert!(errors.is_empty(), "verify {relative}: {errors:?}");
        fixtures += 1;
    }
    assert_eq!(fixtures, 2757);
}
