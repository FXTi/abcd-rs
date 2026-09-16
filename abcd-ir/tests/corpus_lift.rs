use abcd_file::decode;
use abcd_ir::lift::lift_file;

fn corpus_root() -> std::path::PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        })
}

#[test]
#[ignore = "requires exported GHCR corpus"]
fn exported_corpus_lifts_every_fixture() {
    let root = corpus_root();
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
        lift_file(&file).unwrap_or_else(|e| {
            for (_, method) in file.all_methods() {
                if let Some(body) = &method.body {
                    if body
                        .bytecodes
                        .iter()
                        .any(|bc| format!("{bc:?}").contains("id:12"))
                    {
                        println!(
                            "method {:?}: {:?}",
                            file.strings.resolve(method.name),
                            body.bytecodes
                        );
                    }
                }
            }
            println!("literal offsets: {:?}", file.literal_array_offsets);
            for (_, method) in file.all_methods() {
                if let Some(body) = &method.body
                    && body
                        .entity_offsets
                        .contains_key(&(abcd_isa::EntityKind::LiteralarrayId, 12))
                {
                    println!("failing body map: {:?}", body.entity_offsets);
                }
            }
            panic!("lift {relative}: {e}")
        });
        fixtures += 1;
    }
    assert_eq!(fixtures, 2757);
}
