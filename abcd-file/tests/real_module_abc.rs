//! Group J — full-opcode decode coverage against a real production file.
//!
//! Uses a device stock `modules.abc` (21.6 MB, 12.0.6.0, 2035 classes).
//! That file is local-only and gitignored (Huawei distribution
//! restrictions), so this test is `#[ignore]`d in CI and run explicitly
//! whenever the corpus is present:
//!
//! ```text
//! cargo test --test real_module_abc -- --ignored
//! ```

use abcd_file::{decode, encode};
use abcd_isa::{Version, decode as decode_isa, encode as encode_isa};

fn exported_corpus_root() -> std::path::PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        })
}

fn corpus_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("modules.abc")
}

/// The whole production file decodes with the vendored 24.0.0.0 opcode
/// table (see design/isa-compat.md: 12.0.6.0 is a strict subset of 24).
/// Any unknown opcode aborts `decode`, so merely reaching the asserts
/// proves full opcode coverage.
#[test]
#[ignore = "requires local-only modules.abc (gitignored)"]
fn modules_abc_decodes_fully_with_v24_table() {
    let path = corpus_path();
    let data = std::fs::read(&path)
        .unwrap_or_else(|e| panic!("corpus missing at {}: {e}", path.display()));

    let file = decode(&data).expect("decode modules.abc without errors");

    assert_eq!(file.version, Version::new(12, 0, 6, 0));

    let mut classes = 0usize;
    let mut methods = 0usize;
    let mut instructions = 0usize;
    let mut proto_shorty = 0usize;
    for c in file.classes.values() {
        classes += 1;
        for m in &c.methods {
            methods += 1;
            // Format fact #A7: 12.0.6.0 protos carry no shorty signature —
            // return types are absent from every method item.
            if m.return_type.is_some() {
                proto_shorty += 1;
            }
            if let Some(body) = &m.body {
                instructions += body.bytecodes.len();
            }
        }
    }

    assert_eq!(proto_shorty, 0, "12.0.6.0 protos must have no return types");

    // Snapshot floors recorded at 12.0.6.0 stock (2,946,777 instructions):
    // they exist to catch table regressions, not to track exact builds.
    assert!(classes >= 2000, "expected >=2000 classes, got {classes}");
    assert!(methods >= 12000, "expected >=12000 methods, got {methods}");
    assert!(
        instructions > 2_000_000,
        "expected >2,000,000 decoded instructions, got {instructions}"
    );
}

/// Decode every fixture listed by the exported corpus manifest.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn exported_corpus_index_decodes_every_fixture() {
    let root = exported_corpus_root();
    let manifest = root.join("index.jsonl");
    let text = std::fs::read_to_string(&manifest)
        .unwrap_or_else(|e| panic!("corpus manifest missing at {}: {e}", manifest.display()));
    let mut count = 0usize;
    for (line_no, line) in text.lines().enumerate() {
        let prefix = "\"abc\": \"";
        let start = line
            .find(prefix)
            .unwrap_or_else(|| panic!("manifest line {} has no abc path", line_no + 1))
            + prefix.len();
        let end = line[start..]
            .find('"')
            .map(|i| start + i)
            .unwrap_or_else(|| panic!("manifest line {} has unterminated abc path", line_no + 1));
        let rel = &line[start..end];
        let path = root.join(rel);
        let data = std::fs::read(&path)
            .unwrap_or_else(|e| panic!("fixture missing at {}: {e}", path.display()));
        let file =
            decode(&data).unwrap_or_else(|e| panic!("decode failed at {}: {e:?}", path.display()));
        let version = rel
            .split('/')
            .next()
            .and_then(|v| {
                v.split('.')
                    .map(|n| n.parse::<u8>().ok())
                    .collect::<Option<Vec<_>>>()
            })
            .and_then(|v| (v.len() == 4).then(|| Version::new(v[0], v[1], v[2], v[3])))
            .unwrap_or_else(|| panic!("invalid version path in manifest line {}", line_no + 1));
        assert_eq!(
            file.version,
            version,
            "version mismatch at {}",
            path.display()
        );
        count += 1;
    }
    assert_eq!(count, 2757, "unexpected exported corpus size");
}

/// Exercise the ISA encode/decode layer for every decoded method body.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn exported_corpus_method_bytecodes_roundtrip_through_isa() {
    let root = exported_corpus_root();
    let manifest = root.join("index.jsonl");
    let text = std::fs::read_to_string(&manifest).expect("corpus manifest");
    let mut methods = 0usize;
    for line in text.lines() {
        let prefix = "\"abc\": \"";
        let start = line.find(prefix).expect("abc path") + prefix.len();
        let end = start + line[start..].find('"').expect("abc path terminator");
        let data = std::fs::read(root.join(&line[start..end])).expect("fixture");
        let file = decode(&data).expect("decode fixture");
        for class in file.classes.values() {
            for method in &class.methods {
                let Some(body) = &method.body else { continue };
                let encoded = encode_isa(&body.bytecodes).expect("encode method bytecodes");
                let decoded = decode_isa(&encoded.0).expect("decode encoded method bytecodes");
                assert_eq!(decoded.len(), body.bytecodes.len());
                methods += 1;
            }
        }
    }
    assert!(methods > 10_000, "unexpected method count: {methods}");
}

#[test]
#[ignore = "requires exported GHCR corpus"]
fn rewritten_corpus_preserves_arithmetic_entities() {
    let root = exported_corpus_root();
    let rows: Vec<serde_json::Value> = std::fs::read_to_string(root.join("index.jsonl"))
        .expect("corpus index")
        .lines()
        .map(|line| serde_json::from_str(line).expect("valid index JSON"))
        .collect();
    let mut checked = 0;
    for row in rows.iter().filter(|row| row["case"] == "local/arithmetic") {
        let relative = row["abc"].as_str().expect("abc path");
        let file = decode(&std::fs::read(root.join(relative)).expect("fixture"))
            .unwrap_or_else(|error| panic!("decode {relative}: {error}"));
        let output = encode(&file).unwrap_or_else(|error| panic!("encode {relative}: {error}"));
        let rewritten = decode(&output).expect("decode rewritten fixture");
        let snapshot = |f: &abcd_file::File| {
            f.all_methods()
                .map(|(_, method)| {
                    let name = f.strings.resolve(method.name).unwrap().to_owned();
                    let body = method.body.as_ref().unwrap();
                    let operands = body
                        .bytecodes
                        .iter()
                        .flat_map(|bc| {
                            bc.entity_operands().into_iter().map(|(kind, id)| {
                                let offset = body.entity_offsets[&(kind, id.0)];
                                (
                                    bc.mnemonic(),
                                    kind,
                                    f.resolve_entity_str(offset).unwrap().to_owned(),
                                )
                            })
                        })
                        .collect::<Vec<_>>();
                    (name, body.bytecodes.len(), operands)
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(rewritten.version, file.version, "{relative}");
        assert_eq!(snapshot(&rewritten), snapshot(&file), "{relative}");
        if let Some(directory) = std::env::var_os("ABCD_REWRITTEN_DIR") {
            let target = std::path::PathBuf::from(directory).join(relative);
            std::fs::create_dir_all(target.parent().unwrap()).unwrap();
            std::fs::write(target, output).expect("write oracle candidate");
        }
        checked += 1;
    }
    assert_eq!(checked, 18, "arithmetic version/profile matrix");
}

/// Render a module/scope record field value into comparable strings.
///
/// Module blobs carry string-offset references, so equality across a
/// rewrite must be checked through the string pool, not raw offsets.
fn module_field_snapshots(f: &abcd_file::File) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for (desc, cls) in &f.classes {
        for field in &cls.fields {
            let key = format!(
                "{}.{}",
                f.strings.resolve(*desc).unwrap_or("?"),
                f.strings.resolve(field.name).unwrap_or("?")
            );
            let value = match &field.initial_value {
                Some(abcd_file::FieldValue::ModuleData(md)) => {
                    let requests: Vec<&str> = md
                        .requests
                        .iter()
                        .map(|&sid| f.strings.resolve(sid).expect("request string"))
                        .collect();
                    let records: Vec<String> = md
                        .records
                        .iter()
                        .map(|rec| {
                            use abcd_file::ModuleRecord::*;
                            let r = |sid: abcd_file::StringId| {
                                f.strings.resolve(sid).unwrap_or("?").to_owned()
                            };
                            match rec {
                                RegularImport {
                                    local_name,
                                    import_name,
                                    module_request_idx,
                                } => format!(
                                    "regular({},{},{module_request_idx})",
                                    r(*local_name),
                                    r(*import_name)
                                ),
                                NamespaceImport {
                                    local_name,
                                    module_request_idx,
                                } => format!("namespace({},{module_request_idx})", r(*local_name)),
                                LocalExport {
                                    local_name,
                                    export_name,
                                } => format!("local({},{})", r(*local_name), r(*export_name)),
                                IndirectExport {
                                    export_name,
                                    import_name,
                                    module_request_idx,
                                } => format!(
                                    "indirect({},{},{module_request_idx})",
                                    r(*export_name),
                                    r(*import_name)
                                ),
                                StarExport { module_request_idx } => {
                                    format!("star({module_request_idx})")
                                }
                            }
                        })
                        .collect();
                    format!("module({requests:?};{})", records.join(","))
                }
                Some(abcd_file::FieldValue::LiteralArrayRef(off)) => {
                    let idx = f
                        .literal_array_offsets
                        .get(off)
                        .unwrap_or_else(|| panic!("scope blob offset {off:#x} must decode"));
                    let values: Vec<String> = f.literal_arrays[*idx as usize]
                        .values
                        .iter()
                        .map(|v| match v {
                            abcd_file::LiteralValue::String(sid) => {
                                f.strings.resolve(*sid).unwrap_or("?").to_owned()
                            }
                            other => format!("{other:?}"),
                        })
                        .collect();
                    format!("scope({})", values.join(","))
                }
                other => format!("{other:?}"),
            };
            out.push((key, value));
        }
    }
    out
}

/// Identity rewrite of module-record-bearing corpus fixtures (S4/S5/N1/N6
/// evidence): decode -> encode must succeed, and the rewritten file's module
/// and scope-names data must be equivalent to the source.
///
/// Before the module-record modeling fix, the rewritten bytes aborted
/// ark_disasm ('This line should be unreachable') and FATALed the VM
/// ('Invalid span offset'): the field value was written back as a dangling
/// source offset and (<=12.x) the module blob was misparsed as a tagged
/// literal array of zeros.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn rewritten_corpus_module_cases() {
    const CASES: &[&str] = &[
        "local/module-exports",
        "local/module-imports",
        "upstream/bytecode/ts/cases/test-namespace",
        "upstream/optimizer/js/branch-elimination/test-constant-propagation",
    ];
    let root = exported_corpus_root();
    let rows: Vec<serde_json::Value> = std::fs::read_to_string(root.join("index.jsonl"))
        .expect("corpus index")
        .lines()
        .map(|line| serde_json::from_str(line).expect("valid index JSON"))
        .collect();
    let mut checked = 0;
    for row in rows.iter().filter(|row| {
        row["case"]
            .as_str()
            .is_some_and(|case| CASES.contains(&case))
    }) {
        let relative = row["abc"].as_str().expect("abc path");
        let file = decode(&std::fs::read(root.join(relative)).expect("fixture"))
            .unwrap_or_else(|error| panic!("decode {relative}: {error}"));
        let expected = module_field_snapshots(&file);
        assert!(
            expected.iter().any(|(_, v)| v.starts_with("module(")),
            "{relative}: fixture must carry module-record data"
        );
        let output = encode(&file).unwrap_or_else(|error| panic!("encode {relative}: {error}"));
        let rewritten =
            decode(&output).unwrap_or_else(|error| panic!("decode rewritten {relative}: {error}"));
        assert_eq!(
            module_field_snapshots(&rewritten),
            expected,
            "{relative}: module/scope data must survive the identity rewrite"
        );
        if let Some(directory) = std::env::var_os("ABCD_REWRITTEN_DIR") {
            let target = std::path::PathBuf::from(directory).join(relative);
            std::fs::create_dir_all(target.parent().unwrap()).unwrap();
            std::fs::write(target, output).expect("write oracle candidate");
        }
        checked += 1;
    }
    assert_eq!(checked, 72, "4 module cases x 6 versions x 3 profiles");
}
