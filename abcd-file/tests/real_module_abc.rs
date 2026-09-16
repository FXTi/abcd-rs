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

use abcd_file::decode;
use abcd_isa::{decode as decode_isa, encode as encode_isa, Version};

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
        let file = decode(&data)
            .unwrap_or_else(|e| panic!("decode failed at {}: {e:?}", path.display()));
        let version = rel
            .split('/')
            .next()
            .and_then(|v| v.split('.').map(|n| n.parse::<u8>().ok()).collect::<Option<Vec<_>>>())
            .and_then(|v| (v.len() == 4).then(|| Version::new(v[0], v[1], v[2], v[3])))
            .unwrap_or_else(|| panic!("invalid version path in manifest line {}", line_no + 1));
        assert_eq!(file.version, version, "version mismatch at {}", path.display());
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
