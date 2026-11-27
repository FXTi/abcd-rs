//! file → isa cross-crate corpus & container round-trip gates.
//!
//! Covers:
//! - Group J (`modules_abc_decodes_fully_with_v24_table`): full-opcode decode
//!   against a local-only production `modules.abc` when present;
//! - ISA round-trip (`exported_corpus_method_bytecodes_roundtrip_through_isa`):
//!   `abcd_isa::encode` → `abcd_isa::decode` over every method of all 5,517
//!   corpus fixtures;
//! - Group K (`pandasm_dis`): byte-for-byte `abcd dis` identity against
//!   upstream `ark_disasm` (`reference.pa`) across all 5,517 fixtures;
//! - Group L (`pandasm_asm`): text and binary `abcd asm` round-trips across all
//!   5,517 fixtures;
//! - Entity & `--merge-abc` metadata identity rewrites (`arithmetic`,
//!   `moduleRecordIdx`, `scopeNames`, `moduleRequestPhaseIdx`).

use abcd_file::{decode, encode};
use abcd_isa::{Version, decode as decode_isa, encode as encode_isa};
use rayon::prelude::*;
use std::process::Command;

mod pandasm_asm;
mod pandasm_dis;

pub(crate) fn exported_corpus_root() -> std::path::PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus"))
}

fn corpus_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("modules.abc")
}

/// Parse the corpus manifest with Python's standard JSON parser.
pub(crate) fn manifest_select(root: &std::path::Path, select: &str) -> Vec<String> {
    let program = format!(
        r#"
import json, sys
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
{select}
"#
    );
    let output = Command::new("python3")
        .arg("-c")
        .arg(program)
        .arg(root.join("index.jsonl"))
        .output()
        .expect("python3 is required by corpus tooling");
    assert!(
        output.status.success(),
        "manifest selection failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("UTF-8 manifest selection")
        .lines()
        .map(str::to_owned)
        .collect()
}

/// Every row, as its `abc` path.
const SELECT_ABC: &str = r#"        assert "\n" not in row["abc"] and "\t" not in row["abc"]
        print(row["abc"])"#;

/// Every row, as `abc<TAB>pandasm`.
pub(crate) const SELECT_ABC_PANDASM: &str = r#"        assert all("\n" not in row[key] and "\t" not in row[key] for key in ("abc", "pandasm"))
        print(row["abc"] + "\t" + row["pandasm"])"#;

/// The whole production file decodes with the vendored 24.0.0.0 opcode
/// table (see `design/isa-compat.md`: 12.0.6.0 is a strict subset of 24).
#[test]
#[ignore = "requires local-only modules.abc (gitignored)"]
fn modules_abc_decodes_fully_with_v24_table() {
    let path = corpus_path();
    let Ok(data) = std::fs::read(&path) else {
        eprintln!("modules.abc absent at {} — skipped", path.display());
        return;
    };

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
            if m.return_type.is_some() {
                proto_shorty += 1;
            }
            if let Some(body) = &m.body {
                instructions += body.insn_count();
            }
        }
    }

    assert_eq!(proto_shorty, 0, "12.0.6.0 protos must have no return types");
    assert!(classes >= 2000, "expected >=2000 classes, got {classes}");
    assert!(methods >= 12000, "expected >=12000 methods, got {methods}");
    assert!(
        instructions > 2_000_000,
        "expected >2,000,000 decoded instructions, got {instructions}"
    );
}

/// Exercise the ISA encode/decode layer for every decoded method body across
/// all 5,517 corpus fixtures, including version-header agreement.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn exported_corpus_method_bytecodes_roundtrip_through_isa() {
    let root = exported_corpus_root();
    let rows = manifest_select(&root, SELECT_ABC);
    assert_eq!(rows.len(), 5517, "expected the full 5517-fixture corpus");
    let methods: usize = rows
        .par_iter()
        .map(|rel| {
            let path = root.join(rel);
            let data = std::fs::read(&path)
                .unwrap_or_else(|e| panic!("fixture missing at {}: {e}", path.display()));
            let file = decode(&data)
                .unwrap_or_else(|e| panic!("decode failed at {}: {e:?}", path.display()));
            let expected_version = rel
                .split('/')
                .next()
                .and_then(|v| {
                    v.split('.')
                        .map(|n| n.parse::<u8>().ok())
                        .collect::<Option<Vec<_>>>()
                })
                .and_then(|v| (v.len() == 4).then(|| Version::new(v[0], v[1], v[2], v[3])))
                .unwrap_or_else(|| panic!("invalid version path in manifest row: {rel}"));
            assert_eq!(
                file.version,
                expected_version,
                "version mismatch at {}",
                path.display()
            );
            let mut methods = 0usize;
            for class in file.classes.values() {
                for method in &class.methods {
                    let Some(body) = &method.body else { continue };
                    let bcs = body.bytecodes();
                    let encoded = encode_isa(&bcs).expect("encode method bytecodes");
                    let decoded = decode_isa(&encoded.0).expect("decode encoded method bytecodes");
                    assert_eq!(decoded.len(), bcs.len());
                    methods += 1;
                }
            }
            methods
        })
        .sum();
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
    let relatives: Vec<&str> = rows
        .iter()
        .filter(|row| row["case"] == "local/arithmetic")
        .map(|row| row["abc"].as_str().expect("abc path"))
        .collect();
    let outputs: Vec<Vec<u8>> = relatives
        .par_iter()
        .map(|relative| {
            let file = decode(&std::fs::read(root.join(relative)).expect("fixture"))
                .unwrap_or_else(|error| panic!("decode {relative}: {error}"));
            let output = encode(&file).unwrap_or_else(|error| panic!("encode {relative}: {error}"));
            let rewritten = decode(&output).expect("decode rewritten fixture");
            let snapshot = |f: &abcd_file::File| {
                f.all_methods()
                    .map(|(_, method)| {
                        let name = f.strings.resolve(method.name).unwrap().to_owned();
                        let body = method.body.as_ref().unwrap();
                        let bcs = body.bytecodes();
                        let operands = bcs
                            .iter()
                            .flat_map(|bc| {
                                bc.entity_operands().into_iter().map(|(kind, id)| {
                                    let resolved = match body.entities[&(kind, id.0)] {
                                        abcd_file::EntityRef::String { id: sid, .. } => {
                                            f.strings.resolve(sid).unwrap().to_owned()
                                        }
                                        abcd_file::EntityRef::Method(midx) => {
                                            let (_, _, m) = f.method_by_idx(midx).unwrap();
                                            f.strings.resolve(m.name).unwrap().to_owned()
                                        }
                                        abcd_file::EntityRef::ExternalMethod { name, .. } => {
                                            f.strings.resolve(name).unwrap().to_owned()
                                        }
                                        abcd_file::EntityRef::LiteralArray(lidx) => format!(
                                            "lit_len={}",
                                            f.literal_arrays[lidx.index()].values.len()
                                        ),
                                    };
                                    (bc.mnemonic(), kind, resolved)
                                })
                            })
                            .collect::<Vec<_>>();
                        (name, bcs.len(), operands)
                    })
                    .collect::<Vec<_>>()
            };
            assert_eq!(rewritten.version, file.version, "{relative}");
            assert_eq!(snapshot(&rewritten), snapshot(&file), "{relative}");
            output
        })
        .collect();
    let mut checked = 0;
    for (relative, output) in relatives.iter().zip(&outputs) {
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
                Some(abcd_file::FieldValue::ModuleRequestPhase(p)) => {
                    format!("phase({:?})", p.flags)
                }
                Some(abcd_file::FieldValue::LiteralArrayRef { index, .. }) => {
                    let values: Vec<String> = f.literal_arrays[index.index()]
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
                Some(abcd_file::FieldValue::JsonFileContent { content, .. }) => {
                    format!("json({:?})", f.strings.resolve(*content).unwrap_or("?"))
                }
                other => format!("{other:?}"),
            };
            out.push((key, value));
        }
    }
    out
}

/// Identity rewrite of module-record-bearing corpus fixtures.
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
    let relatives: Vec<&str> = rows
        .iter()
        .filter(|row| {
            row["case"]
                .as_str()
                .is_some_and(|case| CASES.contains(&case))
        })
        .map(|row| row["abc"].as_str().expect("abc path"))
        .collect();
    let outputs: Vec<Vec<u8>> = relatives
        .par_iter()
        .map(|relative| {
            let file = decode(&std::fs::read(root.join(relative)).expect("fixture"))
                .unwrap_or_else(|error| panic!("decode {relative}: {error}"));
            let expected = module_field_snapshots(&file);
            assert!(
                expected.iter().any(|(_, v)| v.starts_with("module(")),
                "{relative}: fixture must carry module-record data"
            );
            let output = encode(&file).unwrap_or_else(|error| panic!("encode {relative}: {error}"));
            let rewritten = decode(&output)
                .unwrap_or_else(|error| panic!("decode rewritten {relative}: {error}"));
            assert_eq!(
                module_field_snapshots(&rewritten),
                expected,
                "{relative}: module/scope data must survive the identity rewrite"
            );
            output
        })
        .collect();
    let mut checked = 0;
    for (relative, output) in relatives.iter().zip(&outputs) {
        if let Some(directory) = std::env::var_os("ABCD_REWRITTEN_DIR") {
            let target = std::path::PathBuf::from(directory).join(relative);
            std::fs::create_dir_all(target.parent().unwrap()).unwrap();
            std::fs::write(target, output).expect("write oracle candidate");
        }
        checked += 1;
    }
    assert_eq!(checked, 72, "4 module cases x 6 versions x 3 profiles");
}

/// Identity rewrite of fixtures carrying `moduleRequestPhaseIdx` fields (N7).
#[test]
#[ignore = "requires exported GHCR corpus"]
fn rewritten_corpus_module_request_phase_cases() {
    const CASES: &[&str] = &[
        "upstream/version_control/API12beta3/syntax_feature/lazy_import",
        "upstream/version_control/API12beta3/bytecode_feature/lazy_import_bytecode",
        "upstream/version_control/API12beta3/bytecode_feature/wide_lazy_import_bytecode",
    ];
    let root = exported_corpus_root();
    let rows: Vec<serde_json::Value> = std::fs::read_to_string(root.join("index.jsonl"))
        .expect("corpus index")
        .lines()
        .map(|line| serde_json::from_str(line).expect("valid index JSON"))
        .collect();
    let relatives: Vec<&str> = rows
        .iter()
        .filter(|row| {
            row["case"]
                .as_str()
                .is_some_and(|case| CASES.contains(&case))
        })
        .map(|row| row["abc"].as_str().expect("abc path"))
        .collect();
    let outputs: Vec<Vec<u8>> = relatives
        .par_iter()
        .map(|relative| {
            let file = decode(&std::fs::read(root.join(relative)).expect("fixture"))
                .unwrap_or_else(|error| panic!("decode {relative}: {error}"));
            let phase_flags: Vec<Vec<u8>> = file
                .classes
                .values()
                .flat_map(|c| c.fields.iter())
                .filter_map(|f| match &f.initial_value {
                    Some(abcd_file::FieldValue::ModuleRequestPhase(p)) => Some(p.flags.clone()),
                    _ => None,
                })
                .collect();
            assert!(
                !phase_flags.is_empty(),
                "{relative}: fixture must carry module-request-phase data"
            );

            let expected = module_field_snapshots(&file);
            let output = encode(&file).unwrap_or_else(|error| panic!("encode {relative}: {error}"));
            let rewritten = decode(&output)
                .unwrap_or_else(|error| panic!("decode rewritten {relative}: {error}"));
            assert_eq!(
                module_field_snapshots(&rewritten),
                expected,
                "{relative}: module/scope/phase data must survive the identity rewrite"
            );
            let rewritten_flags: Vec<Vec<u8>> = rewritten
                .classes
                .values()
                .flat_map(|c| c.fields.iter())
                .filter_map(|f| match &f.initial_value {
                    Some(abcd_file::FieldValue::ModuleRequestPhase(p)) => Some(p.flags.clone()),
                    _ => None,
                })
                .collect();
            assert_eq!(
                rewritten_flags, phase_flags,
                "{relative}: lazy-import flags must survive the rewrite"
            );
            output
        })
        .collect();
    let mut checked = 0;
    for (relative, output) in relatives.iter().zip(&outputs) {
        if let Some(directory) = std::env::var_os("ABCD_REWRITTEN_DIR") {
            let target = std::path::PathBuf::from(directory).join(relative);
            std::fs::create_dir_all(target.parent().unwrap()).unwrap();
            std::fs::write(target, output).expect("write disasm candidate");
        }
        checked += 1;
    }
    assert_eq!(
        checked, 9,
        "3 lazy-import cases x 3 profiles (12.0.6.0 only)"
    );
}

/// Across all 5,517 exported corpus fixtures, verify that lazy zero-copy
/// decoding (`abcd_file::decode_lazy`, `#49`) produces byte-identical `pandasm`
/// disassembly to eager `abcd_file::decode` and keeps every method body in
/// `MethodCode::Span` form without upfront `Vec<Bytecode>` materialization.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn exported_corpus_decode_lazy_matches_eager_pandasm() {
    let root = exported_corpus_root();
    let rows = manifest_select(&root, SELECT_ABC);
    assert_eq!(rows.len(), 5517, "expected the full 5517-fixture corpus");
    rows.par_iter().for_each(|rel| {
        let path = root.join(rel);
        let data = std::fs::read(&path)
            .unwrap_or_else(|e| panic!("fixture missing at {}: {e}", path.display()));
        let eager =
            decode(&data).unwrap_or_else(|e| panic!("decode failed at {}: {e:?}", path.display()));
        let lazy = abcd_file::decode_lazy(std::sync::Arc::from(data.as_slice()))
            .unwrap_or_else(|e| panic!("decode_lazy failed at {}: {e:?}", path.display()));
        for (_, m) in lazy.all_methods() {
            if let Some(body) = &m.body {
                assert!(
                    matches!(body.code, abcd_file::MethodCode::Span(_)),
                    "{rel}: decode_lazy must retain MethodCode::Span"
                );
            }
        }
        let pa_eager = abcd_file::pandasm::emit_file(&eager, "corpus.abc");
        let pa_lazy = abcd_file::pandasm::emit_file(&lazy, "corpus.abc");
        assert_eq!(pa_eager, pa_lazy, "{rel}: lazy vs eager pandasm mismatch");
    });
}

/// Across all 5,517 exported corpus fixtures, verify that parallel lifting
/// (`LiftOptions { parallel: true }`, `#84`) produces a 100% structurally
/// identical `abcd_ir::Module` to sequential lifting (`parallel: false`).
#[test]
#[ignore = "requires exported GHCR corpus"]
fn exported_corpus_parallel_lift_matches_sequential_structurally() {
    let root = exported_corpus_root();
    let rows = manifest_select(&root, SELECT_ABC);
    assert_eq!(rows.len(), 5517, "expected the full 5517-fixture corpus");
    rows.par_iter().for_each(|rel| {
        let path = root.join(rel);
        let data = std::fs::read(&path)
            .unwrap_or_else(|e| panic!("fixture missing at {}: {e}", path.display()));
        let file = abcd_file::decode_lazy(std::sync::Arc::from(data))
            .unwrap_or_else(|e| panic!("decode_lazy failed at {}: {e:?}", path.display()));
        let seq = abcd_lift::lift_file_with_options(
            &file,
            &abcd_lift::LiftOptions {
                retain_tail_capacity: false,
                parallel: false,
            },
        );
        let par = abcd_lift::lift_file_with_options(
            &file,
            &abcd_lift::LiftOptions {
                retain_tail_capacity: false,
                parallel: true,
            },
        );
        match (seq, par) {
            (Ok(m_seq), Ok(m_par)) => {
                if let Err(diff) = abcd_ir::modules_structurally_eq(&m_seq, &m_par) {
                    panic!("{rel}: parallel vs sequential lift mismatch: {diff}");
                }
            }
            (Err(e_seq), Err(e_par)) => {
                assert_eq!(
                    e_seq.to_string(),
                    e_par.to_string(),
                    "{rel}: parallel vs sequential error mismatch"
                );
            }
            (res_seq, res_par) => {
                panic!(
                    "{rel}: parallel vs sequential outcome mismatch: seq={:?}, par={:?}",
                    res_seq.err(),
                    res_par.err()
                );
            }
        }
    });
}

/// On local `modules.abc` (when present), verify that parallel lifting over a
/// lazy-decoded container is 100% structurally identical to sequential lifting.
#[test]
#[ignore = "requires local-only modules.abc (gitignored)"]
fn modules_abc_parallel_lift_matches_sequential_structurally() {
    let path = corpus_path();
    let Ok(data) = std::fs::read(&path) else {
        eprintln!("modules.abc absent at {} — skipped", path.display());
        return;
    };
    let file = abcd_file::decode_lazy(std::sync::Arc::from(data)).expect("decode_lazy modules.abc");
    let m_seq = abcd_lift::lift_file_with_options(
        &file,
        &abcd_lift::LiftOptions {
            retain_tail_capacity: false,
            parallel: false,
        },
    )
    .expect("sequential lift modules.abc");
    let m_par = abcd_lift::lift_file_with_options(
        &file,
        &abcd_lift::LiftOptions {
            retain_tail_capacity: true,
            parallel: true,
        },
    )
    .expect("parallel lift modules.abc");
    abcd_ir::modules_structurally_eq(&m_seq, &m_par)
        .expect("modules.abc parallel vs sequential Module must be 100% structurally identical");
}
