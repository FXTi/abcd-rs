//! Focused regression for indexed entity resolution; requires the exported
//! black-box ArkCompiler corpus. This does not claim full IR equivalence.
use abcd_file::decode;
use abcd_ir::{Module, inst::InstData, lift::lift_file};
use abcd_isa::{Bytecode, EntityKind};
use std::{collections::HashSet, path::PathBuf, process::Command};

fn contains_named_instruction(module: &Module, expected: &str, define: bool) -> bool {
    module.insts.iter().any(|inst| {
        let name = match inst.data {
            InstData::DefineFunc { method_id, .. } if define => method_id,
            InstData::TryLoadGlobalByName { name } if !define => name,
            _ => return false,
        };
        module.strings.get(name) == expected
    })
}

#[test]
#[ignore = "requires exported GHCR corpus (ABCD_CORPUS_ROOT)"]
fn arithmetic_entities_match_upstream_in_all_manifest_profiles() {
    let root = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../exports/corpus"));
    // Corpus tooling already uses Python. Parse JSON with its standard
    // library instead of assuming a particular JSON whitespace/key order.
    let output = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, sys
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        if row["case"] == "local/arithmetic":
            assert all("\n" not in row[key] and "\t" not in row[key] for key in ("abc", "pandasm"))
            print(row["abc"] + "\t" + row["pandasm"])
"#,
        )
        .arg(root.join("index.jsonl"))
        .output()
        .expect("python3 is required by corpus tooling");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let paths = String::from_utf8(output.stdout).expect("UTF-8 fixture paths");
    let mut checked = HashSet::new();
    for line in paths.lines() {
        let (relative, pandasm) = line.split_once('\t').expect("manifest paths");
        let reference = std::fs::read_to_string(root.join(pandasm)).expect("upstream pandasm");
        // This regression uses the simple arithmetic case, whose sole
        // definefunc names the add function. Preserve the compiler's name,
        // including any mangling, without reproducing version rules here.
        let define_line = reference
            .lines()
            .find(|line| line.trim_start().starts_with("definefunc "))
            .expect("upstream definefunc");
        let expected_method = define_line
            .split_once(',')
            .expect("IC operand")
            .1
            .trim()
            .split_once(':')
            .expect("method signature")
            .0;
        assert!(
            checked.insert(relative.to_owned()),
            "duplicate fixture: {relative}"
        );
        let data = std::fs::read(root.join(relative)).expect("fixture");
        let file = decode(&data).unwrap_or_else(|e| panic!("{relative}: {e}"));
        let mut saw_function = false;
        for (_, method) in file.all_methods() {
            let Some(body) = &method.body else { continue };
            for instruction in &body.bytecodes {
                if let Bytecode::Definefunc(_, id, _) = instruction {
                    let offset = body.entity_offsets[&(EntityKind::MethodId, id.0)];
                    assert_eq!(
                        file.resolve_entity_str(offset),
                        Some(expected_method),
                        "{relative}"
                    );
                    // The definition already belongs to a class; no global
                    // method enumeration or synthetic index/offset alias is needed.
                    assert!(file.all_methods().any(|(_, m)| m.offset == offset));
                    saw_function = true;
                }
                for (kind, id) in instruction.entity_operands() {
                    if kind == EntityKind::StringId {
                        let offset = body.entity_offsets[&(kind, id.0)];
                        assert!(
                            matches!(file.resolve_entity_str(offset), Some("add" | "print")),
                            "{relative}"
                        );
                    }
                }
            }
        }
        assert!(saw_function, "{relative}");
        let module = lift_file(&file).unwrap_or_else(|e| panic!("{relative}: {e}"));
        assert!(
            contains_named_instruction(&module, expected_method, true),
            "{relative}"
        );
        assert!(
            contains_named_instruction(&module, "print", false),
            "{relative}"
        );
    }
    // Fixed black-box matrix: six versions and three compile profiles.
    assert_eq!(checked.len(), 18);
}
