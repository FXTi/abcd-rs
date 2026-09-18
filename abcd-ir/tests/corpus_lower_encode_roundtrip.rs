//! Opt-in corpus test (requires the exported GHCR corpus): for the
//! `local/arithmetic` fixtures (6 versions × 3 profiles = 18 rows),
//! decode → lift → verify → lower every function → rebuild a File whose
//! method bodies come from `lower::to_method_body` → `abcd_file::encode` →
//! decode the output → assert every function's entity operands resolve to
//! the same targets as the input (resolved names / literal-array contents,
//! not raw indices). This exercises the real relocation channel
//! (`MethodBody.entity_offsets` + `Builder::relocate_code_id`); it is a
//! structural roundtrip, not a VM oracle result.

use std::collections::HashMap;

use abcd_file::File;
use abcd_ir::entity::FuncId;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::{lower_function, to_method_body};
use abcd_ir::verify::verify_module;
use abcd_isa::EntityKind;

/// Multiset of resolved entity references in one method body, keyed by
/// entity kind. Targets are resolved through the owning file: names for
/// string/method operands, decoded literal-array contents for buffer
/// operands — never raw operand indices.
fn resolved_entities(
    file: &File,
    body: &abcd_file::MethodBody,
) -> HashMap<EntityKind, Vec<String>> {
    let mut out: HashMap<EntityKind, Vec<String>> = HashMap::new();
    for bc in &body.bytecodes {
        for (kind, id) in bc.entity_operands() {
            let Some(&offset) = body.entity_offsets.get(&(kind, id.0)) else {
                panic!(
                    "decoded body missing entity_offsets entry for {kind:?} {}",
                    id.0
                );
            };
            let resolved = match kind {
                EntityKind::StringId | EntityKind::MethodId => file
                    .resolve_entity_str(offset)
                    .unwrap_or_else(|| panic!("entity offset {offset:#x} has no name"))
                    .to_string(),
                EntityKind::LiteralarrayId => {
                    let index = file.literal_array_offsets[&offset] as usize;
                    format!("{:?}", file.literal_arrays[index].values)
                }
            };
            out.entry(kind).or_default().push(resolved);
        }
    }
    for refs in out.values_mut() {
        refs.sort();
    }
    out
}

#[test]
#[ignore = "requires exported GHCR corpus"]
fn arithmetic_corpus_lowered_bodies_roundtrip_through_encode() {
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
    let mut failures: Vec<String> = Vec::new();
    let mut header_evidence_printed = false;

    for line in manifest.lines() {
        if !line.contains("\"case\": \"local/arithmetic\"") {
            continue;
        }
        fixtures += 1;
        let marker = "\"abc\": \"";
        let start = line.find(marker).expect("abc path") + marker.len();
        let end = start + line[start..].find('"').expect("abc path terminator");
        let relative = &line[start..end];

        let result =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> Result<usize, String> {
                let file = abcd_file::decode(&std::fs::read(root.join(relative)).expect("fixture"))
                    .map_err(|e| format!("decode: {e}"))?;
                let module = lift_file(&file).map_err(|e| format!("lift: {e}"))?;
                let verify_errors = verify_module(&module);
                if !verify_errors.is_empty() {
                    return Err(format!("verify: {verify_errors:?}"));
                }

                // Lower every function and produce its MethodBody. Function i
                // corresponds to the i-th method in lift order (classes in
                // BTreeMap order, methods in declaration order) — the same
                // iteration lift_file performs.
                let mut bodies = Vec::new();
                for index in 0..module.functions.len() {
                    let func_id = FuncId::from_index(index);
                    let name = module.strings.get(module.func(func_id).name).to_string();
                    let lowered = lower_function(&module, func_id)
                        .map_err(|e| format!("lower {name}: {e}"))?;
                    let body = to_method_body(&module, func_id, &lowered, &file)
                        .map_err(|e| format!("to_method_body {name}: {e}"))?;

                    if !header_evidence_printed {
                        let (in_vregs, in_args) = file
                            .classes
                            .values()
                            .flat_map(|c| &c.methods)
                            .nth(index)
                            .and_then(|m| m.body.as_ref())
                            .map(|b| (b.num_vregs, b.num_args))
                            .unwrap_or((0, 0));
                        eprintln!(
                            "  header {relative} {name}: input num_vregs={in_vregs} \
                         num_args={in_args} arg_types={} -> lowered num_regs={} \
                         (out num_vregs) num_args={}",
                            file.classes
                                .values()
                                .flat_map(|c| &c.methods)
                                .nth(index)
                                .map(|m| m.arg_types.len())
                                .unwrap_or(0),
                            lowered.num_regs,
                            module.func(func_id).param_count,
                        );
                    }
                    bodies.push(body);
                }
                header_evidence_printed = true;

                // Rebuild the file with the lowered bodies spliced in (same
                // method iteration order as above).
                let mut rebuilt = file.clone();
                let mut cursor = bodies.into_iter();
                for class in rebuilt.classes.values_mut() {
                    for method in &mut class.methods {
                        method.body = Some(cursor.next().expect("one body per method"));
                    }
                }
                assert!(cursor.next().is_none());

                let encoded = abcd_file::encode(&rebuilt).map_err(|e| format!("encode: {e}"))?;
                let output = abcd_file::decode(&encoded).map_err(|e| format!("re-decode: {e}"))?;

                // Compare resolved entity references per method.
                let mut compared = 0usize;
                for (desc, class) in &file.classes {
                    let out_class = output.class(*desc).expect("class survives encode");
                    for method in &class.methods {
                        let name = file.strings.resolve(method.name).expect("method name");
                        let out_method = out_class
                            .method_by_name(method.name)
                            .unwrap_or_else(|| panic!("method {name} survives encode"));
                        let input_refs =
                            resolved_entities(&file, method.body.as_ref().expect("input body"));
                        let output_refs = resolved_entities(
                            &output,
                            out_method.body.as_ref().expect("output body"),
                        );
                        assert_eq!(
                            input_refs, output_refs,
                            "{relative} method {name}: resolved entity references differ"
                        );
                        compared += input_refs.values().map(Vec::len).sum::<usize>();
                    }
                }
                Ok(compared)
            }));

        match result {
            Ok(Ok(refs)) => eprintln!("PASS {relative} ({refs} entity references compared)"),
            Ok(Err(reason)) => {
                eprintln!("FAIL {relative}: {reason}");
                failures.push(format!("{relative}: {reason}"));
            }
            Err(payload) => {
                let reason = payload
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_else(|| "unknown panic".to_string());
                eprintln!("FAIL {relative}: panic: {reason}");
                failures.push(format!("{relative}: panic: {reason}"));
            }
        }
    }

    assert_eq!(fixtures, 18, "expected 18 local/arithmetic fixtures");
    eprintln!(
        "corpus lower→encode roundtrip: {}/{} fixtures passed",
        fixtures - failures.len(),
        fixtures
    );
    assert!(
        failures.is_empty(),
        "{} fixture(s) failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
