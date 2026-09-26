//! v2-P1a — nested literal arrays referenced from literal-array payloads.
//!
//! A `LITERALARRAY` slot inside a decoded literal array holds the target
//! array's FILE OFFSET. Sendable-class buffers reference arrays that are
//! registered nowhere: not in the header literal-array table and not in any
//! method index region (e.g. 13.0.1.0/24.0.0.0 sendable-class-export-1
//! baseline: a class-buffer slot references 0x523c, where a real tagged
//! `{ 1 [ i32:0, ] }` array lives). Before the fix, decode left such slots
//! as raw offsets and never surfaced the target arrays, so encode hard-errored
//! (`nested literal array index 0x523c out of bounds`) and the v0.2 lift
//! converter could not resolve the content on 57 sendable fixtures.
//!
//! Decode now recovers nested arrays transitively (cycle-safe, module/phase
//! blob exclusions honored, deterministic table order); these tests pin the
//! recovery and the identity-rewrite contract on the corpus fixtures.

use abcd_file::{Builder, LiteralValue, decode, encode};
use std::collections::{BTreeSet, HashSet};
use std::process::Command;

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

/// Parse the corpus manifest with Python's standard JSON parser — the
/// `real_module_abc.rs` pattern. Prints one `abc<TAB>case` record per row.
fn manifest_rows(root: &std::path::Path) -> Vec<(String, String)> {
    let program = r#"
import json, sys
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        assert "\n" not in row["abc"] and "\t" not in row["abc"]
        assert "\n" not in row["case"] and "\t" not in row["case"]
        print(row["abc"] + "\t" + row["case"])
"#;
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
        .map(|line| {
            let (abc, case) = line.split_once('\t').expect("manifest record");
            (abc.to_owned(), case.to_owned())
        })
        .collect()
}

/// Table indices registered in `File::literal_array_offsets`.
fn registered_indices(file: &abcd_file::File) -> HashSet<u32> {
    file.literal_array_offsets.values().copied().collect()
}

/// Every `LiteralValue::LiteralArray` slot in the decoded table must resolve
/// to a registered table index. A slot left holding a raw file offset (the
/// pre-fix representation for unregistered targets) is an offender.
fn unresolved_nested_refs(file: &abcd_file::File) -> Vec<u32> {
    let registered = registered_indices(file);
    let mut unresolved = Vec::new();
    for array in &file.literal_arrays {
        for value in &array.values {
            if let LiteralValue::LiteralArray(idx) = value
                && !registered.contains(&idx.0)
            {
                unresolved.push(idx.0);
            }
        }
    }
    unresolved
}

/// Full-corpus guard: no fixture may carry an unresolvable nested
/// literal-array reference. Pre-fix this failed on exactly the 57 sendable
/// fixtures (run log: the offender list is the v2-P1 finding set); because
/// the recovery only fires on such slots, an empty offender list here also
/// proves no other fixture's decoded output changed.
#[test]
#[ignore = "requires exported GHCR corpus + python3"]
fn corpus_nested_literal_refs_resolve() {
    let root = exported_corpus_root();
    let rows = manifest_rows(&root);
    assert_eq!(rows.len(), 5517, "corpus manifest row count");
    let mut offenders = Vec::new();
    for (rel, _case) in &rows {
        let data = std::fs::read(root.join(rel))
            .unwrap_or_else(|e| panic!("fixture missing at {rel}: {e}"));
        let file = decode(&data).unwrap_or_else(|e| panic!("decode {rel}: {e:?}"));
        let bad = unresolved_nested_refs(&file);
        if !bad.is_empty() {
            offenders.push(format!(
                "{rel}: {} unresolved (e.g. {:#x})",
                bad.len(),
                bad[0]
            ));
        }
        // Optional per-fixture literal-content dump for pre/post decode
        // diffs (ABCD_LA_DUMP_DIR=<dir>): the recovery must not alter any
        // fixture beyond the offenders.
        if let Some(directory) = std::env::var_os("ABCD_LA_DUMP_DIR") {
            let target = std::path::PathBuf::from(directory).join(rel);
            std::fs::create_dir_all(target.parent().unwrap()).unwrap();
            let dump = literal_snapshot(&file, &data)
                .into_iter()
                .collect::<Vec<_>>()
                .join("\n");
            std::fs::write(target, dump).expect("write literal dump");
        }
    }
    assert!(
        offenders.is_empty(),
        "fixtures with unresolved nested literal-array refs:\n{}",
        offenders.join("\n")
    );
}

/// Flagship content assertion: the sendable-class-export-1 buffers reference
/// a `{ 1 [ i32:0, ] }` array through a nested LITERALARRAY slot. The target
/// must be decoded (pre-fix: absent) and reachable through the table index
/// left in the slot.
#[test]
#[ignore = "requires exported GHCR corpus + python3"]
fn sendable_export_1_nested_i32_array_is_decoded() {
    let root = exported_corpus_root();
    let rows = manifest_rows(&root);
    let mut checked = 0usize;
    for (rel, case) in &rows {
        if case != "upstream/bytecode/ts/api18/sendable-class-export-1" {
            continue;
        }
        let data = std::fs::read(root.join(rel)).expect("fixture");
        let file = decode(&data).unwrap_or_else(|e| panic!("decode {rel}: {e:?}"));
        // No unresolved slots at all (subsumed by the full-corpus guard,
        // asserted here for a fixture-local red message).
        assert!(
            unresolved_nested_refs(&file).is_empty(),
            "{rel}: nested literal-array refs must resolve"
        );
        // The nested shape (an outer buffer slot referencing the `[i32:0]`
        // array) exists only on 13.x/24.x files; <=12.x registers the
        // `{ 1 [ i32:0, ] }` array in the header table directly.
        let version = rel.split('/').next().expect("version path");
        if !matches!(version, "13.0.1.0" | "24.0.0.0") {
            checked += 1;
            continue;
        }
        // Some outer array must reference a decoded `[i32:0]` array
        // (`{ 1 [ i32:0, ] }` in pandasm) through a resolved slot.
        let found = file.literal_arrays.iter().any(|array| {
            array.values.iter().any(|value| {
                matches!(
                    value,
                    LiteralValue::LiteralArray(idx)
                        if file
                            .literal_arrays
                            .get(idx.0 as usize)
                            .is_some_and(|target| target.values
                                == vec![LiteralValue::Integer(0)])
                )
            })
        });
        assert!(
            found,
            "{rel}: the nested `[i32:0]` array referenced from a class buffer \
             must be decoded and reachable through the table"
        );
        checked += 1;
    }
    assert_eq!(
        checked, 18,
        "sendable-class-export-1: 6 versions x 3 profiles"
    );
}

/// Render one literal array offset-independently: strings/methods by name,
/// nested references structurally (cycle-guarded), typed-array payloads by
/// content read from the owning file's bytes at the raw payload offset (the
/// N52 representation — ARRAY_* slots keep raw payload offsets).
fn render_array(
    file: &abcd_file::File,
    bytes: &[u8],
    index: u32,
    visiting: &mut HashSet<u32>,
) -> String {
    if !visiting.insert(index) {
        return "cycle".to_owned();
    }
    let Some(array) = file.literal_arrays.get(index as usize) else {
        return format!("oob:{index}");
    };
    let rendered: Vec<String> = array
        .values
        .iter()
        .map(|v| render_value(file, bytes, v, visiting))
        .collect();
    visiting.remove(&index);
    format!("[{}]", rendered.join(","))
}

fn render_value(
    file: &abcd_file::File,
    bytes: &[u8],
    value: &LiteralValue,
    visiting: &mut HashSet<u32>,
) -> String {
    use abcd_file::LiteralValue::*;
    match value {
        String(sid) | EtsImplements(sid) => {
            format!("s:{}", file.strings.resolve(*sid).unwrap_or("?"))
        }
        Method(off)
        | GeneratorMethod(off)
        | AsyncGeneratorMethod(off)
        | Getter(off)
        | Setter(off) => format!("m:{}", file.resolve_entity_str(*off).unwrap_or("?")),
        LiteralArray(idx) => render_array(file, bytes, idx.0, visiting),
        ArrayU1(idx) | ArrayU8(idx) | ArrayI8(idx) | ArrayU16(idx) | ArrayI16(idx)
        | ArrayU32(idx) | ArrayI32(idx) | ArrayU64(idx) | ArrayI64(idx) | ArrayF32(idx)
        | ArrayF64(idx) | ArrayString(idx) => {
            // Typed-array payload at the raw source offset: u32 element
            // count followed by the elements (vendor
            // literal_data_accessor-inl.h:94-115; N52 keeps this raw).
            let off = idx.0 as usize;
            let Some(raw) = bytes.get(off..off + 4) else {
                return format!("typed:{value:?}@oob");
            };
            let count = u32::from_le_bytes(raw.try_into().unwrap());
            format!("typed:{}:n{count}", tag_name(value))
        }
        other => format!("{other:?}"),
    }
}

fn tag_name(value: &LiteralValue) -> &'static str {
    use abcd_file::LiteralValue::*;
    match value {
        ArrayU1(_) => "u1",
        ArrayU8(_) => "u8",
        ArrayI8(_) => "i8",
        ArrayU16(_) => "u16",
        ArrayI16(_) => "i16",
        ArrayU32(_) => "u32",
        ArrayI32(_) => "i32",
        ArrayU64(_) => "u64",
        ArrayI64(_) => "i64",
        ArrayF32(_) => "f32",
        ArrayF64(_) => "f64",
        ArrayString(_) => "string",
        _ => unreachable!(),
    }
}

/// All literal arrays of a file as a sorted set of structural renderings
/// (immune to table-order permutations across a rewrite).
fn literal_snapshot(file: &abcd_file::File, bytes: &[u8]) -> BTreeSet<String> {
    (0..file.literal_arrays.len() as u32)
        .map(|i| render_array(file, bytes, i, &mut HashSet::new()))
        .collect()
}

/// Identity rewrite of every sendable-case fixture: decode -> encode ->
/// decode must succeed and preserve the literal-array content. Pre-fix,
/// encode hard-errored on the 57 fixtures whose class buffers reference
/// unregistered nested arrays (`nested literal array index 0x.... out of
/// bounds`).
#[test]
#[ignore = "requires exported GHCR corpus + python3"]
fn rewritten_sendable_fixtures_preserve_literal_content() {
    let root = exported_corpus_root();
    let rows = manifest_rows(&root);
    let mut checked = 0usize;
    for (rel, case) in &rows {
        if !case.contains("sendable") {
            continue;
        }
        let data = std::fs::read(root.join(rel)).expect("fixture");
        let file = decode(&data).unwrap_or_else(|e| panic!("decode {rel}: {e:?}"));
        let expected = literal_snapshot(&file, &data);
        let output = encode(&file).unwrap_or_else(|e| panic!("encode {rel}: {e:?}"));
        let rewritten = decode(&output).unwrap_or_else(|e| panic!("decode rewritten {rel}: {e:?}"));
        assert_eq!(
            literal_snapshot(&rewritten, &output),
            expected,
            "{rel}: literal content must survive the identity rewrite"
        );
        if let Some(directory) = std::env::var_os("ABCD_REWRITTEN_DIR") {
            let target = std::path::PathBuf::from(directory).join(rel);
            std::fs::create_dir_all(target.parent().unwrap()).unwrap();
            std::fs::write(target, output).expect("write ark_disasm candidate");
        }
        checked += 1;
    }
    assert!(checked > 0, "no sendable fixtures selected");
}

/// Unit-level red: a nested array absent from the header literal-array index
/// region must still be decoded. Builds outer -> inner through the public
/// Builder, then patches the index region to drop the inner entry (replacing
/// it with a duplicate of the outer entry), leaving the inner reachable only
/// through the outer array's LITERALARRAY slot.
#[test]
fn nested_array_missing_from_index_region_is_recovered() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, abcd_file::SourceLang::EcmaScript);
    let proto = b.create_proto(abcd_file::Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        abcd_file::AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, abcd_file::SourceLang::EcmaScript);

    let inner = b.add_literal_array("inner");
    b.literal_array_add_integer(inner, 5);
    let outer = b.add_literal_array("outer");
    b.literal_array_add_literalarray(outer, inner);

    let mut data = b.finalize().expect("finalize");

    // Locate the two arrays in the header index region (vendored Header:
    // num_literalarrays @0x2c, literalarray_idx_off @0x30).
    let num = u32::from_le_bytes(data[0x2c..0x30].try_into().unwrap()) as usize;
    let idx_off = u32::from_le_bytes(data[0x30..0x34].try_into().unwrap()) as usize;
    assert_eq!(num, 2, "builder must emit exactly two literal arrays");
    let entries: Vec<u32> = (0..num)
        .map(|i| {
            u32::from_le_bytes(
                data[idx_off + 4 * i..idx_off + 4 * i + 4]
                    .try_into()
                    .unwrap(),
            )
        })
        .collect();

    // Identify the inner array by decoding the unpatched file.
    let file = decode(&data).expect("decode unpatched");
    let inner_offset = *file
        .literal_array_offsets
        .iter()
        .find(|&(_, &i)| file.literal_arrays[i as usize].values == vec![LiteralValue::Integer(5)])
        .map(|(o, _)| o)
        .expect("inner array decoded");
    let outer_offset = *entries
        .iter()
        .find(|o| **o != inner_offset)
        .expect("outer array offset");

    // Drop the inner entry from the index region: overwrite it with the
    // outer offset (keeping the entry count, so no layout fixups).
    for i in 0..num {
        let at = idx_off + 4 * i;
        let entry = u32::from_le_bytes(data[at..at + 4].try_into().unwrap());
        if entry == inner_offset {
            data[at..at + 4].copy_from_slice(&outer_offset.to_le_bytes());
        }
    }

    let file = decode(&data).expect("decode patched");
    // The inner array must be recovered through the outer array's slot…
    let outer = file
        .literal_arrays
        .iter()
        .find(|la| {
            la.values
                .iter()
                .any(|v| matches!(v, LiteralValue::LiteralArray(_)))
        })
        .expect("outer array with a nested reference");
    match &outer.values[0] {
        LiteralValue::LiteralArray(idx) => {
            let registered = registered_indices(&file);
            assert!(
                registered.contains(&idx.0),
                "the nested reference must resolve to a table index, \
                 not stay a raw offset ({idx:#x?})"
            );
            assert_eq!(
                file.literal_arrays[idx.0 as usize].values,
                vec![LiteralValue::Integer(5)],
                "the recovered nested array must carry its content"
            );
        }
        other => panic!("expected nested LiteralArray, got {other:?}"),
    }
    // …and `literal_array_offsets` must expose the dropped source offset.
    assert!(
        file.literal_array_offsets.contains_key(&inner_offset),
        "the recovered array's source offset must map to its table index"
    );
}
