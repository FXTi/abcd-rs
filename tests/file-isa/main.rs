//! Group J — full-opcode decode coverage against a real production file.
//!
//! Uses a device stock `modules.abc` (21.6 MB, 12.0.6.0, 2035 classes).
//! That file is local-only and gitignored (Huawei distribution
//! restrictions), so this test is `#[ignore]`d in CI and run explicitly
//! whenever the corpus is present:
//!
//! ```text
//! cargo test -p abcd-rs --test file-isa -- --ignored
//! ```
//!
//! Migrated from `abcd-file/tests/real_module_abc.rs` to the root
//! package's cross-crate integration layout (file → isa data flow); the
//! root package's manifest dir IS the repo root, so the corpus paths
//! resolve without the crate-local `..`.

use abcd_file::{decode, encode};
use abcd_isa::{
    decode as decode_isa, encode as encode_isa, BytecodeFlags, EntityKind, Operand, Version,
};
use std::process::Command;

fn exported_corpus_root() -> std::path::PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus"))
}

fn corpus_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("modules.abc")
}

/// Parse the corpus manifest with Python's standard JSON parser — the
/// `abcd-ir/tests/corpus_entities.rs` pattern. Corpus tooling already
/// requires python3; this makes no JSON whitespace/key-order assumptions.
/// `select` is Python source executed per manifest row (as `row`) inside
/// the read loop; it prints one tab-separated record per selected row.
fn manifest_select(root: &std::path::Path, select: &str) -> Vec<String> {
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
const SELECT_ABC_PANDASM: &str = r#"        assert all("\n" not in row[key] and "\t" not in row[key] for key in ("abc", "pandasm"))
        print(row["abc"] + "\t" + row["pandasm"])"#;

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
    let rows = manifest_select(&root, SELECT_ABC);
    let mut count = 0usize;
    for rel in &rows {
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
            .unwrap_or_else(|| panic!("invalid version path in manifest row: {rel}"));
        assert_eq!(
            file.version,
            version,
            "version mismatch at {}",
            path.display()
        );
        count += 1;
    }
    // Floor recorded at the 2757-fixture export; new fixtures only grow it.
    assert!(count >= 2757, "unexpected exported corpus size: {count}");
}

/// Exercise the ISA encode/decode layer for every decoded method body.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn exported_corpus_method_bytecodes_roundtrip_through_isa() {
    let root = exported_corpus_root();
    let rows = manifest_select(&root, SELECT_ABC);
    let mut methods = 0usize;
    for rel in &rows {
        let data = std::fs::read(root.join(rel)).expect("fixture");
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

// ============================================================================
// Per-instruction comparison against upstream ark_disasm (reference.pa)
// ============================================================================
//
// `reference.pa` is upstream's OWN disassembly of the fixture .abc. Decoding
// each fixture through abcd-file and comparing every method's instruction
// stream against reference.pa PER INSTRUCTION (mnemonic + operands) is the
// real read-path verification: 9.0.0.0 + 11.0.2.0 fixtures decode through
// the v24 superset table, so an exact match proves the superset decode is
// correct for those versions (not just "produces some instruction count").
//
// Canonical operand mapping — both sides render to identical tokens:
//
//   pandasm text            | decoded `Operand`               | token
//   ------------------------+-------------------------------+----------------
//   `v3`                    | `Reg(3)`, 3 < num_vregs         | `v3`
//   `a0`                    | `Reg(r)`, r >= num_vregs        | `a{r-num_vregs}`
//   `0x2a`                  | `Imm(i)` (integer)              | `0x2a`
//   `1.000000e-01` (fldai)  | `Imm(bits)` under FLOAT flag    | `f64:0x{bits}`
//   `"name"`                | `Entity(StringId)`              | `s:{mutf8 hex}`
//   `name:(sig)`            | `Entity(MethodId)`              | `m:{mutf8 hex}`
//   `jump_label_3`          | `Label(idx)`                    | `@{idx}`
//   `{ N [ i32:1, … ]}`     | `Entity(LiteralarrayId)`        | `la:{…}`
//
// Strings and method names compare as raw stored bytes: pandasm prints
// string items unescaped (reference.pa is not even UTF-8 for the
// local/strings fixtures), so our side re-encodes the decoded string to
// MUTF-8 and both sides compare as hex. Literal-array items use the same
// token forms (`s:`/`m:`/`f64:` plus `i32:{n}`/`u1:{n}`/`null_value:{n}`/
// `method_affiliate:{n}`/`lit:0x{offset}`); the corpus exercises exactly
// these seven tags (grep-verified), other `LiteralValue` variants render
// best-effort as `raw:{debug}` and would surface as mismatches.

/// One parsed pandasm instruction line.
struct PaInsn {
    mnemonic: String,
    /// Raw operand tokens, split at top-level commas.
    operands: Vec<Vec<u8>>,
    /// Lossy source line, for mismatch reports.
    line: String,
}

/// One pandasm `.function` block.
struct PaFunction {
    /// Raw method-name bytes (compared against MUTF-8 re-encoded names).
    name: Vec<u8>,
    instrs: Vec<PaInsn>,
    /// Label name → index of the instruction it binds to.
    labels: std::collections::HashMap<Vec<u8>, usize>,
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Re-encode a decoded string to the MUTF-8 bytes the file stores
/// (embedded NUL as C0 80, astral chars as surrogate pairs), matching
/// pandasm's raw print byte-exactly.
fn mutf8_bytes(s: &str) -> Vec<u8> {
    let mut out = Vec::new();
    for c in s.chars() {
        let c = c as u32;
        if c == 0 {
            out.extend_from_slice(&[0xC0, 0x80]);
        } else if c >= 0x10000 {
            let c = c - 0x10000;
            for unit in [0xD800 + (c >> 10), 0xDC00 + (c & 0x3FF)] {
                out.extend_from_slice(&[
                    0xE0 | (unit >> 12) as u8,
                    0x80 | ((unit >> 6) & 0x3F) as u8,
                    0x80 | (unit & 0x3F) as u8,
                ]);
            }
        } else {
            let mut buf = [0u8; 4];
            out.extend_from_slice(char::from_u32(c).unwrap().encode_utf8(&mut buf).as_bytes());
        }
    }
    out
}

/// Split a pandasm operand list at top-level commas, respecting quoted
/// strings (pandasm does not escape string contents) and `()`/`{}`/`[]`
/// groups (method signatures, literal arrays).
fn split_operands(rest: &[u8]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut cur = Vec::new();
    let mut in_string = false;
    let mut depth = 0i32;
    for &b in rest {
        match b {
            b'"' => {
                in_string = !in_string;
                cur.push(b);
            }
            b'{' | b'[' | b'(' if !in_string => {
                depth += 1;
                cur.push(b);
            }
            b'}' | b']' | b')' if !in_string => {
                depth -= 1;
                cur.push(b);
            }
            b',' if !in_string && depth == 0 => {
                let token = trim_bytes(&cur);
                if !token.is_empty() {
                    out.push(token.to_vec());
                }
                cur.clear();
            }
            _ => cur.push(b),
        }
    }
    let token = trim_bytes(&cur);
    if !token.is_empty() {
        out.push(token.to_vec());
    }
    out
}

fn trim_bytes(mut b: &[u8]) -> &[u8] {
    while let [first, rest @ ..] = b {
        if first.is_ascii_whitespace() {
            b = rest;
        } else {
            break;
        }
    }
    while let [rest @ .., last] = b {
        if last.is_ascii_whitespace() {
            b = rest;
        } else {
            break;
        }
    }
    b
}

/// Whether every quoted string in a partial pandasm line is closed
/// (pandasm prints string contents raw, so a string containing a newline
/// — e.g. template literals — spans multiple physical lines).
fn strings_closed(bytes: &[u8]) -> bool {
    bytes.iter().filter(|&&b| b == b'"').count() % 2 == 0
}

/// Parse ark_disasm output into per-function instruction streams.
/// The parse is byte-level: reference.pa is raw (not UTF-8-safe) text.
fn parse_pandasm(bytes: &[u8]) -> Vec<PaFunction> {
    let mut functions = Vec::new();
    let mut current: Option<PaFunction> = None;
    // Accumulates an instruction whose string operand spans lines.
    let mut continuation: Option<Vec<u8>> = None;
    for raw in bytes.split(|&b| b == b'\n') {
        let line = raw.strip_suffix(b"\r").unwrap_or(raw);
        let Some(fun) = current.as_mut() else {
            if line.starts_with(b".function ") && line.ends_with(b"{") {
                let head = &line[b".function ".len()..line.len() - 1];
                let paren = head
                    .iter()
                    .position(|&b| b == b'(')
                    .expect("pandasm function argument list");
                let before = trim_bytes(&head[..paren]);
                // Strip the return-type token; the remainder is the name
                // (mangled names may contain spaces, e.g. accessors).
                let name = before
                    .split(|&b| b == b' ')
                    .skip(1)
                    .collect::<Vec<_>>()
                    .join(&b' ');
                current = Some(PaFunction {
                    name,
                    instrs: Vec::new(),
                    labels: std::collections::HashMap::new(),
                });
            }
            continue;
        };
        if line == b"}" {
            assert!(
                continuation.is_none(),
                "unterminated string at function end"
            );
            functions.push(current.take().unwrap());
            continue;
        }
        if let Some(mut acc) = continuation.take() {
            acc.push(b'\n');
            acc.extend_from_slice(line);
            if strings_closed(&acc) {
                push_pa_insn(fun, &acc);
            } else {
                continuation = Some(acc);
            }
            continue;
        }
        if line.is_empty() || line[0] == b'.' {
            continue; // blank lines and directives (.catchall, …)
        }
        if line[0] != b'\t' && line[0] != b' ' {
            // Label definition: binds to the next instruction's index.
            assert!(
                line.ends_with(b":"),
                "unexpected pandasm line: {}",
                String::from_utf8_lossy(line)
            );
            fun.labels
                .insert(line[..line.len() - 1].to_vec(), fun.instrs.len());
            continue;
        }
        let text = trim_bytes(line);
        if strings_closed(text) {
            push_pa_insn(fun, text);
        } else {
            continuation = Some(text.to_vec());
        }
    }
    assert!(current.is_none(), "unterminated pandasm .function block");
    functions
}

fn push_pa_insn(fun: &mut PaFunction, text: &[u8]) {
    let split = text
        .iter()
        .position(|b| b.is_ascii_whitespace())
        .unwrap_or(text.len());
    let mnemonic = String::from_utf8_lossy(&text[..split]).into_owned();
    let operands = split_operands(&text[split..]);
    fun.instrs.push(PaInsn {
        mnemonic,
        operands,
        line: String::from_utf8_lossy(text).into_owned(),
    });
}

/// Canonical token for one pandasm operand.
fn pa_operand_token(fun: &PaFunction, token: &[u8]) -> String {
    if token.len() >= 2 && token[0] == b'"' && token[token.len() - 1] == b'"' {
        return format!("s:{}", hex(&token[1..token.len() - 1]));
    }
    if token[0] == b'{' {
        return pa_literal_token(token);
    }
    if let Some(&index) = fun.labels.get(token) {
        return format!("@{index}");
    }
    if token.is_ascii() {
        let text = std::str::from_utf8(token).unwrap();
        if let Some(rest) = text.strip_prefix('v') {
            if !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()) {
                return format!("v{rest}");
            }
        }
        if let Some(rest) = text.strip_prefix('a') {
            if !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()) {
                return format!("a{rest}");
            }
        }
        if let Some((name, _sig)) = text.split_once(":(") {
            return format!("m:{}", hex(name.as_bytes()));
        }
        if let Some(digits) = text.strip_prefix("0x") {
            let value = u64::from_str_radix(digits, 16).expect("pandasm hex immediate");
            return format!("0x{value:x}");
        }
        if text.contains('.') || text.contains('e') || text.contains("inf") || text.contains("nan")
        {
            let value: f64 = text.parse().expect("pandasm float immediate");
            return format!("f64:0x{:016x}", value.to_bits());
        }
        if let Ok(value) = text.parse::<i64>() {
            return format!("0x{value:x}");
        }
    }
    // Unknown rendering: kept byte-exact so it surfaces as a mismatch.
    format!("raw:{}", hex(token))
}

/// Canonical token for one pandasm literal-array operand (`{ N [ … ]}`).
fn pa_literal_token(token: &[u8]) -> String {
    let open = token
        .iter()
        .position(|&b| b == b'[')
        .expect("literal items");
    let close = token
        .iter()
        .rposition(|&b| b == b']')
        .expect("literal items");
    let items = split_operands(&token[open + 1..close]);
    let rendered: Vec<String> = items.iter().map(|item| pa_literal_item(item)).collect();
    format!("la:{}", rendered.join(","))
}

fn pa_literal_item(item: &[u8]) -> String {
    let colon = item
        .iter()
        .position(|&b| b == b':')
        .expect("tagged literal");
    let tag = &item[..colon];
    let value = &item[colon + 1..];
    match tag {
        b"string" => {
            assert!(value.len() >= 2 && value[0] == b'"' && value[value.len() - 1] == b'"');
            format!("s:{}", hex(&value[1..value.len() - 1]))
        }
        b"method" => format!("m:{}", hex(value)),
        b"f64" | b"f32" => {
            let value: f64 = std::str::from_utf8(value)
                .unwrap()
                .parse()
                .expect("pandasm float literal");
            format!("f64:0x{:016x}", value.to_bits())
        }
        b"lit_offset" => {
            let text = std::str::from_utf8(value).unwrap();
            let offset = u32::from_str_radix(text.strip_prefix("0x").unwrap_or(text), 16)
                .expect("pandasm lit_offset");
            format!("lit:0x{offset:x}")
        }
        _ => {
            // Integer-valued tags: i32/u1/null_value/method_affiliate/…
            let number: i64 = std::str::from_utf8(value)
                .unwrap()
                .parse()
                .expect("pandasm integer literal");
            format!("{}:{number}", String::from_utf8_lossy(tag))
        }
    }
}

/// Canonical `(mnemonic, operand tokens)` for one decoded instruction.
fn our_canonical(
    file: &abcd_file::File,
    body: &abcd_file::MethodBody,
    bc: &abcd_isa::Bytecode,
) -> (String, Vec<String>) {
    let tokens = bc
        .operands()
        .iter()
        .map(|op| match *op {
            Operand::Reg(r) => {
                if r as u32 >= body.num_vregs {
                    format!("a{}", r as u32 - body.num_vregs)
                } else {
                    format!("v{r}")
                }
            }
            Operand::Imm(i) => {
                if bc.has_flag(BytecodeFlags::FLOAT) {
                    // fldai: the immediate carries the f64 value bits.
                    format!("f64:0x{:016x}", i as u64)
                } else {
                    format!("0x{i:x}")
                }
            }
            Operand::Label(l) => format!("@{l}"),
            Operand::Entity(EntityKind::LiteralarrayId, id) => our_literal_token(file, body, id),
            Operand::Entity(kind @ (EntityKind::StringId | EntityKind::MethodId), id) => {
                let offset = body.entity_offsets[&(kind, id)];
                let resolved = file
                    .resolve_entity_str(offset)
                    .expect("entity offset resolves to a string");
                let prefix = if kind == EntityKind::StringId {
                    "s"
                } else {
                    "m"
                };
                format!("{prefix}:{}", hex(&mutf8_bytes(resolved)))
            }
        })
        .collect();
    (bc.mnemonic().to_owned(), tokens)
}

/// Canonical token for one decoded literal-array operand.
fn our_literal_token(file: &abcd_file::File, body: &abcd_file::MethodBody, id: u32) -> String {
    let offset = body.entity_offsets[&(EntityKind::LiteralarrayId, id)];
    let index = file.literal_array_offsets[&offset] as usize;
    let rendered: Vec<String> = file.literal_arrays[index]
        .values
        .iter()
        .map(|v| our_literal_item(file, v))
        .collect();
    format!("la:{}", rendered.join(","))
}

fn our_literal_item(file: &abcd_file::File, value: &abcd_file::LiteralValue) -> String {
    use abcd_file::LiteralValue::*;
    match value {
        Bool(b) => format!("u1:{}", *b as i32),
        Integer8(v) => format!("i8:{}", *v as i8),
        Integer(v) => format!("i32:{}", *v as i32),
        Float(v) => format!("f32:0x{:08x}", v.to_bits()), // best-effort; not in corpus
        Double(v) => format!("f64:0x{:016x}", v.to_bits()),
        String(sid) => format!(
            "s:{}",
            hex(&mutf8_bytes(
                file.strings.resolve(*sid).expect("literal string")
            ))
        ),
        Method(offset) => format!(
            "m:{}",
            hex(&mutf8_bytes(
                file.resolve_entity_str(*offset).expect("literal method")
            ))
        ),
        NullValue(v) => format!("null_value:{v}"),
        MethodAffiliate(v) => format!("method_affiliate:{v}"),
        LiteralArray(idx) => {
            // pandasm prints the nested array's source-file offset. Decode
            // rewrites the reference to a table index only when the target
            // is a decoded top-level array; otherwise `idx.0` IS the raw
            // offset pandasm prints (abcd-file/src/decode.rs:1474).
            let offset = file
                .literal_array_offsets
                .iter()
                .find(|(_, i)| **i == idx.0)
                .map(|(o, _)| *o)
                .unwrap_or(idx.0);
            format!("lit:0x{offset:x}")
        }
        other => format!("raw:{other:?}"),
    }
}

#[derive(Default, Clone, Copy)]
struct PaStats {
    fixtures: usize,
    methods: usize,
    instructions: usize,
    mismatched: usize,
}

/// Compare every decoded method of one fixture against its reference.pa,
/// per instruction. Returns the fixture's stats; mismatches are appended
/// to `register` as human-readable records.
fn compare_fixture_with_pandasm(
    root: &std::path::Path,
    rel: &str,
    pandasm: &str,
    register: &mut Vec<String>,
) -> PaStats {
    let data = std::fs::read(root.join(rel)).expect("fixture");
    let file = decode(&data).unwrap_or_else(|e| panic!("{rel}: {e}"));
    let pa_bytes = std::fs::read(root.join(pandasm)).expect("reference.pa");
    let functions = parse_pandasm(&pa_bytes);
    // Method names are not unique across classes: pool unconsumed pandasm
    // functions per name and pair by (name, instruction count).
    let mut pool: std::collections::HashMap<Vec<u8>, Vec<PaFunction>> =
        std::collections::HashMap::new();
    for fun in functions {
        pool.entry(fun.name.clone()).or_default().push(fun);
    }
    let mut stats = PaStats {
        fixtures: 1,
        ..PaStats::default()
    };
    for (_desc, method) in file.all_methods() {
        let Some(body) = &method.body else { continue };
        let name = mutf8_bytes(file.strings.resolve(method.name).expect("method name"));
        let ours: Vec<(String, Vec<String>)> = body
            .bytecodes
            .iter()
            .map(|bc| our_canonical(&file, body, bc))
            .collect();
        stats.methods += 1;
        stats.instructions += ours.len();
        let candidates = pool.get_mut(&name).unwrap_or_else(|| {
            panic!(
                "{rel}: method {} missing from reference.pa",
                String::from_utf8_lossy(&name)
            )
        });
        // Pairing: first same-length candidate with a full match, else the
        // first same-length candidate, else the first candidate at all.
        let rendered: Vec<Vec<(String, Vec<String>)>> = candidates
            .iter()
            .map(|cand| {
                cand.instrs
                    .iter()
                    .map(|insn| {
                        (
                            insn.mnemonic.clone(),
                            insn.operands
                                .iter()
                                .map(|token| pa_operand_token(cand, token))
                                .collect(),
                        )
                    })
                    .collect()
            })
            .collect();
        let pick = rendered
            .iter()
            .position(|cand| cand.as_slice() == ours.as_slice())
            .or_else(|| rendered.iter().position(|cand| cand.len() == ours.len()))
            .unwrap_or(0);
        let cand = candidates.remove(pick);
        let rendered = rendered.into_iter().nth(pick).unwrap();
        if rendered == ours {
            continue;
        }
        for (index, (our, expect)) in ours.iter().zip(rendered.iter()).enumerate() {
            if our != expect {
                stats.mismatched += 1;
                register.push(format!(
                    "{rel} method {} instruction {index}:\n  pandasm: {}\n  tokens:  {:?}\n  ours:    {:?}",
                    String::from_utf8_lossy(&name),
                    cand.instrs[index].line,
                    expect,
                    our,
                ));
            }
        }
        if rendered.len() != ours.len() {
            stats.mismatched += 1;
            register.push(format!(
                "{rel} method {}: instruction count differs (pandasm {}, ours {})",
                String::from_utf8_lossy(&name),
                rendered.len(),
                ours.len(),
            ));
        }
    }
    for (name, remaining) in &pool {
        for fun in remaining {
            stats.mismatched += 1;
            register.push(format!(
                "{rel}: reference.pa function {} ({} instructions) has no decoded method",
                String::from_utf8_lossy(name),
                fun.instrs.len(),
            ));
        }
    }
    stats
}

/// The REAL 9/11 read verification: every corpus fixture's decoded
/// instruction stream must match upstream's own disassembly instruction by
/// instruction. Any mismatch is a registered finding (fixture + method +
/// instruction index + both renderings), not silently absorbed.
#[test]
#[ignore = "requires exported GHCR corpus + python3"]
fn exported_corpus_instructions_match_upstream_pandasm() {
    let root = exported_corpus_root();
    let rows = manifest_select(&root, SELECT_ABC_PANDASM);
    let mut register: Vec<String> = Vec::new();
    let mut matrix: std::collections::BTreeMap<(String, String), PaStats> =
        std::collections::BTreeMap::new();
    let mut total = PaStats::default();
    for line in &rows {
        let (rel, pandasm) = line.split_once('\t').expect("manifest paths");
        let stats = compare_fixture_with_pandasm(&root, rel, pandasm, &mut register);
        let version = rel.split('/').next().expect("version path").to_owned();
        let profile = std::path::Path::new(rel)
            .parent()
            .and_then(|p| p.file_name())
            .and_then(|n| n.to_str())
            .expect("profile directory")
            .to_owned();
        let entry = matrix.entry((version, profile)).or_default();
        entry.fixtures += stats.fixtures;
        entry.methods += stats.methods;
        entry.instructions += stats.instructions;
        entry.mismatched += stats.mismatched;
        total.fixtures += stats.fixtures;
        total.methods += stats.methods;
        total.instructions += stats.instructions;
        total.mismatched += stats.mismatched;
    }
    eprintln!("pandasm per-instruction comparison (version x profile):");
    for ((version, profile), stats) in &matrix {
        eprintln!(
            "  {version:9} {profile:10} fixtures {:4} methods {:6} instructions {:8} matched {:8} mismatched {}",
            stats.fixtures,
            stats.methods,
            stats.instructions,
            stats.instructions - stats.mismatched.min(stats.instructions),
            stats.mismatched,
        );
    }
    eprintln!(
        "  TOTAL fixtures {} methods {} instructions {} mismatched {}",
        total.fixtures, total.methods, total.instructions, total.mismatched
    );
    for record in register.iter().take(50) {
        eprintln!("MISMATCH: {record}");
    }
    assert_eq!(
        total.fixtures,
        rows.len(),
        "every manifest fixture must compare"
    );
    assert_eq!(
        register.len(),
        0,
        "{} per-instruction mismatches against upstream pandasm (first 50 above)",
        register.len()
    );
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
                Some(abcd_file::FieldValue::ModuleRequestPhase(p)) => {
                    // source_offset is informational (the blob relocates on
                    // rewrite); the flags are the content.
                    format!("phase({:?})", p.flags)
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

/// Identity rewrite of fixtures carrying `moduleRequestPhaseIdx` fields
/// (N7): the u32 field value is the file offset of an UNTAGGED
/// module-request-phase blob (one u8 lazy flag per module request; vendored
/// runtime reader ModuleLazyImportFlagAccessor, ecmascript/module/
/// module_data_extractor.cpp:178-189; excluded from tagged literal-array
/// disassembly upstream, disassembler.cpp:372). Pre-N7 the field wrote the
/// raw source offset back (dangling on rewrite) and the blob was misdecoded
/// as a tagged literal array.
///
/// Evidence beyond this snapshot equality: the rewritten bytes are written
/// to $ABCD_REWRITTEN_DIR for a local ark_disasm check (must be clean —
/// a dangling field value makes the disassembler parse the wrong blob).
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
    let mut checked = 0;
    for row in rows.iter().filter(|row| {
        row["case"]
            .as_str()
            .is_some_and(|case| CASES.contains(&case))
    }) {
        let relative = row["abc"].as_str().expect("abc path");
        let file = decode(&std::fs::read(root.join(relative)).expect("fixture"))
            .unwrap_or_else(|error| panic!("decode {relative}: {error}"));
        // The fixture must actually carry phase data (guard against drift).
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
        let rewritten =
            decode(&output).unwrap_or_else(|error| panic!("decode rewritten {relative}: {error}"));
        assert_eq!(
            module_field_snapshots(&rewritten),
            expected,
            "{relative}: module/scope/phase data must survive the identity rewrite"
        );
        // The rewritten field must point at a VALID re-emitted blob:
        // decoding the rewritten file must yield the same flags.
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
