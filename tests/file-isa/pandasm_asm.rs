//! Group L — pandasm asm round-trip gates (`abcd asm`'s foundation).
//!
//! Two gates over every corpus fixture's `reference.pa`:
//!
//! - **Text round-trip** (`..._text_roundtrip`): `parse_file` →
//!   `emit_file` must reproduce `reference.pa` BYTE FOR BYTE. The parser
//!   keeps every layout offset the text carries (LITERALS keys, STRING
//!   section offsets, field `= 0x…` values, `lit_offset:0x…`) in the model,
//!   so a faithful parse re-emits the identical bytes without any binary
//!   layout step.
//!
//! - **Binary round-trip** (`..._binary_roundtrip`): `parse_file` →
//!   `encode` → `decode` → `emit_file`, compared against `reference.pa`
//!   under LAYOUT-OFFSET NORMALIZATION (see [`canonicalize`]). A fresh
//!   encode re-lays the file out (the vendored writer assigns string and
//!   literal-array offsets in its own order), so the original offsets are
//!   unrecoverable from the text — upstream `ark_asm` has exactly the same
//!   property (its own asm→disasm round-trip renumbers offsets too). What
//!   must survive the binary leg is everything ELSE: section structure,
//!   record/function identity and order, every instruction, label, literal
//!   content, string content, and the offset reference GRAPH (which field
//!   points at which literal array, which literal array nests which).
//!
//! Intentional divergences go through the self-cleaning ledger
//! `scripts/pandasm-asm-divergences.json` (same discipline as
//! `pandasm-dis`): class names are prefixed `text:` / `binary:` for the
//! gate they belong to; a failing fixture must be listed (unlisted = red),
//! a listed fixture that starts passing is stale (red). The empty ledger is
//! the healthy state.
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test file-isa -- --ignored --nocapture pandasm_asm
//! ```
//!
//! `ABCD_PANDASM_ASM_FILTER=<substring>` restricts to manifest rows whose
//! `abc` path contains the substring (iteration aid; full-corpus CI runs
//! unset).

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write as _;

/// Ledger of documented divergences (class name → abc paths).
const LEDGER_PATH: &str = "scripts/pandasm-asm-divergences.json";

fn load_ledger() -> BTreeMap<String, BTreeSet<String>> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(LEDGER_PATH);
    let text =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let value: serde_json::Value = serde_json::from_str(&text).expect("ledger is valid JSON");
    let mut ledger: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (class, paths) in value.as_object().expect("ledger is an object") {
        // "$comment" and per-class "$class:<name>" documentation keys.
        if class.starts_with('$') {
            continue;
        }
        let set = paths
            .as_array()
            .unwrap_or_else(|| panic!("ledger class {class} must be an array"))
            .iter()
            .map(|p| p.as_str().expect("ledger paths are strings").to_owned())
            .collect();
        ledger.insert(class.clone(), set);
    }
    ledger
}

/// The fixture's file version, from its manifest path's first component
/// (`9.0.0.0/…` — the same convention `main.rs` uses).
fn version_of(rel: &str) -> abcd_isa::Version {
    rel.split('/')
        .next()
        .and_then(|v| {
            v.split('.')
                .map(|n| n.parse::<u8>().ok())
                .collect::<Option<Vec<_>>>()
        })
        .and_then(|v| (v.len() == 4).then(|| abcd_isa::Version::new(v[0], v[1], v[2], v[3])))
        .unwrap_or_else(|| panic!("invalid version path in manifest row: {rel}"))
}

/// First-difference report for one mismatched fixture: byte offset, plus
/// the differing line from each side (lossy — pandasm text is raw bytes).
fn first_diff(rel: &str, ours: &[u8], reference: &[u8]) -> String {
    let pos = ours
        .iter()
        .zip(reference.iter())
        .position(|(a, b)| a != b)
        .unwrap_or(ours.len().min(reference.len()));
    let line_of = |bytes: &[u8]| {
        let start = bytes[..pos]
            .iter()
            .rposition(|&b| b == b'\n')
            .map_or(0, |i| i + 1);
        let end = bytes[pos..]
            .iter()
            .position(|&b| b == b'\n')
            .map_or(bytes.len(), |i| pos + i);
        String::from_utf8_lossy(&bytes[start..end]).into_owned()
    };
    format!(
        "{rel}: first diff at byte {pos} (ours {} bytes, reference {} bytes)\n  ours:      {:?}\n  reference: {:?}",
        ours.len(),
        reference.len(),
        line_of(ours),
        line_of(reference),
    )
}

// ---------------------------------------------------------------------------
// Layout-offset normalization for the binary round-trip gate
// ---------------------------------------------------------------------------

/// Split pandasm text into (header, literals, records, methods, strings)
/// section bodies. Sections are delimited by the `# ====================`
/// banners; missing sections yield empty bodies (the normalizer is
/// deliberately tolerant — it runs on gate failures too).
fn split_sections(pa: &[u8]) -> (Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>) {
    const BANNER: &[u8] = b"# ====================\n";
    let mut marks = Vec::new();
    let mut pos = 0usize;
    while pos + BANNER.len() <= pa.len() {
        if &pa[pos..pos + BANNER.len()] == BANNER {
            marks.push(pos);
            pos += BANNER.len();
            continue;
        }
        pos += 1;
    }
    // Header: everything before the first banner. Then each banner is
    // followed by `# NAME\n\n` and the body runs to the next banner.
    let header = pa[..marks.first().copied().unwrap_or(pa.len())].to_vec();
    let mut bodies: Vec<Vec<u8>> = Vec::new();
    for (i, &m) in marks.iter().enumerate() {
        let name_start = m + BANNER.len();
        let body_start = pa[name_start..]
            .windows(2)
            .position(|w| w == b"\n\n")
            .map(|p| name_start + p + 2)
            .unwrap_or(pa.len());
        let end = marks.get(i + 1).copied().unwrap_or(pa.len());
        bodies.push(pa[body_start.min(end)..end].to_vec());
    }
    while bodies.len() < 4 {
        bodies.push(Vec::new());
    }
    let mut it = bodies.into_iter();
    (
        header,
        it.next().unwrap(),
        it.next().unwrap(),
        it.next().unwrap(),
        it.next().unwrap(),
    )
}

/// Does this line start a LITERALS entry (`{index} 0x{offset} …`)?
fn is_literal_key_line(line: &[u8]) -> bool {
    literal_key_offset(line).is_some()
}

/// Parse the key offset out of a LITERALS entry's first line.
fn literal_key_offset(line: &[u8]) -> Option<u32> {
    let sp = line.iter().position(|&b| b == b' ')?;
    if line[..sp].is_empty() || !line[..sp].iter().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let hex = line[sp + 1..].strip_prefix(b"0x")?;
    let hex_len = hex.iter().take_while(|b| b.is_ascii_hexdigit()).count();
    if hex_len == 0 {
        return None;
    }
    u32::from_str_radix(std::str::from_utf8(&hex[..hex_len]).ok()?, 16).ok()
}

/// Split a section body into entries starting at key lines (LITERALS) or
/// `[offset:0x` lines (STRING); multi-line entries (raw string contents may
/// contain newlines) stay whole.
fn split_keyed_entries(body: &[u8], key_start: fn(&[u8]) -> bool) -> Vec<Vec<u8>> {
    let mut entries: Vec<Vec<u8>> = Vec::new();
    for line in body.split(|&b| b == b'\n') {
        if key_start(line) || entries.is_empty() {
            entries.push(line.to_vec());
        } else if line.is_empty() && entries.last().is_some_and(|e| e.is_empty()) {
            // Collapse consecutive blank separators (section tail).
        } else {
            let e = entries.last_mut().expect("non-empty");
            e.push(b'\n');
            e.extend_from_slice(line);
        }
    }
    // Drop the trailing empty entry a section's final newline creates, and
    // trim trailing whitespace a multi-line entry may have absorbed.
    while entries.last().is_some_and(|e| e.is_empty()) {
        entries.pop();
    }
    for e in &mut entries {
        while e.last().is_some_and(|b| b.is_ascii_whitespace()) {
            e.pop();
        }
    }
    entries
}

/// Layout-insensitive canonical form of pandasm text for the binary
/// round-trip gate. Everything that is pure writer layout is factored out;
/// content and the reference graph are kept:
///
/// - LITERALS entry keys (`{index} 0x{offset}`) are dropped and entries are
///   sorted by canonical content (both sides keep entry multiplicity, so a
///   lost or duplicated array still fails).
/// - `lit_offset:0x{offset}` (nested literal arrays) and field
///   `= 0x{offset}` values that name a literal table are replaced by the
///   target's canonical content, so the reference GRAPH is compared, not
///   the addresses (iterative deepening resolves nesting chains).
/// - STRING entry offsets are dropped and entries sorted.
pub(crate) fn canonicalize(pa: &[u8]) -> Vec<u8> {
    let (header, literals, records, methods, strings) = split_sections(pa);

    // Pass 1: canonical content per literal-table offset, lit_offset links
    // replaced iteratively ( nesting depth is tiny in practice; a reference
    // cycle — impossible to encode — would leave the raw offset in place).
    let entries = split_keyed_entries(&literals, is_literal_key_line);
    let mut by_offset: BTreeMap<u32, Vec<u8>> = BTreeMap::new();
    for entry in &entries {
        if let Some(off) = literal_key_offset(entry) {
            // Strip the `{index} 0x{offset}` key (and its one trailing
            // space when a value follows): pure writer layout.
            let mut i = entry.iter().position(|&b| b == b' ').unwrap_or(0) + 1;
            i += 2; // "0x"
            while i < entry.len() && entry[i].is_ascii_hexdigit() {
                i += 1;
            }
            if i < entry.len() && entry[i] == b' ' {
                i += 1;
            }
            by_offset.insert(off, entry[i.min(entry.len())..].to_vec());
        }
    }
    fn replace_lit_offsets(text: &[u8], resolve: &dyn Fn(u32) -> Option<Vec<u8>>) -> Vec<u8> {
        let mut out = Vec::with_capacity(text.len());
        let mut i = 0usize;
        while i < text.len() {
            if text[i..].starts_with(b"lit_offset:0x") {
                let start = i + b"lit_offset:0x".len();
                let end = text[start..]
                    .iter()
                    .position(|&b| !b.is_ascii_hexdigit())
                    .map(|p| start + p)
                    .unwrap_or(text.len());
                if let Ok(off) =
                    u32::from_str_radix(std::str::from_utf8(&text[start..end]).unwrap_or(""), 16)
                {
                    if let Some(target) = resolve(off) {
                        out.extend_from_slice(b"lit_offset:@[");
                        out.extend_from_slice(&target);
                        out.extend_from_slice(b"]");
                        i = end;
                        continue;
                    }
                }
            }
            out.push(text[i]);
            i += 1;
        }
        out
    }
    let mut canonical = by_offset.clone();
    for _ in 0..8 {
        let next: BTreeMap<u32, Vec<u8>> = canonical
            .iter()
            .map(|(off, content)| {
                let c = replace_lit_offsets(content, &|t| canonical.get(&t).cloned());
                (*off, c)
            })
            .collect();
        if next == canonical {
            break;
        }
        canonical = next;
    }
    let mut lit_lines: Vec<Vec<u8>> = canonical.values().cloned().collect();
    lit_lines.sort();

    // RECORDS: field `= 0x…` values naming a literal table become content
    // references. Blob offsets the LITERALS section never lists (the 13/24
    // collector skips module/scope/phase blobs unless a field is named
    // scopeNames/moduleRecordIdx) canonicalize to a plain `@blob` marker —
    // their content is unrecoverable from the text, but the offset is pure
    // layout.
    let blob_records: &[&[u8]] = &[
        b"_ESModuleRecord",
        b"_ESScopeNamesRecord",
        b"_ModuleRequestPhaseRecord",
    ];
    let mut cur_record: Vec<u8> = Vec::new();
    let mut rec_out = Vec::with_capacity(records.len());
    for line in records.split(|&b| b == b'\n') {
        let mut line_out = line.to_vec();
        if let Some(rest) = line.strip_prefix(b".record ") {
            cur_record = rest
                .trim_ascii()
                .strip_suffix(b" {")
                .or_else(|| rest.trim_ascii().strip_suffix(b" <external>"))
                .unwrap_or(rest.trim_ascii())
                .to_vec();
        }
        if let Some(eq) = line.windows(3).rposition(|w| w == b" = ") {
            if line[eq + 3..].starts_with(b"0x") {
                if let Ok(off) =
                    u32::from_str_radix(std::str::from_utf8(&line[eq + 5..]).unwrap_or(""), 16)
                {
                    let field_name = line
                        .get(1..eq)
                        .and_then(|t| t.iter().position(|&b| b == b' ').map(|sp| &t[sp + 1..]))
                        .unwrap_or(b"");
                    let is_blob_field = blob_records.contains(&cur_record.as_slice())
                        || field_name == b"moduleRequestPhaseIdx"
                        || field_name == b"scopeNames";
                    if let Some(target) = canonical.get(&off) {
                        line_out = line[..eq + 3].to_vec();
                        line_out.extend_from_slice(b"@[");
                        line_out.extend_from_slice(target);
                        line_out.extend_from_slice(b"]");
                    } else if is_blob_field {
                        line_out = line[..eq + 3].to_vec();
                        line_out.extend_from_slice(b"@blob");
                    }
                }
            }
        }
        rec_out.extend_from_slice(&line_out);
        rec_out.push(b'\n');
    }
    if rec_out.last() == Some(&b'\n') && !records.ends_with(b"\n") {
        rec_out.pop();
    }

    // METHODS: inline literal arrays may carry lit_offset references.
    let methods_out = replace_lit_offsets(&methods, &|t| canonical.get(&t).cloned());

    // STRING: drop offsets, sort entries.
    let mut str_entries = split_keyed_entries(&strings, |line| line.starts_with(b"[offset:0x"));
    for entry in &mut str_entries {
        if let Some(p) = entry
            .windows(b", name_value:".len())
            .position(|w| w == b", name_value:")
        {
            entry.drain(1..p + 2); // keep '[' then 'name_value:…'
        }
    }
    str_entries.sort();

    let mut out = header;
    out.extend_from_slice(b"# ====================\n# LITERALS\n\n");
    for l in &lit_lines {
        out.extend_from_slice(l);
        out.push(b'\n');
    }
    out.extend_from_slice(b"\n# ====================\n# RECORDS\n\n");
    out.extend_from_slice(&rec_out);
    out.extend_from_slice(b"\n# ====================\n# METHODS\n\n");
    out.extend_from_slice(&methods_out);
    out.extend_from_slice(b"\n# ====================\n# STRING\n\n");
    for s in &str_entries {
        out.extend_from_slice(s);
        out.push(b'\n');
    }
    out
}

// ---------------------------------------------------------------------------
// Shared gate driver
// ---------------------------------------------------------------------------

/// One fixture's verdict: Ok(byte-identical / canonically identical) or a
/// human-readable failure reason.
type Verdict = Result<(), String>;

fn run_gate(prefix: &str, check: impl Fn(&std::path::Path, &str, &str) -> Verdict) {
    let root = crate::exported_corpus_root();
    let rows = crate::manifest_select(&root, crate::SELECT_ABC_PANDASM);
    let filter = std::env::var("ABCD_PANDASM_ASM_FILTER").ok();
    let ledger = load_ledger();
    // This gate's classes only (the two gates share one ledger file).
    let ledger: BTreeMap<String, BTreeSet<String>> = ledger
        .into_iter()
        .filter(|(class, _)| class.starts_with(prefix))
        .collect();
    // Reverse index: path → divergence class (double-listing is red).
    let mut listed: BTreeMap<&str, &str> = BTreeMap::new();
    for (class, paths) in &ledger {
        for path in paths {
            assert!(
                listed.insert(path.as_str(), class.as_str()).is_none(),
                "ledger lists {path} under two {prefix} classes"
            );
        }
    }
    let seen: BTreeSet<&str> = rows
        .iter()
        .map(|line| line.split_once('\t').expect("manifest paths").0)
        .collect();

    let mut total = 0usize;
    let mut matched = 0usize;
    let mut documented: BTreeMap<&str, usize> = BTreeMap::new();
    let mut failing: BTreeSet<String> = BTreeSet::new();
    let mut undocumented: Vec<String> = Vec::new();
    let mut reasons: Vec<String> = Vec::new();
    for line in &rows {
        let (rel, pandasm) = line.split_once('\t').expect("manifest paths");
        if let Some(f) = &filter {
            if !rel.contains(f.as_str()) {
                continue;
            }
        }
        total += 1;
        match check(&root, rel, pandasm) {
            Ok(()) => matched += 1,
            Err(reason) => {
                failing.insert(rel.to_owned());
                match listed.get(rel) {
                    Some(class) => *documented.entry(class).or_default() += 1,
                    None => {
                        undocumented.push(rel.to_owned());
                        if reasons.len() < 20 {
                            reasons.push(reason);
                        }
                    }
                }
            }
        }
    }

    // Stale entries: ledgered in-scope paths that no longer fail — the
    // ledger self-cleans by turning red.
    let stale: Vec<String> = ledger
        .iter()
        .flat_map(|(class, paths)| paths.iter().map(move |p| (class, p)))
        .filter(|(_, path)| {
            filter.as_ref().is_none_or(|f| path.contains(f.as_str()))
                && seen.contains(path.as_str())
                && !failing.contains(path.as_str())
        })
        .map(|(class, path)| format!("{path} (class {class})"))
        .collect();

    std::io::stderr().flush().ok();
    eprintln!(
        "pandasm asm {prefix}: total {total} matched {matched} documented {} undocumented {}",
        documented.values().sum::<usize>(),
        undocumented.len()
    );
    for (class, n) in &documented {
        eprintln!("  documented[{class}]: {n}");
    }
    for u in &undocumented {
        eprintln!("  UNDOCUMENTED: {u}");
    }
    for record in &reasons {
        eprintln!("FAIL: {record}");
    }
    assert!(
        undocumented.is_empty(),
        "{} fixtures fail the pandasm asm {prefix} gate without a ledger entry (first {} above)",
        undocumented.len(),
        reasons.len()
    );
    assert!(
        stale.is_empty(),
        "stale ledger entries (fixtures now passing — delist): {stale:?}"
    );
    if filter.is_none() {
        assert_eq!(
            matched + documented.values().sum::<usize>(),
            total,
            "every fixture either matches or is documented"
        );
        assert_eq!(total, rows.len(), "every manifest fixture must run");
    }
}

/// The text round-trip gate: `parse_file` → `emit_file` must reproduce
/// `reference.pa` byte for byte.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn exported_corpus_pandasm_asm_text_roundtrip() {
    run_gate("text:", |root, rel, pandasm| {
        let reference = std::fs::read(root.join(pandasm)).expect("reference.pa");
        // The .pa text does not carry the file version; the gate knows it
        // from the manifest path. The version selects the parser's proto
        // reconstruction and the emitter's literal-table collection path
        // (≤12 header table vs 13/24 unordered_set simulation), so it must
        // be right for byte identity.
        let file = abcd_file::pandasm::parse_file_with_version(&reference, version_of(rel))
            .map_err(|e| format!("{rel}: parse failed: {e}"))?;
        let source_name = std::path::Path::new(rel)
            .file_name()
            .and_then(|n| n.to_str())
            .expect("fixture basename");
        let ours = abcd_file::pandasm::emit_file(&file, source_name);
        if ours == reference {
            Ok(())
        } else {
            Err(first_diff(rel, &ours, &reference))
        }
    });
}

/// The binary round-trip gate: `parse_file` → `encode` → `decode` →
/// `emit_file`, compared under layout-offset normalization.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn exported_corpus_pandasm_asm_binary_roundtrip() {
    run_gate("binary:", |root, rel, pandasm| {
        let reference = std::fs::read(root.join(pandasm)).expect("reference.pa");
        let file = abcd_file::pandasm::parse_file_with_version(&reference, version_of(rel))
            .map_err(|e| format!("{rel}: parse failed: {e}"))?;
        let bytes = abcd_file::encode(&file).map_err(|e| format!("{rel}: encode failed: {e}"))?;
        let file2 =
            abcd_file::decode(&bytes).map_err(|e| format!("{rel}: re-decode failed: {e}"))?;
        let source_name = std::path::Path::new(rel)
            .file_name()
            .and_then(|n| n.to_str())
            .expect("fixture basename");
        let ours = abcd_file::pandasm::emit_file(&file2, source_name);
        let (ours_c, reference_c) = (canonicalize(&ours), canonicalize(&reference));
        if ours_c == reference_c {
            Ok(())
        } else {
            Err(first_diff(rel, &ours_c, &reference_c))
        }
    });
}
