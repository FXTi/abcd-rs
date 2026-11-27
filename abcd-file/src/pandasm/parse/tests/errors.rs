//! Parser smoke tests, deterministic fuzzing, MUTF-8/key/language helpers,
//! and negative malformed-document structured error tests.

use super::super::scan::parse_language;
use super::super::*;
use super::{MINIMAL, doc, one_function, parse_err};
use crate::{FieldValue, LiteralArrayIdx};

#[test]
fn minimal_roundtrip_is_byte_exact() {
    let file = parse_file(MINIMAL).expect("minimal parses");
    let out = crate::pandasm::emit_file(&file, "t.abc");
    assert_eq!(out, MINIMAL, "parse->emit must be byte-exact");
    // And the model must assemble.
    crate::encode(&file).expect("minimal encodes");
}

#[test]
fn string_operands_use_the_string_section_oracle() {
    let text: &[u8] = b"# source binary: t.abc\n\n# ====================\n# LITERALS\n\n\n# ====================\n# RECORDS\n\n# ====================\n# METHODS\n\n.language ECMAScript\n.function any f() <static> {\n\tlda.str \"a,b}\"\n\tthrow.undefinedifholewithname \"a,b}\"\n\treturnundefined\n}\n\n# ====================\n# STRING\n\n[offset:0x40, name_value:a,b}]\n";
    let file = parse_file(text).expect("quoted-comma string parses");
    let out = crate::pandasm::emit_file(&file, "t.abc");
    assert_eq!(out, text);
    crate::encode(&file).expect("encodes");
}

#[test]
fn garbage_is_a_structured_error() {
    let err = parse_file(b"hello world").expect_err("garbage rejected");
    assert!(err.message.contains("section banners"), "{err}");
    // A truncated file: banners present, body cut mid-function.
    let truncated = &MINIMAL[..MINIMAL.len() - 30];
    let res = parse_file(truncated);
    assert!(res.is_err(), "truncated input must fail, not panic");
}

/// Deterministic fuzz round: random buffers, mutations, truncations,
/// and duplicated lines of a valid document. The parser must never
/// panic; errors are fine.
#[test]
fn fuzz_never_panics() {
    let mut state = 0x853c_49e6_748f_ea9bu64;
    let mut rng = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for round in 0..4000u32 {
        let input: Vec<u8> = match round % 4 {
            0 => {
                // Random bytes.
                let len = (rng() % 200) as usize;
                (0..len).map(|_| rng() as u8).collect()
            }
            1 => {
                // Point mutations of a valid document.
                let mut v = MINIMAL.to_vec();
                for _ in 0..(rng() % 8 + 1) {
                    let pos = (rng() as usize) % v.len();
                    v[pos] = rng() as u8;
                }
                v
            }
            2 => {
                // Truncation at a random point.
                let end = (rng() as usize) % (MINIMAL.len() + 1);
                MINIMAL[..end].to_vec()
            }
            _ => {
                // Splice a random slice of the document back into it.
                let mut v = MINIMAL.to_vec();
                let start = (rng() as usize) % MINIMAL.len();
                let len = (rng() as usize) % (MINIMAL.len() - start);
                let at = (rng() as usize) % v.len();
                let piece: Vec<u8> = MINIMAL[start..start + len].to_vec();
                v.splice(at..at, piece);
                v
            }
        };
        // A panic fails the test outright; Err is fine.
        let _ = parse_file(&input);
    }
}

// -- mutf8_decode: strict decoder, direct calls -----------------------
use crate::string_pool::mutf8_decode_utf8 as mutf8_decode;

#[test]
fn mutf8_decode_valid_forms() {
    assert_eq!(mutf8_decode(b"abc").as_deref(), Some("abc"));
    assert_eq!(mutf8_decode(b"").as_deref(), Some(""));
    // 2-byte.
    assert_eq!(mutf8_decode(&[0xC3, 0xA9]).as_deref(), Some("\u{00e9}"));
    // 3-byte.
    assert_eq!(
        mutf8_decode(&[0xE2, 0x82, 0xAC]).as_deref(),
        Some("\u{20ac}")
    );
    // Embedded NUL (MUTF-8 C0 80).
    assert_eq!(
        mutf8_decode(&[b'a', 0xC0, 0x80, b'b']).as_deref(),
        Some("a\0b")
    );
    // CESU-8 surrogate pair (U+1F600).
    assert_eq!(
        mutf8_decode(&[0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80]).as_deref(),
        Some("\u{1F600}")
    );
    // Raw 4-byte UTF-8 (handwritten-only: the emitter prints CESU-8).
    assert_eq!(
        mutf8_decode(&[0xF0, 0x9F, 0x98, 0x80]).as_deref(),
        Some("\u{1F600}")
    );
    // Round-trip through the emitter's encoder.
    assert_eq!(
        mutf8_decode(&crate::pandasm::mutf8_bytes("a\0\u{1F600}\u{20ac}")).as_deref(),
        Some("a\0\u{1F600}\u{20ac}")
    );
}

#[test]
fn mutf8_decode_rejects_malformed() {
    // Raw NUL is never valid MUTF-8.
    assert_eq!(mutf8_decode(b"a\0b"), None);
    // 2-byte: bad continuation, truncated.
    assert_eq!(mutf8_decode(&[0xC3, 0x28]), None);
    assert_eq!(mutf8_decode(&[0xC3]), None);
    // 3-byte: bad second/third continuation, truncated.
    assert_eq!(mutf8_decode(&[0xE2, 0x28, 0xAC]), None);
    assert_eq!(mutf8_decode(&[0xE2, 0x82, 0x28]), None);
    assert_eq!(mutf8_decode(&[0xE2, 0x82]), None);
    // Lone high surrogate (truncated pair), high surrogate followed by
    // a non-low 3-byte sequence, lone low surrogate.
    assert_eq!(mutf8_decode(&[0xED, 0xA0, 0xBD]), None);
    assert_eq!(mutf8_decode(&[0xED, 0xA0, 0xBD, 0xE1, 0x80, 0x80]), None);
    assert_eq!(mutf8_decode(&[0xED, 0xB0, 0x80]), None);
    // High surrogate followed by an ASCII byte (not a 3-byte lead), in
    // both short and full-lookahead forms.
    assert_eq!(mutf8_decode(&[0xED, 0xA0, 0xBD, b'a']), None);
    assert_eq!(mutf8_decode(&[0xED, 0xA0, 0xBD, b'a', 0x80, 0x80]), None);
    // 4-byte: bad continuation, truncated, out-of-range code point.
    assert_eq!(mutf8_decode(&[0xF0, 0x9F, 0x28, 0x80]), None);
    assert_eq!(mutf8_decode(&[0xF0, 0x9F]), None);
    assert_eq!(mutf8_decode(&[0xF4, 0x90, 0x80, 0x80]), None);
    // Invalid lead bytes.
    assert_eq!(mutf8_decode(&[0x80]), None);
    assert_eq!(mutf8_decode(&[0xFF]), None);
}

// -- parse_literal_key / parse_language: direct calls ------------------

#[test]
fn parse_literal_key_forms() {
    assert_eq!(parse_literal_key(b"0 0x10 { }"), Some((0, 0x10, 7)));
    assert_eq!(parse_literal_key(b"10 0x2a "), Some((10, 0x2a, 8)));
    assert_eq!(parse_literal_key(b""), None);
    assert_eq!(parse_literal_key(b"0"), None);
    assert_eq!(parse_literal_key(b"x 0x10"), None);
    assert_eq!(parse_literal_key(b" 0x10"), None);
    assert_eq!(parse_literal_key(b"0 zz"), None);
    assert_eq!(parse_literal_key(b"0 0x"), None);
    assert_eq!(parse_literal_key(b"0 0x10"), None);
    assert_eq!(parse_literal_key(b"99999999999 0x1 "), None);
}

#[test]
fn parse_language_all_variants() {
    assert_eq!(parse_language(b"ECMAScript"), Some(SourceLang::EcmaScript));
    assert_eq!(parse_language(b"JavaScript"), Some(SourceLang::JavaScript));
    assert_eq!(parse_language(b"TypeScript"), Some(SourceLang::TypeScript));
    assert_eq!(parse_language(b"ArkTS"), Some(SourceLang::ArkTs));
    assert_eq!(
        parse_language(b"PandaAssembly"),
        Some(SourceLang::PandaAssembly)
    );
    assert_eq!(parse_language(b"Klingon"), None);
}

// -- Negative batch: one malformed document per structured error -------

/// A module-array LITERALS entry whose record section is `record_line`.
fn module_blob_doc(record_line: &[u8]) -> Vec<u8> {
    let mut lit = b"0 0x100 { 1 [\n\tMODULE_REQUEST_ARRAY: {\n\t\t0 : r,\n\t};\n".to_vec();
    lit.extend_from_slice(record_line);
    lit.extend_from_slice(b"\n]}\n");
    doc(&lit, b"", b"", b"")
}

#[test]
fn malformed_documents_fail_with_structured_errors() {
    let cases: Vec<(Vec<u8>, String)> = vec![
        // Section splitting.
        (
            b"# ====================\n# LITERALS\n\n# ====================\n# RECORDS\n\n# ====================\n# METHODS\n\n# ====================\n".to_vec(),
            "truncated section name".to_owned(),
        ),
        // STRING section entries.
        (
            doc(b"", b"", b"", b"[offset:0x40]"),
            "malformed STRING entry (missing `, name_value:`)".to_owned(),
        ),
        (
            doc(b"", b"", b"", b"[offset:0xZZ, name_value:ab]"),
            "malformed STRING entry offset".to_owned(),
        ),
        (
            doc(b"", b"", b"", b"[offset:0x40, name_value:ab"),
            "malformed STRING entry (missing `]`)".to_owned(),
        ),
        // LITERALS section entries.
        (
            doc(b"foo bar\n", b"", b"", b""),
            "malformed LITERALS entry key".to_owned(),
        ),
        (
            doc(b"0 0x10 { 1 [ string:\"abc\n", b"", b"", b""),
            "unterminated LITERALS entry value".to_owned(),
        ),
        (
            // Brace-balanced and `]}`-terminated, but not `{`-started.
            doc(b"0 0x10 [{ ]}\n", b"", b"", b""),
            "malformed LITERALS entry value".to_owned(),
        ),
        // Literal array shape (reached via an inline literal operand:
        // the section path pre-checks completeness).
        (
            doc(b"", b"", &one_function(b"\tcreatearraywithbuffer 0x0, { 1 }\n"), b""),
            "literal array missing `[`".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tcreatearraywithbuffer 0x0, { 1 [ i32:1 }\n"), b""),
            "literal array missing `]}`".to_owned(),
        ),
        // A multi-line string not in the oracle: complete by the
        // section scanner's fallback, unsplittable per-line.
        (
            doc(b"0 0x10 { 1 [ string:\"ab\ncd\", ]}\n", b"", b"", b""),
            "unterminated string in literal array".to_owned(),
        ),
        // Literal items.
        (
            doc(b"0 0x10 { 1 [ hello, ]}\n", b"", b"", b""),
            "literal item missing `tag:`".to_owned(),
        ),
        (
            doc(b"0 0x10 { 1 [ string:abc, ]}\n", b"", b"", b""),
            "literal string item is not quoted".to_owned(),
        ),
        (
            doc(b"0 0x10 { 1 [ i32:\xff, ]}\n", b"", b"", b""),
            "literal integer is not ASCII".to_owned(),
        ),
        (
            doc(b"0 0x10 { 1 [ i32:zz, ]}\n", b"", b"", b""),
            "literal integer `zz` does not parse".to_owned(),
        ),
        (
            doc(b"0 0x10 { 1 [ f64:\xff, ]}\n", b"", b"", b""),
            "literal float is not ASCII".to_owned(),
        ),
        (
            doc(b"0 0x10 { 1 [ f64:zz, ]}\n", b"", b"", b""),
            "literal float `zz` does not parse".to_owned(),
        ),
        (
            doc(b"0 0x10 { 1 [ lit_offset:\xff, ]}\n", b"", b"", b""),
            "lit_offset is not ASCII".to_owned(),
        ),
        (
            doc(b"0 0x10 { 1 [ lit_offset:zz, ]}\n", b"", b"", b""),
            "lit_offset `zz` does not parse".to_owned(),
        ),
        (
            doc(b"0 0x10 { 1 [ what:1, ]}\n", b"", b"", b""),
            "unknown literal tag `what`".to_owned(),
        ),
        // Module-array values.
        (
            doc(b"0 0x99 { 5 [ junk\n\tMODULE_REQUEST_ARRAY: {\n\t};\n]}\n", b"", b"", b""),
            "module array missing `[`".to_owned(),
        ),
        (
            doc(
                b"0 0x99 { 0 [\n\tjunk\n\tMODULE_REQUEST_ARRAY: {\n\t};\n]}\n",
                b"",
                b"",
                b"",
            ),
            "module array missing MODULE_REQUEST_ARRAY".to_owned(),
        ),
        (
            doc(
                b"0 0x99 { 0 [\n\tMODULE_REQUEST_ARRAY: {\n\t\tjunkline\n\t};\n]}\n",
                b"",
                b"",
                b"",
            ),
            "malformed module request line".to_owned(),
        ),
        (
            doc(
                b"0 0x99 { 0 [\n\tMODULE_REQUEST_ARRAY: {\n\t};\n\tjunk\n]}\n",
                b"",
                b"",
                b"",
            ),
            "malformed module record line".to_owned(),
        ),
        (
            doc(
                b"0 0x99 { 0 [\n\tMODULE_REQUEST_ARRAY: {\n\t};\n\tModuleTag: STAR_EXPORT, module_request: r\n]}\n",
                b"",
                b"",
                b"",
            ),
            "module record line missing `;`".to_owned(),
        ),
        // Module records.
        (
            module_blob_doc(b"\tModuleTag: STAR_EXPORT;"),
            "malformed module record (no tag)".to_owned(),
        ),
        (
            module_blob_doc(b"\tModuleTag: STAR_EXPORT, module_request;"),
            "malformed module record (field without colon)".to_owned(),
        ),
        (
            module_blob_doc(b"\tModuleTag: STAR_EXPORT, other: x;"),
            "malformed module record (missing module_request)".to_owned(),
        ),
        (
            module_blob_doc(b"\tModuleTag: REGULAR_IMPORT, import_name: b, module_request: r;"),
            "malformed module record (missing local_name)".to_owned(),
        ),
        (
            module_blob_doc(b"\tModuleTag: FROB, module_request: r;"),
            "unknown ModuleTag `FROB`".to_owned(),
        ),
        // RECORDS section.
        (
            doc(b"", b".language Klingon\n", b"", b""),
            "unknown language `Klingon`".to_owned(),
        ),
        (
            doc(b"", b"garbage\n", b"", b""),
            "expected `.record` or `.language`".to_owned(),
        ),
        (
            doc(b"", b".record Foo\n", b"", b""),
            "malformed `.record` header".to_owned(),
        ),
        (
            doc(b"", b".record R {\n u32 x\n}\n", b"", b""),
            "record field line must be tab-indented".to_owned(),
        ),
        (
            doc(b"", b".record R {\n\tu32 x\n", b"", b""),
            "unterminated `.record` body".to_owned(),
        ),
        (
            doc(b"", b".record R {\n\tu32\n}\n", b"", b""),
            "malformed field line (no type/name split)".to_owned(),
        ),
        // METHODS section framing.
        (
            doc(b"", b"", b"garbage\n", b""),
            "expected `.language` before `.function`".to_owned(),
        ),
        (
            doc(b"", b"", b".language Klingon\n.function any f() <static> {\n}\n", b""),
            "unknown language `Klingon`".to_owned(),
        ),
        (
            // No trailing newline: the section ends with the directive.
            doc(b"", b"", b".language ECMAScript", b""),
            "unexpected end of METHODS section".to_owned(),
        ),
        (
            doc(b"", b"", b".language ECMAScript\ngarbage\n", b""),
            "expected `.function`".to_owned(),
        ),
        // Function headers.
        (
            doc(b"", b"", b".language ECMAScript\n.function any f <static> {\n}\n", b""),
            "`.function` missing parameter list".to_owned(),
        ),
        (
            doc(b"", b"", b".language ECMAScript\n.function any() <static> {\n}\n", b""),
            "`.function` missing name".to_owned(),
        ),
        (
            doc(b"", b"", b".language ECMAScript\n.function any f( <static> {\n}\n", b""),
            "`.function` missing `)`".to_owned(),
        ),
        (
            doc(b"", b"", b".language ECMAScript\n.function any f)a( <static> {\n}\n", b""),
            "`.function` has `)` before `(`".to_owned(),
        ),
        (
            doc(b"", b"", b".language ECMAScript\n.function any f(any) <static> {\n}\n", b""),
            "malformed parameter".to_owned(),
        ),
        (
            doc(b"", b"", b".language ECMAScript\n.function any f() <static>\n", b""),
            "`.function` missing `{`".to_owned(),
        ),
        (
            doc(b"", b"", b".language ECMAScript\n.function any f() static {\n}\n", b""),
            "malformed `.function` attributes".to_owned(),
        ),
        (
            doc(b"", b"", b".language ECMAScript\n.function any f() <bogus> {\n}\n", b""),
            "unknown function attribute `bogus`".to_owned(),
        ),
        (
            doc(b"", b"", b".language ECMAScript\n.function any f() <static> {\n", b""),
            "unterminated `.function` body".to_owned(),
        ),
        (
            doc(b"", b"", b".language ECMAScript\n.function any f() <static> {\ngarbage\n}\n", b""),
            "unexpected line in function body".to_owned(),
        ),
        // Annotation elements.
        (
            doc(b"", b"", b"LAnno:\n\tu32 x 5 }\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
            "annotation element missing `{`".to_owned(),
        ),
        (
            doc(b"", b"", b"LAnno:\n\tu32 x { 5\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
            "annotation element missing `}`".to_owned(),
        ),
        (
            doc(b"", b"", b"LAnno:\n\tu32 { 5 }\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
            "annotation element missing name".to_owned(),
        ),
        (
            doc(b"", b"", b"LAnno:\n\tu32 x { zz }\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
            "annotation u32 `zz` does not parse".to_owned(),
        ),
        (
            doc(b"", b"", b"LAnno:\n\tf64 x { zz }\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
            "annotation f64 `zz` does not parse".to_owned(),
        ),
        (
            doc(b"", b"", b"LAnno:\n\tpanda.String x { hi }\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
            "annotation string is not quoted".to_owned(),
        ),
        (
            doc(b"", b"", b"LAnno:\n\tq32 x { 1 }\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
            "unknown annotation element tag `q32`".to_owned(),
        ),
        // Instructions.
        (
            doc(b"", b"", &one_function(b"\tbogusinsn\n"), b""),
            "unknown instruction `bogusinsn`".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\t\xff\n"), b""),
            "instruction mnemonic is not ASCII".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tldai\n"), b""),
            "`ldai` expects more operands".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tldai 0x1, 0x2\n"), b""),
            "`ldai` has more operands than the ISA allows".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tldai v0\n"), b""),
            "`ldai` operand 0 has the wrong kind for the ISA".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tldai 0xZZ\n"), b""),
            "hex immediate `0xZZ` does not parse".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tmov v65536, v0\n"), b""),
            "register `v65536` out of range".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tmov v65535, a0\n"), b""),
            "`mov` register 65536 out of range".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tjmp nowhere\n"), b""),
            "undefined label `nowhere`".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tdefinefunc 0x0, missing:(), 0x0\n"), b""),
            "method reference `missing:()` names no defined function".to_owned(),
        ),
        // Unterminated multi-line instruction string: the lookahead
        // walks to the section end while an oracle prefix is pending.
        (
            doc(
                b"",
                b"",
                b".language ECMAScript\n.function any f() <static> {\n\tlda.str \"abc\n",
                b"[offset:0x40, name_value:abc\ndef]",
            ),
            "unterminated string in instruction".to_owned(),
        ),
        // An oracle-listed string whose close quote is NOT followed by
        // a separator: the close scan skips it and the token is not a
        // string at all.
        (
            doc(
                b"",
                b"",
                &one_function(b"\tlda.str \"a\"x\n"),
                b"[offset:0x40, name_value:a]",
            ),
            "`lda.str` operand 0 has the wrong kind for the ISA".to_owned(),
        ),
        // Whitespace between the closing quote and the separator.
        (
            doc(
                b"",
                b"",
                &one_function(b"\tlda.str \"a\"  , v0\n"),
                b"[offset:0x40, name_value:a]",
            ),
            "`lda.str` has more operands than the ISA allows".to_owned(),
        ),
        // Literal resolution.
        (
            doc(b"0 0x10 { 1 [ method:ghost, ]}\n", b"", b"", b""),
            "literal method reference `ghost` names no defined function".to_owned(),
        ),
        (
            doc(b"0 0x10 { 1 [ lit_offset:0x99, ]}\n", b"", b"", b""),
            "lit_offset 0x99 names no literal array".to_owned(),
        ),
        // Field values.
        (
            doc(b"", b".record R {\n\tu32 x = zz\n}\n", b"", b""),
            "field value `zz` does not parse as hex".to_owned(),
        ),
        (
            doc(b"", b".record R {\n\tu32 x = \xff\n}\n", b"", b""),
            "field value is not ASCII".to_owned(),
        ),
        (
            doc(b"", b".record R {\n\tf64 x = zz\n}\n", b"", b""),
            "field f64 `zz` does not parse".to_owned(),
        ),
        (
            doc(b"", b".record R {\n\tf64 x = \xff\n}\n", b"", b""),
            "field f64 value is not ASCII".to_owned(),
        ),
        // Code-less function carrying a body.
        (
            doc(
                b"",
                b"",
                b".language ECMAScript\n.function  f() <external> {\n\tnop\n}\n",
                b"",
            ),
            "code-less function (no return type) with a body".to_owned(),
        ),
        // Catch directives.
        (
            doc(b"", b"", &one_function(b"\tnop\n.catch NoComma\n"), b""),
            "malformed .catch directive".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tnop\n.catchfoo a, b, c\n"), b""),
            "malformed .catch directive".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tnop\n.catchall a, b\n"), b""),
            "malformed .catch directive".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tnop\nl1:\nl2:\n.catchall l1, l2, l3\n"), b""),
            "undefined catch label `l3`".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tnop\nl1:\n\tnop\nh:\nl2:\n.catchall l2, l1, h\n"), b""),
            "catch try range out of bounds".to_owned(),
        ),
        (
            doc(b"", b"", &one_function(b"\tnop\nh1:\nl1:\n\tnop\nh2:\nl2:\n.catchall l1, l2, h2, h1\n"), b""),
            "catch handler range out of bounds".to_owned(),
        ),
    ];
    for (input, expected) in cases {
        let err = parse_err(&input);
        assert_eq!(
            err.message,
            expected,
            "input: {}",
            String::from_utf8_lossy(&input)
        );
    }
}

#[test]
fn module_request_must_be_in_the_request_array() {
    let input = doc(
        b"0 0x100 { 1 [\n\tMODULE_REQUEST_ARRAY: {\n\t\t0 : other,\n\t};\n\tModuleTag: STAR_EXPORT, module_request: missing;\n]}\n",
        b".record _ESModuleRecord {\n\tu32 moduleRecordIdx = 0x100\n}\n",
        b"",
        b"",
    );
    let err = parse_err(&input);
    assert_eq!(
        err.message,
        "module_request `missing` not in the request array"
    );
}

#[test]
fn module_array_is_not_an_instruction_operand() {
    // The module marker inside a multi-line STRING operand fools the
    // value classifier into the module form, which the instruction
    // operand path rejects.
    let methods: &[u8] = b".language ECMAScript\n.function any f() <static> {\n\tcreatearraywithbuffer 0x0, { 1 [ string:\"z\n{ [\n\tMODULE_REQUEST_ARRAY: {\n\t};\n]}\n\"\n}\n";
    let input = doc(
        b"",
        b"",
        methods,
        b"[offset:0x40, name_value:z\n{ [\n\tMODULE_REQUEST_ARRAY: {\n\t};\n]}\n]",
    );
    let err = parse_err(&input);
    assert_eq!(err.message, "module array as an instruction operand");
}

// -- A9: the two deliberate hard errors (exact messages) ---------------

#[test]
fn unsupported_constructs_are_hard_errors() {
    let input = doc(
        b"",
        b".record R {\n\tu32 jsonFileContent = 0x40\n}\n",
        b"",
        b"",
    );
    let err = parse_err(&input);
    assert_eq!(
        err.message,
        "jsonFileContent fields are not representable in pandasm text"
    );

    let input = doc(b"", b".record R {\n\ti32 x = 0x1\n}\n", b"", b"");
    let err = parse_err(&input);
    assert_eq!(
        err.message,
        "field initial value on a type the emitter never prints"
    );

    // `typeSummaryOffset` parses to I32(0) when zero and LiteralArrayRef when non-zero.
    let input = doc(
        b"0 0x40 { 1 [ i32:7, ]}\n",
        b".record R0 {\n\tu32 typeSummaryOffset = 0x0\n}\n.record R1 {\n\tu32 typeSummaryOffset = 0x40\n}\n",
        b"",
        b"",
    );
    let parsed = parse_file(&input).expect("typeSummaryOffset fields parse");
    let r0 = parsed.class_by_str("LR0;").expect("R0");
    assert_eq!(r0.fields[0].initial_value, Some(FieldValue::I32(0)));
    let r1 = parsed.class_by_str("LR1;").expect("R1");
    assert_eq!(
        r1.fields[0].initial_value,
        Some(FieldValue::LiteralArrayRef {
            index: LiteralArrayIdx(0),
            source_offset: Some(0x40),
        })
    );
}
