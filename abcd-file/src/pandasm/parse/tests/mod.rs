//! Topic-organized unit tests for the pandasm `.pa` parser (`#96`).

mod errors;
mod roundtrip;

use super::{ParseError, parse_file};

/// A minimal but complete pandasm text (one static function).
pub(super) const MINIMAL: &[u8] = b"# source binary: t.abc\n\n# ====================\n# LITERALS\n\n\n# ====================\n# RECORDS\n\n# ====================\n# METHODS\n\n.language ECMAScript\n.function any f() <static> {\n\tldai 0x7\n\treturnundefined\n}\n\n# ====================\n# STRING\n\n";

/// Assemble a four-section pandasm document from section bodies.
pub(super) fn doc(literals: &[u8], records: &[u8], methods: &[u8], strings: &[u8]) -> Vec<u8> {
    let mut v = Vec::new();
    v.extend_from_slice(b"# source binary: t.abc\n\n# ====================\n# LITERALS\n\n");
    v.extend_from_slice(literals);
    v.extend_from_slice(b"# ====================\n# RECORDS\n\n");
    v.extend_from_slice(records);
    v.extend_from_slice(b"# ====================\n# METHODS\n\n");
    v.extend_from_slice(methods);
    v.extend_from_slice(b"# ====================\n# STRING\n\n");
    v.extend_from_slice(strings);
    v
}

/// A methods section carrying one function with the given body lines.
pub(super) fn one_function(body: &[u8]) -> Vec<u8> {
    let mut m = b".language ECMAScript\n.function any f() <static> {\n".to_vec();
    m.extend_from_slice(body);
    m.extend_from_slice(b"}\n");
    m
}

pub(super) fn parse_err(input: &[u8]) -> ParseError {
    parse_file(input).expect_err("document must be rejected")
}
