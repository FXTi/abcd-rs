//! [`Const`] → [`Lit`] conversion and literal rendering (f64 bit-exact,
//! shortest round-trip; JS string escaping).
//!
//! Number rendering contract (design/decompile.md §5 row 5): raw bits are
//! preserved, so NaN payloads and `-0.0` round-trip exactly; the printed
//! form is the **shortest round-trip representation** — Rust's `Debug`
//! formatter for `f64` emits exactly that (with exponent notation when
//! shorter), and the non-finite values are mapped to their JS spellings
//! (`NaN`, `Infinity`, `-Infinity`).

use abcd_ir::consts::Const;
use abcd_ir::module::Module;
use abcd_ir::{ConstId, Sym};

use crate::expr::Lit;

/// Resolve a [`Sym`] to its string; foreign/unknown ids (library rule:
/// no panics on data) become a visible placeholder.
pub fn sym_str(module: &Module, sym: Sym) -> String {
    module
        .sym
        .resolve(sym)
        .map(str::to_string)
        .unwrap_or_else(|| format!("<sym#{}>", sym.index()))
}

/// Convert a pooled constant to a [`Lit`]; `None` for a [`ConstId`] the
/// pool never issued (data, not a panic).
pub fn lit_of(module: &Module, id: ConstId) -> Option<Lit> {
    const_to_lit(module, module.consts.get(id)?)
}

/// Convert a [`Const`] tree to a [`Lit`] tree (recursive; shapes nest).
pub fn const_to_lit(module: &Module, c: &Const) -> Option<Lit> {
    Some(match c {
        Const::Undefined => Lit::Undefined,
        Const::Hole => Lit::Hole,
        Const::Null => Lit::Null,
        Const::Bool(b) => Lit::Bool(*b),
        Const::Number(bits) => Lit::Number(*bits),
        Const::String(s) => Lit::String(sym_str(module, *s)),
        Const::BigInt(s) => Lit::BigInt(sym_str(module, *s)),
        Const::ArrayLiteral(items) => Lit::Array(
            items
                .iter()
                .map(|i| const_to_lit(module, i))
                .collect::<Option<Vec<_>>>()?,
        ),
        Const::ObjectLiteral { keys, values } => Lit::Object(
            keys.iter()
                .zip(values.iter())
                .map(|(k, v)| Some((const_to_lit(module, k)?, const_to_lit(module, v)?)))
                .collect::<Option<Vec<_>>>()?,
        ),
        Const::MethodRef(f) => Lit::MethodRef(*f),
    })
}

/// Render an `f64` bit pattern as the shortest JS number literal that
/// round-trips to the same bits.
pub fn render_number(bits: u64) -> String {
    let v = f64::from_bits(bits);
    if v.is_nan() {
        // All NaN payloads print as `NaN` (JS has a single NaN literal;
        // the payload survives in the IR but cannot be spelled in JS).
        return "NaN".to_string();
    }
    if v == f64::INFINITY {
        return "Infinity".to_string();
    }
    if v == f64::NEG_INFINITY {
        return "-Infinity".to_string();
    }
    // `{:?}` is the shortest round-trip form (exponent notation when
    // shorter); it prints `-0.0` for negative zero, which JS reads back
    // as exactly -0.
    format!("{v:?}")
}

/// Render a string as a JS double-quoted string literal (deterministic
/// escaping: control characters as short escapes where they exist,
/// `\u{XXXX}` otherwise; non-ASCII printable characters pass through
/// verbatim).
pub fn render_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        push_js_char(&mut out, c);
    }
    out.push('"');
    out
}

/// One scalar value inside a JS double-quoted string literal, per
/// [`render_string`]'s escaping contract (shared with the raw-bytes
/// renderer below so both spellings stay in lockstep).
fn push_js_char(out: &mut String, c: char) {
    match c {
        '"' => out.push_str("\\\""),
        '\\' => out.push_str("\\\\"),
        '\n' => out.push_str("\\n"),
        '\r' => out.push_str("\\r"),
        '\t' => out.push_str("\\t"),
        '\u{08}' => out.push_str("\\b"),
        '\u{0C}' => out.push_str("\\f"),
        '\u{0B}' => out.push_str("\\v"),
        '\0' => out.push_str("\\0"),
        c if (c as u32) < 0x20 || (0x7F..0xA0).contains(&(c as u32)) => {
            out.push_str(&format!("\\u{{{:X}}}", c as u32));
        }
        // Line/paragraph separators are valid in string literals since
        // ES2019 but escaped for maximal parser compatibility.
        '\u{2028}' => out.push_str("\\u{2028}"),
        '\u{2029}' => out.push_str("\\u{2029}"),
        c => out.push(c),
    }
}

/// Decode MUTF-8 bytes (CESU-8: every UTF-16 code unit encoded as up to
/// three bytes; U+0000 as `C0 80`) to UTF-16 code units. A 4-byte UTF-8
/// sequence (not MUTF-8-canonical; defensive) decodes to its scalar's
/// UTF-16 units; a truncated/invalid lead degrades to U+FFFD — data,
/// never a panic.
pub fn mutf8_units(raw: &[u8]) -> Vec<u16> {
    let mut units = Vec::with_capacity(raw.len());
    let mut i = 0;
    while i < raw.len() {
        let b = raw[i];
        if b < 0x80 {
            units.push(b as u16);
            i += 1;
        } else if b >> 5 == 0b110 && i + 1 < raw.len() {
            units.push((((b as u16) & 0x1F) << 6) | ((raw[i + 1] as u16) & 0x3F));
            i += 2;
        } else if b >> 4 == 0b1110 && i + 2 < raw.len() {
            units.push(
                (((b as u16) & 0x0F) << 12)
                    | (((raw[i + 1] as u16) & 0x3F) << 6)
                    | ((raw[i + 2] as u16) & 0x3F),
            );
            i += 3;
        } else if b >> 3 == 0b11110 && i + 3 < raw.len() {
            let cp = (((b as u32) & 0x07) << 18)
                | (((raw[i + 1] as u32) & 0x3F) << 12)
                | (((raw[i + 2] as u32) & 0x3F) << 6)
                | ((raw[i + 3] as u32) & 0x3F);
            match char::from_u32(cp) {
                Some(c) => {
                    let mut buf = [0u16; 2];
                    units.extend_from_slice(c.encode_utf16(&mut buf));
                }
                None => units.push(0xFFFD),
            }
            i += 4;
        } else {
            units.push(0xFFFD);
            i += 1;
        }
    }
    units
}

/// Render UTF-16 code units as the BODY of a JS double-quoted string
/// literal: a well-formed surrogate pair renders as its astral
/// character (es2abc's CESU-8 re-encode is byte-identical to the
/// original pair), a LONE surrogate unit — which has no valid UTF-8
/// spelling — renders as a `\uXXXX` escape (valid JS that es2abc
/// recompiles to exactly the original MUTF-8 bytes, N75); every other
/// unit follows [`render_string`]'s escaping contract.
fn push_units_string_body(out: &mut String, units: &[u16]) {
    let mut i = 0;
    while i < units.len() {
        let u = units[i];
        if (0xD800..0xDC00).contains(&u)
            && i + 1 < units.len()
            && (0xDC00..0xE000).contains(&units[i + 1])
        {
            let cp = 0x10000 + (((u as u32) - 0xD800) << 10) + ((units[i + 1] as u32) - 0xDC00);
            // A well-formed pair always decodes to a scalar value.
            if let Some(c) = char::from_u32(cp) {
                push_js_char(out, c);
            }
            i += 2;
        } else if (0xD800..0xE000).contains(&u) {
            out.push_str(&format!("\\u{u:04X}"));
            i += 1;
        } else {
            // A BMP unit is always a scalar value.
            if let Some(c) = char::from_u32(u as u32) {
                push_js_char(out, c);
            }
            i += 1;
        }
    }
}

/// Render raw MUTF-8 string bytes as a JS double-quoted string literal
/// (see [`push_units_string_body`]).
pub fn render_mutf8_string(raw: &[u8]) -> String {
    let mut out = String::with_capacity(raw.len() + 2);
    out.push('"');
    push_units_string_body(&mut out, &mutf8_units(raw));
    out.push('"');
    out
}

/// Render raw MUTF-8 bytes of a REGEXP pattern (N75): like
/// [`render_mutf8_string`] but for the `/…/` body — no quotes, `/`
/// escaped (mirroring the non-raw `pattern.replace('/', "\\/")` path),
/// line terminators always escaped (they are illegal in a regexp
/// literal even though [`push_js_char`] would pass `\n` as `\\n`, which
/// is also fine here), and lone surrogates as `\uXXXX` escapes.
pub fn render_mutf8_regexp(raw: &[u8]) -> String {
    let mut body = String::new();
    push_units_string_body(&mut body, &mutf8_units(raw));
    body.replace('/', "\\/")
}

/// Render a pooled string as a JS string literal, honoring the module's
/// raw-bytes side table (N75): a string whose pool identity carries
/// original MUTF-8 bytes (lone surrogates have no lossless Rust
/// `String` form — and a colliding identity carries a disambiguation
/// sentinel that must never reach the output) renders from those bytes;
/// anything else renders verbatim.
pub fn render_pool_string(module: &Module, s: &str) -> String {
    match module.string_raw_bytes.get(s) {
        Some(raw) => render_mutf8_string(raw),
        None => render_string(s),
    }
}

/// Render a [`Lit`] as its JS literal text (used by the dump; Stage C
/// reuses the same renderer).
pub fn render_lit(lit: &Lit) -> String {
    render_lit_inner(None, lit)
}

/// [`render_lit`] with the module's raw-bytes side table consulted for
/// string leaves (N75) — the Stage C emission path uses this one.
pub fn render_lit_m(module: &Module, lit: &Lit) -> String {
    render_lit_inner(Some(module), lit)
}

/// The shared [`render_lit`]/[`render_lit_m`] walker.
fn render_lit_inner(module: Option<&Module>, lit: &Lit) -> String {
    match lit {
        Lit::Undefined => "undefined".to_string(),
        // The hole has no JS spelling (see expr.rs); annotated.
        Lit::Hole => "undefined/*hole*/".to_string(),
        Lit::Null => "null".to_string(),
        Lit::Bool(b) => b.to_string(),
        Lit::Number(bits) => render_number(*bits),
        Lit::String(s) => match module {
            Some(m) => render_pool_string(m, s),
            None => render_string(s),
        },
        Lit::BigInt(s) => format!("{s}n"),
        Lit::Array(items) => {
            let inner: Vec<String> = items.iter().map(|i| render_lit_inner(module, i)).collect();
            format!("[{}]", inner.join(", "))
        }
        Lit::Object(entries) => {
            let inner: Vec<String> = entries
                .iter()
                .map(|(k, v)| {
                    format!(
                        "{}: {}",
                        render_lit_key_inner(module, k),
                        render_lit_inner(module, v)
                    )
                })
                .collect();
            format!("{{{}}}", inner.join(", "))
        }
        Lit::MethodRef(f) => format!("<method fn#{}>", f.index()),
    }
}

/// [`render_lit_key_inner`]: an object-literal key: identifier form
/// when legal, string form otherwise.
fn render_lit_key_inner(module: Option<&Module>, lit: &Lit) -> String {
    if let Lit::String(s) = lit
        && crate::legalize::is_legal_ident(s)
    {
        return s.clone();
    }
    render_lit_inner(module, lit)
}

/// Map the vendor RegExp flag bits (arkcompiler
/// `ecmascript/regexp/regexp_parser.h`: FLAG_GLOBAL=1, IGNORECASE=2,
/// MULTILINE=4, DOTALL=8, UTF16=16, STICKY=32, HASINDICES=64) to the JS
/// flag string in canonical `dgimsuy` order.
pub fn render_regexp_flags(bits: u32) -> String {
    let mut out = String::new();
    let table = [
        (1 << 6, 'd'),
        (1 << 0, 'g'),
        (1 << 1, 'i'),
        (1 << 2, 'm'),
        (1 << 3, 's'),
        (1 << 4, 'u'),
        (1 << 5, 'y'),
    ];
    for (bit, flag) in table {
        if bits & bit != 0 {
            out.push(flag);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn number_rendering_is_shortest_round_trip() {
        let cases = [
            0.0f64,
            -0.0,
            1.0,
            -1.5,
            0.1,
            1e300,
            5e-324,
            123456789.0,
            f64::MAX,
            f64::MIN_POSITIVE,
        ];
        for v in cases {
            let text = render_number(v.to_bits());
            let back: f64 = if text == "Infinity" {
                f64::INFINITY
            } else if text == "-Infinity" {
                f64::NEG_INFINITY
            } else {
                text.parse().expect("parseable as JS/Rust number")
            };
            assert_eq!(back.to_bits(), v.to_bits(), "round-trip of {text}");
        }
        assert_eq!(render_number(f64::NAN.to_bits()), "NaN");
        assert_eq!(render_number(f64::INFINITY.to_bits()), "Infinity");
        assert_eq!(render_number(f64::NEG_INFINITY.to_bits()), "-Infinity");
        assert_eq!(render_number((-0.0f64).to_bits()), "-0.0");
        assert_eq!(render_number(1.0f64.to_bits()), "1.0");
        assert_eq!(render_number((1e300f64).to_bits()), "1e300");
    }

    #[test]
    fn string_escaping() {
        assert_eq!(render_string("hello"), "\"hello\"");
        assert_eq!(render_string("a\"b\\c\n"), "\"a\\\"b\\\\c\\n\"");
        assert_eq!(render_string("\u{1}"), "\"\\u{1}\"");
        assert_eq!(render_string("héllo"), "\"héllo\"");
        assert_eq!(render_string("\u{2028}"), "\"\\u{2028}\"");
    }

    #[test]
    fn regexp_flags() {
        assert_eq!(render_regexp_flags(0), "");
        assert_eq!(render_regexp_flags(1), "g");
        assert_eq!(render_regexp_flags(1 | 2 | 16), "giu");
        assert_eq!(render_regexp_flags(64 | 1), "dg");
    }

    #[test]
    fn mutf8_units_decoding() {
        // ASCII.
        assert_eq!(mutf8_units(b"a"), vec![0x61]);
        // 2-byte form (U+00E9).
        assert_eq!(mutf8_units(&[0xC3, 0xA9]), vec![0xE9]);
        // 3-byte form (U+4E2D).
        assert_eq!(mutf8_units(&[0xE4, 0xB8, 0xAD]), vec![0x4E2D]);
        // MUTF-8 NUL (C0 80).
        assert_eq!(mutf8_units(&[0xC0, 0x80]), vec![0x0000]);
        // CESU-8 encoded UTF-16 surrogate unit (no scalar decoding).
        assert_eq!(mutf8_units(&[0xED, 0xA0, 0x80]), vec![0xD800]);
        // A 4-byte UTF-8 sequence (non-canonical MUTF-8) decodes to the
        // scalar's UTF-16 surrogate pair (U+1F600).
        assert_eq!(mutf8_units(&[0xF0, 0x9F, 0x98, 0x80]), vec![0xD83D, 0xDE00]);
        // A 4-byte sequence above U+10FFFF is not a scalar: U+FFFD.
        assert_eq!(mutf8_units(&[0xF4, 0x90, 0x80, 0x80]), vec![0xFFFD]);
        // Truncated / invalid leads degrade to U+FFFD PER BYTE, never
        // panic (a truncated multi-byte lead leaves its continuation
        // bytes to degrade individually).
        assert_eq!(mutf8_units(&[0xC3]), vec![0xFFFD]);
        assert_eq!(mutf8_units(&[0xE4, 0xB8]), vec![0xFFFD, 0xFFFD]);
        assert_eq!(
            mutf8_units(&[0xF0, 0x9F, 0x98]),
            vec![0xFFFD, 0xFFFD, 0xFFFD]
        );
        assert_eq!(mutf8_units(&[0x80]), vec![0xFFFD]);
        // Mixed stream: valid, 2-byte, invalid lead, ASCII.
        assert_eq!(
            mutf8_units(b"a\xC3\xA9\xFFb"),
            vec![0x61, 0xE9, 0xFFFD, 0x62]
        );
    }

    #[test]
    fn mutf8_string_rendering() {
        // A lone surrogate unit renders as a \uXXXX escape (N75).
        assert_eq!(
            render_mutf8_string(&[0x61, 0xED, 0xA0, 0x80]),
            "\"a\\uD800\""
        );
        // A well-formed CESU-8 pair renders as its astral character.
        assert_eq!(
            render_mutf8_string(&[0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80]),
            "\"\u{1F600}\""
        );
        // Ordinary escapes still apply on the unit path.
        assert_eq!(render_mutf8_string(b"a\"b"), "\"a\\\"b\"");
    }

    #[test]
    fn mutf8_regexp_rendering() {
        // `/` is escaped in the regexp body; lone surrogates escape.
        assert_eq!(render_mutf8_regexp(b"a/b"), "a\\/b");
        assert_eq!(render_mutf8_regexp(&[0xED, 0xA0, 0x80]), "\\uD800");
    }

    #[test]
    fn pool_string_raw_bytes() {
        let mut m = Module::new();
        m.string_raw_bytes
            .insert("raw".to_string(), vec![0xED, 0xA0, 0x80].into());
        // A pool identity with raw bytes renders from those bytes.
        assert_eq!(render_pool_string(&m, "raw"), "\"\\uD800\"");
        // Anything else renders verbatim.
        assert_eq!(render_pool_string(&m, "plain"), "\"plain\"");
    }
}
