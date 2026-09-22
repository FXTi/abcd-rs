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
    out.push('"');
    out
}

/// Render a [`Lit`] as its JS literal text (used by the dump; Stage C
/// reuses the same renderer).
pub fn render_lit(lit: &Lit) -> String {
    match lit {
        Lit::Undefined => "undefined".to_string(),
        // The hole has no JS spelling (see expr.rs); annotated.
        Lit::Hole => "undefined/*hole*/".to_string(),
        Lit::Null => "null".to_string(),
        Lit::Bool(b) => b.to_string(),
        Lit::Number(bits) => render_number(*bits),
        Lit::String(s) => render_string(s),
        Lit::BigInt(s) => format!("{s}n"),
        Lit::Array(items) => {
            let inner: Vec<String> = items.iter().map(render_lit).collect();
            format!("[{}]", inner.join(", "))
        }
        Lit::Object(entries) => {
            let inner: Vec<String> = entries
                .iter()
                .map(|(k, v)| format!("{}: {}", render_lit_key(k), render_lit(v)))
                .collect();
            format!("{{{}}}", inner.join(", "))
        }
        Lit::MethodRef(f) => format!("<method fn#{}>", f.index()),
    }
}

/// An object-literal key: identifier form when legal, string form
/// otherwise.
fn render_lit_key(lit: &Lit) -> String {
    if let Lit::String(s) = lit
        && crate::legalize::is_legal_ident(s)
    {
        return s.clone();
    }
    render_lit(lit)
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
}
