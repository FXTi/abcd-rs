//! The identifier legalizer (design/decompile.md §4.1): every emitted
//! identifier passes through here so that Stage-C output *parses* — the
//! d-P4 recompile gate depends on it.
//!
//! Rules:
//!
//! 1. **Valid JS identifier**: ASCII letters/`_`/`$` start, plus Unicode
//!    letters (approximated by [`char::is_alphabetic`]/`is_alphanumeric` —
//!    close enough to ID_Start/ID_Continue for corpus names, documented);
//!    anything else becomes `_`.
//! 2. **No reserved words** (full ES2022 keyword + future-reserved +
//!    strict-reserved set, plus `undefined`/`arguments`/`eval` which are
//!    legal but shadow-hostile): a trailing `_` is appended.
//! 3. **Collision-disambiguated per scope**: a [`Legalizer`] owns a
//!    used-name set (one per function); collisions get `$1`, `$2`, …
//!    suffixes in first-come-first-served order (deterministic).
//!
//! Special forms (`this`, `super`, `new.target`, `globalThis`) never pass
//! through here — they are not declared names.

use std::collections::HashSet;

/// The reserved-word set: ES2022 keywords, future reserved words,
/// strict-mode reserved words, and the shadow-hostile-but-legal trio
/// (`undefined`, `arguments`, `eval`).
const RESERVED: &[&str] = &[
    // Keywords (ECMA-262 §12.7.2).
    "await",
    "break",
    "case",
    "catch",
    "class",
    "const",
    "continue",
    "debugger",
    "default",
    "delete",
    "do",
    "else",
    "enum",
    "export",
    "extends",
    "false",
    "finally",
    "for",
    "function",
    "if",
    "import",
    "in",
    "instanceof",
    "new",
    "null",
    "return",
    "super",
    "switch",
    "this",
    "throw",
    "true",
    "try",
    "typeof",
    "var",
    "void",
    "while",
    "with",
    "yield",
    // Future reserved.
    "enum",
    // Strict-mode reserved.
    "implements",
    "interface",
    "let",
    "package",
    "private",
    "protected",
    "public",
    "static",
    // Legal but shadow-hostile.
    "undefined",
    "arguments",
    "eval",
];

/// Whether `s` is a reserved (or shadow-hostile) word.
pub fn is_reserved(s: &str) -> bool {
    RESERVED.contains(&s)
}

/// Whether `s` is already a valid, non-reserved JS identifier.
pub fn is_legal_ident(s: &str) -> bool {
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !is_ident_start(first) {
        return false;
    }
    chars.all(is_ident_part) && !is_reserved(s)
}

fn is_ident_start(c: char) -> bool {
    c == '_' || c == '$' || c.is_ascii_alphabetic() || (c as u32) > 0x7F && c.is_alphabetic()
}

fn is_ident_part(c: char) -> bool {
    is_ident_start(c) || c.is_ascii_digit() || (c as u32) > 0x7F && c.is_alphanumeric()
}

/// Sanitize `raw` into a valid, non-reserved identifier shape (rule 1+2,
/// WITHOUT collision handling): invalid characters become `_`, an empty
/// result becomes `"_"`, a reserved word gets a trailing `_`.
pub fn sanitize(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len() + 1);
    for (i, c) in raw.chars().enumerate() {
        let ok = if i == 0 {
            is_ident_start(c)
        } else {
            is_ident_part(c)
        };
        out.push(if ok { c } else { '_' });
    }
    if out.is_empty() {
        out.push('_');
    }
    // A leading digit slipped through when `raw` started with one: the
    // first-char rule replaced it with `_` only if it wasn't a valid
    // start — digits aren't, so this is already handled. Double-check:
    if out.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        out.insert(0, '_');
    }
    if is_reserved(&out) {
        out.push('_');
    }
    out
}

/// A per-function legalizer: sanitizes AND disambiguates against every
/// name previously minted in the same scope.
#[derive(Default, Debug)]
pub struct Legalizer {
    used: HashSet<String>,
}

impl Legalizer {
    /// A fresh legalizer (empty scope).
    pub fn new() -> Self {
        Self::default()
    }

    /// Mint a legal, collision-free identifier from `raw`. Deterministic:
    /// the same sequence of calls yields the same names.
    pub fn mint(&mut self, raw: &str) -> String {
        let base = sanitize(raw);
        if self.used.insert(base.clone()) {
            return base;
        }
        for n in 1u32.. {
            let candidate = format!("{base}${n}");
            if self.used.insert(candidate.clone()) {
                return candidate;
            }
        }
        unreachable!()
    }

    /// Reserve a name WITHOUT minting it (e.g. `this` must never be
    /// handed out as a temp name).
    pub fn reserve(&mut self, name: &str) {
        self.used.insert(name.to_string());
    }

    /// Whether `name` is already taken in this scope.
    pub fn is_used(&self, name: &str) -> bool {
        self.used.contains(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sanitize_shapes() {
        assert_eq!(sanitize("foo"), "foo");
        assert_eq!(sanitize("class"), "class_");
        assert_eq!(sanitize("hello world"), "hello_world");
        assert_eq!(sanitize("2fast"), "_fast");
        assert_eq!(sanitize(""), "_");
        assert_eq!(sanitize("a-b.c"), "a_b_c");
        assert_eq!(sanitize("let"), "let_");
        assert_eq!(sanitize("yield"), "yield_");
        assert_eq!(sanitize("$ok"), "$ok");
        assert_eq!(sanitize("_ok_2"), "_ok_2");
    }

    #[test]
    fn collision_disambiguation_is_deterministic() {
        let mut l = Legalizer::new();
        assert_eq!(l.mint("x"), "x");
        assert_eq!(l.mint("x"), "x$1");
        assert_eq!(l.mint("x$1"), "x$1$1"); // the shape itself is taken
        assert_eq!(l.mint("x"), "x$2");
        assert_eq!(l.mint("class"), "class_");
        assert_eq!(l.mint("class"), "class_$1");
    }

    #[test]
    fn legality_check() {
        assert!(is_legal_ident("foo"));
        assert!(!is_legal_ident("class"));
        assert!(!is_legal_ident("2x"));
        assert!(!is_legal_ident(""));
        assert!(!is_legal_ident("arguments"));
    }
}
