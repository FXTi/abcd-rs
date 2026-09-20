//! Symbol table: names as identity (T9).
//!
//! Replaces v0.1's `StringPool`/`StringId`. A [`Sym`] is the *only* way a
//! name appears in the IR — property names, class descriptors, module
//! specifiers, debug names. The table is append-only: interning never
//! invalidates or renumbers an existing [`Sym`] (T1).

use string_interner::{DefaultStringInterner, DefaultSymbol, Symbol};

use crate::id::Sym;

/// Deduplicating, append-only symbol table backed by `string-interner`
/// (the same backend v0.1 proved on the full corpus).
#[derive(Clone, Debug, Default)]
pub struct SymbolTable {
    inner: DefaultStringInterner,
}

impl SymbolTable {
    /// An empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern `s`, returning its [`Sym`]. Interning the same string twice
    /// returns the same id; interning more strings never changes existing
    /// ids (append-only).
    pub fn intern(&mut self, s: &str) -> Sym {
        Sym(self.inner.get_or_intern(s).to_usize() as u32)
    }

    /// Resolve a [`Sym`] back to its string. Returns `None` for an id the
    /// table never issued (library rule: no panics on data).
    pub fn resolve(&self, sym: Sym) -> Option<&str> {
        let inner = DefaultSymbol::try_from_usize(sym.index())?;
        self.inner.resolve(inner)
    }

    /// Number of interned symbols.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Whether the table is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intern_is_stable_and_deduplicating() {
        let mut t = SymbolTable::new();
        let a = t.intern("foo");
        let b = t.intern("bar");
        assert_ne!(a, b);
        // Same string interns to the same id.
        assert_eq!(t.intern("foo"), a);
        // Existing ids survive further interning (append-only, T1).
        for i in 0..100 {
            t.intern(&format!("sym{i}"));
        }
        assert_eq!(t.intern("bar"), b);
        assert_eq!(t.resolve(a), Some("foo"));
        assert_eq!(t.resolve(b), Some("bar"));
        assert_eq!(t.len(), 102);
    }

    #[test]
    fn resolve_rejects_foreign_ids_without_panicking() {
        let t = SymbolTable::new();
        assert_eq!(t.resolve(Sym::new(0)), None);
        assert_eq!(t.resolve(Sym::new(u32::MAX)), None);
    }
}
