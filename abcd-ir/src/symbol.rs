//! Symbol table: names and string constants as lossless identity (T9, #30).
//!
//! A [`Sym`] is the *only* way a name or string constant appears in the IR —
//! property names, class descriptors, module specifiers, string literals,
//! regexp patterns, debug names. The table is append-only: interning never
//! invalidates or renumbers an existing [`Sym`] (T1).
//!
//! Valid Unicode strings (including embedded `U+0000`, astral planes, and BMP
//! Private Use Area code points `U+E000..=U+F8FF`) are stored as lossless
//! UTF-8 `Arc<str>` entries ([`SymbolTable::as_str`] returns `Some(&str)`).
//! ECMAScript strings containing lone surrogates (`U+D800..=U+DFFF`, encoded
//! in MUTF-8 as `ED A0..BF 80..BF`) are stored in a separate byte-keyed
//! bucket carrying their exact MUTF-8 / UTF-16 identity without any sentinel
//! mangling or side tables on [`crate::Module`].

use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::Arc;

use crate::id::Sym;

#[derive(Clone, Debug)]
enum SymEntry {
    /// Lossless valid UTF-8 string.
    Utf8(Arc<str>),
    /// Lossy MUTF-8 byte sequence (lone surrogates), deduplicated by exact
    /// wire bytes. `lossy` holds the clean `U+FFFD`-substituted display text.
    RawMutf8 { raw: Arc<[u8]>, lossy: Arc<str> },
}

/// Deduplicating, append-only symbol table supporting both valid UTF-8
/// strings and ECMAScript lone-surrogate MUTF-8 strings (#30).
#[derive(Clone, Debug, Default)]
pub struct SymbolTable {
    entries: Vec<SymEntry>,
    utf8_to_sym: HashMap<Arc<str>, Sym>,
    raw_to_sym: HashMap<Arc<[u8]>, Sym>,
}

impl SymbolTable {
    /// An empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern a valid UTF-8 string `s`, returning its [`Sym`]. Interning the
    /// same string twice returns the same id; interning more strings never
    /// changes existing ids (append-only).
    pub fn intern(&mut self, s: &str) -> Sym {
        if let Some(&sym) = self.utf8_to_sym.get(s) {
            return sym;
        }
        let sym = Sym(self.entries.len() as u32);
        let shared: Arc<str> = Arc::from(s);
        self.entries.push(SymEntry::Utf8(Arc::clone(&shared)));
        self.utf8_to_sym.insert(shared, sym);
        sym
    }

    /// Intern raw MUTF-8 bytes losslessly: valid Unicode sequences intern via
    /// [`Self::intern`]; lone-surrogate sequences intern in the byte-keyed
    /// bucket deduplicated by exact `raw` bytes.
    pub fn intern_raw_mutf8(&mut self, raw: &[u8]) -> Sym {
        if let Some(text) = mutf8_decode_utf8(raw) {
            return self.intern(&text);
        }
        if let Some(&sym) = self.raw_to_sym.get(raw) {
            return sym;
        }
        let lossy = String::from_utf8_lossy(raw);
        self.intern_lossy_raw(&lossy, raw)
    }

    /// Intern a pre-classified lossy MUTF-8 sequence (`raw` has no lossless
    /// UTF-8 `str` form; `lossy` is its replacement display text). If `raw` is
    /// actually lossless MUTF-8/UTF-8, routes to [`Self::intern`] so duplicate
    /// UTF-8 vs raw symbols can never be created (`R2-M9`).
    pub fn intern_lossy_raw(&mut self, lossy: &str, raw: &[u8]) -> Sym {
        if let Some(text) = mutf8_decode_utf8(raw) {
            return self.intern(&text);
        }
        if let Some(&sym) = self.raw_to_sym.get(raw) {
            return sym;
        }
        let raw_idx =
            u32::try_from(self.entries.len()).expect("SymbolTable exceeded u32::MAX entries");
        let sym = Sym(raw_idx);
        let raw_arc: Arc<[u8]> = Arc::from(raw);
        self.entries.push(SymEntry::RawMutf8 {
            raw: Arc::clone(&raw_arc),
            lossy: Arc::from(lossy),
        });
        self.raw_to_sym.insert(raw_arc, sym);
        sym
    }

    /// Borrow the exact UTF-8 string if `sym` was interned as valid Unicode;
    /// returns `None` for lone-surrogate entries or foreign/out-of-range ids.
    pub fn as_str(&self, sym: Sym) -> Option<&str> {
        match self.entries.get(sym.index())? {
            SymEntry::Utf8(s) => Some(s),
            SymEntry::RawMutf8 { .. } => None,
        }
    }

    /// Resolve a [`Sym`] back to display UTF-8 (`&str` for valid Unicode,
    /// clean `U+FFFD`-substituted text without synthetic sentinels for lone
    /// surrogates). Returns `None` for an id the table never issued (library
    /// rule: no panics on data).
    pub fn resolve(&self, sym: Sym) -> Option<&str> {
        match self.entries.get(sym.index())? {
            SymEntry::Utf8(s) => Some(s),
            SymEntry::RawMutf8 { lossy, .. } => Some(lossy),
        }
    }

    /// Explicit alias for [`Self::resolve`].
    #[inline]
    pub fn to_str_lossy(&self, sym: Sym) -> Option<&str> {
        self.resolve(sym)
    }

    /// Exact original MUTF-8 bytes when `sym` is a lone-surrogate entry;
    /// `None` for valid UTF-8 entries or out-of-range ids.
    pub fn raw_mutf8(&self, sym: Sym) -> Option<&[u8]> {
        match self.entries.get(sym.index())? {
            SymEntry::Utf8(_) => None,
            SymEntry::RawMutf8 { raw, .. } => Some(raw),
        }
    }

    /// Canonical MUTF-8 wire bytes for any valid `sym`. ASCII and BMP UTF-8
    /// strings without embedded `U+0000` borrow directly without allocating.
    pub fn to_mutf8_bytes(&self, sym: Sym) -> Option<Cow<'_, [u8]>> {
        match self.entries.get(sym.index())? {
            SymEntry::Utf8(s) => {
                if s.bytes().all(|b| b != 0 && b < 0xF0) {
                    Some(Cow::Borrowed(s.as_bytes()))
                } else {
                    Some(Cow::Owned(mutf8_encode(s)))
                }
            }
            SymEntry::RawMutf8 { raw, .. } => Some(Cow::Borrowed(raw)),
        }
    }

    /// Exact ECMAScript UTF-16 code units for `sym` (valid Unicode or lone
    /// surrogates).
    pub fn utf16_units(&self, sym: Sym) -> Option<Vec<u16>> {
        match self.entries.get(sym.index())? {
            SymEntry::Utf8(s) => Some(s.encode_utf16().collect()),
            SymEntry::RawMutf8 { raw, .. } => Some(mutf8_to_utf16_lossy(raw)),
        }
    }

    /// Look up an already-interned lossless UTF-8 string without mutating.
    pub fn get(&self, s: &str) -> Option<Sym> {
        self.utf8_to_sym.get(s).copied()
    }

    /// Look up an already-interned lone-surrogate entry by exact wire bytes.
    pub fn get_raw_mutf8(&self, raw: &[u8]) -> Option<Sym> {
        self.raw_to_sym.get(raw).copied()
    }

    /// Number of interned symbols.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the table is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Number of lone-surrogate / raw-MUTF-8 symbols in the table.
    pub fn lossy_count(&self) -> usize {
        self.raw_to_sym.len()
    }
}

fn mutf8_encode(s: &str) -> Vec<u8> {
    let mut out = Vec::with_capacity(s.len());
    for ch in s.chars() {
        let code = ch as u32;
        if code == 0 {
            out.extend_from_slice(&[0xC0, 0x80]);
        } else if code >= 0x10000 {
            let sub = code - 0x10000;
            for unit in [0xD800 + (sub >> 10), 0xDC00 + (sub & 0x3FF)] {
                out.extend_from_slice(&[
                    0xE0 | (unit >> 12) as u8,
                    0x80 | ((unit >> 6) & 0x3F) as u8,
                    0x80 | (unit & 0x3F) as u8,
                ]);
            }
        } else {
            let mut buf = [0u8; 4];
            out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
        }
    }
    out
}

fn mutf8_to_utf16_lossy(raw: &[u8]) -> Vec<u16> {
    let mut units = Vec::with_capacity(raw.len());
    let mut i = 0;
    while i < raw.len() {
        let b0 = raw[i];
        if b0 < 0x80 {
            units.push(u16::from(b0));
            i += 1;
        } else if b0 == 0xC0 && i + 1 < raw.len() && raw[i + 1] == 0x80 {
            units.push(0);
            i += 2;
        } else if (0xC2..0xE0).contains(&b0) && i + 1 < raw.len() && (raw[i + 1] & 0xC0) == 0x80 {
            let u = (u16::from(b0 & 0x1F) << 6) | u16::from(raw[i + 1] & 0x3F);
            units.push(u);
            i += 2;
        } else if (0xE0..0xF0).contains(&b0)
            && i + 2 < raw.len()
            && (raw[i + 1] & 0xC0) == 0x80
            && (raw[i + 2] & 0xC0) == 0x80
        {
            let b1 = raw[i + 1];
            if b0 == 0xE0 && b1 < 0xA0 {
                units.push(0xFFFD);
                i += 1;
            } else {
                let u = (u16::from(b0 & 0x0F) << 12)
                    | (u16::from(b1 & 0x3F) << 6)
                    | u16::from(raw[i + 2] & 0x3F);
                units.push(u);
                i += 3;
            }
        } else if (0xF0..=0xF4).contains(&b0)
            && i + 3 < raw.len()
            && let Ok(s) = std::str::from_utf8(&raw[i..i + 4])
            && let Some(ch) = s.chars().next()
        {
            let mut pair = [0u16; 2];
            units.extend_from_slice(ch.encode_utf16(&mut pair));
            i += 4;
        } else {
            units.push(0xFFFD);
            i += 1;
        }
    }
    units
}

fn mutf8_decode_utf8(raw: &[u8]) -> Option<Cow<'_, str>> {
    if !raw.contains(&0)
        && let Ok(s) = std::str::from_utf8(raw)
    {
        return Some(Cow::Borrowed(s));
    }
    let mut units = Vec::with_capacity(raw.len());
    let mut i = 0;
    while i < raw.len() {
        let b0 = raw[i];
        if b0 == 0 {
            return None;
        } else if b0 < 0x80 {
            units.push(u16::from(b0));
            i += 1;
        } else if b0 == 0xC0 && i + 1 < raw.len() && raw[i + 1] == 0x80 {
            units.push(0);
            i += 2;
        } else if (0xC2..0xE0).contains(&b0) && i + 1 < raw.len() && (raw[i + 1] & 0xC0) == 0x80 {
            let u = (u16::from(b0 & 0x1F) << 6) | u16::from(raw[i + 1] & 0x3F);
            units.push(u);
            i += 2;
        } else if (0xE0..0xF0).contains(&b0)
            && i + 2 < raw.len()
            && (raw[i + 1] & 0xC0) == 0x80
            && (raw[i + 2] & 0xC0) == 0x80
        {
            let b1 = raw[i + 1];
            if b0 == 0xE0 && b1 < 0xA0 {
                return None;
            }
            let u = (u16::from(b0 & 0x0F) << 12)
                | (u16::from(b1 & 0x3F) << 6)
                | u16::from(raw[i + 2] & 0x3F);
            units.push(u);
            i += 3;
        } else if (0xF0..=0xF4).contains(&b0)
            && i + 3 < raw.len()
            && let Ok(s) = std::str::from_utf8(&raw[i..i + 4])
            && let Some(ch) = s.chars().next()
        {
            let mut pair = [0u16; 2];
            units.extend_from_slice(ch.encode_utf16(&mut pair));
            i += 4;
        } else {
            return None;
        }
    }
    String::from_utf16(&units).ok().map(Cow::Owned)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbol_table_is_send_and_sync_and_shares_arc_backing() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<SymbolTable>();

        let mut t = SymbolTable::new();
        let utf8 = t.intern("shared_utf8_symbol");
        let raw = t.intern_raw_mutf8(&[0xED, 0xA0, 0xB4]);
        let cloned = t.clone();

        assert_eq!(
            t.as_str(utf8).unwrap().as_ptr(),
            cloned.as_str(utf8).unwrap().as_ptr(),
            "cloned SymbolTable must share Arc<str> backing"
        );
        assert_eq!(
            t.raw_mutf8(raw).unwrap().as_ptr(),
            cloned.raw_mutf8(raw).unwrap().as_ptr(),
            "cloned SymbolTable must share Arc<[u8]> backing"
        );
        assert_eq!(
            t.resolve(raw).unwrap().as_ptr(),
            cloned.resolve(raw).unwrap().as_ptr(),
            "cloned SymbolTable must share lossy Arc<str> backing"
        );

        let (key_arc, &mapped) = t.utf8_to_sym.get_key_value("shared_utf8_symbol").unwrap();
        assert_eq!(mapped, utf8);
        assert_eq!(key_arc.as_ptr(), t.as_str(utf8).unwrap().as_ptr());

        let (raw_key_arc, &raw_mapped) =
            t.raw_to_sym.get_key_value(&[0xED, 0xA0, 0xB4][..]).unwrap();
        assert_eq!(raw_mapped, raw);
        assert_eq!(raw_key_arc.as_ptr(), t.raw_mutf8(raw).unwrap().as_ptr());
    }

    #[test]
    fn intern_is_stable_and_deduplicating() {
        let mut t = SymbolTable::new();
        let a = t.intern("foo");
        let b = t.intern("bar");
        assert_ne!(a, b);
        assert_eq!(t.intern("foo"), a);
        for i in 0..100 {
            t.intern(&format!("sym{i}"));
        }
        assert_eq!(t.intern("bar"), b);
        assert_eq!(t.resolve(a), Some("foo"));
        assert_eq!(t.as_str(a), Some("foo"));
        assert_eq!(t.resolve(b), Some("bar"));
        assert_eq!(t.len(), 102);
    }

    #[test]
    fn resolve_rejects_foreign_ids_without_panicking() {
        let t = SymbolTable::new();
        assert_eq!(t.resolve(Sym::new(0)), None);
        assert_eq!(t.as_str(Sym::new(0)), None);
        assert_eq!(t.raw_mutf8(Sym::new(0)), None);
        assert_eq!(t.utf16_units(Sym::new(0)), None);
        assert_eq!(t.resolve(Sym::new(u32::MAX)), None);
    }

    #[test]
    fn lone_surrogates_and_pua_coexist_without_sentinels() {
        let mut t = SymbolTable::new();
        let pua = t.intern("\u{E000}eda0b4");
        let fffd = t.intern("\u{FFFD}\u{FFFD}\u{FFFD}");
        let d834 = t.intern_raw_mutf8(&[0xED, 0xA0, 0xB4]);
        let df06 = t.intern_raw_mutf8(&[0xED, 0xBC, 0x86]);

        assert_ne!(pua, fffd);
        assert_ne!(d834, df06);
        assert_ne!(d834, fffd);
        assert_ne!(df06, pua);

        assert_eq!(t.as_str(pua), Some("\u{E000}eda0b4"));
        assert_eq!(t.as_str(d834), None);
        assert_eq!(t.as_str(df06), None);
        assert_eq!(t.resolve(d834), Some("\u{FFFD}\u{FFFD}\u{FFFD}"));
        assert_eq!(t.resolve(df06), Some("\u{FFFD}\u{FFFD}\u{FFFD}"));
        assert_eq!(t.utf16_units(d834), Some(vec![0xD834]));
        assert_eq!(t.utf16_units(df06), Some(vec![0xDF06]));
    }
}
