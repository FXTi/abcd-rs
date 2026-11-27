//! Symbol table: names and string constants as lossless identity (`T9`, `#30`,
//! `#72`, `#77`).
//!
//! A [`Sym`] is the *only* way a name or string constant appears in the IR —
//! property names, class descriptors, module specifiers, string literals,
//! regexp patterns, debug names. The table is append-only: interning never
//! invalidates or renumbers an existing [`Sym`] (`T1`).
//!
//! Internally, all display UTF-8 text (both valid Unicode entries and the clean
//! `U+FFFD` display form of lone-surrogate MUTF-8 entries) lives in a single
//! contiguous `Arc`-shared flat arena (`text: String` + `offs: Vec<u32>`), with
//! lone-surrogate wire bytes stored in a sparse `id`-sorted `cold: Vec<Cold>`
//! side table (`#72`). Deduplication tables (`hashbrown::HashTable<u32>`) store
//! bare `u32` indices without duplicating string keys and can be released via
//! [`SymbolTable::drop_index`] once lifting/linking completes while keeping all
//! `&self` queries total.

use std::borrow::Cow;
use std::fmt;
use std::hash::{BuildHasher, RandomState};
use std::sync::Arc;

use hashbrown::HashTable;

use crate::id::Sym;

/// Capacity overflow error returned by [`SymbolTable::try_intern`] and its
/// MUTF-8 variants when the symbol count reaches `u32::MAX` (`Sym(u32::MAX)` is
/// reserved as an unmapped sentinel) or the concatenated UTF-8 text buffer
/// exceeds `u32::MAX` bytes (`#77`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum SymbolTableOverflow {
    /// Entry count reached `u32::MAX` (`Sym(u32::MAX)` is reserved as a sentinel).
    #[error("SymbolTable entry count reached u32::MAX sentinel limit")]
    TooManySymbols,
    /// Concatenated display UTF-8 arena exceeded `u32::MAX` bytes.
    #[error("SymbolTable UTF-8 text arena exceeded u32::MAX bytes")]
    TextArenaOverflow,
}

#[derive(Clone, Debug)]
struct Cold {
    id: u32,
    raw: Box<[u8]>,
}

#[derive(Clone, Debug)]
struct Arena {
    /// Display UTF-8 text of EVERY entry (including clean `U+FFFD` display text
    /// of lossy entries), concatenated in [`Sym`] ID order.
    text: String,
    /// `len() + 1` byte offsets (`offs[0] == 0`, `offs[len] == text.len() as u32`).
    /// Entry `i` is `text[offs[i] as usize .. offs[i + 1] as usize]`.
    offs: Vec<u32>,
    /// Lone-surrogate / ill-formed MUTF-8 entries ONLY, strictly ascending by `id`.
    cold: Vec<Cold>,
}

impl Default for Arena {
    fn default() -> Self {
        Self {
            text: String::new(),
            offs: vec![0],
            cold: Vec::new(),
        }
    }
}

#[derive(Clone)]
struct Index {
    hasher: RandomState,
    /// Lossless UTF-8 entries ONLY -> `Sym.0`.
    utf8: HashTable<u32>,
    /// Lossy MUTF-8 entries ONLY -> index into `arena.cold` (hashed by raw wire bytes).
    raw: HashTable<u32>,
}

impl Index {
    fn new() -> Self {
        Self {
            hasher: RandomState::new(),
            utf8: HashTable::new(),
            raw: HashTable::new(),
        }
    }

    fn rebuild(arena: &Arena) -> Self {
        let n = arena.offs.len().saturating_sub(1);
        let cold_len = arena.cold.len();
        let hasher = RandomState::new();
        let mut utf8 = HashTable::with_capacity(n.saturating_sub(cold_len));
        let mut raw = HashTable::with_capacity(cold_len);

        let mut cold_cur = 0usize;
        for i in 0..n {
            let id = i as u32;
            if arena.cold.get(cold_cur).is_some_and(|c| c.id == id) {
                let raw_bytes: &[u8] = &arena.cold[cold_cur].raw;
                let hash = hasher.hash_one(raw_bytes);
                let cold_idx = cold_cur as u32;
                raw.insert_unique(hash, cold_idx, |&existing_ci| {
                    hasher.hash_one(arena.cold[existing_ci as usize].raw.as_ref())
                });
                cold_cur += 1;
            } else {
                let s = arena_str(arena, i).unwrap_or("");
                let hash = hasher.hash_one(s);
                utf8.insert_unique(hash, id, |&existing_id| {
                    hasher.hash_one(arena_str(arena, existing_id as usize).unwrap_or(""))
                });
            }
        }

        Self { hasher, utf8, raw }
    }
}

#[inline]
fn arena_str(arena: &Arena, idx: usize) -> Option<&str> {
    let start = *arena.offs.get(idx)? as usize;
    let end = *arena.offs.get(idx.checked_add(1)?)? as usize;
    arena.text.get(start..end)
}

#[inline]
const fn check_arena_capacity(
    cur_entries: usize,
    cur_text_len: usize,
    add_bytes: usize,
) -> Result<(u32, u32), SymbolTableOverflow> {
    if cur_entries >= (u32::MAX as usize) || cur_entries.checked_add(2).is_none() {
        return Err(SymbolTableOverflow::TooManySymbols);
    }
    let Some(new_text_len) = cur_text_len.checked_add(add_bytes) else {
        return Err(SymbolTableOverflow::TextArenaOverflow);
    };
    if new_text_len > (u32::MAX as usize) {
        return Err(SymbolTableOverflow::TextArenaOverflow);
    }
    Ok((cur_entries as u32, new_text_len as u32))
}

/// Deduplicating, append-only symbol table supporting both valid UTF-8
/// strings and ECMAScript lone-surrogate MUTF-8 strings (`#30`, `#72`, `#77`).
#[derive(Clone)]
pub struct SymbolTable {
    arena: Arc<Arena>,
    index: Option<Index>,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self {
            arena: Arc::new(Arena::default()),
            index: Some(Index::new()),
        }
    }
}

impl fmt::Debug for SymbolTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SymbolTable")
            .field("len", &self.len())
            .field("lossy_count", &self.lossy_count())
            .field("has_index", &self.has_index())
            .field("arena", &self.arena)
            .finish()
    }
}

impl SymbolTable {
    /// An empty table with an active deduplication index.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Release the hash-table deduplication index while retaining the flat
    /// `Arc`-backed string arena (`#72`).
    ///
    /// All `&self` lookup methods ([`Self::resolve`], [`Self::as_str`],
    /// [`Self::raw_mutf8`], [`Self::get`], [`Self::get_raw_mutf8`],
    /// [`Self::lossy_syms`]) remain total after `drop_index()`. Calling any
    /// `intern*` / `try_intern*` method rebuilds the index automatically.
    pub fn drop_index(&mut self) {
        self.index = None;
    }

    /// Whether the hash-table deduplication index is currently resident.
    #[must_use]
    #[inline]
    pub fn has_index(&self) -> bool {
        self.index.is_some()
    }

    /// Yield every lone-surrogate / ill-formed MUTF-8 [`Sym`] in strictly
    /// ascending ID order (`O(lossy_count)`).
    pub fn lossy_syms(&self) -> impl Iterator<Item = Sym> + '_ {
        self.arena.cold.iter().map(|c| Sym::new(c.id))
    }

    fn ensure_index(&mut self) {
        if self.index.is_none() {
            self.index = Some(Index::rebuild(&self.arena));
        }
    }

    /// Fallibly intern a valid UTF-8 string `s`, returning [`SymbolTableOverflow`]
    /// if the symbol count reaches `u32::MAX` or the concatenated UTF-8 arena
    /// exceeds `u32::MAX` bytes (`#77`).
    pub fn try_intern(&mut self, s: &str) -> Result<Sym, SymbolTableOverflow> {
        self.ensure_index();
        let Some(index) = &mut self.index else {
            unreachable!("ensure_index populated self.index");
        };
        let hash = index.hasher.hash_one(s);
        let arena_ref = &self.arena;
        if let Some(&id) = index
            .utf8
            .find(hash, |&id| arena_str(arena_ref, id as usize) == Some(s))
        {
            return Ok(Sym::new(id));
        }

        let cur_entries = self.arena.offs.len().saturating_sub(1);
        let (new_id, end_off) = check_arena_capacity(cur_entries, self.arena.text.len(), s.len())?;

        let arena = Arc::make_mut(&mut self.arena);
        arena.text.push_str(s);
        arena.offs.push(end_off);
        index.utf8.insert_unique(hash, new_id, |&existing_id| {
            index
                .hasher
                .hash_one(arena_str(arena, existing_id as usize).unwrap_or(""))
        });
        Ok(Sym::new(new_id))
    }

    /// Intern a valid UTF-8 string `s`, returning its [`Sym`]. Interning the
    /// same string twice returns the same id; interning more strings never
    /// changes existing ids (append-only).
    ///
    /// Panics only if the table exceeds `u32::MAX - 1` entries or `u32::MAX`
    /// UTF-8 bytes; use [`Self::try_intern`] for fallible capacity checking.
    pub fn intern(&mut self, s: &str) -> Sym {
        self.try_intern(s).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallibly intern raw MUTF-8 bytes losslessly: valid Unicode sequences
    /// route to [`Self::try_intern`]; lone-surrogate / ill-formed sequences
    /// intern in the byte-keyed cold table deduplicated by exact `raw` bytes.
    pub fn try_intern_raw_mutf8(&mut self, raw: &[u8]) -> Result<Sym, SymbolTableOverflow> {
        if let Some(text) = mutf8_decode_utf8(raw) {
            return self.try_intern(&text);
        }
        self.ensure_index();
        if let Some(sym) = self.find_indexed_raw(raw) {
            return Ok(sym);
        }
        let lossy = String::from_utf8_lossy(raw);
        self.insert_lossy_unchecked(&lossy, raw)
    }

    /// Intern raw MUTF-8 bytes losslessly: valid Unicode sequences intern via
    /// [`Self::intern`]; lone-surrogate sequences intern in the byte-keyed
    /// bucket deduplicated by exact `raw` bytes.
    pub fn intern_raw_mutf8(&mut self, raw: &[u8]) -> Sym {
        self.try_intern_raw_mutf8(raw)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallibly intern a pre-classified lossy MUTF-8 sequence (`raw` has no
    /// lossless UTF-8 `str` form; `lossy` is its replacement display text). If
    /// `raw` is actually lossless MUTF-8/UTF-8, routes to [`Self::try_intern`]
    /// so duplicate UTF-8 vs raw symbols can never be created (`R2-M9`).
    pub fn try_intern_lossy_raw(
        &mut self,
        lossy: &str,
        raw: &[u8],
    ) -> Result<Sym, SymbolTableOverflow> {
        if let Some(text) = mutf8_decode_utf8(raw) {
            return self.try_intern(&text);
        }
        self.ensure_index();
        if let Some(sym) = self.find_indexed_raw(raw) {
            return Ok(sym);
        }
        self.insert_lossy_unchecked(lossy, raw)
    }

    /// Intern a pre-classified lossy MUTF-8 sequence (`raw` has no lossless
    /// UTF-8 `str` form; `lossy` is its replacement display text). If `raw` is
    /// actually lossless MUTF-8/UTF-8, routes to [`Self::intern`] so duplicate
    /// UTF-8 vs raw symbols can never be created (`R2-M9`).
    pub fn intern_lossy_raw(&mut self, lossy: &str, raw: &[u8]) -> Sym {
        self.try_intern_lossy_raw(lossy, raw)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    fn find_indexed_raw(&self, raw: &[u8]) -> Option<Sym> {
        let index = self.index.as_ref()?;
        let hash = index.hasher.hash_one(raw);
        let cold = &self.arena.cold;
        index
            .raw
            .find(hash, |&ci| cold[ci as usize].raw.as_ref() == raw)
            .map(|&ci| Sym::new(cold[ci as usize].id))
    }

    /// Append a verified-lossy `(lossy, raw)` entry that is not yet in `self.index`.
    fn insert_lossy_unchecked(
        &mut self,
        lossy: &str,
        raw: &[u8],
    ) -> Result<Sym, SymbolTableOverflow> {
        let cur_entries = self.arena.offs.len().saturating_sub(1);
        let (new_id, end_off) =
            check_arena_capacity(cur_entries, self.arena.text.len(), lossy.len())?;

        let Some(index) = &mut self.index else {
            unreachable!("caller ensured self.index is Some");
        };
        let hash = index.hasher.hash_one(raw);
        let arena = Arc::make_mut(&mut self.arena);
        let cold_idx = arena.cold.len() as u32;
        arena.text.push_str(lossy);
        arena.offs.push(end_off);
        arena.cold.push(Cold {
            id: new_id,
            raw: Box::from(raw),
        });
        let cold = &arena.cold;
        index.raw.insert_unique(hash, cold_idx, |&existing_ci| {
            index
                .hasher
                .hash_one(cold[existing_ci as usize].raw.as_ref())
        });
        Ok(Sym::new(new_id))
    }

    /// Borrow the exact UTF-8 string if `sym` was interned as valid Unicode;
    /// returns `None` for lone-surrogate entries or foreign/out-of-range ids.
    #[must_use]
    #[inline]
    pub fn as_str(&self, sym: Sym) -> Option<&str> {
        if self.arena.cold.is_empty() {
            return self.resolve(sym);
        }
        match self.arena.cold.binary_search_by_key(&sym.raw(), |c| c.id) {
            Ok(_) => None,
            Err(_) => self.resolve(sym),
        }
    }

    /// Resolve a [`Sym`] back to display UTF-8 (`&str` for valid Unicode,
    /// clean `U+FFFD`-substituted text without synthetic sentinels for lone
    /// surrogates). Returns `None` for an id the table never issued (library
    /// rule: no panics on data).
    #[must_use]
    #[inline]
    pub fn resolve(&self, sym: Sym) -> Option<&str> {
        arena_str(&self.arena, sym.index())
    }

    /// Explicit alias for [`Self::resolve`].
    #[must_use]
    #[inline]
    pub fn to_str_lossy(&self, sym: Sym) -> Option<&str> {
        self.resolve(sym)
    }

    /// Exact original MUTF-8 bytes when `sym` is a lone-surrogate entry;
    /// `None` for valid UTF-8 entries or out-of-range ids.
    #[must_use]
    pub fn raw_mutf8(&self, sym: Sym) -> Option<&[u8]> {
        if self.arena.cold.is_empty() {
            return None;
        }
        let idx = self
            .arena
            .cold
            .binary_search_by_key(&sym.raw(), |c| c.id)
            .ok()?;
        Some(&self.arena.cold[idx].raw)
    }

    /// Canonical MUTF-8 wire bytes for any valid `sym`. ASCII and BMP UTF-8
    /// strings without embedded `U+0000` borrow directly without allocating.
    #[must_use]
    pub fn to_mutf8_bytes(&self, sym: Sym) -> Option<Cow<'_, [u8]>> {
        if let Some(raw) = self.raw_mutf8(sym) {
            return Some(Cow::Borrowed(raw));
        }
        let s = self.resolve(sym)?;
        if s.bytes().all(|b| b != 0 && b < 0xF0) {
            Some(Cow::Borrowed(s.as_bytes()))
        } else {
            Some(Cow::Owned(mutf8_encode(s)))
        }
    }

    /// Exact ECMAScript UTF-16 code units for `sym` (valid Unicode or lone
    /// surrogates).
    #[must_use]
    pub fn utf16_units(&self, sym: Sym) -> Option<Vec<u16>> {
        if let Some(raw) = self.raw_mutf8(sym) {
            return Some(mutf8_to_utf16_lossy(raw));
        }
        let s = self.resolve(sym)?;
        Some(s.encode_utf16().collect())
    }

    /// Look up an already-interned lossless UTF-8 string without mutating.
    ///
    /// Uses `O(1)` hash lookup when [`Self::has_index`] is `true`, or a total
    /// length-prefiltered `O(len)` scan skipping `cold` entries after
    /// [`Self::drop_index`] (`S5`).
    #[must_use]
    pub fn get(&self, s: &str) -> Option<Sym> {
        if let Some(index) = &self.index {
            let hash = index.hasher.hash_one(s);
            return index
                .utf8
                .find(hash, |&id| arena_str(&self.arena, id as usize) == Some(s))
                .copied()
                .map(Sym::new);
        }

        let want_len = u32::try_from(s.len()).ok()?;
        let n = self.len();
        let offs = &self.arena.offs;
        let text = self.arena.text.as_bytes();
        let s_bytes = s.as_bytes();
        let cold = &self.arena.cold;
        let mut cold_cur = 0usize;
        for i in 0..n {
            let id = i as u32;
            if cold.get(cold_cur).is_some_and(|c| c.id == id) {
                cold_cur += 1;
                continue;
            }
            let start = offs[i];
            let end = offs[i + 1];
            if end - start == want_len && &text[start as usize..end as usize] == s_bytes {
                return Some(Sym::new(id));
            }
        }
        None
    }

    /// Look up an already-interned lone-surrogate entry by exact wire bytes.
    ///
    /// Uses `O(1)` hash lookup when [`Self::has_index`] is `true`, or a total
    /// `O(lossy_count)` scan over `cold` after [`Self::drop_index`] (`S5`).
    #[must_use]
    pub fn get_raw_mutf8(&self, raw: &[u8]) -> Option<Sym> {
        if self.index.is_some() {
            return self.find_indexed_raw(raw);
        }
        self.arena
            .cold
            .iter()
            .find(|c| c.raw.as_ref() == raw)
            .map(|c| Sym::new(c.id))
    }

    /// Number of interned symbols.
    #[must_use]
    #[inline]
    pub fn len(&self) -> usize {
        self.arena.offs.len().saturating_sub(1)
    }

    /// Whether the table is empty.
    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Number of lone-surrogate / raw-MUTF-8 symbols in the table.
    #[must_use]
    #[inline]
    pub fn lossy_count(&self) -> usize {
        self.arena.cold.len()
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
    fn symbol_table_is_send_and_sync_shares_arc_backing_and_isolates_cow() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<SymbolTable>();

        let mut t = SymbolTable::new();
        assert!(t.is_empty());
        assert_eq!(t.arena.offs, vec![0]);
        assert!(t.has_index());

        let utf8 = t.intern("shared_utf8_symbol");
        let raw = t.intern_raw_mutf8(&[0xED, 0xA0, 0xB4]);
        let mut cloned = t.clone();

        assert_eq!(
            t.as_str(utf8).unwrap().as_ptr(),
            cloned.as_str(utf8).unwrap().as_ptr(),
            "cloned SymbolTable must share flat Arena UTF-8 backing"
        );
        assert_eq!(
            t.raw_mutf8(raw).unwrap().as_ptr(),
            cloned.raw_mutf8(raw).unwrap().as_ptr(),
            "cloned SymbolTable must share Cold raw backing"
        );
        assert_eq!(
            t.resolve(raw).unwrap().as_ptr(),
            cloned.resolve(raw).unwrap().as_ptr(),
            "cloned SymbolTable must share lossy UTF-8 display backing"
        );

        // Re-interning an already-present symbol must NOT unshare `Arc<Arena>`.
        assert_eq!(cloned.intern("shared_utf8_symbol"), utf8);
        assert!(Arc::ptr_eq(&t.arena, &cloned.arena));

        // Interning a new symbol on `cloned` triggers COW without affecting `t`.
        let extra = cloned.intern("only_in_clone");
        assert!(!Arc::ptr_eq(&t.arena, &cloned.arena));
        assert_eq!(t.len(), 2);
        assert_eq!(cloned.len(), 3);
        assert_eq!(t.get("only_in_clone"), None);
        assert_eq!(t.resolve(extra), None);
        assert_eq!(cloned.as_str(extra), Some("only_in_clone"));
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
        assert_eq!(t.to_str_lossy(a), Some("foo"));
        assert_eq!(t.resolve(b), Some("bar"));
        assert_eq!(t.len(), 102);
    }

    #[test]
    fn resolve_rejects_foreign_ids_without_panicking() {
        let mut t = SymbolTable::new();
        assert_eq!(t.resolve(Sym::new(0)), None);
        assert_eq!(t.as_str(Sym::new(0)), None);
        assert_eq!(t.raw_mutf8(Sym::new(0)), None);
        assert_eq!(t.to_mutf8_bytes(Sym::new(0)), None);
        assert_eq!(t.utf16_units(Sym::new(0)), None);
        assert_eq!(t.resolve(Sym::new(u32::MAX)), None);
        assert_eq!(t.as_str(Sym::new(u32::MAX)), None);

        // Also check foreign ids when `cold` is non-empty (`binary_search` branch).
        let _ = t.intern_raw_mutf8(&[0xED, 0xA0, 0x80]);
        assert_eq!(t.as_str(Sym::new(99)), None);
        assert_eq!(t.as_str(Sym::new(u32::MAX)), None);
        assert_eq!(t.raw_mutf8(Sym::new(u32::MAX)), None);
    }

    #[test]
    fn empty_string_lossy_collision_mutf8_nul_cesu8_and_pua_invariants() {
        // Order 1: lossy interned BEFORE lossless U+FFFD display collision + empty string.
        let mut t1 = SymbolTable::new();
        let empty = t1.intern("");
        let d834 = t1.intern_raw_mutf8(&[0xED, 0xA0, 0xB4]);
        let fffd = t1.intern("\u{FFFD}\u{FFFD}\u{FFFD}");
        let df06 = t1.intern_raw_mutf8(&[0xED, 0xBC, 0x86]);
        let pua = t1.intern("\u{E000}eda0b4\u{F8FF}");

        assert_eq!(t1.as_str(empty), Some(""));
        assert_eq!(t1.resolve(empty), Some(""));
        assert_eq!(t1.raw_mutf8(empty), None);
        assert_eq!(t1.get(""), Some(empty));

        assert_ne!(d834, fffd);
        assert_ne!(d834, df06);
        assert_ne!(fffd, pua);
        assert_eq!(t1.as_str(d834), None);
        assert_eq!(t1.as_str(df06), None);
        assert_eq!(t1.as_str(fffd), Some("\u{FFFD}\u{FFFD}\u{FFFD}"));
        assert_eq!(t1.resolve(d834), Some("\u{FFFD}\u{FFFD}\u{FFFD}"));
        assert_eq!(t1.resolve(df06), Some("\u{FFFD}\u{FFFD}\u{FFFD}"));
        assert_eq!(t1.get("\u{FFFD}\u{FFFD}\u{FFFD}"), Some(fffd));
        assert_eq!(t1.get_raw_mutf8(&[0xED, 0xA0, 0xB4]), Some(d834));
        assert_eq!(t1.get_raw_mutf8(&[0xED, 0xBC, 0x86]), Some(df06));
        assert_eq!(t1.utf16_units(d834), Some(vec![0xD834]));
        assert_eq!(t1.utf16_units(df06), Some(vec![0xDF06]));
        assert_eq!(t1.as_str(pua), Some("\u{E000}eda0b4\u{F8FF}"));
        assert_eq!(t1.lossy_syms().collect::<Vec<_>>(), vec![d834, df06]);

        // Order 2: lossy ONLY (no lossless U+FFFD interned) -> `get("\u{FFFD}...")` MUST be `None`!
        let mut t2 = SymbolTable::new();
        let only_lossy = t2.intern_raw_mutf8(&[0xED, 0xA0, 0xB4]);
        assert_eq!(t2.resolve(only_lossy), Some("\u{FFFD}\u{FFFD}\u{FFFD}"));
        assert_eq!(t2.get("\u{FFFD}\u{FFFD}\u{FFFD}"), None);
        t2.drop_index();
        assert_eq!(t2.get("\u{FFFD}\u{FFFD}\u{FFFD}"), None);
        assert_eq!(t2.get_raw_mutf8(&[0xED, 0xA0, 0xB4]), Some(only_lossy));

        // C0 80 MUTF-8 NUL vs raw 0x00 byte vs CESU-8 surrogate pair vs 4-byte astral UTF-8.
        let mut t3 = SymbolTable::new();
        let nul_utf8 = t3.intern("a\0b");
        let nul_mutf8 = t3.intern_raw_mutf8(&[b'a', 0xC0, 0x80, b'b']);
        assert_eq!(nul_utf8, nul_mutf8);
        assert_eq!(
            t3.to_mutf8_bytes(nul_utf8).as_deref(),
            Some(&[b'a', 0xC0, 0x80, b'b'][..])
        );

        let raw_zero = t3.intern_raw_mutf8(&[b'a', 0x00, b'b']);
        assert_ne!(raw_zero, nul_utf8);
        assert_eq!(t3.as_str(raw_zero), None);
        assert_eq!(t3.raw_mutf8(raw_zero), Some(&[b'a', 0x00, b'b'][..]));

        // U+1F600 (😀): 4-byte UTF-8 `F0 9F 98 80` vs 6-byte CESU-8 `ED A0 BD ED B8 80`.
        let astral_utf8 = t3.intern_raw_mutf8(&[0xF0, 0x9F, 0x98, 0x80]);
        let astral_cesu8 = t3.intern_raw_mutf8(&[0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80]);
        let astral_str = t3.intern("😀");
        assert_eq!(astral_utf8, astral_cesu8);
        assert_eq!(astral_utf8, astral_str);
        assert_eq!(
            t3.to_mutf8_bytes(astral_str).as_deref(),
            Some(&[0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80][..])
        );
        assert_eq!(t3.lossy_count(), 1);
        assert_eq!(t3.lossy_syms().collect::<Vec<_>>(), vec![raw_zero]);
    }

    #[test]
    fn drop_index_preserves_total_queries_and_rebuilds_on_intern() {
        let mut t = SymbolTable::new();
        let s_empty = t.intern("");
        let s_alpha = t.intern("alpha");
        let s_lossy1 = t.intern_raw_mutf8(&[0xED, 0xA0, 0x81]);
        let s_fffd = t.intern("\u{FFFD}\u{FFFD}\u{FFFD}");
        let s_lossy2 = t.intern_lossy_raw("\u{FFFD}", &[0xED, 0xBF, 0xBF]);
        let s_beta = t.intern("beta");

        assert!(t.has_index());
        t.drop_index();
        assert!(!t.has_index());

        // Total `&self` queries without rebuilding `self.index`.
        assert_eq!(t.get(""), Some(s_empty));
        assert_eq!(t.get("alpha"), Some(s_alpha));
        assert_eq!(t.get("\u{FFFD}\u{FFFD}\u{FFFD}"), Some(s_fffd));
        assert_eq!(t.get("\u{FFFD}"), None);
        assert_eq!(t.get("beta"), Some(s_beta));
        assert_eq!(t.get("missing"), None);
        assert_eq!(t.get_raw_mutf8(&[0xED, 0xA0, 0x81]), Some(s_lossy1));
        assert_eq!(t.get_raw_mutf8(&[0xED, 0xBF, 0xBF]), Some(s_lossy2));
        assert_eq!(t.get_raw_mutf8(&[0xED, 0xA0, 0x82]), None);
        assert_eq!(t.lossy_syms().collect::<Vec<_>>(), vec![s_lossy1, s_lossy2]);
        assert!(!t.has_index(), "&self lookups must not rebuild index");

        // Subsequent `intern*` rebuilds the index and deduplicates existing entries.
        assert_eq!(t.intern("alpha"), s_alpha);
        assert!(t.has_index());
        assert_eq!(t.intern_raw_mutf8(&[0xED, 0xA0, 0x81]), s_lossy1);
        let s_gamma = t.intern("gamma");
        assert_eq!(t.len(), 7);
        assert_eq!(t.get("gamma"), Some(s_gamma));
    }

    #[test]
    fn capacity_checks_reserve_u32_max_sentinel_and_catch_text_overflow() {
        // `arena.offs` stores `cur_entries + 1` offsets (`cur_entries + 2` after
        // appending one entry), so 32-bit `usize` caps at `usize::MAX - 2` while
        // 64-bit `usize` caps at `(u32::MAX as usize) - 1` (`Sym(u32::MAX)` sentinel).
        let max_entries = ((u32::MAX as usize) - 1).min(usize::MAX - 2);
        assert_eq!(
            check_arena_capacity(max_entries, 10, 5),
            Ok((max_entries as u32, 15))
        );
        assert_eq!(
            check_arena_capacity(max_entries + 1, 10, 5),
            Err(SymbolTableOverflow::TooManySymbols)
        );
        assert_eq!(
            check_arena_capacity(u32::MAX as usize, 10, 5),
            Err(SymbolTableOverflow::TooManySymbols)
        );
        assert_eq!(
            check_arena_capacity(10, (u32::MAX as usize) - 3, 3),
            Ok((10, u32::MAX))
        );
        assert_eq!(
            check_arena_capacity(10, (u32::MAX as usize) - 3, 4),
            Err(SymbolTableOverflow::TextArenaOverflow)
        );
        assert_eq!(
            check_arena_capacity(10, usize::MAX, 1),
            Err(SymbolTableOverflow::TextArenaOverflow)
        );

        let mut t = SymbolTable::new();
        let a = t.try_intern("ok").unwrap();
        let b = t.try_intern_raw_mutf8(&[0xED, 0xA0, 0x99]).unwrap();
        let c = t
            .try_intern_lossy_raw("\u{FFFD}", &[0xED, 0xA0, 0x99])
            .unwrap();
        assert_eq!(b, c);
        assert_ne!(a, b);
    }
}
