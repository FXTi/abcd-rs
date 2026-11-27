//! Lossless flat-arena string pool for `.abc` MUTF-8 strings (`#30`, `#72`, `#77`).
//!
//! `.abc` string items are encoded in Modified UTF-8 (MUTF-8: `U+0000` as
//! `C0 80`, astral scalar values as CESU-8 6-byte surrogate pairs, and
//! ECMAScript lone surrogates `U+D800..=U+DFFF` as 3-byte `ED A0..BF 80..BF`
//! sequences).
//!
//! All display UTF-8 strings (exact UTF-8 for lossless entries and replacement
//! `U+FFFD` display text for lone-surrogate entries) live in a single
//! contiguous `String` arena indexed by `len() + 1` `u32` byte offsets inside
//! `Arc<Arena>` (`O(1)` copy-on-write `clone()`, `O(1)` `resolve()`).
//! Lone-surrogate / ill-formed MUTF-8 entries additionally record their exact
//! wire bytes in `Arena::cold` (sorted strictly ascending by `id`), while
//! deduplication uses SipHash-keyed `hashbrown::HashTable<u32>` indices that
//! can be dropped via [`StringPool::drop_index`] once construction finishes.

#![forbid(unsafe_code)]

use std::borrow::Cow;
use std::fmt;
use std::hash::{BuildHasher, RandomState};
use std::sync::Arc;

use hashbrown::HashTable;

/// Capacity error returned when [`StringPool`] would exceed `< u32::MAX`
/// entries or `< u32::MAX` UTF-8 arena bytes (`#77`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StringPoolOverflow;

impl fmt::Display for StringPoolOverflow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("string pool exceeded u32::MAX entries or UTF-8 arena bytes")
    }
}

impl std::error::Error for StringPoolOverflow {}

/// Handle to an interned entry in [`StringPool`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StringId(u32);

impl StringId {
    /// Construct from a raw 0-based pool index.
    #[inline]
    pub const fn new(raw: u32) -> Self {
        Self(raw)
    }

    /// Underlying `usize` index into [`StringPool`].
    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Debug)]
struct Cold {
    id: u32,
    raw: Box<[u8]>,
}

#[derive(Clone, Debug)]
struct Arena {
    /// Concatenated display UTF-8 text of every entry in `StringId` order
    /// (exact UTF-8 for lossless entries, `U+FFFD` display text for `cold`).
    text: String,
    /// `len() + 1` byte offsets into `text` (`offs[0] == 0`,
    /// `offs[len] == text.len() as u32`).
    offs: Vec<u32>,
    /// Lossy MUTF-8 entries (lone surrogates / ill-formed MUTF-8), strictly
    /// ascending by `id`.
    cold: Vec<Cold>,
}

impl Arena {
    fn new() -> Self {
        Self {
            text: String::new(),
            offs: vec![0],
            cold: Vec::new(),
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.offs.len() - 1
    }

    #[inline]
    fn slice(&self, id: u32) -> Option<&str> {
        let idx = id as usize;
        let start = *self.offs.get(idx)? as usize;
        let end = *self.offs.get(idx + 1)? as usize;
        self.text.get(start..end)
    }

    #[inline]
    fn cold_index(&self, id: u32) -> Option<usize> {
        if self.cold.is_empty() {
            return None;
        }
        self.cold.binary_search_by_key(&id, |c| c.id).ok()
    }
}

impl Default for Arena {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Debug)]
struct Index {
    hasher: RandomState,
    /// Lossless entries ONLY -> `StringId` (`u32`).
    utf8: HashTable<u32>,
    /// Lossy entries ONLY -> index into `Arena::cold` (`u32`).
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
        let hasher = RandomState::new();
        let total = arena.len();
        let cold_len = arena.cold.len();
        let mut utf8 = HashTable::with_capacity(total.saturating_sub(cold_len));
        let mut raw = HashTable::with_capacity(cold_len);

        let mut cold_cur = 0usize;
        for idx in 0..total {
            let id = idx as u32;
            if cold_cur < cold_len && arena.cold[cold_cur].id == id {
                let bytes = &*arena.cold[cold_cur].raw;
                let h = hasher.hash_one(bytes);
                let cidx = cold_cur as u32;
                raw.insert_unique(h, cidx, |&existing_cidx| {
                    hasher.hash_one(&*arena.cold[existing_cidx as usize].raw)
                });
                cold_cur += 1;
            } else if let Some(s) = arena.slice(id) {
                let h = hasher.hash_one(s);
                utf8.insert_unique(h, id, |&existing_id| {
                    hasher.hash_one(arena.slice(existing_id).unwrap_or(""))
                });
            }
        }

        Self { hasher, utf8, raw }
    }
}

/// Append-only, deduplicating flat-arena MUTF-8 / UTF-8 string pool.
#[derive(Clone, Debug)]
pub struct StringPool {
    arena: Arc<Arena>,
    index: Option<Index>,
}

impl Default for StringPool {
    fn default() -> Self {
        Self::new()
    }
}

impl StringPool {
    /// Create an empty string pool with an active deduplication index.
    pub fn new() -> Self {
        Self {
            arena: Arc::new(Arena::new()),
            index: Some(Index::new()),
        }
    }

    /// Drop the transient reverse-lookup hash tables while retaining all
    /// `StringId -> str / MUTF-8` arena data (`#72`).
    ///
    /// Subsequent [`Self::get`] and [`Self::get_raw_mutf8`] calls fall back to
    /// length-prefiltered linear scans without mutating `self`; mutating
    /// `intern` calls automatically rebuild the index if needed.
    pub fn drop_index(&mut self) {
        self.index = None;
    }

    /// Whether the deduplication hash index is currently resident.
    #[inline]
    pub fn has_index(&self) -> bool {
        self.index.is_some()
    }

    /// Iterate all lossy (lone-surrogate / ill-formed MUTF-8) [`StringId`]s in
    /// strictly ascending ID order.
    pub fn lossy_ids(&self) -> impl Iterator<Item = StringId> + '_ {
        self.arena.cold.iter().map(|c| StringId(c.id))
    }

    fn ensure_index(&mut self) -> &mut Index {
        if self.index.is_none() {
            self.index = Some(Index::rebuild(&self.arena));
        }
        match &mut self.index {
            Some(idx) => idx,
            None => unreachable!("index was just populated"),
        }
    }

    fn check_append_bounds(&self, add_bytes: usize) -> Result<(u32, u32), StringPoolOverflow> {
        let next_id_usize = self.arena.len();
        let next_id = u32::try_from(next_id_usize)
            .ok()
            .filter(|&id| id < u32::MAX)
            .ok_or(StringPoolOverflow)?;
        let new_text_len = self
            .arena
            .text
            .len()
            .checked_add(add_bytes)
            .ok_or(StringPoolOverflow)?;
        let end_off = u32::try_from(new_text_len)
            .ok()
            .filter(|&off| off < u32::MAX)
            .ok_or(StringPoolOverflow)?;
        Ok((next_id, end_off))
    }

    /// Fallible counterpart of [`Self::get_or_intern`], enforcing `< u32::MAX`
    /// entry count and UTF-8 arena byte-offset bounds (`#77`).
    pub fn try_get_or_intern<T: AsRef<str>>(
        &mut self,
        s: T,
    ) -> Result<StringId, StringPoolOverflow> {
        let s = s.as_ref();
        self.ensure_index();
        let hash = match &self.index {
            Some(idx) => idx.hasher.hash_one(s),
            None => unreachable!("ensure_index guarantees Some"),
        };
        if let Some(idx) = &self.index
            && let Some(&existing) = idx.utf8.find(hash, |&id| self.arena.slice(id) == Some(s))
        {
            return Ok(StringId(existing));
        }

        let (id, end_off) = self.check_append_bounds(s.len())?;
        let arena = Arc::make_mut(&mut self.arena);
        arena.text.push_str(s);
        arena.offs.push(end_off);

        if let Some(idx) = &mut self.index {
            let hasher = &idx.hasher;
            idx.utf8.insert_unique(hash, id, |&existing_id| {
                hasher.hash_one(arena.slice(existing_id).unwrap_or(""))
            });
        }
        Ok(StringId(id))
    }

    /// Intern a lossless UTF-8 string, returning its stable [`StringId`].
    pub fn get_or_intern<T: AsRef<str>>(&mut self, s: T) -> StringId {
        match self.try_get_or_intern(s) {
            Ok(id) => id,
            Err(e) => panic!("{e}"),
        }
    }

    /// Fallible counterpart of [`Self::intern_mutf8`], enforcing `< u32::MAX`
    /// entry count and UTF-8 arena byte-offset bounds (`#77`).
    pub fn try_intern_mutf8(&mut self, raw: &[u8]) -> Result<StringId, StringPoolOverflow> {
        if !raw.contains(&0)
            && let Ok(s) = std::str::from_utf8(raw)
        {
            return self.try_get_or_intern(s);
        }
        if let Some(text) = mutf8_decode_utf8(raw) {
            return self.try_get_or_intern(&text);
        }
        let lossy = String::from_utf8_lossy(raw);
        self.try_intern_lossy_internal(&lossy, raw)
    }

    /// Intern raw MUTF-8 bytes losslessly:
    /// - If `raw` decodes to valid Unicode (ASCII, BMP including PUA
    ///   `U+E000..=U+F8FF`, `C0 80` NUL, and CESU-8 / UTF-8 astral pairs), it
    ///   interns as a standard UTF-8 entry (sharing the same [`StringId`] as
    ///   [`Self::get_or_intern`]).
    /// - Otherwise (lone surrogates or malformed MUTF-8), it interns as a
    ///   byte-backed entry deduplicated by exact `raw` bytes.
    pub fn intern_mutf8(&mut self, raw: &[u8]) -> StringId {
        match self.try_intern_mutf8(raw) {
            Ok(id) => id,
            Err(e) => panic!("{e}"),
        }
    }

    /// Fallible counterpart of [`Self::intern_lossy_raw`], enforcing `< u32::MAX`
    /// entry count and UTF-8 arena byte-offset bounds (`#77`) and `R2-M9`
    /// lossless MUTF-8 normalization (`#72`).
    pub fn try_intern_lossy_raw(
        &mut self,
        lossy: &str,
        raw: &[u8],
    ) -> Result<StringId, StringPoolOverflow> {
        if !raw.contains(&0)
            && let Ok(s) = std::str::from_utf8(raw)
        {
            return self.try_get_or_intern(s);
        }
        if let Some(text) = mutf8_decode_utf8(raw) {
            return self.try_get_or_intern(&text);
        }
        self.try_intern_lossy_internal(lossy, raw)
    }

    fn try_intern_lossy_internal(
        &mut self,
        lossy: &str,
        raw: &[u8],
    ) -> Result<StringId, StringPoolOverflow> {
        self.ensure_index();
        let hash = match &self.index {
            Some(idx) => idx.hasher.hash_one(raw),
            None => unreachable!("ensure_index guarantees Some"),
        };
        if let Some(idx) = &self.index
            && let Some(&cidx) = idx
                .raw
                .find(hash, |&ci| &*self.arena.cold[ci as usize].raw == raw)
        {
            return Ok(StringId(self.arena.cold[cidx as usize].id));
        }

        let cold_idx = u32::try_from(self.arena.cold.len())
            .ok()
            .filter(|&ci| ci < u32::MAX)
            .ok_or(StringPoolOverflow)?;
        let (id, end_off) = self.check_append_bounds(lossy.len())?;

        let arena = Arc::make_mut(&mut self.arena);
        arena.text.push_str(lossy);
        arena.offs.push(end_off);
        arena.cold.push(Cold {
            id,
            raw: Box::from(raw),
        });

        if let Some(idx) = &mut self.index {
            let hasher = &idx.hasher;
            idx.raw.insert_unique(hash, cold_idx, |&existing_ci| {
                hasher.hash_one(&*arena.cold[existing_ci as usize].raw)
            });
        }
        Ok(StringId(id))
    }

    /// Intern a MUTF-8 byte sequence alongside its replacement display form.
    ///
    /// Per `R2-M9` (`#72`), if `raw` actually decodes to valid Unicode via
    /// [`mutf8_decode_utf8`], this routes to [`Self::get_or_intern`] so
    /// duplicate UTF-8 vs. raw `StringId`s can never be created.
    pub fn intern_lossy_raw(&mut self, lossy: &str, raw: &[u8]) -> StringId {
        match self.try_intern_lossy_raw(lossy, raw) {
            Ok(id) => id,
            Err(e) => panic!("{e}"),
        }
    }

    /// Look up an already-interned lossless UTF-8 string without mutating.
    /// Never collides with lossy lone-surrogate entries.
    pub fn get<T: AsRef<str>>(&self, s: T) -> Option<StringId> {
        let s = s.as_ref();
        if let Some(idx) = &self.index {
            let hash = idx.hasher.hash_one(s);
            return idx
                .utf8
                .find(hash, |&id| self.arena.slice(id) == Some(s))
                .map(|&id| StringId(id));
        }

        let target_len = s.len();
        let offs = &self.arena.offs;
        let text = &self.arena.text;
        let cold = &self.arena.cold;
        let mut cold_cur = 0usize;
        let total = self.len();
        for i in 0..total {
            let id = i as u32;
            if cold_cur < cold.len() && cold[cold_cur].id == id {
                cold_cur += 1;
                continue;
            }
            let start = offs[i] as usize;
            let end = offs[i + 1] as usize;
            if end - start == target_len && text.get(start..end) == Some(s) {
                return Some(StringId(id));
            }
        }
        None
    }

    /// Look up an already-interned lossy MUTF-8 byte entry by exact wire bytes.
    pub fn get_raw_mutf8(&self, raw: &[u8]) -> Option<StringId> {
        if let Some(idx) = &self.index {
            let hash = idx.hasher.hash_one(raw);
            return idx
                .raw
                .find(hash, |&ci| &*self.arena.cold[ci as usize].raw == raw)
                .map(|&ci| StringId(self.arena.cold[ci as usize].id));
        }

        let target_len = raw.len();
        self.arena
            .cold
            .iter()
            .find(|c| c.raw.len() == target_len && &*c.raw == raw)
            .map(|c| StringId(c.id))
    }

    /// Borrow the exact UTF-8 string if `id` is valid AND lossless (`None` for
    /// lone-surrogate entries or out-of-range IDs).
    pub fn as_str(&self, id: StringId) -> Option<&str> {
        if self.arena.cold.is_empty() {
            return self.arena.slice(id.0);
        }
        if self.arena.cold_index(id.0).is_some() {
            return None;
        }
        self.arena.slice(id.0)
    }

    /// Resolve `id` to a UTF-8 `&str` (exact for lossless strings; clean
    /// `U+FFFD`-substituted display text for lone-surrogate strings, never
    /// carrying synthetic sentinels). Returns `None` for out-of-range IDs.
    #[inline]
    pub fn resolve(&self, id: StringId) -> Option<&str> {
        self.arena.slice(id.0)
    }

    /// Explicit alias for [`Self::resolve`].
    #[inline]
    pub fn to_str_lossy(&self, id: StringId) -> Option<&str> {
        self.resolve(id)
    }

    /// Exact original MUTF-8 bytes when `id` is a lossy (lone-surrogate) entry;
    /// `None` for lossless UTF-8 entries or out-of-range IDs.
    pub fn raw_mutf8(&self, id: StringId) -> Option<&[u8]> {
        let cidx = self.arena.cold_index(id.0)?;
        Some(&self.arena.cold[cidx].raw)
    }

    /// Canonical MUTF-8 wire bytes for any valid `id`: borrowed verbatim for
    /// lossy entries and for lossless ASCII/BMP strings without `U+0000`,
    /// or encoded as canonical MUTF-8 (`C0 80` NUL, 6-byte CESU-8 astral pairs)
    /// when needed.
    pub fn to_mutf8_bytes(&self, id: StringId) -> Option<Cow<'_, [u8]>> {
        if let Some(raw) = self.raw_mutf8(id) {
            return Some(Cow::Borrowed(raw));
        }
        let s = self.arena.slice(id.0)?;
        Some(mutf8_encode_cow(s))
    }

    /// Lossless UTF-16 code-unit view of `id` (both valid Unicode strings and
    /// lone-surrogate MUTF-8 strings decode to their exact ECMAScript UTF-16
    /// code units).
    pub fn utf16_units(&self, id: StringId) -> Option<Vec<u16>> {
        if let Some(raw) = self.raw_mutf8(id) {
            return Some(mutf8_to_utf16_lossy(raw));
        }
        let s = self.arena.slice(id.0)?;
        Some(s.encode_utf16().collect())
    }

    /// Total number of interned entries (lossless + lossy).
    #[inline]
    pub fn len(&self) -> usize {
        self.arena.len()
    }

    /// Whether the pool contains zero entries.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Number of lossy (lone-surrogate / raw-MUTF-8) entries in the pool.
    #[inline]
    pub fn lossy_count(&self) -> usize {
        self.arena.cold.len()
    }

    /// Iterate `(id, lossy_or_exact_str)` in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = (StringId, &str)> {
        let total = self.len();
        (0..total).map(move |i| {
            let id = i as u32;
            (StringId(id), self.arena.slice(id).unwrap_or(""))
        })
    }
}

/// Borrow `s` directly when its UTF-8 bytes are already canonical `es2abc`
/// MUTF-8 (no `U+0000` and no 4-byte astral sequence `>= 0xF0`), or allocate
/// via [`mutf8_encode`] otherwise (`O(n)` scan, zero allocations for ASCII/BMP).
pub fn mutf8_encode_cow(s: &str) -> Cow<'_, [u8]> {
    if s.bytes().all(|b| b != 0 && b < 0xF0) {
        Cow::Borrowed(s.as_bytes())
    } else {
        Cow::Owned(mutf8_encode(s))
    }
}

/// Encode a valid UTF-8 `&str` as MUTF-8 (`U+0000` → `C0 80`, astral scalar
/// values → 6-byte CESU-8 surrogate pairs, all BMP characters including PUA
/// `U+E000..=U+F8FF` preserved verbatim).
pub fn mutf8_encode(s: &str) -> Vec<u8> {
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

/// Decode MUTF-8 / UTF-8 bytes into UTF-16 code units, degrading malformed
/// byte sequences to `0xFFFD` while preserving lone surrogates (`ED A0..BF
/// 80..BF`) as their exact `0xD800..=0xDFFF` code units.
pub fn mutf8_to_utf16_lossy(raw: &[u8]) -> Vec<u16> {
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
            // Reject overlong 3-byte sequences (`E0 80..9F xx`).
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

/// Strictly decode MUTF-8 / UTF-8 bytes into a lossless Rust `String`.
/// Returns `None` if `raw` contains a raw `0x00` byte (MUTF-8 encodes NUL as
/// `C0 80`), any lone surrogate, or any malformed byte sequence.
pub fn mutf8_decode_utf8(raw: &[u8]) -> Option<String> {
    if !raw.contains(&0)
        && let Ok(s) = std::str::from_utf8(raw)
    {
        return Some(s.to_owned());
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
    String::from_utf16(&units).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pua_and_colliding_lone_surrogates_coexist_losslessly() {
        let mut pool = StringPool::new();
        let pua_icon = "\u{E000}\u{E001}\u{F8FF}";
        let fake_sentinel = "\u{FFFD}\u{FFFD}\u{FFFD}\u{E000}eda0b4";
        let replacement = "\u{FFFD}\u{FFFD}\u{FFFD}";
        let raw_hi = [0xED, 0xA0, 0xB4]; // U+D834
        let raw_lo = [0xED, 0xBC, 0x86]; // U+DF06

        let id_pua = pool.get_or_intern(pua_icon);
        let id_fake = pool.get_or_intern(fake_sentinel);
        let id_repl = pool.get_or_intern(replacement);
        let id_hi = pool.intern_mutf8(&raw_hi);
        let id_lo = pool.intern_mutf8(&raw_lo);

        // Every identity is distinct; re-interning deduplicates cleanly.
        let ids = [id_pua, id_fake, id_repl, id_hi, id_lo];
        for (i, &lhs) in ids.iter().enumerate() {
            for &rhs in &ids[(i + 1)..] {
                assert_ne!(lhs, rhs);
            }
        }
        assert_eq!(pool.intern_mutf8(&raw_hi), id_hi);
        assert_eq!(pool.intern_mutf8(&raw_lo), id_lo);
        assert_eq!(pool.get(pua_icon), Some(id_pua));
        assert_eq!(pool.get(fake_sentinel), Some(id_fake));
        assert_eq!(pool.get(replacement), Some(id_repl));
        assert_eq!(pool.lossy_count(), 2);
        let lossy_vec: Vec<StringId> = pool.lossy_ids().collect();
        assert_eq!(lossy_vec, vec![id_hi, id_lo]);

        // PUA strings round-trip their exact MUTF-8 bytes with zero truncation.
        assert_eq!(pool.as_str(id_pua), Some(pua_icon));
        assert_eq!(
            pool.to_mutf8_bytes(id_pua).as_deref(),
            Some(pua_icon.as_bytes())
        );
        assert_eq!(pool.as_str(id_fake), Some(fake_sentinel));
        assert_eq!(
            pool.to_mutf8_bytes(id_fake).as_deref(),
            Some(fake_sentinel.as_bytes())
        );

        // Lone surrogates report `as_str() == None`, clean `resolve()` without
        // sentinels, exact `raw_mutf8()`, and exact `utf16_units()`.
        assert_eq!(pool.as_str(id_hi), None);
        assert_eq!(pool.as_str(id_lo), None);
        assert_eq!(pool.resolve(id_hi), Some(replacement));
        assert_eq!(pool.resolve(id_lo), Some(replacement));
        assert_eq!(pool.raw_mutf8(id_hi), Some(&raw_hi[..]));
        assert_eq!(pool.raw_mutf8(id_lo), Some(&raw_lo[..]));
        assert_eq!(pool.utf16_units(id_hi), Some(vec![0xD834]));
        assert_eq!(pool.utf16_units(id_lo), Some(vec![0xDF06]));
    }

    #[test]
    fn cesu8_astral_and_mutf8_nul_decode_as_lossless_utf8() {
        let mut pool = StringPool::new();
        // U+0000 (`C0 80`) + U+1F600 (`ED A0 BD ED B8 80`)
        let cesu = [0xC0, 0x80, 0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80];
        let id = pool.intern_mutf8(&cesu);
        assert_eq!(pool.lossy_count(), 0);
        assert_eq!(pool.as_str(id), Some("\0\u{1F600}"));
        assert_eq!(pool.to_mutf8_bytes(id).as_deref(), Some(&cesu[..]));

        // 4-byte UTF-8 astral input (`F0 9F 98 80`) normalizes to the exact
        // same lossless StringId and re-emits canonical 6-byte CESU-8.
        let id_emoji_cesu = pool.intern_mutf8(&[0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80]);
        let id_emoji_utf8 = pool.intern_mutf8("\u{1F600}".as_bytes());
        assert_eq!(id_emoji_cesu, id_emoji_utf8);
        assert_eq!(pool.as_str(id_emoji_cesu), Some("\u{1F600}"));
        assert_eq!(
            pool.to_mutf8_bytes(id_emoji_utf8).as_deref(),
            Some(&[0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80][..])
        );
    }

    #[test]
    fn mutf8_encode_cow_borrows_ascii_and_bmp_without_nul() {
        let mut pool = StringPool::new();
        let ascii = pool.get_or_intern("hello_world");
        let pua = pool.get_or_intern("中\u{E000}\u{F8FF}");
        let nul = pool.get_or_intern("a\0b");
        let astral = pool.get_or_intern("😀");

        assert!(matches!(
            pool.to_mutf8_bytes(ascii),
            Some(Cow::Borrowed(b"hello_world"))
        ));
        assert!(matches!(pool.to_mutf8_bytes(pua), Some(Cow::Borrowed(_))));
        assert!(matches!(pool.to_mutf8_bytes(nul), Some(Cow::Owned(_))));
        assert!(matches!(pool.to_mutf8_bytes(astral), Some(Cow::Owned(_))));
    }

    #[test]
    fn pool_shares_single_arc_allocation_between_entries_and_lookup_maps() {
        let mut pool = StringPool::new();
        let id_utf8 = pool.get_or_intern("shared_utf8_entry");
        let raw_surrogate = [0xED, 0xA0, 0xB4];
        let id_raw = pool.intern_mutf8(&raw_surrogate);

        // Flat arena invariants: offs[0] == 0, offs[len] == text.len(), and a
        // single `Arc<Arena>` backs all strings without duplicate key buffers.
        assert_eq!(pool.arena.offs[0], 0);
        assert_eq!(pool.arena.offs[pool.len()] as usize, pool.arena.text.len());
        assert_eq!(Arc::strong_count(&pool.arena), 1);

        let entry_str = pool.as_str(id_utf8).unwrap();
        let arena_base = pool.arena.text.as_ptr() as usize;
        let arena_end = arena_base + pool.arena.text.len();
        let ptr = entry_str.as_ptr() as usize;
        assert!(
            ptr >= arena_base && ptr + entry_str.len() <= arena_end,
            "resolved UTF-8 slice must point directly into the single flat Arena::text"
        );
        assert_eq!(pool.raw_mutf8(id_raw), Some(&raw_surrogate[..]));

        // Cloning shares the single `Arc<Arena>` without copying text/offs/cold.
        let cloned = pool.clone();
        assert_eq!(Arc::strong_count(&pool.arena), 2);
        assert!(Arc::ptr_eq(&pool.arena, &cloned.arena));
    }

    #[test]
    fn empty_string_vs_lossy_and_r2_m9_intern_lossy_raw_normalization() {
        let mut pool = StringPool::new();
        let raw_lossy = [0xED, 0xA0, 0x80]; // lone high surrogate U+D800
        let id_lossy_empty_display = pool.intern_lossy_raw("", &raw_lossy);
        let id_empty = pool.get_or_intern("");

        assert_ne!(id_lossy_empty_display, id_empty);
        assert_eq!(pool.as_str(id_lossy_empty_display), None);
        assert_eq!(pool.resolve(id_lossy_empty_display), Some(""));
        assert_eq!(pool.as_str(id_empty), Some(""));
        assert_eq!(pool.get(""), Some(id_empty));
        assert_eq!(pool.get_raw_mutf8(&raw_lossy), Some(id_lossy_empty_display));

        // R2-M9: calling `intern_lossy_raw` with valid MUTF-8 / UTF-8 routes to
        // `get_or_intern` and never creates a duplicate cold entry.
        let id_valid_ascii = pool.intern_lossy_raw("bogus", b"hello");
        assert_eq!(id_valid_ascii, pool.get_or_intern("hello"));
        assert_eq!(pool.as_str(id_valid_ascii), Some("hello"));
        assert_eq!(pool.raw_mutf8(id_valid_ascii), None);

        let cesu_pair = [0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80];
        let id_valid_cesu = pool.intern_lossy_raw("\u{FFFD}", &cesu_pair);
        assert_eq!(id_valid_cesu, pool.get_or_intern("😀"));
        assert_eq!(pool.lossy_count(), 1);
    }

    #[test]
    fn lossy_and_lossless_equal_display_fffd_and_drop_index_parity() {
        let mut pool = StringPool::new();
        let fffd = "\u{FFFD}\u{FFFD}\u{FFFD}";
        let raw_a = [0xED, 0xA0, 0xB4];
        let raw_b = [0xED, 0xB4, 0x86];

        // Intern lossy BEFORE lossless with the exact same `U+FFFD` display text.
        let id_a = pool.intern_mutf8(&raw_a);
        let id_fffd = pool.get_or_intern(fffd);
        let id_b = pool.intern_mutf8(&raw_b);
        let id_other = pool.get_or_intern("alpha");

        assert!(pool.has_index());
        assert_eq!(pool.get(fffd), Some(id_fffd));
        assert_eq!(pool.get("alpha"), Some(id_other));
        assert_eq!(pool.get("missing"), None);
        assert_eq!(pool.get_raw_mutf8(&raw_a), Some(id_a));
        assert_eq!(pool.get_raw_mutf8(&raw_b), Some(id_b));

        // Drop index: `get` and `get_raw_mutf8` must stay total and exact
        // without mutating `self` or resurrecting the index.
        pool.drop_index();
        assert!(!pool.has_index());
        assert_eq!(pool.get(fffd), Some(id_fffd));
        assert_eq!(pool.get("alpha"), Some(id_other));
        assert_eq!(pool.get("missing"), None);
        assert_eq!(pool.get_raw_mutf8(&raw_a), Some(id_a));
        assert_eq!(pool.get_raw_mutf8(&raw_b), Some(id_b));
        assert_eq!(pool.get_raw_mutf8(&[0xED, 0xB4, 0x87]), None);
        assert!(!pool.has_index());

        // Subsequent mutation rebuilds the index automatically and preserves IDs.
        assert_eq!(pool.get_or_intern(fffd), id_fffd);
        assert!(pool.has_index());
        assert_eq!(pool.intern_mutf8(&raw_b), id_b);
        let id_new = pool.get_or_intern("beta");
        assert_eq!(pool.get("beta"), Some(id_new));
    }

    #[test]
    fn cow_clone_and_mutation_isolation() {
        let mut base = StringPool::new();
        let id0 = base.get_or_intern("zero");
        let id1 = base.intern_mutf8(&[0xED, 0xA0, 0x81]);

        let mut fork = base.clone();
        assert!(Arc::ptr_eq(&base.arena, &fork.arena));

        // Read hit on fork does not detach COW arena.
        assert_eq!(fork.get_or_intern("zero"), id0);
        assert!(Arc::ptr_eq(&base.arena, &fork.arena));

        // Appending to fork detaches `fork.arena` without mutating `base`.
        let id2 = fork.get_or_intern("two");
        assert!(!Arc::ptr_eq(&base.arena, &fork.arena));
        assert_eq!(base.len(), 2);
        assert_eq!(base.get("two"), None);
        assert_eq!(fork.len(), 3);
        assert_eq!(fork.as_str(id0), Some("zero"));
        assert_eq!(fork.raw_mutf8(id1), Some(&[0xED, 0xA0, 0x81][..]));
        assert_eq!(fork.as_str(id2), Some("two"));
    }

    #[test]
    fn checked_u32_overflow_bounds_surface_typed_error() {
        let mut pool = StringPool::new();
        pool.get_or_intern("seed");
        // Check byte-offset overflow against `< u32::MAX` without allocating 4 GiB:
        assert_eq!(
            pool.check_append_bounds(u32::MAX as usize),
            Err(StringPoolOverflow)
        );
        assert_eq!(
            pool.check_append_bounds((u32::MAX as usize) - pool.arena.text.len()),
            Err(StringPoolOverflow)
        );
    }
}
