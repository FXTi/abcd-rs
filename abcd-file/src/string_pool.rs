//! Lossless string pool for `.abc` MUTF-8 strings (#30).
//!
//! `.abc` string items are encoded in Modified UTF-8 (MUTF-8: `U+0000` as
//! `C0 80`, astral scalar values as CESU-8 6-byte surrogate pairs, and
//! ECMAScript lone surrogates `U+D800..=U+DFFF` as 3-byte `ED A0..BF 80..BF`
//! sequences). Valid Unicode strings — including embedded `U+0000`, astral
//! planes, and BMP Private Use Area code points (`U+E000..=U+F8FF`, used
//! heavily for HarmonyOS IconFont / SymbolGlyph icons) — are stored as native
//! UTF-8 `Box<str>` entries (`as_str` returns `Some(&str)`).
//!
//! Strings that contain lone surrogates (or ill-formed byte sequences) have
//! no lossless UTF-8 `str` representation; they are stored in a separate
//! byte-keyed bucket carrying BOTH their exact MUTF-8 wire bytes and their
//! replacement-character (`U+FFFD`) display string, with zero sentinel
//! mangling in `str` space.

use std::borrow::Cow;
use std::collections::HashMap;

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
enum PoolEntry {
    /// Lossless valid UTF-8 string.
    Utf8(Box<str>),
    /// MUTF-8 byte sequence with no lossless UTF-8 `str` form (e.g. ECMAScript
    /// lone surrogates). Deduplicated by exact `raw` wire bytes; `lossy` holds
    /// the clean `U+FFFD`-substituted display text (never sentinel-mangled).
    RawMutf8 { raw: Box<[u8]>, lossy: Box<str> },
}

/// Append-only, deduplicating MUTF-8 / UTF-8 string pool.
#[derive(Clone, Debug, Default)]
pub struct StringPool {
    entries: Vec<PoolEntry>,
    utf8_to_id: HashMap<Box<str>, StringId>,
    raw_to_id: HashMap<Box<[u8]>, StringId>,
}

impl StringPool {
    /// Create an empty string pool.
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern a lossless UTF-8 string, returning its stable [`StringId`].
    pub fn get_or_intern<T: AsRef<str>>(&mut self, s: T) -> StringId {
        let s = s.as_ref();
        if let Some(&id) = self.utf8_to_id.get(s) {
            return id;
        }
        let id = StringId(self.entries.len() as u32);
        let boxed: Box<str> = s.into();
        self.entries.push(PoolEntry::Utf8(boxed.clone()));
        self.utf8_to_id.insert(boxed, id);
        id
    }

    /// Intern raw MUTF-8 bytes losslessly:
    /// - If `raw` decodes to valid Unicode (ASCII, BMP including PUA
    ///   `U+E000..=U+F8FF`, `C0 80` NUL, and CESU-8 / UTF-8 astral pairs), it
    ///   interns as a standard UTF-8 entry (sharing the same [`StringId`] as
    ///   [`Self::get_or_intern`]).
    /// - Otherwise (lone surrogates or malformed MUTF-8), it interns as a
    ///   byte-backed entry deduplicated by exact `raw` bytes.
    pub fn intern_mutf8(&mut self, raw: &[u8]) -> StringId {
        if let Some(text) = mutf8_decode_utf8(raw) {
            return self.get_or_intern(&text);
        }
        let lossy = String::from_utf8_lossy(raw);
        self.intern_lossy_raw(&lossy, raw)
    }

    /// Intern a pre-classified lossy MUTF-8 byte sequence (`raw` has no
    /// lossless UTF-8 representation; `lossy` is its replacement display form).
    pub fn intern_lossy_raw(&mut self, lossy: &str, raw: &[u8]) -> StringId {
        if let Some(&id) = self.raw_to_id.get(raw) {
            return id;
        }
        let id = StringId(self.entries.len() as u32);
        let raw_box: Box<[u8]> = raw.into();
        self.entries.push(PoolEntry::RawMutf8 {
            raw: raw_box.clone(),
            lossy: lossy.into(),
        });
        self.raw_to_id.insert(raw_box, id);
        id
    }

    /// Look up an already-interned lossless UTF-8 string without mutating.
    /// Never collides with lossy lone-surrogate entries.
    pub fn get<T: AsRef<str>>(&self, s: T) -> Option<StringId> {
        self.utf8_to_id.get(s.as_ref()).copied()
    }

    /// Look up an already-interned lossy MUTF-8 byte entry by exact wire bytes.
    pub fn get_raw_mutf8(&self, raw: &[u8]) -> Option<StringId> {
        self.raw_to_id.get(raw).copied()
    }

    /// Borrow the exact UTF-8 string if `id` is valid AND lossless (`None` for
    /// lone-surrogate entries or out-of-range IDs).
    pub fn as_str(&self, id: StringId) -> Option<&str> {
        match self.entries.get(id.index())? {
            PoolEntry::Utf8(s) => Some(s),
            PoolEntry::RawMutf8 { .. } => None,
        }
    }

    /// Resolve `id` to a UTF-8 `&str` (exact for lossless strings; clean
    /// `U+FFFD`-substituted display text for lone-surrogate strings, never
    /// carrying synthetic sentinels). Returns `None` for out-of-range IDs.
    pub fn resolve(&self, id: StringId) -> Option<&str> {
        match self.entries.get(id.index())? {
            PoolEntry::Utf8(s) => Some(s),
            PoolEntry::RawMutf8 { lossy, .. } => Some(lossy),
        }
    }

    /// Explicit alias for [`Self::resolve`].
    #[inline]
    pub fn to_str_lossy(&self, id: StringId) -> Option<&str> {
        self.resolve(id)
    }

    /// Exact original MUTF-8 bytes when `id` is a lossy (lone-surrogate) entry;
    /// `None` for lossless UTF-8 entries or out-of-range IDs.
    pub fn raw_mutf8(&self, id: StringId) -> Option<&[u8]> {
        match self.entries.get(id.index())? {
            PoolEntry::Utf8(_) => None,
            PoolEntry::RawMutf8 { raw, .. } => Some(raw),
        }
    }

    /// Canonical MUTF-8 wire bytes for any valid `id`: borrowed verbatim for
    /// lossy entries, encoded on demand for lossless UTF-8 entries.
    pub fn to_mutf8_bytes(&self, id: StringId) -> Option<Cow<'_, [u8]>> {
        match self.entries.get(id.index())? {
            PoolEntry::Utf8(s) => Some(Cow::Owned(mutf8_encode(s))),
            PoolEntry::RawMutf8 { raw, .. } => Some(Cow::Borrowed(raw)),
        }
    }

    /// Lossless UTF-16 code-unit view of `id` (both valid Unicode strings and
    /// lone-surrogate MUTF-8 strings decode to their exact ECMAScript UTF-16
    /// code units).
    pub fn utf16_units(&self, id: StringId) -> Option<Vec<u16>> {
        match self.entries.get(id.index())? {
            PoolEntry::Utf8(s) => Some(s.encode_utf16().collect()),
            PoolEntry::RawMutf8 { raw, .. } => Some(mutf8_to_utf16_lossy(raw)),
        }
    }

    /// Total number of interned entries (lossless + lossy).
    #[inline]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the pool contains zero entries.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Number of lossy (lone-surrogate / raw-MUTF-8) entries in the pool.
    #[inline]
    pub fn lossy_count(&self) -> usize {
        self.raw_to_id.len()
    }

    /// Iterate `(id, lossy_or_exact_str)` in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = (StringId, &str)> {
        self.entries.iter().enumerate().map(|(i, e)| {
            let s: &str = match e {
                PoolEntry::Utf8(s) => s,
                PoolEntry::RawMutf8 { lossy, .. } => lossy,
            };
            (StringId(i as u32), s)
        })
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
        for i in 0..ids.len() {
            for j in (i + 1)..ids.len() {
                assert_ne!(ids[i], ids[j], "collision between {i} and {j}");
            }
        }
        assert_eq!(pool.intern_mutf8(&raw_hi), id_hi);
        assert_eq!(pool.intern_mutf8(&raw_lo), id_lo);
        assert_eq!(pool.get(pua_icon), Some(id_pua));
        assert_eq!(pool.get(fake_sentinel), Some(id_fake));
        assert_eq!(pool.get(replacement), Some(id_repl));
        assert_eq!(pool.lossy_count(), 2);

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
    }
}
