use std::ffi::{CStr, c_char};
use std::marker::PhantomData;

use abcd_file_sys as sys;
use abcd_isa::Version;

use crate::error::Error;

pub(crate) const ABSENT: u32 = u32::MAX;

/// ABC file handle.
///
/// Borrows the underlying byte slice for its lifetime, ensuring the data
/// remains valid while the file is open.
pub struct AbcFile<'data> {
    pub(crate) raw: *mut sys::AbcFileHandle,
    _data: PhantomData<&'data [u8]>,
}

impl<'data> AbcFile<'data> {
    /// Open an ABC file from a byte slice.
    pub fn open(data: &'data [u8]) -> Result<Self, Error> {
        // SAFETY: `data` is a valid byte slice of `data.len()` bytes; `abc_file_open`
        // copies the input into a 16-byte zero-padded C++ buffer before returning.
        let raw = unsafe { sys::abc_file_open(data.as_ptr(), data.len()) };
        if raw.is_null() {
            // SAFETY: `abc_file_open_error` returns a thread-local NUL-terminated
            // C string populated by the failed `abc_file_open` call on this thread.
            let reason = unsafe { CStr::from_ptr(sys::abc_file_open_error()) }
                .to_string_lossy()
                .into_owned();
            return Err(Error::Open(reason));
        }
        Ok(Self {
            raw,
            _data: PhantomData,
        })
    }

    /// Open an ABC file without allocating a C++ copy buffer by borrowing a
    /// slice whose last 16 bytes are zero padding (`orig_len = padded_data.len() - 16`).
    pub fn open_zeropadded(padded_data: &'data [u8]) -> Result<Self, Error> {
        // SAFETY: `padded_data` is valid for `padded_data.len()` bytes and borrows
        // `'data`, outliving the returned `AbcFile<'data>`.
        let raw = unsafe { sys::abc_file_open_zeropadded(padded_data.as_ptr(), padded_data.len()) };
        if raw.is_null() {
            // SAFETY: `abc_file_open_error` returns a thread-local NUL-terminated
            // C string populated by the failed `abc_file_open_zeropadded` call.
            let reason = unsafe { CStr::from_ptr(sys::abc_file_open_error()) }
                .to_string_lossy()
                .into_owned();
            return Err(Error::Open(reason));
        }
        Ok(Self {
            raw,
            _data: PhantomData,
        })
    }

    /// File format version.
    pub fn version(&self) -> Version {
        let mut out = [0u8; 4];
        // SAFETY: `self.raw` is a live `AbcFileHandle` and `out` has 4 writable bytes.
        unsafe { sys::abc_file_version(self.raw, out.as_mut_ptr()) };
        Version::from(out)
    }

    /// Adler-32 checksum stored in the file header.
    #[inline]
    pub fn checksum(&self) -> u32 {
        // SAFETY: `self.raw` is a live `AbcFileHandle`.
        unsafe { sys::abc_file_checksum(self.raw) }
    }

    /// Total file size in bytes.
    #[inline]
    pub fn size(&self) -> u32 {
        // SAFETY: `self.raw` is a live `AbcFileHandle`.
        unsafe { sys::abc_file_size(self.raw) }
    }
}

impl Drop for AbcFile<'_> {
    fn drop(&mut self) {
        // SAFETY: `self.raw` was created by `abc_file_open` / `abc_file_open_zeropadded`
        // and is closed once here on drop.
        unsafe { sys::abc_file_close(self.raw) };
    }
}

/// File type detection from raw bytes (does not require opening the file).
pub fn file_type(data: &[u8]) -> sys::FileType {
    if data.len() < 8 {
        return sys::FileType::Invalid;
    }
    let Ok(len) = i32::try_from(data.len()) else {
        return sys::FileType::Invalid;
    };
    // SAFETY: `data` has at least 8 readable bytes and `len` equals `data.len()`.
    let t = unsafe { sys::abc_file_get_type(data.as_ptr(), len) };
    sys::FileType::try_from(t).unwrap_or(sys::FileType::Invalid)
}

// --- Internal helpers ---

/// Bounded 32-bit unsigned LEB128 reader (at most 5 bytes, rejecting overflow
/// past 32 bits). Advances `*sp` on success.
#[inline]
pub(crate) fn read_uleb128_slice(sp: &mut &[u8]) -> Option<u32> {
    let mut result = 0u32;
    for i in 0..5usize {
        let &b = sp.get(i)?;
        if i == 4 && (b & 0xF0) != 0 {
            return None;
        }
        result |= u32::from(b & 0x7F) << (7 * i);
        if (b & 0x80) == 0 {
            *sp = &sp[i + 1..];
            return Some(result);
        }
    }
    None
}

/// Validated zero-allocation ASCII `StringItem` fast path: checks
/// `offset > sizeof(Header)` (`60`), ULEB128 `tag_len`, exact `0x00` NUL byte
/// at `utf16_len`, and all payload bytes in `0x01..=0x7F` (each 1 UTF-16 unit,
/// matching `convert_string_utf16_bounded`).
#[inline]
pub(crate) fn try_ascii_string_item(file_bytes: &[u8], offset: u32) -> Option<&str> {
    if offset <= 60 {
        return None;
    }
    let mut sp = file_bytes.get(offset as usize..)?;
    let tag_len = read_uleb128_slice(&mut sp)?;
    let utf16_len = (tag_len >> 1) as usize;
    if sp.len() <= utf16_len || sp[utf16_len] != 0 {
        return None;
    }
    let payload = &sp[..utf16_len];
    if !payload.iter().all(|&b| (1..=0x7F).contains(&b)) {
        return None;
    }
    std::str::from_utf8(payload).ok()
}

/// Read a string from the file, converting to a Rust String.
///
/// Uses the bridge's MUTF-8 → UTF-16 conversion (lossless for the whole
/// Unicode range: NUL, surrogate pairs, astral characters) and falls back
/// to the raw-byte view if the conversion is unavailable or malformed.
pub(crate) fn read_string(file: *const sys::AbcFileHandle, offset: u32) -> Option<String> {
    read_string_reporting_lossy(file, offset).map(|(text, _)| text)
}

/// `read_string` plus the exact lossiness signal: the flag is true ONLY
/// when the lossless UTF-16 conversion failed (MUTF-8 lone surrogates —
/// Rust `String` cannot hold them) and the raw-byte lossy fallback
/// produced the text. A CESU-8-encoded astral character (old writers
/// emit per-unit 3-byte forms) is NOT lossy — it converts through
/// UTF-16 like any 4-byte form (N72).
pub(crate) fn read_string_reporting_lossy(
    file: *const sys::AbcFileHandle,
    offset: u32,
) -> Option<(String, bool)> {
    let mut scratch = Vec::new();
    read_string_reporting_lossy_with_scratch(file, offset, &mut scratch)
}

fn read_string_reporting_lossy_with_scratch(
    file: *const sys::AbcFileHandle,
    offset: u32,
    utf16_scratch: &mut Vec<u16>,
) -> Option<(String, bool)> {
    // SAFETY: `file` is a valid `AbcFileHandle`; passing a null destination
    // buffer with capacity 0 queries the validated UTF-16 unit count.
    let units = unsafe { sys::abc_file_get_string_utf16(file, offset, std::ptr::null_mut(), 0) };
    if units == usize::MAX {
        return None;
    }
    if units == 0 {
        return Some((String::new(), false));
    }
    utf16_scratch.clear();
    utf16_scratch.resize(units, 0);
    // SAFETY: `file` is valid and `utf16_scratch` holds `units` writable `u16` elements.
    let written =
        unsafe { sys::abc_file_get_string_utf16(file, offset, utf16_scratch.as_mut_ptr(), units) };
    if written != units {
        return None;
    }
    if let Ok(s) = String::from_utf16(utf16_scratch) {
        return Some((s, false));
    }

    // Fallback: raw bytes (lossy — only reached for lone-surrogate strings).
    // SAFETY: `file` is valid; null buffer queries the bounded byte length.
    let len = unsafe { sys::abc_file_get_string(file, offset, std::ptr::null_mut(), 0) };
    if len == 0 {
        return None;
    }
    let mut buf = vec![0u8; len.checked_add(1)?];
    // SAFETY: `file` is valid and `buf` has `len + 1` writable bytes.
    unsafe {
        sys::abc_file_get_string(file, offset, buf.as_mut_ptr().cast::<c_char>(), buf.len());
    }
    let cstr = CStr::from_bytes_until_nul(&buf).ok()?;
    Some((cstr.to_string_lossy().into_owned(), true))
}

/// Read the RAW MUTF-8 bytes of the string at `offset` (NUL-free by
/// construction — MUTF-8 encodes U+0000 as `C0 80`). `None` for an
/// invalid offset or an empty string (an empty string is never lossy, so
/// it never needs a raw-bytes record — see
/// [`crate::model::File::string_raw_bytes`], N72).
pub(crate) fn read_string_raw_bytes(
    file: *const sys::AbcFileHandle,
    offset: u32,
) -> Option<Vec<u8>> {
    // SAFETY: `file` is valid; null buffer queries the bounded byte length.
    let len = unsafe { sys::abc_file_get_string(file, offset, std::ptr::null_mut(), 0) };
    if len == 0 {
        return None;
    }
    let mut buf = vec![0u8; len.checked_add(1)?];
    // SAFETY: `file` is valid and `buf` has `len + 1` writable bytes.
    let copied = unsafe {
        sys::abc_file_get_string(file, offset, buf.as_mut_ptr().cast::<c_char>(), buf.len())
    };
    if copied == 0 {
        return None;
    }
    buf.truncate(copied);
    Some(buf)
}

/// Read the string at `offset` and intern it into `strings`, capturing the
/// exact MUTF-8 wire bytes when the string has no lossless UTF-8 `str`
/// representation (e.g. lone surrogates, #30). Returns `None` for an invalid
/// offset.
pub(crate) fn intern_string(
    file: *const sys::AbcFileHandle,
    offset: u32,
    strings: &mut crate::StringPool,
) -> Option<crate::StringId> {
    let (text, lossy) = read_string_reporting_lossy(file, offset)?;
    if !lossy {
        return Some(strings.get_or_intern(&text));
    }
    match read_string_raw_bytes(file, offset) {
        Some(raw) => Some(strings.intern_lossy_raw(&text, &raw)),
        None => Some(strings.get_or_intern(&text)),
    }
}

/// Compact open-addressed `(u32 -> StringId)` cache keyed by non-`ABSENT` file
/// offsets.
#[derive(Default)]
struct OffsetStringMap {
    slots: Vec<(u32, Option<crate::StringId>)>,
    len: usize,
}

impl OffsetStringMap {
    #[inline]
    fn mix(mut x: u32) -> usize {
        x ^= x >> 16;
        x = x.wrapping_mul(0x7feb_352d);
        x ^= x >> 15;
        x = x.wrapping_mul(0x846c_a68b);
        x ^= x >> 16;
        x as usize
    }

    #[inline]
    fn get(&self, key: u32) -> Option<crate::StringId> {
        if key == ABSENT || self.slots.is_empty() {
            return None;
        }
        let mask = self.slots.len() - 1;
        let mut idx = Self::mix(key) & mask;
        loop {
            let (cur_k, cur_v) = self.slots[idx];
            if cur_k == key {
                return cur_v;
            }
            if cur_k == ABSENT {
                return None;
            }
            idx = (idx + 1) & mask;
        }
    }

    fn insert(&mut self, key: u32, val: crate::StringId) {
        if key == ABSENT {
            return;
        }
        if (self.len + 1) * 10 >= self.slots.len() * 7 {
            let new_cap = if self.slots.is_empty() {
                64
            } else {
                self.slots.len() * 2
            };
            self.rehash(new_cap);
        }
        let mask = self.slots.len() - 1;
        let mut idx = Self::mix(key) & mask;
        loop {
            let cur_k = self.slots[idx].0;
            if cur_k == key {
                self.slots[idx].1 = Some(val);
                return;
            }
            if cur_k == ABSENT {
                self.slots[idx] = (key, Some(val));
                self.len += 1;
                return;
            }
            idx = (idx + 1) & mask;
        }
    }

    fn rehash(&mut self, new_cap: usize) {
        let old = std::mem::replace(&mut self.slots, vec![(ABSENT, None); new_cap]);
        let mask = new_cap - 1;
        for (k, v) in old {
            if k == ABSENT {
                continue;
            }
            let mut idx = Self::mix(k) & mask;
            while self.slots[idx].0 != ABSENT {
                idx = (idx + 1) & mask;
            }
            self.slots[idx] = (k, v);
        }
    }
}

/// Per-decode string-item reader & `(offset -> StringId)` memoizer.
///
/// Serves ASCII `StringItem`s directly from `file_bytes` with zero allocations
/// and zero FFI calls while preserving exact `intern_string` (lossy-preserving)
/// and `read_string` (UTF-8) semantics for non-ASCII / lone-surrogate items.
pub(crate) struct StringItemCache<'a> {
    file: *const sys::AbcFileHandle,
    file_bytes: &'a [u8],
    lossy_cache: OffsetStringMap,
    utf8_cache: OffsetStringMap,
    utf16_scratch: Vec<u16>,
}

impl<'a> StringItemCache<'a> {
    pub(crate) fn new(file: *const sys::AbcFileHandle, file_bytes: &'a [u8]) -> Self {
        Self {
            file,
            file_bytes,
            lossy_cache: OffsetStringMap::default(),
            utf8_cache: OffsetStringMap::default(),
            utf16_scratch: Vec::new(),
        }
    }

    /// Equivalent to [`intern_string`]: preserves lone-surrogate wire bytes in
    /// `PoolEntry::RawMutf8`.
    pub(crate) fn intern_lossy(
        &mut self,
        offset: u32,
        strings: &mut crate::StringPool,
    ) -> Option<crate::StringId> {
        if offset <= 60 {
            return None;
        }
        if let Some(sid) = self.lossy_cache.get(offset) {
            return Some(sid);
        }
        if let Some(ascii) = try_ascii_string_item(self.file_bytes, offset) {
            let sid = strings.get_or_intern(ascii);
            self.lossy_cache.insert(offset, sid);
            self.utf8_cache.insert(offset, sid);
            return Some(sid);
        }
        let (text, lossy) =
            read_string_reporting_lossy_with_scratch(self.file, offset, &mut self.utf16_scratch)?;
        let sid = if !lossy {
            let sid = strings.get_or_intern(&text);
            self.utf8_cache.insert(offset, sid);
            sid
        } else {
            match read_string_raw_bytes(self.file, offset) {
                Some(raw) => strings.intern_lossy_raw(&text, &raw),
                None => strings.get_or_intern(&text),
            }
        };
        self.lossy_cache.insert(offset, sid);
        Some(sid)
    }

    /// Equivalent to `read_string(file, offset).map(|s| strings.get_or_intern(&s))`.
    pub(crate) fn intern_utf8(
        &mut self,
        offset: u32,
        strings: &mut crate::StringPool,
    ) -> Option<crate::StringId> {
        if offset <= 60 {
            return None;
        }
        if let Some(sid) = self.utf8_cache.get(offset) {
            return Some(sid);
        }
        if let Some(ascii) = try_ascii_string_item(self.file_bytes, offset) {
            let sid = strings.get_or_intern(ascii);
            self.utf8_cache.insert(offset, sid);
            self.lossy_cache.insert(offset, sid);
            return Some(sid);
        }
        let (text, lossy) =
            read_string_reporting_lossy_with_scratch(self.file, offset, &mut self.utf16_scratch)?;
        let sid = strings.get_or_intern(&text);
        self.utf8_cache.insert(offset, sid);
        if !lossy {
            self.lossy_cache.insert(offset, sid);
        }
        Some(sid)
    }

    /// Equivalent to `read_method_name(mr)` + `strings.get_or_intern`: reads
    /// the method's `name_off` directly from `file_bytes` (`method_off + 4`)
    /// when non-empty ASCII, falling back to `abc_method_get_name_utf16`.
    pub(crate) fn intern_method_name(
        &mut self,
        method_off: u32,
        mr: *const sys::AbcMethodAccessor,
        strings: &mut crate::StringPool,
    ) -> Option<crate::StringId> {
        if let Some(name_off_bytes) = (method_off as usize)
            .checked_add(4)
            .and_then(|start| self.file_bytes.get(start..start + 4))
            && let Ok(arr) = <[u8; 4]>::try_from(name_off_bytes)
        {
            let name_off = u32::from_le_bytes(arr);
            if let Some(ascii) = try_ascii_string_item(self.file_bytes, name_off)
                && !ascii.is_empty()
            {
                let sid = if let Some(cached) = self.utf8_cache.get(name_off) {
                    cached
                } else {
                    let s = strings.get_or_intern(ascii);
                    self.utf8_cache.insert(name_off, s);
                    self.lossy_cache.insert(name_off, s);
                    s
                };
                return Some(sid);
            }
        }
        // SAFETY: `mr` is a valid `AbcMethodAccessor`; null buffer queries unit count.
        let units = unsafe { sys::abc_method_get_name_utf16(mr, std::ptr::null_mut(), 0) };
        if units == 0 {
            return None;
        }
        self.utf16_scratch.clear();
        self.utf16_scratch.resize(units, 0);
        // SAFETY: `mr` is valid and `utf16_scratch` holds `units` writable `u16`s.
        let written =
            unsafe { sys::abc_method_get_name_utf16(mr, self.utf16_scratch.as_mut_ptr(), units) };
        if written != units {
            return None;
        }
        let s = String::from_utf16(&self.utf16_scratch).ok()?;
        Some(strings.get_or_intern(&s))
    }
}

/// Whether the entity at the given offset is in the foreign section.
pub(crate) fn is_external(file: *const sys::AbcFileHandle, offset: u32) -> bool {
    // SAFETY: `file` is a valid `AbcFileHandle`.
    unsafe { sys::abc_file_is_external(file, offset) != 0 }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_string_is_distinct_from_invalid_offset() {
        let mut builder = crate::Builder::new();
        builder.add_foreign_class(""); // A foreign class item is a string.
        let data = builder.finalize().unwrap();
        let file = AbcFile::open(&data).unwrap();
        // SAFETY: `file.raw` is a live `AbcFileHandle`.
        let offset = unsafe { sys::abc_file_class_offset(file.raw, 0) };
        assert_ne!(offset, ABSENT);
        assert_eq!(read_string(file.raw, offset), Some(String::new()));
        assert_eq!(read_string(file.raw, data.len() as u32), None);
        assert_eq!(read_string(file.raw, ABSENT), None);
    }

    /// Build a file whose foreign-class string item carries the MUTF-8
    /// bytes of a lone surrogate (`ED A0 B4` = U+D834).
    fn lossy_string_file() -> (Vec<u8>, u32) {
        const LOSSY: &str = "\u{FFFD}\u{FFFD}\u{FFFD}";
        const RAW: [u8; 3] = [0xED, 0xA0, 0xB4];
        let mut builder = crate::Builder::new();
        builder.add_foreign_class_mutf8(&RAW).unwrap();
        let data = builder.finalize().unwrap();
        let offset = {
            let file = AbcFile::open(&data).unwrap();
            // SAFETY: `file.raw` is a live `AbcFileHandle`.
            let offset = unsafe { sys::abc_file_class_offset(file.raw, 0) };
            assert_ne!(offset, ABSENT);
            assert_eq!(read_string(file.raw, offset), Some(LOSSY.to_string()));
            offset
        };
        (data, offset)
    }

    /// Colliding lone surrogates (`U+D834` and `U+DF06`) and genuine BMP PUA
    /// strings (`U+E000..=U+F8FF`) intern with distinct lossless identities
    /// and zero sentinel mangling (#30).
    #[test]
    fn intern_string_lossless_surrogate_and_pua_coexistence() {
        const LOSSY: &str = "\u{FFFD}\u{FFFD}\u{FFFD}";
        const RAW: [u8; 3] = [0xED, 0xA0, 0xB4];
        const OTHER_RAW: [u8; 3] = [0xED, 0xB4, 0x86];
        let (data, offset) = lossy_string_file();
        let file = AbcFile::open(&data).unwrap();

        let mut strings = crate::StringPool::default();
        let pua_sid = strings.get_or_intern("\u{E000}eda0b4");
        let fffd_sid = strings.get_or_intern(LOSSY);
        let other_sid = strings.intern_mutf8(&OTHER_RAW);

        let first = intern_string(file.raw, offset, &mut strings).expect("string present");
        let dup = intern_string(file.raw, offset, &mut strings).expect("string present");
        assert_eq!(dup, first);
        assert_ne!(first, other_sid);
        assert_ne!(first, fffd_sid);
        assert_ne!(first, pua_sid);

        assert_eq!(strings.as_str(first), None);
        assert_eq!(strings.resolve(first), Some(LOSSY));
        assert_eq!(strings.raw_mutf8(first), Some(&RAW[..]));
        assert_eq!(strings.as_str(pua_sid), Some("\u{E000}eda0b4"));
    }

    /// `read_string_raw_bytes` guards: an invalid offset (the raw reader
    /// reports length 0) and a valid EMPTY string both yield `None` — an
    /// empty string is never lossy, so it never needs a raw-bytes record.
    #[test]
    fn raw_bytes_guards_reject_invalid_offset_and_empty_string() {
        let mut builder = crate::Builder::new();
        builder.add_foreign_class(""); // A foreign class item is a string.
        let data = builder.finalize().unwrap();
        let offset = {
            let file = AbcFile::open(&data).unwrap();
            // SAFETY: `file.raw` is a live `AbcFileHandle`.
            unsafe { sys::abc_file_class_offset(file.raw, 0) }
        };
        let file = AbcFile::open(&data).unwrap();
        assert_eq!(read_string_raw_bytes(file.raw, offset), None);
        assert_eq!(read_string_raw_bytes(file.raw, data.len() as u32), None);
        assert_eq!(read_string_raw_bytes(file.raw, ABSENT), None);
    }

    #[test]
    fn utf16_fill_and_raw_fallback_agree_on_valid_strings() {
        let (data, offset) = lossy_string_file();
        let file = AbcFile::open(&data).unwrap();
        let raw = read_string_raw_bytes(file.raw, offset);
        assert_eq!(raw.as_deref(), Some(&[0xED, 0xA0, 0xB4][..]));
    }

    #[test]
    fn open_zeropadded_borrows_and_rejects_bad_tail_or_bounds() {
        let mut builder = crate::Builder::new();
        builder.add_foreign_class("LForeign;");
        let data = builder.finalize().unwrap();
        let expected = AbcFile::open(&data).unwrap();

        let mut padded = data.clone();
        padded.extend_from_slice(&[0u8; 16]);

        let zf = AbcFile::open_zeropadded(&padded).unwrap();
        assert_eq!(zf.version(), expected.version());
        assert_eq!(zf.checksum(), expected.checksum());
        assert_eq!(zf.size(), expected.size());
        // SAFETY: `zf.raw` is a live `AbcFileHandle`.
        let cls_off = unsafe { sys::abc_file_class_offset(zf.raw, 0) };
        assert_eq!(read_string(zf.raw, cls_off).as_deref(), Some("LForeign;"));
        drop(zf);

        // Every non-zero byte in the 16-byte trailing padding must be rejected.
        for tail_idx in 0..16 {
            let mut bad = padded.clone();
            bad[data.len() + tail_idx] = 1;
            assert!(
                matches!(AbcFile::open_zeropadded(&bad), Err(Error::Open(_))),
                "tail byte {tail_idx} must be rejected"
            );
        }

        // Buffers shorter than Header + 16 must be rejected.
        for len in [0usize, 15, 16, 75] {
            let short = vec![0u8; len];
            assert!(matches!(
                AbcFile::open_zeropadded(&short),
                Err(Error::Open(_))
            ));
        }

        // Declared file_size exceeding logical length (even within padded_len) must fail.
        let mut inflated = padded.clone();
        let bad_size = (data.len() as u32) + 1;
        inflated[16..20].copy_from_slice(&bad_size.to_le_bytes());
        assert!(matches!(
            AbcFile::open_zeropadded(&inflated),
            Err(Error::Open(_))
        ));
    }
}
