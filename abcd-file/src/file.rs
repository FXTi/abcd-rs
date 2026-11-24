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
        let raw = unsafe { sys::abc_file_open(data.as_ptr(), data.len()) };
        if raw.is_null() {
            // SAFETY: abc_file_open_error returns a thread-local NUL-terminated
            // string set by the failed open call.
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
        unsafe { sys::abc_file_version(self.raw, out.as_mut_ptr()) };
        Version::from(out)
    }

    /// Adler-32 checksum stored in the file header.
    #[inline]
    pub fn checksum(&self) -> u32 {
        unsafe { sys::abc_file_checksum(self.raw) }
    }

    /// Total file size in bytes.
    #[inline]
    pub fn size(&self) -> u32 {
        unsafe { sys::abc_file_size(self.raw) }
    }
}

impl Drop for AbcFile<'_> {
    fn drop(&mut self) {
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
    let t = unsafe { sys::abc_file_get_type(data.as_ptr(), len) };
    sys::FileType::try_from(t).unwrap_or(sys::FileType::Invalid)
}

// --- Internal helpers ---

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
    // SAFETY: null buffer queries the UTF-16 unit count. SIZE_MAX denotes
    // failure; zero denotes a valid empty string.
    let units = unsafe { sys::abc_file_get_string_utf16(file, offset, std::ptr::null_mut(), 0) };
    if units == usize::MAX {
        return None;
    }
    if units == 0 {
        return Some((String::new(), false));
    }
    if units > 0 {
        let mut buf = vec![0u16; units];
        // SAFETY: buf holds exactly `units` UTF-16 units.
        let written =
            unsafe { sys::abc_file_get_string_utf16(file, offset, buf.as_mut_ptr(), buf.len()) };
        if written != units {
            return None;
        }
        if let Ok(s) = String::from_utf16(&buf) {
            return Some((s, false));
        }
    }

    // Fallback: raw bytes (lossy — only reached for malformed strings).
    let len = unsafe { sys::abc_file_get_string(file, offset, std::ptr::null_mut(), 0) };
    if len == 0 {
        return None;
    }
    let mut buf = vec![0u8; len.checked_add(1)?];
    unsafe {
        sys::abc_file_get_string(file, offset, buf.as_mut_ptr() as *mut c_char, buf.len());
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
    let len = unsafe { sys::abc_file_get_string(file, offset, std::ptr::null_mut(), 0) };
    if len == 0 {
        return None;
    }
    let mut buf = vec![0u8; len.checked_add(1)?];
    let copied = unsafe {
        sys::abc_file_get_string(file, offset, buf.as_mut_ptr() as *mut c_char, buf.len())
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

/// Whether the entity at the given offset is in the foreign section.
pub(crate) fn is_external(file: *const sys::AbcFileHandle, offset: u32) -> bool {
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
}
