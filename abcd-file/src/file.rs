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
    let t = unsafe { sys::abc_file_get_type(data.as_ptr(), data.len() as i32) };
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
        let mut buf = vec![0u16; units as usize];
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
    let mut buf = vec![0u8; len + 1];
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
    let mut buf = vec![0u8; len + 1];
    let copied = unsafe {
        sys::abc_file_get_string(file, offset, buf.as_mut_ptr() as *mut c_char, buf.len())
    };
    if copied == 0 {
        return None;
    }
    buf.truncate(copied);
    Some(buf)
}

/// Identity sentinel introducing the raw-bytes disambiguation suffix of a
/// COLLIDING lossy string (N72): two distinct MUTF-8 byte strings whose
/// lossy Rust forms are equal (e.g. `'\u{D834}'` and `'\u{DF06}'` — both
/// decode to three U+FFFD) cannot share one pool identity, or encode
/// could re-emit only one of them. The second and later raw forms for the
/// same lossy content intern as `content + SENTINEL + lowercase hex(raw)`
/// — an identity that is distinct per raw form by construction. U+E000
/// is a deprecated TAGS-plane code point no frontend emits; if a genuine
/// file string ever collides with a synthesized identity, decode fails
/// loudly (`Error::Malformed`) rather than corrupting silently.
pub(crate) const RAW_ID_SENTINEL: char = '\u{E000}';

/// Read the string at `offset` and intern it, capturing the original
/// MUTF-8 bytes for the lossy (lone-surrogate) case and disambiguating
/// pool identities on a raw-form collision (see [`RAW_ID_SENTINEL`]).
/// `None` mirrors [`read_string`]'s invalid-offset case. `Err` is the
/// loud genuine-content collision guard.
pub(crate) fn intern_string(
    file: *const sys::AbcFileHandle,
    offset: u32,
    strings: &mut crate::StringPool,
    string_raw_bytes: &mut std::collections::HashMap<String, Box<[u8]>>,
) -> Result<Option<crate::StringId>, Error> {
    let Some((text, lossy)) = read_string_reporting_lossy(file, offset) else {
        return Ok(None);
    };
    if !lossy {
        // Lossless string (including CESU-8-encoded astral characters):
        // no side record needed.
        return Ok(Some(strings.get_or_intern(&text)));
    }
    let Some(raw) = read_string_raw_bytes(file, offset) else {
        return Ok(Some(strings.get_or_intern(&text)));
    };
    // Classify without holding the map borrow across the inserts below.
    enum Case {
        /// Same lossy content, same raw form (duplicate string-table
        /// entry): reuse the plain identity.
        Duplicate,
        /// First time this lossy content is seen.
        First,
        /// A DIFFERENT raw form for an already-seen lossy content.
        Collision,
    }
    let case = match string_raw_bytes.get(&text) {
        Some(existing) if existing.as_ref() == raw.as_slice() => Case::Duplicate,
        Some(_) => Case::Collision,
        None => Case::First,
    };
    let identity = match case {
        Case::Duplicate => text,
        Case::First => {
            string_raw_bytes.insert(text.clone(), raw.into_boxed_slice());
            text
        }
        Case::Collision => {
            let mut disambiguated = text.clone();
            disambiguated.push(RAW_ID_SENTINEL);
            for b in &raw {
                disambiguated.push_str(&format!("{b:02x}"));
            }
            match string_raw_bytes.get(&disambiguated) {
                Some(existing) => {
                    if existing.as_ref() != raw.as_slice() {
                        return Err(Error::Malformed {
                            field: "string",
                            context: format!(
                                "disambiguated lossy-string identity collision at offset {offset:#x}"
                            ),
                        });
                    }
                }
                None => {
                    // A genuine file string already carrying this exact
                    // identity would corrupt silently — refuse loudly.
                    if strings.get(disambiguated.as_str()).is_some() {
                        return Err(Error::Malformed {
                            field: "string",
                            context: format!(
                                "genuine string collides with a disambiguated \
                                 lossy-string identity at offset {offset:#x}"
                            ),
                        });
                    }
                    string_raw_bytes.insert(disambiguated.clone(), raw.into_boxed_slice());
                }
            }
            disambiguated
        }
    };
    Ok(Some(strings.get_or_intern(&identity)))
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
}
