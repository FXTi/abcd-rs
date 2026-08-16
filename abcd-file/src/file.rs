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

// SAFETY: AbcFileHandle is internally thread-safe (read-only after open).
unsafe impl Send for AbcFile<'_> {}
unsafe impl Sync for AbcFile<'_> {}

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

/// Read a MUTF-8 string from the file, converting to a Rust String.
pub(crate) fn read_string(file: *const sys::AbcFileHandle, offset: u32) -> Option<String> {
    let len = unsafe { sys::abc_file_get_string(file, offset, std::ptr::null_mut(), 0) };
    if len == 0 {
        return None;
    }
    let mut buf = vec![0u8; len + 1];
    unsafe {
        sys::abc_file_get_string(file, offset, buf.as_mut_ptr() as *mut c_char, buf.len());
    }
    let cstr = CStr::from_bytes_until_nul(&buf).ok()?;
    Some(cstr.to_string_lossy().into_owned())
}

/// Whether the entity at the given offset is in the foreign section.
pub(crate) fn is_external(file: *const sys::AbcFileHandle, offset: u32) -> bool {
    unsafe { sys::abc_file_is_external(file, offset) != 0 }
}
