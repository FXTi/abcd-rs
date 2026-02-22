//! Index accessor for resolving instruction entity IDs.

use crate::{EntityId, File, error::Error, types::FunctionKind};

/// An index accessor. Borrows from a [`File`].
pub struct Index<'f> {
    handle: *mut abcd_file_sys::AbcIndexAccessor,
    file: &'f File,
    method_off: EntityId,
}

impl<'f> Index<'f> {
    pub(crate) fn open(file: &'f File, method_off: EntityId) -> Result<Self, Error> {
        let handle = unsafe { abcd_file_sys::abc_index_open(file.handle(), method_off.0) };
        if handle.is_null() {
            return Err(Error::Ffi(format!(
                "abc_index_open failed for method at {method_off:?}"
            )));
        }
        Ok(Self {
            handle,
            file,
            method_off,
        })
    }

    /// The method offset this index was opened for.
    pub fn offset(&self) -> EntityId {
        self.method_off
    }

    /// Resolve a 16-bit instruction index to an entity offset.
    ///
    /// Returns `None` when the C++ runtime returns 0 (invalid/unresolvable index).
    /// Note: unlike other resolve methods that use `u32::MAX` as sentinel, the
    /// index accessor uses 0 because ABC file offsets are always > 0 (offset 0
    /// is the file header magic).
    pub fn offset_by_id(&self, idx: u16) -> Option<EntityId> {
        let v = unsafe { abcd_file_sys::abc_index_get_offset_by_id(self.handle, idx) };
        if v == 0 { None } else { Some(EntityId(v)) }
    }

    /// Get the function kind encoded in the method's access flags.
    pub fn function_kind(&self) -> FunctionKind {
        let v = unsafe { abcd_file_sys::abc_index_get_function_kind(self.handle) };
        FunctionKind::from_u8(v).unwrap_or(FunctionKind::None)
    }

    /// Get the index header index for this method.
    pub fn header_index(&self) -> u16 {
        unsafe { abcd_file_sys::abc_index_get_header_index(self.handle) }
    }

    /// Get the total number of index headers.
    pub fn num_headers(&self) -> u32 {
        unsafe { abcd_file_sys::abc_index_get_num_headers(self.handle) }
    }

    pub fn file(&self) -> &'f File {
        self.file
    }
}

impl Drop for Index<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_index_close(self.handle) };
        }
    }
}

impl std::fmt::Debug for Index<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Index")
            .field("method_off", &self.method_off)
            .finish()
    }
}
