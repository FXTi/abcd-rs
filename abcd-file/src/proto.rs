//! Proto (function signature) accessor.

use crate::{EntityId, File, error::Error, types::TypeId};

/// A proto data accessor. Borrows from a [`File`].
pub struct Proto<'f> {
    handle: *mut abcd_file_sys::AbcProtoAccessor,
    file: &'f File,
    off: EntityId,
}

impl<'f> Proto<'f> {
    pub(crate) fn open(file: &'f File, offset: EntityId) -> Result<Self, Error> {
        let handle = unsafe { abcd_file_sys::abc_proto_open(file.handle(), offset.0) };
        if handle.is_null() {
            return Err(Error::Ffi(format!(
                "abc_proto_open failed at offset {offset:?}"
            )));
        }
        Ok(Self {
            handle,
            file,
            off: offset,
        })
    }

    /// The offset in the ABC file where this proto was opened.
    pub fn offset(&self) -> EntityId {
        self.off
    }

    pub fn proto_id(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_proto_get_proto_id(self.handle) })
    }

    pub fn return_type(&self) -> Option<TypeId> {
        TypeId::from_u8(unsafe { abcd_file_sys::abc_proto_get_return_type(self.handle) })
    }

    pub fn num_args(&self) -> u32 {
        unsafe { abcd_file_sys::abc_proto_num_args(self.handle) }
    }

    /// Get the type of argument at `idx`.
    /// Returns `None` if `idx` is out of bounds.
    pub fn arg_type(&self, idx: u32) -> Option<TypeId> {
        if idx >= self.num_args() {
            return None;
        }
        TypeId::from_u8(unsafe { abcd_file_sys::abc_proto_get_arg_type(self.handle, idx) })
    }

    pub fn ref_num(&self) -> u32 {
        unsafe { abcd_file_sys::abc_proto_get_ref_num(self.handle) }
    }

    /// Get the reference type at `idx`.
    /// Returns `None` if `idx` is out of bounds.
    pub fn reference_type(&self, idx: u32) -> Option<EntityId> {
        if idx >= self.ref_num() {
            return None;
        }
        Some(EntityId(unsafe {
            abcd_file_sys::abc_proto_get_reference_type(self.handle, idx)
        }))
    }

    pub fn types(&self) -> Vec<Option<TypeId>> {
        let mut types = Vec::new();
        unsafe extern "C" fn cb(type_id: u8, ctx: *mut std::ffi::c_void) {
            unsafe {
                let v = &mut *(ctx as *mut Vec<Option<TypeId>>);
                v.push(TypeId::from_u8(type_id));
            }
        }
        unsafe {
            abcd_file_sys::abc_proto_enumerate_types(
                self.handle,
                Some(cb),
                &mut types as *mut Vec<Option<TypeId>> as *mut std::ffi::c_void,
            );
        }
        types
    }

    pub fn shorty(&self) -> &[u8] {
        let mut ptr = std::ptr::null();
        let len = unsafe { abcd_file_sys::abc_proto_get_shorty(self.handle, &mut ptr) };
        if ptr.is_null() || len == 0 {
            return &[];
        }
        unsafe { std::slice::from_raw_parts(ptr, len as usize) }
    }

    pub fn size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_proto_get_size(self.handle) }
    }

    pub fn is_equal(&self, other: &Proto) -> bool {
        unsafe { abcd_file_sys::abc_proto_is_equal(self.handle, other.handle) != 0 }
    }

    pub fn file(&self) -> &'f File {
        self.file
    }
}

impl Drop for Proto<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_proto_close(self.handle) };
        }
    }
}

impl std::fmt::Debug for Proto<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Proto").field("offset", &self.off).finish()
    }
}
