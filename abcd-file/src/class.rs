//! Class data accessor.

use crate::{EntityId, File, collect_entity_ids, error::Error, types::SourceLang};
use std::ffi::CStr;

/// A class data accessor. Borrows from a [`File`].
pub struct Class<'f> {
    handle: *mut abcd_file_sys::AbcClassAccessor,
    file: &'f File,
    off: EntityId,
}

impl<'f> Class<'f> {
    pub(crate) fn open(file: &'f File, offset: EntityId) -> Result<Self, Error> {
        let handle = unsafe { abcd_file_sys::abc_class_open(file.handle(), offset.0) };
        if handle.is_null() {
            return Err(Error::Ffi(format!(
                "abc_class_open failed at offset {offset:?}"
            )));
        }
        Ok(Self {
            handle,
            file,
            off: offset,
        })
    }

    /// The offset in the ABC file where this class was opened.
    pub fn offset(&self) -> EntityId {
        self.off
    }

    pub fn super_class_off(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_class_super_class_off(self.handle) })
    }

    pub fn access_flags(&self) -> u32 {
        unsafe { abcd_file_sys::abc_class_access_flags(self.handle) }
    }

    pub fn num_fields(&self) -> u32 {
        unsafe { abcd_file_sys::abc_class_num_fields(self.handle) }
    }

    pub fn num_methods(&self) -> u32 {
        unsafe { abcd_file_sys::abc_class_num_methods(self.handle) }
    }

    pub fn size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_class_size(self.handle) }
    }

    pub fn source_file_off(&self) -> Option<EntityId> {
        let off = unsafe { abcd_file_sys::abc_class_source_file_off(self.handle) };
        if off == u32::MAX {
            None
        } else {
            Some(EntityId(off))
        }
    }

    pub fn source_lang(&self) -> Option<SourceLang> {
        let v = unsafe { abcd_file_sys::abc_class_get_source_lang(self.handle) };
        if v == u8::MAX {
            None
        } else {
            SourceLang::from_u8(v)
        }
    }

    pub fn class_id(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_class_get_class_id(self.handle) })
    }

    pub fn name(&self) -> Result<String, Error> {
        let len =
            unsafe { abcd_file_sys::abc_class_get_name(self.handle, std::ptr::null_mut(), 0) };
        if len == 0 {
            return Ok(String::new());
        }
        let mut buf = vec![0u8; len];
        let written = unsafe {
            abcd_file_sys::abc_class_get_name(
                self.handle,
                buf.as_mut_ptr() as *mut std::ffi::c_char,
                buf.len(),
            )
        };
        buf.truncate(written);
        String::from_utf8(buf).map_err(|e| Error::Ffi(e.to_string()))
    }

    pub fn descriptor(&self) -> &[u8] {
        let ptr = unsafe { abcd_file_sys::abc_class_get_descriptor(self.handle) };
        if ptr.is_null() {
            return &[];
        }
        // SAFETY: The C++ side returns a null-terminated MUTF-8 string.
        let cstr = unsafe { CStr::from_ptr(ptr as *const std::ffi::c_char) };
        cstr.to_bytes()
    }

    pub fn num_interfaces(&self) -> u32 {
        unsafe { abcd_file_sys::abc_class_get_ifaces_number(self.handle) }
    }

    pub fn interface_id(&self, idx: u32) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_class_get_interface_id(self.handle, idx) })
    }

    pub fn interface_ids(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_class_enumerate_interfaces(self.handle, Some(cb), ctx);
        })
    }

    pub fn method_offsets(&self) -> Vec<EntityId> {
        let mut offsets = Vec::new();
        unsafe extern "C" fn cb(offset: u32, ctx: *mut std::ffi::c_void) {
            unsafe {
                let v = &mut *(ctx as *mut Vec<EntityId>);
                v.push(EntityId(offset));
            }
        }
        unsafe {
            abcd_file_sys::abc_class_enumerate_methods(
                self.handle,
                Some(cb),
                &mut offsets as *mut Vec<EntityId> as *mut std::ffi::c_void,
            );
        }
        offsets
    }

    pub fn field_offsets(&self) -> Vec<EntityId> {
        let mut offsets = Vec::new();
        unsafe extern "C" fn cb(offset: u32, ctx: *mut std::ffi::c_void) {
            unsafe {
                let v = &mut *(ctx as *mut Vec<EntityId>);
                v.push(EntityId(offset));
            }
        }
        unsafe {
            abcd_file_sys::abc_class_enumerate_fields(
                self.handle,
                Some(cb),
                &mut offsets as *mut Vec<EntityId> as *mut std::ffi::c_void,
            );
        }
        offsets
    }

    pub fn annotations(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_class_enumerate_annotations(self.handle, Some(cb), ctx);
        })
    }

    pub fn runtime_annotations(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_class_enumerate_runtime_annotations(self.handle, Some(cb), ctx);
        })
    }

    pub fn type_annotations(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_class_enumerate_type_annotations(self.handle, Some(cb), ctx);
        })
    }

    pub fn runtime_type_annotations(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_class_enumerate_runtime_type_annotations(self.handle, Some(cb), ctx);
        })
    }

    pub fn num_annotations(&self) -> u32 {
        unsafe { abcd_file_sys::abc_class_get_annotations_number(self.handle) }
    }

    pub fn num_runtime_annotations(&self) -> u32 {
        unsafe { abcd_file_sys::abc_class_get_runtime_annotations_number(self.handle) }
    }

    pub fn file(&self) -> &'f File {
        self.file
    }
}

impl Drop for Class<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_class_close(self.handle) };
        }
    }
}

impl std::fmt::Debug for Class<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Class").field("offset", &self.off).finish()
    }
}
