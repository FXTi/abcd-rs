//! Method data accessor.

use crate::{EntityId, File, collect_entity_ids, error::Error, types::SourceLang};

/// A method data accessor. Borrows from a [`File`].
pub struct Method<'f> {
    handle: *mut abcd_file_sys::AbcMethodAccessor,
    file: &'f File,
    off: EntityId,
}

impl<'f> Method<'f> {
    pub(crate) fn open(file: &'f File, offset: EntityId) -> Result<Self, Error> {
        let handle = unsafe { abcd_file_sys::abc_method_open(file.handle(), offset.0) };
        if handle.is_null() {
            return Err(Error::Ffi(format!(
                "abc_method_open failed at offset {offset:?}"
            )));
        }
        Ok(Self {
            handle,
            file,
            off: offset,
        })
    }

    /// The offset in the ABC file where this method was opened.
    pub fn offset(&self) -> EntityId {
        self.off
    }

    pub fn name_off(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_method_name_off(self.handle) })
    }

    pub fn class_idx(&self) -> u16 {
        unsafe { abcd_file_sys::abc_method_class_idx(self.handle) }
    }

    pub fn proto_idx(&self) -> u16 {
        unsafe { abcd_file_sys::abc_method_proto_idx(self.handle) }
    }

    pub fn access_flags(&self) -> u32 {
        unsafe { abcd_file_sys::abc_method_access_flags(self.handle) }
    }

    pub fn code_off(&self) -> Option<EntityId> {
        let off = unsafe { abcd_file_sys::abc_method_code_off(self.handle) };
        if off == u32::MAX {
            None
        } else {
            Some(EntityId(off))
        }
    }

    pub fn debug_info_off(&self) -> Option<EntityId> {
        let off = unsafe { abcd_file_sys::abc_method_debug_info_off(self.handle) };
        if off == u32::MAX {
            None
        } else {
            Some(EntityId(off))
        }
    }

    pub fn is_external(&self) -> bool {
        unsafe { abcd_file_sys::abc_method_is_external(self.handle) != 0 }
    }

    pub fn class_id(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_method_get_class_id(self.handle) })
    }

    pub fn proto_id(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_method_get_proto_id(self.handle) })
    }

    pub fn source_lang(&self) -> Option<SourceLang> {
        let v = unsafe { abcd_file_sys::abc_method_get_source_lang(self.handle) };
        if v == u8::MAX {
            None
        } else {
            SourceLang::from_u8(v)
        }
    }

    pub fn size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_method_get_size(self.handle) }
    }

    pub fn method_id(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_method_get_method_id(self.handle) })
    }

    pub fn name(&self) -> Result<String, Error> {
        let len =
            unsafe { abcd_file_sys::abc_method_get_name(self.handle, std::ptr::null_mut(), 0) };
        if len == 0 {
            return Ok(String::new());
        }
        let mut buf = vec![0u8; len];
        let written = unsafe {
            abcd_file_sys::abc_method_get_name(
                self.handle,
                buf.as_mut_ptr() as *mut std::ffi::c_char,
                buf.len(),
            )
        };
        buf.truncate(written);
        String::from_utf8(buf).map_err(|e| Error::Ffi(e.to_string()))
    }

    pub fn has_valid_proto(&self) -> bool {
        unsafe { abcd_file_sys::abc_method_has_valid_proto(self.handle) != 0 }
    }

    pub fn numerical_annotation(&self, field_id: u32) -> u32 {
        unsafe { abcd_file_sys::abc_method_get_numerical_annotation(self.handle, field_id) }
    }

    /// Enumerate proto types inline: returns `(type_id, Option<ref_type_offset>)` pairs.
    pub fn proto_types(&self) -> Vec<(u8, Option<EntityId>)> {
        let mut types = Vec::new();
        unsafe extern "C" fn cb(type_id: u8, ref_type: u32, ctx: *mut std::ffi::c_void) -> i32 {
            unsafe {
                let v = &mut *(ctx as *mut Vec<(u8, Option<EntityId>)>);
                let r = if ref_type == u32::MAX {
                    None
                } else {
                    Some(EntityId(ref_type))
                };
                v.push((type_id, r));
            }
            0
        }
        unsafe {
            abcd_file_sys::abc_method_enumerate_types_in_proto(
                self.handle,
                Some(cb),
                &mut types as *mut Vec<(u8, Option<EntityId>)> as *mut std::ffi::c_void,
            );
        }
        types
    }

    pub fn annotations(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_method_enumerate_annotations(self.handle, Some(cb), ctx);
        })
    }

    pub fn runtime_annotations(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_method_enumerate_runtime_annotations(self.handle, Some(cb), ctx);
        })
    }

    pub fn type_annotations(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_method_enumerate_type_annotations(self.handle, Some(cb), ctx);
        })
    }

    pub fn runtime_type_annotations(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_method_enumerate_runtime_type_annotations(
                self.handle,
                Some(cb),
                ctx,
            );
        })
    }

    pub fn num_annotations(&self) -> u32 {
        unsafe { abcd_file_sys::abc_method_get_annotations_number(self.handle) }
    }

    pub fn num_runtime_annotations(&self) -> u32 {
        unsafe { abcd_file_sys::abc_method_get_runtime_annotations_number(self.handle) }
    }

    pub fn num_type_annotations(&self) -> u32 {
        unsafe { abcd_file_sys::abc_method_get_type_annotations_number(self.handle) }
    }

    pub fn num_runtime_type_annotations(&self) -> u32 {
        unsafe { abcd_file_sys::abc_method_get_runtime_type_annotations_number(self.handle) }
    }

    pub fn param_annotation_id(&self) -> Option<EntityId> {
        let v = unsafe { abcd_file_sys::abc_method_get_param_annotation_id(self.handle) };
        if v == u32::MAX {
            None
        } else {
            Some(EntityId(v))
        }
    }

    pub fn runtime_param_annotation_id(&self) -> Option<EntityId> {
        let v = unsafe { abcd_file_sys::abc_method_get_runtime_param_annotation_id(self.handle) };
        if v == u32::MAX {
            None
        } else {
            Some(EntityId(v))
        }
    }

    pub fn file(&self) -> &'f File {
        self.file
    }
}

impl Drop for Method<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_method_close(self.handle) };
        }
    }
}

impl std::fmt::Debug for Method<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Method").field("offset", &self.off).finish()
    }
}
