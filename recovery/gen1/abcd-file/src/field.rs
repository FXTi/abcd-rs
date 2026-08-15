//! Field data accessor.

use crate::{EntityId, File, collect_entity_ids, error::Error};

/// A field data accessor. Borrows from a [`File`].
pub struct Field<'f> {
    handle: *mut abcd_file_sys::AbcFieldAccessor,
    file: &'f File,
    off: EntityId,
}

impl<'f> Field<'f> {
    pub(crate) fn open(file: &'f File, offset: EntityId) -> Result<Self, Error> {
        let handle = unsafe { abcd_file_sys::abc_field_open(file.handle(), offset.0) };
        if handle.is_null() {
            return Err(Error::Ffi(format!(
                "abc_field_open failed at offset {offset:?}"
            )));
        }
        Ok(Self {
            handle,
            file,
            off: offset,
        })
    }

    /// The offset in the ABC file where this field was opened.
    pub fn offset(&self) -> EntityId {
        self.off
    }

    pub fn name_off(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_field_name_off(self.handle) })
    }

    pub fn type_id(&self) -> u32 {
        unsafe { abcd_file_sys::abc_field_type(self.handle) }
    }

    pub fn access_flags(&self) -> u32 {
        unsafe { abcd_file_sys::abc_field_access_flags(self.handle) }
    }

    pub fn is_external(&self) -> bool {
        unsafe { abcd_file_sys::abc_field_is_external(self.handle) != 0 }
    }

    pub fn class_off(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_field_class_off(self.handle) })
    }

    pub fn size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_field_size(self.handle) }
    }

    pub fn field_id(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_field_get_field_id(self.handle) })
    }

    pub fn value_i32(&self) -> Option<i32> {
        let mut out = 0i32;
        let ok = unsafe { abcd_file_sys::abc_field_get_value_i32(self.handle, &mut out) };
        if ok != 0 { Some(out) } else { None }
    }

    pub fn value_i64(&self) -> Option<i64> {
        let mut out = 0i64;
        let ok = unsafe { abcd_file_sys::abc_field_get_value_i64(self.handle, &mut out) };
        if ok != 0 { Some(out) } else { None }
    }

    pub fn value_f32(&self) -> Option<f32> {
        let mut out = 0f32;
        let ok = unsafe { abcd_file_sys::abc_field_get_value_f32(self.handle, &mut out) };
        if ok != 0 { Some(out) } else { None }
    }

    pub fn value_f64(&self) -> Option<f64> {
        let mut out = 0f64;
        let ok = unsafe { abcd_file_sys::abc_field_get_value_f64(self.handle, &mut out) };
        if ok != 0 { Some(out) } else { None }
    }

    pub fn annotations(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_field_enumerate_annotations(self.handle, Some(cb), ctx);
        })
    }

    pub fn runtime_annotations(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_field_enumerate_runtime_annotations(self.handle, Some(cb), ctx);
        })
    }

    pub fn type_annotations(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_field_enumerate_type_annotations(self.handle, Some(cb), ctx);
        })
    }

    pub fn runtime_type_annotations(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_field_enumerate_runtime_type_annotations(self.handle, Some(cb), ctx);
        })
    }

    pub fn num_annotations(&self) -> u32 {
        unsafe { abcd_file_sys::abc_field_get_annotations_number(self.handle) }
    }

    pub fn num_runtime_annotations(&self) -> u32 {
        unsafe { abcd_file_sys::abc_field_get_runtime_annotations_number(self.handle) }
    }

    pub fn num_type_annotations(&self) -> u32 {
        unsafe { abcd_file_sys::abc_field_get_type_annotations_number(self.handle) }
    }

    pub fn num_runtime_type_annotations(&self) -> u32 {
        unsafe { abcd_file_sys::abc_field_get_runtime_type_annotations_number(self.handle) }
    }

    pub fn file(&self) -> &'f File {
        self.file
    }
}

impl Drop for Field<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_field_close(self.handle) };
        }
    }
}

impl std::fmt::Debug for Field<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Field").field("offset", &self.off).finish()
    }
}
