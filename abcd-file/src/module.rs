//! Module data accessor.

use crate::{EntityId, File, error::Error, types::ModuleTag};

/// A module record entry.
#[derive(Debug, Clone)]
pub struct ModuleRecord {
    pub tag: ModuleTag,
    pub export_name_off: EntityId,
    pub module_request_idx: u32,
    pub import_name_off: EntityId,
    pub local_name_off: EntityId,
}

/// A module data accessor. Borrows from a [`File`].
pub struct Module<'f> {
    handle: *mut abcd_file_sys::AbcModuleAccessor,
    file: &'f File,
    off: EntityId,
}

impl<'f> Module<'f> {
    pub(crate) fn open(file: &'f File, offset: EntityId) -> Result<Self, Error> {
        let handle = unsafe { abcd_file_sys::abc_module_open(file.handle(), offset.0) };
        if handle.is_null() {
            return Err(Error::Ffi(format!(
                "abc_module_open failed at offset {offset:?}"
            )));
        }
        Ok(Self {
            handle,
            file,
            off: offset,
        })
    }

    /// The offset in the ABC file where this module was opened.
    pub fn offset(&self) -> EntityId {
        self.off
    }

    pub fn data_id(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_module_get_data_id(self.handle) })
    }

    pub fn num_requests(&self) -> u32 {
        unsafe { abcd_file_sys::abc_module_num_requests(self.handle) }
    }

    pub fn request_off(&self, idx: u32) -> Option<EntityId> {
        let off = unsafe { abcd_file_sys::abc_module_request_off(self.handle, idx) };
        if off == u32::MAX {
            None
        } else {
            Some(EntityId(off))
        }
    }

    pub fn records(&self) -> Vec<ModuleRecord> {
        let mut records = Vec::new();
        unsafe extern "C" fn cb(
            tag: u8,
            export_name_off: u32,
            module_request_idx: u32,
            import_name_off: u32,
            local_name_off: u32,
            ctx: *mut std::ffi::c_void,
        ) {
            unsafe {
                let v = &mut *(ctx as *mut Vec<ModuleRecord>);
                v.push(ModuleRecord {
                    tag: ModuleTag::from_u8(tag),
                    export_name_off: EntityId(export_name_off),
                    module_request_idx,
                    import_name_off: EntityId(import_name_off),
                    local_name_off: EntityId(local_name_off),
                });
            }
        }
        unsafe {
            abcd_file_sys::abc_module_enumerate_records(
                self.handle,
                Some(cb),
                &mut records as *mut Vec<ModuleRecord> as *mut std::ffi::c_void,
            );
        }
        records
    }

    pub fn file(&self) -> &'f File {
        self.file
    }
}

impl Drop for Module<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_module_close(self.handle) };
        }
    }
}

impl std::fmt::Debug for Module<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Module").field("offset", &self.off).finish()
    }
}
