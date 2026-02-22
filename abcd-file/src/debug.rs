//! Debug info extractor.

use crate::{EntityId, File, collect_entity_ids, error::Error};
use std::ffi::CStr;

/// A line number table entry.
#[derive(Debug, Clone, Copy)]
pub struct LineEntry {
    pub offset: u32,
    pub line: u32,
}

/// A column number table entry.
#[derive(Debug, Clone, Copy)]
pub struct ColumnEntry {
    pub offset: u32,
    pub column: u32,
}

/// A local variable info entry.
#[derive(Debug, Clone)]
pub struct LocalVarInfo {
    pub name: String,
    pub type_name: String,
    pub type_signature: String,
    pub reg_number: i32,
    pub start_offset: u32,
    pub end_offset: u32,
}

/// A parameter info entry.
#[derive(Debug, Clone)]
pub struct ParamInfo {
    pub name: String,
    pub signature: String,
}

/// Debug info extractor. Borrows from a [`File`].
pub struct DebugInfo<'f> {
    handle: *mut abcd_file_sys::AbcDebugInfo,
    file: &'f File,
}

impl<'f> DebugInfo<'f> {
    pub(crate) fn open(file: &'f File) -> Result<Self, Error> {
        let handle = unsafe { abcd_file_sys::abc_debug_info_open(file.handle()) };
        if handle.is_null() {
            return Err(Error::Ffi("abc_debug_info_open failed".into()));
        }
        Ok(Self { handle, file })
    }

    pub fn line_table(&self, method_off: EntityId) -> Vec<LineEntry> {
        let mut entries = Vec::new();
        unsafe extern "C" fn cb(
            entry: *const abcd_file_sys::AbcLineEntry,
            ctx: *mut std::ffi::c_void,
        ) -> i32 {
            unsafe {
                let v = &mut *(ctx as *mut Vec<LineEntry>);
                let e = &*entry;
                v.push(LineEntry {
                    offset: e.offset,
                    line: e.line,
                });
            }
            0
        }
        unsafe {
            abcd_file_sys::abc_debug_get_line_table(
                self.handle,
                method_off.0,
                Some(cb),
                &mut entries as *mut Vec<LineEntry> as *mut std::ffi::c_void,
            );
        }
        entries
    }

    pub fn column_table(&self, method_off: EntityId) -> Vec<ColumnEntry> {
        let mut entries = Vec::new();
        unsafe extern "C" fn cb(
            entry: *const abcd_file_sys::AbcColumnEntry,
            ctx: *mut std::ffi::c_void,
        ) -> i32 {
            unsafe {
                let v = &mut *(ctx as *mut Vec<ColumnEntry>);
                let e = &*entry;
                v.push(ColumnEntry {
                    offset: e.offset,
                    column: e.column,
                });
            }
            0
        }
        unsafe {
            abcd_file_sys::abc_debug_get_column_table(
                self.handle,
                method_off.0,
                Some(cb),
                &mut entries as *mut Vec<ColumnEntry> as *mut std::ffi::c_void,
            );
        }
        entries
    }

    pub fn source_file(&self, method_off: EntityId) -> Option<String> {
        let ptr = unsafe { abcd_file_sys::abc_debug_get_source_file(self.handle, method_off.0) };
        if ptr.is_null() {
            return None;
        }
        let cstr = unsafe { CStr::from_ptr(ptr) };
        Some(cstr.to_string_lossy().into_owned())
    }

    pub fn source_code(&self, method_off: EntityId) -> Option<String> {
        let ptr = unsafe { abcd_file_sys::abc_debug_get_source_code(self.handle, method_off.0) };
        if ptr.is_null() {
            return None;
        }
        let cstr = unsafe { CStr::from_ptr(ptr) };
        Some(cstr.to_string_lossy().into_owned())
    }

    pub fn local_vars(&self, method_off: EntityId) -> Vec<LocalVarInfo> {
        let mut vars = Vec::new();
        unsafe extern "C" fn cb(
            info: *const abcd_file_sys::AbcLocalVarInfo,
            ctx: *mut std::ffi::c_void,
        ) -> i32 {
            unsafe {
                let v = &mut *(ctx as *mut Vec<LocalVarInfo>);
                let i = &*info;
                let name = if i.name.is_null() {
                    String::new()
                } else {
                    CStr::from_ptr(i.name).to_string_lossy().into_owned()
                };
                let type_name = if i.type_.is_null() {
                    String::new()
                } else {
                    CStr::from_ptr(i.type_).to_string_lossy().into_owned()
                };
                let type_signature = if i.type_signature.is_null() {
                    String::new()
                } else {
                    CStr::from_ptr(i.type_signature)
                        .to_string_lossy()
                        .into_owned()
                };
                v.push(LocalVarInfo {
                    name,
                    type_name,
                    type_signature,
                    reg_number: i.reg_number,
                    start_offset: i.start_offset,
                    end_offset: i.end_offset,
                });
            }
            0
        }
        unsafe {
            abcd_file_sys::abc_debug_get_local_vars(
                self.handle,
                method_off.0,
                Some(cb),
                &mut vars as *mut Vec<LocalVarInfo> as *mut std::ffi::c_void,
            );
        }
        vars
    }

    pub fn parameter_info(&self, method_off: EntityId) -> Vec<ParamInfo> {
        let mut params = Vec::new();
        unsafe extern "C" fn cb(
            info: *const abcd_file_sys::AbcParamInfo,
            ctx: *mut std::ffi::c_void,
        ) -> i32 {
            unsafe {
                let v = &mut *(ctx as *mut Vec<ParamInfo>);
                let i = &*info;
                let name = if i.name.is_null() {
                    String::new()
                } else {
                    CStr::from_ptr(i.name).to_string_lossy().into_owned()
                };
                let signature = if i.signature.is_null() {
                    String::new()
                } else {
                    CStr::from_ptr(i.signature).to_string_lossy().into_owned()
                };
                v.push(ParamInfo { name, signature });
            }
            0
        }
        unsafe {
            abcd_file_sys::abc_debug_get_parameter_info(
                self.handle,
                method_off.0,
                Some(cb),
                &mut params as *mut Vec<ParamInfo> as *mut std::ffi::c_void,
            );
        }
        params
    }

    pub fn method_list(&self) -> Vec<EntityId> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_debug_get_method_list(self.handle, Some(cb), ctx);
        })
    }

    pub fn file(&self) -> &'f File {
        self.file
    }
}

impl Drop for DebugInfo<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_debug_info_close(self.handle) };
        }
    }
}

impl std::fmt::Debug for DebugInfo<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DebugInfo").finish_non_exhaustive()
    }
}
