//! C++ accessor-backed parsing backend via abcd-file-sys FFI.
//!
//! Provides safe Rust wrappers around arkcompiler's native data accessors.
//! These can be used as an alternative to the pure-Rust parsing in the
//! parent modules, and serve as a cross-validation reference.

use crate::error::ParseError;
use std::ffi::CStr;

/// A file handle backed by the C++ File shim.
///
/// Owns a copy of the data and the native AbcFileHandle.
pub struct SysFile {
    handle: *mut abcd_file_sys::AbcFileHandle,
    _data: Vec<u8>,
}

// SAFETY: AbcFileHandle is single-threaded but can be moved between threads
unsafe impl Send for SysFile {}

impl SysFile {
    /// Open an ABC file from raw bytes.
    pub fn open(data: Vec<u8>) -> Result<Self, ParseError> {
        let handle = unsafe { abcd_file_sys::abc_file_open(data.as_ptr(), data.len()) };
        if handle.is_null() {
            return Err(ParseError::Io("abc_file_open returned null".into()));
        }
        Ok(Self {
            handle,
            _data: data,
        })
    }

    /// Number of classes in the file.
    pub fn num_classes(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_num_classes(self.handle) }
    }

    /// Get class offset by index.
    pub fn class_offset(&self, idx: u32) -> u32 {
        unsafe { abcd_file_sys::abc_file_class_offset(self.handle, idx) }
    }

    /// Number of literal arrays.
    pub fn num_literalarrays(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_num_literalarrays(self.handle) }
    }

    /// Get literal array offset by index.
    pub fn literalarray_offset(&self, idx: u32) -> u32 {
        unsafe { abcd_file_sys::abc_file_literalarray_offset(self.handle, idx) }
    }

    /// File version as `[major, minor, patch, build]`.
    pub fn version(&self) -> [u8; 4] {
        let mut v = [0u8; 4];
        unsafe { abcd_file_sys::abc_file_version(self.handle, v.as_mut_ptr()) };
        v
    }

    /// File size from header.
    pub fn file_size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_size(self.handle) }
    }

    /// Read a string at the given offset.
    pub fn get_string(&self, offset: u32) -> Result<String, ParseError> {
        let mut buf = vec![0u8; 4096];
        let n = unsafe {
            abcd_file_sys::abc_file_get_string(
                self.handle,
                offset,
                buf.as_mut_ptr() as *mut i8,
                buf.len(),
            )
        };
        if n == 0 {
            return Err(ParseError::Io(format!(
                "abc_file_get_string failed at offset {offset}"
            )));
        }
        buf.truncate(n);
        String::from_utf8(buf).map_err(|e| ParseError::Io(e.to_string()))
    }

    /// Resolve a 16-bit method index to a file offset.
    pub fn resolve_method_index(&self, entity_off: u32, idx: u16) -> Option<u32> {
        let off = unsafe { abcd_file_sys::abc_resolve_method_index(self.handle, entity_off, idx) };
        if off == u32::MAX { None } else { Some(off) }
    }

    /// Resolve a 16-bit class index to a file offset.
    pub fn resolve_class_index(&self, entity_off: u32, idx: u16) -> Option<u32> {
        let off = unsafe { abcd_file_sys::abc_resolve_class_index(self.handle, entity_off, idx) };
        if off == u32::MAX { None } else { Some(off) }
    }

    /// Resolve a 16-bit field index to a file offset.
    pub fn resolve_field_index(&self, entity_off: u32, idx: u16) -> Option<u32> {
        let off = unsafe { abcd_file_sys::abc_resolve_field_index(self.handle, entity_off, idx) };
        if off == u32::MAX { None } else { Some(off) }
    }

    /// Open a class accessor at the given offset.
    pub fn class_accessor(&self, offset: u32) -> Result<SysClassAccessor<'_>, ParseError> {
        SysClassAccessor::open(self, offset)
    }

    /// Open a method accessor at the given offset.
    pub fn method_accessor(&self, offset: u32) -> Result<SysMethodAccessor<'_>, ParseError> {
        SysMethodAccessor::open(self, offset)
    }

    /// Open a code accessor at the given offset.
    pub fn code_accessor(&self, offset: u32) -> Result<SysCodeAccessor<'_>, ParseError> {
        SysCodeAccessor::open(self, offset)
    }

    /// Open a field accessor at the given offset.
    pub fn field_accessor(&self, offset: u32) -> Result<SysFieldAccessor<'_>, ParseError> {
        SysFieldAccessor::open(self, offset)
    }

    pub(crate) fn handle(&self) -> *mut abcd_file_sys::AbcFileHandle {
        self.handle
    }
}

impl Drop for SysFile {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_file_close(self.handle) };
        }
    }
}

// ========== Class Accessor ==========

/// Safe wrapper around C++ ClassDataAccessor.
pub struct SysClassAccessor<'f> {
    handle: *mut abcd_file_sys::AbcClassAccessor,
    file: &'f SysFile,
}

impl<'f> SysClassAccessor<'f> {
    fn open(file: &'f SysFile, offset: u32) -> Result<Self, ParseError> {
        let handle = unsafe { abcd_file_sys::abc_class_open(file.handle(), offset) };
        if handle.is_null() {
            return Err(ParseError::Io(format!(
                "abc_class_open failed at offset {offset}"
            )));
        }
        Ok(Self { handle, file })
    }

    pub fn super_class_off(&self) -> u32 {
        unsafe { abcd_file_sys::abc_class_super_class_off(self.handle) }
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

    pub fn source_file_off(&self) -> Option<u32> {
        let off = unsafe { abcd_file_sys::abc_class_source_file_off(self.handle) };
        if off == u32::MAX { None } else { Some(off) }
    }

    /// Collect all method offsets for this class.
    pub fn method_offsets(&self) -> Vec<u32> {
        let mut offsets = Vec::new();
        unsafe extern "C" fn cb(offset: u32, ctx: *mut std::ffi::c_void) -> i32 {
            unsafe {
                let v = &mut *(ctx as *mut Vec<u32>);
                v.push(offset);
            }
            0
        }
        unsafe {
            abcd_file_sys::abc_class_enumerate_methods(
                self.handle,
                Some(cb),
                &mut offsets as *mut Vec<u32> as *mut std::ffi::c_void,
            );
        }
        offsets
    }

    /// Collect all field offsets for this class.
    pub fn field_offsets(&self) -> Vec<u32> {
        let mut offsets = Vec::new();
        unsafe extern "C" fn cb(offset: u32, ctx: *mut std::ffi::c_void) -> i32 {
            unsafe {
                let v = &mut *(ctx as *mut Vec<u32>);
                v.push(offset);
            }
            0
        }
        unsafe {
            abcd_file_sys::abc_class_enumerate_fields(
                self.handle,
                Some(cb),
                &mut offsets as *mut Vec<u32> as *mut std::ffi::c_void,
            );
        }
        offsets
    }

    /// Get the file reference.
    pub fn file(&self) -> &'f SysFile {
        self.file
    }
}

impl Drop for SysClassAccessor<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_class_close(self.handle) };
        }
    }
}

// ========== Method Accessor ==========

/// Safe wrapper around C++ MethodDataAccessor.
pub struct SysMethodAccessor<'f> {
    handle: *mut abcd_file_sys::AbcMethodAccessor,
    _file: &'f SysFile,
}

impl<'f> SysMethodAccessor<'f> {
    fn open(file: &'f SysFile, offset: u32) -> Result<Self, ParseError> {
        let handle = unsafe { abcd_file_sys::abc_method_open(file.handle(), offset) };
        if handle.is_null() {
            return Err(ParseError::Io(format!(
                "abc_method_open failed at offset {offset}"
            )));
        }
        Ok(Self {
            handle,
            _file: file,
        })
    }

    pub fn name_off(&self) -> u32 {
        unsafe { abcd_file_sys::abc_method_name_off(self.handle) }
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

    pub fn code_off(&self) -> Option<u32> {
        let off = unsafe { abcd_file_sys::abc_method_code_off(self.handle) };
        if off == u32::MAX { None } else { Some(off) }
    }

    pub fn debug_info_off(&self) -> Option<u32> {
        let off = unsafe { abcd_file_sys::abc_method_debug_info_off(self.handle) };
        if off == u32::MAX { None } else { Some(off) }
    }
}

impl Drop for SysMethodAccessor<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_method_close(self.handle) };
        }
    }
}

// ========== Code Accessor ==========

/// Safe wrapper around C++ CodeDataAccessor.
pub struct SysCodeAccessor<'f> {
    handle: *mut abcd_file_sys::AbcCodeAccessor,
    _file: &'f SysFile,
}

impl<'f> SysCodeAccessor<'f> {
    fn open(file: &'f SysFile, offset: u32) -> Result<Self, ParseError> {
        let handle = unsafe { abcd_file_sys::abc_code_open(file.handle(), offset) };
        if handle.is_null() {
            return Err(ParseError::Io(format!(
                "abc_code_open failed at offset {offset}"
            )));
        }
        Ok(Self {
            handle,
            _file: file,
        })
    }

    pub fn num_vregs(&self) -> u32 {
        unsafe { abcd_file_sys::abc_code_num_vregs(self.handle) }
    }

    pub fn num_args(&self) -> u32 {
        unsafe { abcd_file_sys::abc_code_num_args(self.handle) }
    }

    pub fn code_size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_code_code_size(self.handle) }
    }

    /// Get a slice of the raw bytecode instructions.
    pub fn instructions(&self) -> &[u8] {
        let ptr = unsafe { abcd_file_sys::abc_code_instructions(self.handle) };
        if ptr.is_null() {
            return &[];
        }
        let size = self.code_size() as usize;
        unsafe { std::slice::from_raw_parts(ptr, size) }
    }

    pub fn tries_size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_code_tries_size(self.handle) }
    }
}

impl Drop for SysCodeAccessor<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_code_close(self.handle) };
        }
    }
}

// ========== Field Accessor ==========

/// Safe wrapper around C++ FieldDataAccessor.
pub struct SysFieldAccessor<'f> {
    handle: *mut abcd_file_sys::AbcFieldAccessor,
    _file: &'f SysFile,
}

impl<'f> SysFieldAccessor<'f> {
    fn open(file: &'f SysFile, offset: u32) -> Result<Self, ParseError> {
        let handle = unsafe { abcd_file_sys::abc_field_open(file.handle(), offset) };
        if handle.is_null() {
            return Err(ParseError::Io(format!(
                "abc_field_open failed at offset {offset}"
            )));
        }
        Ok(Self {
            handle,
            _file: file,
        })
    }

    pub fn name_off(&self) -> u32 {
        unsafe { abcd_file_sys::abc_field_name_off(self.handle) }
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

    pub fn class_off(&self) -> u32 {
        unsafe { abcd_file_sys::abc_field_class_off(self.handle) }
    }

    pub fn size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_field_size(self.handle) }
    }
}

impl Drop for SysFieldAccessor<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_field_close(self.handle) };
        }
    }
}

// ========== Debug Info ==========

/// Safe wrapper around C++ DebugInfoExtractor.
pub struct SysDebugInfo {
    handle: *mut abcd_file_sys::AbcDebugInfo,
}

unsafe impl Send for SysDebugInfo {}

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

impl SysDebugInfo {
    pub fn open(file: &SysFile) -> Result<Self, ParseError> {
        let handle = unsafe { abcd_file_sys::abc_debug_info_open(file.handle()) };
        if handle.is_null() {
            return Err(ParseError::Io("abc_debug_info_open failed".into()));
        }
        Ok(Self { handle })
    }

    /// Get line number table for a method.
    pub fn line_table(&self, method_off: u32) -> Vec<LineEntry> {
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
                method_off,
                Some(cb),
                &mut entries as *mut Vec<LineEntry> as *mut std::ffi::c_void,
            );
        }
        entries
    }

    /// Get column number table for a method.
    pub fn column_table(&self, method_off: u32) -> Vec<ColumnEntry> {
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
                method_off,
                Some(cb),
                &mut entries as *mut Vec<ColumnEntry> as *mut std::ffi::c_void,
            );
        }
        entries
    }

    /// Get source file name for a method.
    pub fn source_file(&self, method_off: u32) -> Option<String> {
        let ptr = unsafe { abcd_file_sys::abc_debug_get_source_file(self.handle, method_off) };
        if ptr.is_null() {
            return None;
        }
        let cstr = unsafe { CStr::from_ptr(ptr) };
        Some(cstr.to_string_lossy().into_owned())
    }

    /// Get source code for a method.
    pub fn source_code(&self, method_off: u32) -> Option<String> {
        let ptr = unsafe { abcd_file_sys::abc_debug_get_source_code(self.handle, method_off) };
        if ptr.is_null() {
            return None;
        }
        let cstr = unsafe { CStr::from_ptr(ptr) };
        Some(cstr.to_string_lossy().into_owned())
    }
}

impl Drop for SysDebugInfo {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_debug_info_close(self.handle) };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_abc_data() -> Vec<u8> {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../modules.abc");
        std::fs::read(path).expect("modules.abc not found")
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn sys_file_open_and_header() {
        let data = test_abc_data();
        let f = SysFile::open(data).unwrap();
        assert!(f.num_classes() > 0);
        assert!(f.file_size() > 0);
        let v = f.version();
        // Should be a valid version
        assert!(v[0] <= 20);
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn sys_class_accessor() {
        let data = test_abc_data();
        let f = SysFile::open(data).unwrap();

        for i in 0..f.num_classes() {
            let off = f.class_offset(i);
            let cls = f.class_accessor(off).unwrap();
            // Just verify we can read basic fields without crashing
            let _flags = cls.access_flags();
            let _nm = cls.num_methods();
            let _nf = cls.num_fields();
        }
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn sys_method_accessor() {
        let data = test_abc_data();
        let f = SysFile::open(data).unwrap();

        let off = f.class_offset(0);
        let cls = f.class_accessor(off).unwrap();
        let method_offs = cls.method_offsets();

        for moff in method_offs {
            let m = f.method_accessor(moff).unwrap();
            let name_off = m.name_off();
            let name = f.get_string(name_off).unwrap();
            assert!(!name.is_empty());

            if let Some(code_off) = m.code_off() {
                let code = f.code_accessor(code_off).unwrap();
                assert!(code.code_size() > 0);
                assert!(!code.instructions().is_empty());
            }
        }
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn sys_cross_validate_class_count() {
        let data = test_abc_data();
        let abc = crate::AbcFile::parse(data.clone()).unwrap();
        let f = SysFile::open(data).unwrap();

        assert_eq!(abc.header.num_classes, f.num_classes());
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn sys_cross_validate_method_names() {
        let data = test_abc_data();
        let abc = crate::AbcFile::parse(data.clone()).unwrap();
        let f = SysFile::open(data).unwrap();

        // Compare first class's method names between Rust and C++ backends
        let class_off = abc.class_offsets().next().unwrap();
        let rust_cls = crate::class::ClassData::parse(abc.data(), class_off).unwrap();

        let sys_cls = f.class_accessor(class_off).unwrap();
        assert_eq!(rust_cls.num_methods, sys_cls.num_methods());

        let sys_method_offs = sys_cls.method_offsets();
        for (i, &rust_off) in rust_cls.method_offsets.iter().enumerate() {
            let rust_m = crate::method::MethodData::parse(abc.data(), rust_off as u32).unwrap();
            let sys_m = f.method_accessor(sys_method_offs[i]).unwrap();

            let sys_name = f.get_string(sys_m.name_off()).unwrap();
            assert_eq!(rust_m.name, sys_name, "method name mismatch at index {i}");
        }
    }

    #[test]
    fn sys_writer_roundtrip() {
        // Build an ABC file with the writer, then parse it with the sys backend
        let mut w = crate::writer::AbcWriter::new();
        let cls = w.add_class("L_GLOBAL;");
        let code = [0xa0u8]; // returnundefined
        w.add_method(cls, "func_main_0", 0x0001, &code, 1, 0)
            .unwrap();

        let data = w.finalize().unwrap();
        let f = SysFile::open(data).unwrap();

        assert!(f.num_classes() > 0);
        let cls_acc = f.class_accessor(f.class_offset(0)).unwrap();
        assert_eq!(cls_acc.num_methods(), 1);

        let method_offs = cls_acc.method_offsets();
        let m = f.method_accessor(method_offs[0]).unwrap();
        let name = f.get_string(m.name_off()).unwrap();
        assert_eq!(name, "func_main_0");
    }
}
