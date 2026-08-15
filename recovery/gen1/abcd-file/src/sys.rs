//! C++ accessor-backed parsing backend via abcd-file-sys FFI.
//!
//! Provides safe Rust wrappers around arkcompiler's native data accessors.
//! These can be used as an alternative to the pure-Rust parsing in the
//! parent modules, and serve as a cross-validation reference.

use crate::error::ParseError;
use std::ffi::CStr;

/// Shared callback for collecting u32 IDs from enumerate-style C APIs.
unsafe extern "C" fn entity_id_cb(id: u32, ctx: *mut std::ffi::c_void) -> i32 {
    unsafe {
        let v = &mut *(ctx as *mut Vec<u32>);
        v.push(id);
    }
    0
}

/// Helper: call an enumerate function and collect all u32 IDs.
fn collect_entity_ids(
    enumerate: impl FnOnce(
        unsafe extern "C" fn(u32, *mut std::ffi::c_void) -> i32,
        *mut std::ffi::c_void,
    ),
) -> Vec<u32> {
    let mut ids = Vec::new();
    enumerate(
        entity_id_cb,
        &mut ids as *mut Vec<u32> as *mut std::ffi::c_void,
    );
    ids
}

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
                buf.as_mut_ptr() as *mut std::ffi::c_char,
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

    /// Resolve a 16-bit proto index to a file offset.
    pub fn resolve_proto_index(&self, entity_off: u32, idx: u16) -> Option<u32> {
        let off = unsafe { abcd_file_sys::abc_resolve_proto_index(self.handle, entity_off, idx) };
        if off == u32::MAX { None } else { Some(off) }
    }

    /// Validate the file checksum.
    pub fn validate_checksum(&self) -> bool {
        unsafe { abcd_file_sys::abc_file_validate_checksum(self.handle) != 0 }
    }

    /// Check if an entity offset is in the foreign section.
    pub fn is_external(&self, entity_off: u32) -> bool {
        unsafe { abcd_file_sys::abc_file_is_external(self.handle, entity_off) != 0 }
    }

    /// Get the UTF-16 length of a string at the given offset.
    pub fn get_string_utf16_len(&self, offset: u32) -> u32 {
        unsafe { abcd_file_sys::abc_file_get_string_utf16_len(self.handle, offset) }
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

    /// Open a proto accessor at the given offset.
    pub fn proto_accessor(&self, offset: u32) -> Result<SysProtoAccessor<'_>, ParseError> {
        SysProtoAccessor::open(self, offset)
    }

    /// Open an annotation accessor at the given offset.
    pub fn annotation_accessor(
        &self,
        offset: u32,
    ) -> Result<SysAnnotationAccessor<'_>, ParseError> {
        SysAnnotationAccessor::open(self, offset)
    }

    /// Open a literal data accessor.
    pub fn literal_accessor(
        &self,
        literal_data_off: u32,
    ) -> Result<SysLiteralAccessor<'_>, ParseError> {
        SysLiteralAccessor::open(self, literal_data_off)
    }

    /// Open a module accessor at the given offset.
    pub fn module_accessor(&self, offset: u32) -> Result<SysModuleAccessor<'_>, ParseError> {
        SysModuleAccessor::open(self, offset)
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

    /// Source language, or `None` if absent.
    pub fn source_lang(&self) -> Option<u8> {
        let v = unsafe { abcd_file_sys::abc_class_get_source_lang(self.handle) };
        if v == u8::MAX { None } else { Some(v) }
    }

    /// Number of interfaces.
    pub fn ifaces_number(&self) -> u32 {
        unsafe { abcd_file_sys::abc_class_get_ifaces_number(self.handle) }
    }

    /// Get interface entity ID by index.
    pub fn interface_id(&self, idx: u32) -> u32 {
        unsafe { abcd_file_sys::abc_class_get_interface_id(self.handle, idx) }
    }

    /// Collect all interface entity IDs.
    pub fn interface_ids(&self) -> Vec<u32> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_class_enumerate_interfaces(self.handle, Some(cb), ctx);
        })
    }

    /// Collect annotation offsets.
    pub fn annotation_offsets(&self) -> Vec<u32> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_class_enumerate_annotations(self.handle, Some(cb), ctx);
        })
    }

    /// Collect runtime annotation offsets.
    pub fn runtime_annotation_offsets(&self) -> Vec<u32> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_class_enumerate_runtime_annotations(self.handle, Some(cb), ctx);
        })
    }

    /// Collect type annotation offsets.
    pub fn type_annotation_offsets(&self) -> Vec<u32> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_class_enumerate_type_annotations(self.handle, Some(cb), ctx);
        })
    }

    /// Collect runtime type annotation offsets.
    pub fn runtime_type_annotation_offsets(&self) -> Vec<u32> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_class_enumerate_runtime_type_annotations(self.handle, Some(cb), ctx);
        })
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

    /// Whether this method is in the foreign section.
    pub fn is_external(&self) -> bool {
        unsafe { abcd_file_sys::abc_method_is_external(self.handle) != 0 }
    }

    /// Resolved class entity ID.
    pub fn get_class_id(&self) -> u32 {
        unsafe { abcd_file_sys::abc_method_get_class_id(self.handle) }
    }

    /// Resolved proto entity ID.
    pub fn get_proto_id(&self) -> u32 {
        unsafe { abcd_file_sys::abc_method_get_proto_id(self.handle) }
    }

    /// Source language, or `None` if absent.
    pub fn source_lang(&self) -> Option<u8> {
        let v = unsafe { abcd_file_sys::abc_method_get_source_lang(self.handle) };
        if v == u8::MAX { None } else { Some(v) }
    }

    /// Collect annotation offsets.
    pub fn annotation_offsets(&self) -> Vec<u32> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_method_enumerate_annotations(self.handle, Some(cb), ctx);
        })
    }

    /// Collect runtime annotation offsets.
    pub fn runtime_annotation_offsets(&self) -> Vec<u32> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_method_enumerate_runtime_annotations(self.handle, Some(cb), ctx);
        })
    }

    /// Collect type annotation offsets.
    pub fn type_annotation_offsets(&self) -> Vec<u32> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_method_enumerate_type_annotations(self.handle, Some(cb), ctx);
        })
    }

    /// Collect runtime type annotation offsets.
    pub fn runtime_type_annotation_offsets(&self) -> Vec<u32> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_method_enumerate_runtime_type_annotations(
                self.handle,
                Some(cb),
                ctx,
            );
        })
    }

    /// Parameter annotation ID, or `None` if absent.
    pub fn param_annotation_id(&self) -> Option<u32> {
        let v = unsafe { abcd_file_sys::abc_method_get_param_annotation_id(self.handle) };
        if v == u32::MAX { None } else { Some(v) }
    }

    /// Runtime parameter annotation ID, or `None` if absent.
    pub fn runtime_param_annotation_id(&self) -> Option<u32> {
        let v = unsafe { abcd_file_sys::abc_method_get_runtime_param_annotation_id(self.handle) };
        if v == u32::MAX { None } else { Some(v) }
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

    /// Get i32 initial value, if present.
    pub fn get_value_i32(&self) -> Option<i32> {
        let mut out = 0i32;
        let ok = unsafe { abcd_file_sys::abc_field_get_value_i32(self.handle, &mut out) };
        if ok != 0 { Some(out) } else { None }
    }

    /// Get i64 initial value, if present.
    pub fn get_value_i64(&self) -> Option<i64> {
        let mut out = 0i64;
        let ok = unsafe { abcd_file_sys::abc_field_get_value_i64(self.handle, &mut out) };
        if ok != 0 { Some(out) } else { None }
    }

    /// Get f32 initial value, if present.
    pub fn get_value_f32(&self) -> Option<f32> {
        let mut out = 0f32;
        let ok = unsafe { abcd_file_sys::abc_field_get_value_f32(self.handle, &mut out) };
        if ok != 0 { Some(out) } else { None }
    }

    /// Get f64 initial value, if present.
    pub fn get_value_f64(&self) -> Option<f64> {
        let mut out = 0f64;
        let ok = unsafe { abcd_file_sys::abc_field_get_value_f64(self.handle, &mut out) };
        if ok != 0 { Some(out) } else { None }
    }

    /// Collect annotation offsets.
    pub fn annotation_offsets(&self) -> Vec<u32> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_field_enumerate_annotations(self.handle, Some(cb), ctx);
        })
    }

    /// Collect runtime annotation offsets.
    pub fn runtime_annotation_offsets(&self) -> Vec<u32> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_field_enumerate_runtime_annotations(self.handle, Some(cb), ctx);
        })
    }

    /// Collect type annotation offsets.
    pub fn type_annotation_offsets(&self) -> Vec<u32> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_field_enumerate_type_annotations(self.handle, Some(cb), ctx);
        })
    }

    /// Collect runtime type annotation offsets.
    pub fn runtime_type_annotation_offsets(&self) -> Vec<u32> {
        collect_entity_ids(|cb, ctx| unsafe {
            abcd_file_sys::abc_field_enumerate_runtime_type_annotations(self.handle, Some(cb), ctx);
        })
    }
}

impl Drop for SysFieldAccessor<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_field_close(self.handle) };
        }
    }
}

// ========== Proto Accessor ==========

/// Safe wrapper around C++ ProtoDataAccessor.
pub struct SysProtoAccessor<'f> {
    handle: *mut abcd_file_sys::AbcProtoAccessor,
    _file: &'f SysFile,
}

impl<'f> SysProtoAccessor<'f> {
    fn open(file: &'f SysFile, offset: u32) -> Result<Self, ParseError> {
        let handle = unsafe { abcd_file_sys::abc_proto_open(file.handle(), offset) };
        if handle.is_null() {
            return Err(ParseError::Io(format!(
                "abc_proto_open failed at offset {offset}"
            )));
        }
        Ok(Self {
            handle,
            _file: file,
        })
    }

    /// Return type ID.
    pub fn return_type(&self) -> u8 {
        unsafe { abcd_file_sys::abc_proto_get_return_type(self.handle) }
    }

    /// Number of arguments.
    pub fn num_args(&self) -> u32 {
        unsafe { abcd_file_sys::abc_proto_num_args(self.handle) }
    }

    /// Argument type ID by index.
    pub fn arg_type(&self, idx: u32) -> u8 {
        unsafe { abcd_file_sys::abc_proto_get_arg_type(self.handle, idx) }
    }

    /// Number of reference types.
    pub fn ref_num(&self) -> u32 {
        unsafe { abcd_file_sys::abc_proto_get_ref_num(self.handle) }
    }

    /// Reference type entity offset by index.
    pub fn reference_type(&self, idx: u32) -> u32 {
        unsafe { abcd_file_sys::abc_proto_get_reference_type(self.handle, idx) }
    }

    /// Collect all type IDs via enumerate.
    pub fn types(&self) -> Vec<u8> {
        let mut types = Vec::new();
        unsafe extern "C" fn cb(type_id: u8, ctx: *mut std::ffi::c_void) -> i32 {
            unsafe {
                let v = &mut *(ctx as *mut Vec<u8>);
                v.push(type_id);
            }
            0
        }
        unsafe {
            abcd_file_sys::abc_proto_enumerate_types(
                self.handle,
                Some(cb),
                &mut types as *mut Vec<u8> as *mut std::ffi::c_void,
            );
        }
        types
    }

    /// Get the raw shorty descriptor bytes.
    pub fn shorty(&self) -> &[u8] {
        let mut ptr = std::ptr::null();
        let len = unsafe { abcd_file_sys::abc_proto_get_shorty(self.handle, &mut ptr) };
        if ptr.is_null() || len == 0 {
            return &[];
        }
        unsafe { std::slice::from_raw_parts(ptr, len as usize) }
    }
}

impl Drop for SysProtoAccessor<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_proto_close(self.handle) };
        }
    }
}

// ========== Annotation Accessor ==========

/// A single annotation element.
#[derive(Debug, Clone)]
pub struct AnnotationElem {
    pub name_off: u32,
    pub tag: u8,
    pub value: u32,
}

/// An annotation array value.
#[derive(Debug, Clone)]
pub struct AnnotationArrayVal {
    pub count: u32,
    pub entity_off: u32,
}

/// Safe wrapper around C++ AnnotationDataAccessor.
pub struct SysAnnotationAccessor<'f> {
    handle: *mut abcd_file_sys::AbcAnnotationAccessor,
    _file: &'f SysFile,
}

impl<'f> SysAnnotationAccessor<'f> {
    fn open(file: &'f SysFile, offset: u32) -> Result<Self, ParseError> {
        let handle = unsafe { abcd_file_sys::abc_annotation_open(file.handle(), offset) };
        if handle.is_null() {
            return Err(ParseError::Io(format!(
                "abc_annotation_open failed at offset {offset}"
            )));
        }
        Ok(Self {
            handle,
            _file: file,
        })
    }

    /// Class entity offset for this annotation.
    pub fn class_off(&self) -> u32 {
        unsafe { abcd_file_sys::abc_annotation_class_off(self.handle) }
    }

    /// Number of elements.
    pub fn count(&self) -> u32 {
        unsafe { abcd_file_sys::abc_annotation_count(self.handle) }
    }

    /// Size in bytes.
    pub fn size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_annotation_size(self.handle) }
    }

    /// Get a scalar element by index.
    pub fn element(&self, idx: u32) -> Option<AnnotationElem> {
        let mut out = abcd_file_sys::AbcAnnotationElem {
            name_off: 0,
            tag: 0,
            value: 0,
        };
        let rc = unsafe { abcd_file_sys::abc_annotation_get_element(self.handle, idx, &mut out) };
        if rc != 0 {
            return None;
        }
        Some(AnnotationElem {
            name_off: out.name_off,
            tag: out.tag,
            value: out.value,
        })
    }

    /// Get an array element by index.
    pub fn array_element(&self, idx: u32) -> Option<AnnotationArrayVal> {
        let mut out = abcd_file_sys::AbcAnnotationArrayVal {
            count: 0,
            entity_off: 0,
        };
        let rc =
            unsafe { abcd_file_sys::abc_annotation_get_array_element(self.handle, idx, &mut out) };
        if rc != 0 {
            return None;
        }
        Some(AnnotationArrayVal {
            count: out.count,
            entity_off: out.entity_off,
        })
    }
}

impl Drop for SysAnnotationAccessor<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_annotation_close(self.handle) };
        }
    }
}

// ========== Literal Accessor ==========

/// A literal value from a literal array.
#[derive(Debug, Clone, Copy)]
pub struct LiteralVal {
    pub tag: u8,
    pub u64_val: u64,
}

impl LiteralVal {
    pub fn as_u8(&self) -> u8 {
        self.u64_val as u8
    }
    pub fn as_u16(&self) -> u16 {
        self.u64_val as u16
    }
    pub fn as_u32(&self) -> u32 {
        self.u64_val as u32
    }
    pub fn as_u64(&self) -> u64 {
        self.u64_val
    }
    pub fn as_f32(&self) -> f32 {
        f32::from_bits(self.u64_val as u32)
    }
    pub fn as_f64(&self) -> f64 {
        f64::from_bits(self.u64_val)
    }
    pub fn as_bool(&self) -> bool {
        self.u64_val != 0
    }
}

/// Safe wrapper around C++ LiteralDataAccessor.
pub struct SysLiteralAccessor<'f> {
    handle: *mut abcd_file_sys::AbcLiteralAccessor,
    _file: &'f SysFile,
}

impl<'f> SysLiteralAccessor<'f> {
    fn open(file: &'f SysFile, literal_data_off: u32) -> Result<Self, ParseError> {
        let handle = unsafe { abcd_file_sys::abc_literal_open(file.handle(), literal_data_off) };
        if handle.is_null() {
            return Err(ParseError::Io(format!(
                "abc_literal_open failed at offset {literal_data_off}"
            )));
        }
        Ok(Self {
            handle,
            _file: file,
        })
    }

    /// Total number of literal arrays.
    pub fn count(&self) -> u32 {
        unsafe { abcd_file_sys::abc_literal_count(self.handle) }
    }

    /// Number of values in a literal array (by entity offset).
    pub fn vals_num(&self, array_off: u32) -> u32 {
        unsafe { abcd_file_sys::abc_literal_get_vals_num(self.handle, array_off) }
    }

    /// Number of values in a literal array (by index).
    pub fn vals_num_by_index(&self, index: u32) -> u32 {
        unsafe { abcd_file_sys::abc_literal_get_vals_num_by_index(self.handle, index) }
    }

    /// Get literal array entity ID by index.
    pub fn array_id(&self, index: u32) -> u32 {
        unsafe { abcd_file_sys::abc_literal_get_array_id(self.handle, index) }
    }

    /// Enumerate literal values by entity offset.
    pub fn enumerate_vals(&self, array_off: u32) -> Vec<LiteralVal> {
        let mut vals = Vec::new();
        unsafe extern "C" fn cb(
            val: *const abcd_file_sys::AbcLiteralVal,
            ctx: *mut std::ffi::c_void,
        ) -> i32 {
            unsafe {
                let v = &mut *(ctx as *mut Vec<LiteralVal>);
                let lv = &*val;
                v.push(LiteralVal {
                    tag: lv.tag,
                    u64_val: lv.__bindgen_anon_1.u64_val,
                });
            }
            0
        }
        unsafe {
            abcd_file_sys::abc_literal_enumerate_vals(
                self.handle,
                array_off,
                Some(cb),
                &mut vals as *mut Vec<LiteralVal> as *mut std::ffi::c_void,
            );
        }
        vals
    }

    /// Enumerate literal values by index.
    pub fn enumerate_vals_by_index(&self, index: u32) -> Vec<LiteralVal> {
        let mut vals = Vec::new();
        unsafe extern "C" fn cb(
            val: *const abcd_file_sys::AbcLiteralVal,
            ctx: *mut std::ffi::c_void,
        ) -> i32 {
            unsafe {
                let v = &mut *(ctx as *mut Vec<LiteralVal>);
                let lv = &*val;
                v.push(LiteralVal {
                    tag: lv.tag,
                    u64_val: lv.__bindgen_anon_1.u64_val,
                });
            }
            0
        }
        unsafe {
            abcd_file_sys::abc_literal_enumerate_vals_by_index(
                self.handle,
                index,
                Some(cb),
                &mut vals as *mut Vec<LiteralVal> as *mut std::ffi::c_void,
            );
        }
        vals
    }
}

impl Drop for SysLiteralAccessor<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_literal_close(self.handle) };
        }
    }
}

// ========== Module Accessor ==========

/// A module record entry.
#[derive(Debug, Clone)]
pub struct ModuleRecord {
    pub tag: u8,
    pub export_name_off: u32,
    pub module_request_idx: u32,
    pub import_name_off: u32,
    pub local_name_off: u32,
}

/// Safe wrapper around C++ ModuleDataAccessor.
pub struct SysModuleAccessor<'f> {
    handle: *mut abcd_file_sys::AbcModuleAccessor,
    _file: &'f SysFile,
}

impl<'f> SysModuleAccessor<'f> {
    fn open(file: &'f SysFile, offset: u32) -> Result<Self, ParseError> {
        let handle = unsafe { abcd_file_sys::abc_module_open(file.handle(), offset) };
        if handle.is_null() {
            return Err(ParseError::Io(format!(
                "abc_module_open failed at offset {offset}"
            )));
        }
        Ok(Self {
            handle,
            _file: file,
        })
    }

    /// Number of request modules.
    pub fn num_requests(&self) -> u32 {
        unsafe { abcd_file_sys::abc_module_num_requests(self.handle) }
    }

    /// Get request module string offset by index.
    pub fn request_off(&self, idx: u32) -> Option<u32> {
        let off = unsafe { abcd_file_sys::abc_module_request_off(self.handle, idx) };
        if off == u32::MAX { None } else { Some(off) }
    }

    /// Collect all module records.
    pub fn records(&self) -> Vec<ModuleRecord> {
        let mut records = Vec::new();
        unsafe extern "C" fn cb(
            tag: u8,
            export_name_off: u32,
            module_request_idx: u32,
            import_name_off: u32,
            local_name_off: u32,
            ctx: *mut std::ffi::c_void,
        ) -> i32 {
            unsafe {
                let v = &mut *(ctx as *mut Vec<ModuleRecord>);
                v.push(ModuleRecord {
                    tag,
                    export_name_off,
                    module_request_idx,
                    import_name_off,
                    local_name_off,
                });
            }
            0
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
}

impl Drop for SysModuleAccessor<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_module_close(self.handle) };
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
