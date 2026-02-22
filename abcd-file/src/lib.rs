//! ABC binary file format reader, writer, and utilities for ArkCompiler bytecode files.

pub mod annotation;
pub mod builder;
pub mod class;
pub mod code;
pub mod debug;
pub mod error;
pub mod field;
pub mod index;
pub mod literal;
pub mod method;
pub mod module;
pub mod proto;
pub mod types;
pub mod util;
pub mod version;

pub use abcd_isa::EntityId;
pub use error::{Error, Result};
pub use types::*;

// Backward-compat aliases for downstream crates in this workspace.
pub type AbcFile = File;
pub use module as module_record;

use std::ffi::CString;
use std::path::Path;

// ---- pub(crate) helpers ----

/// Callback for collecting entity IDs from C++ enumerate functions.
pub(crate) unsafe extern "C" fn entity_id_cb(id: u32, ctx: *mut std::ffi::c_void) -> i32 {
    unsafe {
        let v = &mut *(ctx as *mut Vec<EntityId>);
        v.push(EntityId(id));
    }
    0
}

/// Collect entity IDs from a C++ enumerate function.
pub(crate) fn collect_entity_ids<F>(f: F) -> Vec<EntityId>
where
    F: FnOnce(unsafe extern "C" fn(u32, *mut std::ffi::c_void) -> i32, *mut std::ffi::c_void),
{
    let mut ids = Vec::new();
    f(
        entity_id_cb,
        &mut ids as *mut Vec<EntityId> as *mut std::ffi::c_void,
    );
    ids
}

// ---- FileType ----

/// ABC file type classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FileType {
    /// Invalid or unrecognized file.
    Invalid,
    /// Dynamic ABC file (EcmaScript/ArkTS).
    Dynamic,
    /// Static ABC file (PandaAssembly).
    Static,
}

impl std::fmt::Display for FileType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Invalid => "invalid",
            Self::Dynamic => "dynamic",
            Self::Static => "static",
        })
    }
}

// ---- IndexHeader ----

/// Index header (mirrors AbcIndexHeader from the C++ runtime).
#[derive(Debug, Clone, Copy)]
pub struct IndexHeader {
    pub start: u32,
    pub end: u32,
    pub class_idx_size: u32,
    pub class_idx_off: u32,
    pub method_idx_size: u32,
    pub method_idx_off: u32,
    pub field_idx_size: u32,
    pub field_idx_off: u32,
    pub proto_idx_size: u32,
    pub proto_idx_off: u32,
}

// ---- File ----

/// An opened ABC file backed by the C++ runtime.
pub struct File {
    handle: *mut abcd_file_sys::AbcFileHandle,
    data: Vec<u8>,
}

// SAFETY: The C++ AbcFileHandle is read-only after construction.
unsafe impl Send for File {}
unsafe impl Sync for File {}

impl File {
    /// Open an ABC file from owned bytes.
    pub fn open(data: Vec<u8>) -> Result<Self> {
        let handle = unsafe { abcd_file_sys::abc_file_open(data.as_ptr(), data.len()) };
        if handle.is_null() {
            return Err(Error::Ffi(
                "abc_file_open failed (invalid magic, corrupt data, or allocation failure)".into(),
            ));
        }
        Ok(Self { handle, data })
    }

    /// Open an ABC file from a filesystem path.
    pub fn open_path(path: &Path) -> Result<Self> {
        let data = std::fs::read(path).map_err(|e| Error::Io(e.to_string()))?;
        Self::open(data)
    }

    /// Internal handle accessor for sub-modules.
    pub(crate) fn handle(&self) -> *mut abcd_file_sys::AbcFileHandle {
        self.handle
    }

    // --- Header ---

    pub fn version(&self) -> abcd_isa::Version {
        let mut out = [0u8; 4];
        unsafe { abcd_file_sys::abc_file_version(self.handle, out.as_mut_ptr()) };
        abcd_isa::Version::from(out)
    }

    pub fn file_size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_size(self.handle) }
    }

    pub fn num_classes(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_num_classes(self.handle) }
    }

    pub fn num_literal_arrays(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_num_literalarrays(self.handle) }
    }

    pub fn literal_array_idx_off(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_literalarray_idx_off(self.handle) }
    }

    pub fn validate_checksum(&self) -> bool {
        unsafe { abcd_file_sys::abc_file_validate_checksum(self.handle) != 0 }
    }

    pub fn checksum(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_checksum(self.handle) }
    }

    pub fn foreign_off(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_foreign_off(self.handle) }
    }

    pub fn foreign_size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_foreign_size(self.handle) }
    }

    pub fn class_idx_off(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_class_idx_off(self.handle) }
    }

    pub fn num_lnps(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_num_lnps(self.handle) }
    }

    pub fn lnp_idx_off(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_lnp_idx_off(self.handle) }
    }

    pub fn index_section_off(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_index_section_off(self.handle) }
    }

    // --- Strings ---

    /// Get the string at the given offset.
    ///
    /// Note: the C++ runtime returns length 0 for both empty strings and
    /// missing/invalid offsets, so this method cannot distinguish the two
    /// cases — both return `Ok(String::new())`.
    pub fn get_string(&self, offset: EntityId) -> Result<String> {
        // First call with NULL buf to query the required length.
        let len = unsafe {
            abcd_file_sys::abc_file_get_string(self.handle, offset.0, std::ptr::null_mut(), 0)
        };
        // len == 0 is a valid empty string; the C++ side returns 0 for both
        // empty strings and missing entries, but offset validity is checked
        // upstream so we treat 0 as empty.
        if len == 0 {
            return Ok(String::new());
        }
        let mut buf = vec![0u8; len];
        let written = unsafe {
            abcd_file_sys::abc_file_get_string(
                self.handle,
                offset.0,
                buf.as_mut_ptr() as *mut std::ffi::c_char,
                buf.len(),
            )
        };
        buf.truncate(written);
        String::from_utf8(buf).map_err(|e| Error::Ffi(e.to_string()))
    }

    pub fn string_utf16_len(&self, offset: EntityId) -> u32 {
        unsafe { abcd_file_sys::abc_file_get_string_utf16_len(self.handle, offset.0) }
    }

    pub fn string_is_ascii(&self, offset: EntityId) -> bool {
        unsafe { abcd_file_sys::abc_file_get_string_is_ascii(self.handle, offset.0) != 0 }
    }

    // --- Index resolution ---

    pub fn resolve_method_index(&self, entity_off: EntityId, idx: u16) -> Option<EntityId> {
        let v = unsafe { abcd_file_sys::abc_resolve_method_index(self.handle, entity_off.0, idx) };
        if v == u32::MAX {
            None
        } else {
            Some(EntityId(v))
        }
    }

    pub fn resolve_class_index(&self, entity_off: EntityId, idx: u16) -> Option<EntityId> {
        let v = unsafe { abcd_file_sys::abc_resolve_class_index(self.handle, entity_off.0, idx) };
        if v == u32::MAX {
            None
        } else {
            Some(EntityId(v))
        }
    }

    pub fn resolve_field_index(&self, entity_off: EntityId, idx: u16) -> Option<EntityId> {
        let v = unsafe { abcd_file_sys::abc_resolve_field_index(self.handle, entity_off.0, idx) };
        if v == u32::MAX {
            None
        } else {
            Some(EntityId(v))
        }
    }

    pub fn resolve_proto_index(&self, entity_off: EntityId, idx: u16) -> Option<EntityId> {
        let v = unsafe { abcd_file_sys::abc_resolve_proto_index(self.handle, entity_off.0, idx) };
        if v == u32::MAX {
            None
        } else {
            Some(EntityId(v))
        }
    }

    pub fn resolve_offset_by_index(&self, entity_off: EntityId, idx: u16) -> Option<EntityId> {
        let v =
            unsafe { abcd_file_sys::abc_resolve_offset_by_index(self.handle, entity_off.0, idx) };
        if v == u32::MAX {
            None
        } else {
            Some(EntityId(v))
        }
    }

    pub fn resolve_lnp_index(&self, idx: u32) -> Option<EntityId> {
        let v = unsafe { abcd_file_sys::abc_resolve_lnp_index(self.handle, idx) };
        if v == u32::MAX {
            None
        } else {
            Some(EntityId(v))
        }
    }

    // --- Entity queries ---

    pub fn is_external(&self, entity_off: EntityId) -> bool {
        unsafe { abcd_file_sys::abc_file_is_external(self.handle, entity_off.0) != 0 }
    }

    pub fn class_id_by_name(&self, name: &str) -> Result<Option<EntityId>> {
        let c = CString::new(name)
            .map_err(|_| Error::Ffi("class name contains interior null byte".into()))?;
        let v = unsafe { abcd_file_sys::abc_file_get_class_id(self.handle, c.as_ptr()) };
        Ok(if v == u32::MAX {
            None
        } else {
            Some(EntityId(v))
        })
    }

    pub fn raw_data(&self) -> &[u8] {
        &self.data
    }

    /// Determine file type from raw bytes.
    pub fn file_type(data: &[u8]) -> FileType {
        // Clamp to i32::MAX — safe because abc_file_get_type only inspects the
        // first few header bytes (magic + version), well within i32 range.
        let len: i32 = data.len().try_into().unwrap_or(i32::MAX);
        let v = unsafe { abcd_file_sys::abc_file_get_type(data.as_ptr(), len) };
        match v {
            0 => FileType::Dynamic,
            1 => FileType::Static,
            _ => FileType::Invalid,
        }
    }

    // --- Index headers ---

    pub fn num_index_headers(&self) -> u32 {
        unsafe { abcd_file_sys::abc_file_num_index_headers(self.handle) }
    }

    pub fn index_header(&self, idx: u32) -> Option<IndexHeader> {
        if idx >= self.num_index_headers() {
            return None;
        }
        let mut out = abcd_file_sys::AbcIndexHeader {
            start: 0,
            end: 0,
            class_idx_size: 0,
            class_idx_off: 0,
            method_idx_size: 0,
            method_idx_off: 0,
            field_idx_size: 0,
            field_idx_off: 0,
            proto_idx_size: 0,
            proto_idx_off: 0,
        };
        unsafe { abcd_file_sys::abc_file_get_index_header(self.handle, idx, &mut out) };
        Some(IndexHeader {
            start: out.start,
            end: out.end,
            class_idx_size: out.class_idx_size,
            class_idx_off: out.class_idx_off,
            method_idx_size: out.method_idx_size,
            method_idx_off: out.method_idx_off,
            field_idx_size: out.field_idx_size,
            field_idx_off: out.field_idx_off,
            proto_idx_size: out.proto_idx_size,
            proto_idx_off: out.proto_idx_off,
        })
    }

    // --- Offset iterators ---

    pub fn class_offsets(&self) -> Vec<EntityId> {
        let n = self.num_classes();
        (0..n)
            .map(|i| EntityId(unsafe { abcd_file_sys::abc_file_class_offset(self.handle, i) }))
            .collect()
    }

    /// Get the offset of a single class by index. Returns `None` if out of bounds.
    pub fn class_offset(&self, idx: u32) -> Option<EntityId> {
        if idx >= self.num_classes() {
            return None;
        }
        Some(EntityId(unsafe {
            abcd_file_sys::abc_file_class_offset(self.handle, idx)
        }))
    }

    pub fn literal_array_offsets(&self) -> Vec<EntityId> {
        let n = self.num_literal_arrays();
        (0..n)
            .map(|i| {
                EntityId(unsafe { abcd_file_sys::abc_file_literalarray_offset(self.handle, i) })
            })
            .collect()
    }

    /// Get the offset of a single literal array by index. Returns `None` if out of bounds.
    pub fn literal_array_offset(&self, idx: u32) -> Option<EntityId> {
        if idx >= self.num_literal_arrays() {
            return None;
        }
        Some(EntityId(unsafe {
            abcd_file_sys::abc_file_literalarray_offset(self.handle, idx)
        }))
    }

    // --- Accessor factory methods ---

    pub fn class(&self, offset: EntityId) -> Result<class::Class<'_>> {
        class::Class::open(self, offset)
    }

    pub fn method(&self, offset: EntityId) -> Result<method::Method<'_>> {
        method::Method::open(self, offset)
    }

    pub fn field(&self, offset: EntityId) -> Result<field::Field<'_>> {
        field::Field::open(self, offset)
    }

    pub fn proto(&self, offset: EntityId) -> Result<proto::Proto<'_>> {
        proto::Proto::open(self, offset)
    }

    pub fn code(&self, offset: EntityId) -> Result<code::Code<'_>> {
        code::Code::open(self, offset)
    }

    pub fn annotation(&self, offset: EntityId) -> Result<annotation::Annotation<'_>> {
        annotation::Annotation::open(self, offset)
    }

    pub fn literal(&self, literal_data_off: EntityId) -> Result<literal::Literal<'_>> {
        literal::Literal::open(self, literal_data_off)
    }

    pub fn module(&self, offset: EntityId) -> Result<module::Module<'_>> {
        module::Module::open(self, offset)
    }

    pub fn debug_info(&self) -> Result<debug::DebugInfo<'_>> {
        debug::DebugInfo::open(self)
    }

    pub fn index(&self, method_off: EntityId) -> Result<index::Index<'_>> {
        index::Index::open(self, method_off)
    }

    // --- Static quick-access (no accessor allocation) ---

    /// Get a method's name offset without opening a Method accessor.
    pub fn method_name_off(&self, method_off: EntityId) -> EntityId {
        EntityId(unsafe {
            abcd_file_sys::abc_method_get_name_off_static(self.handle, method_off.0)
        })
    }

    /// Get a method's name as a string without opening a Method accessor.
    pub fn method_name(&self, method_off: EntityId) -> Result<String> {
        // Query length first.
        let len = unsafe {
            abcd_file_sys::abc_method_get_name_static(
                self.handle,
                method_off.0,
                std::ptr::null_mut(),
                0,
            )
        };
        if len == 0 {
            return Ok(String::new());
        }
        let mut buf = vec![0u8; len];
        let written = unsafe {
            abcd_file_sys::abc_method_get_name_static(
                self.handle,
                method_off.0,
                buf.as_mut_ptr() as *mut std::ffi::c_char,
                buf.len(),
            )
        };
        buf.truncate(written);
        String::from_utf8(buf).map_err(|e| Error::Ffi(e.to_string()))
    }

    /// Get a method's class ID without opening a Method accessor.
    pub fn method_class_id(&self, method_off: EntityId) -> EntityId {
        EntityId(unsafe {
            abcd_file_sys::abc_method_get_class_id_static(self.handle, method_off.0)
        })
    }

    /// Get a method's proto ID without opening a Method accessor.
    pub fn method_proto_id(&self, method_off: EntityId) -> EntityId {
        EntityId(unsafe {
            abcd_file_sys::abc_method_get_proto_id_static(self.handle, method_off.0)
        })
    }

    /// Get a field's name offset without opening a Field accessor.
    pub fn field_name_off(&self, field_off: EntityId) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_field_get_name_off_static(self.handle, field_off.0) })
    }

    /// Get a field's type ID without opening a Field accessor.
    pub fn field_type_id(&self, field_off: EntityId) -> u32 {
        unsafe { abcd_file_sys::abc_field_get_type_static(self.handle, field_off.0) }
    }

    /// Get a code block's vreg count without opening a Code accessor.
    pub fn code_num_vregs(&self, code_off: EntityId) -> u32 {
        unsafe { abcd_file_sys::abc_code_get_num_vregs_static(self.handle, code_off.0) }
    }

    /// Get a raw pointer to a code block's instructions without opening a Code accessor.
    ///
    /// # Safety
    /// The returned pointer is valid for the lifetime of this `File`.
    /// The caller must not dereference the pointer beyond `code_size` bytes.
    pub unsafe fn code_instructions_ptr(&self, code_off: EntityId) -> *const u8 {
        unsafe { abcd_file_sys::abc_code_get_instructions_static(self.handle, code_off.0) }
    }
}

impl Drop for File {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_file_close(self.handle) };
        }
    }
}

impl std::fmt::Debug for File {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("File")
            .field("file_size", &self.file_size())
            .field("num_classes", &self.num_classes())
            .finish()
    }
}
