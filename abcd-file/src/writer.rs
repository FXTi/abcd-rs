//! ABC file writer — safe Rust wrapper around abcd-file-sys's AbcBuilder.
//!
//! Provides a builder API for constructing ABC binary files from scratch.

use crate::error::ParseError;
use std::ffi::CString;

/// Handle index for items created by the builder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassHandle(u32);

/// Handle for a method added to a class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MethodHandle(u32);

/// Handle for a field added to a class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FieldHandle(u32);

/// Handle for a literal array.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LiteralArrayHandle(u32);

/// Builder for constructing ABC binary files.
///
/// Uses the C++ ItemContainer and MemoryWriter from arkcompiler
/// via abcd-file-sys FFI bindings.
pub struct AbcWriter {
    inner: *mut abcd_file_sys::AbcBuilder,
}

// SAFETY: AbcBuilder is single-threaded but can be moved between threads
unsafe impl Send for AbcWriter {}

impl AbcWriter {
    /// Create a new ABC file builder with default API version (12, "beta1").
    pub fn new() -> Self {
        let inner = unsafe { abcd_file_sys::abc_builder_new() };
        assert!(!inner.is_null(), "failed to allocate AbcBuilder");
        let mut w = Self { inner };
        w.set_api(12, "beta1");
        w
    }

    /// Set the target API version.
    pub fn set_api(&mut self, api: u8, sub_api: &str) {
        let c_sub = CString::new(sub_api).expect("sub_api contains null byte");
        unsafe {
            abcd_file_sys::abc_builder_set_api(self.inner, api, c_sub.as_ptr());
        }
    }

    /// Add a string to the string table. Returns a string handle index.
    pub fn add_string(&mut self, s: &str) -> u32 {
        let c_str = CString::new(s).expect("string contains null byte");
        unsafe { abcd_file_sys::abc_builder_add_string(self.inner, c_str.as_ptr()) }
    }

    /// Create or get a class by descriptor (e.g. "L_GLOBAL;").
    pub fn add_class(&mut self, descriptor: &str) -> ClassHandle {
        let c_desc = CString::new(descriptor).expect("descriptor contains null byte");
        let idx = unsafe { abcd_file_sys::abc_builder_add_class(self.inner, c_desc.as_ptr()) };
        ClassHandle(idx)
    }

    /// Create or get a foreign class by descriptor.
    pub fn add_foreign_class(&mut self, descriptor: &str) -> u32 {
        let c_desc = CString::new(descriptor).expect("descriptor contains null byte");
        unsafe { abcd_file_sys::abc_builder_add_foreign_class(self.inner, c_desc.as_ptr()) }
    }

    /// Create a literal array with the given ID string.
    pub fn add_literal_array(&mut self, id: &str) -> LiteralArrayHandle {
        let c_id = CString::new(id).expect("id contains null byte");
        let idx =
            unsafe { abcd_file_sys::abc_builder_add_literal_array(self.inner, c_id.as_ptr()) };
        LiteralArrayHandle(idx)
    }

    /// Add a method to a class.
    ///
    /// Uses a default TAGGED return type proto (ECMAScript convention).
    /// For custom protos, use `create_proto` + `add_method_with_proto`.
    ///
    /// - `class_handle`: handle from `add_class`
    /// - `name`: method name
    /// - `access_flags`: ACC_PUBLIC, ACC_STATIC, etc.
    /// - `code`: raw bytecode instructions (can be empty for abstract methods)
    /// - `num_vregs`: number of virtual registers
    /// - `num_args`: number of arguments
    pub fn add_method(
        &mut self,
        class_handle: ClassHandle,
        name: &str,
        access_flags: u32,
        code: &[u8],
        num_vregs: u32,
        num_args: u32,
    ) -> Result<MethodHandle, ParseError> {
        // TAGGED = 0x0d
        let proto = unsafe {
            abcd_file_sys::abc_builder_create_proto(self.inner, 0x0d, std::ptr::null(), 0)
        };
        self.add_method_with_proto(
            class_handle,
            name,
            proto,
            access_flags,
            code,
            num_vregs,
            num_args,
        )
    }

    /// Add a method to a class with an explicit proto handle.
    pub fn add_method_with_proto(
        &mut self,
        class_handle: ClassHandle,
        name: &str,
        proto_handle: u32,
        access_flags: u32,
        code: &[u8],
        num_vregs: u32,
        num_args: u32,
    ) -> Result<MethodHandle, ParseError> {
        let c_name = CString::new(name).expect("name contains null byte");
        let (code_ptr, code_len) = if code.is_empty() {
            (std::ptr::null(), 0)
        } else {
            (code.as_ptr(), code.len() as u32)
        };
        let idx = unsafe {
            abcd_file_sys::abc_builder_class_add_method_with_proto(
                self.inner,
                class_handle.0,
                c_name.as_ptr(),
                proto_handle,
                access_flags,
                code_ptr,
                code_len,
                num_vregs,
                num_args,
            )
        };
        if idx == u32::MAX {
            return Err(ParseError::Io("failed to add method".into()));
        }
        Ok(MethodHandle(idx))
    }

    /// Add a field to a class.
    ///
    /// - `type_id`: TypeId encoding (0x0d = TAGGED for ECMAScript)
    pub fn add_field(
        &mut self,
        class_handle: ClassHandle,
        name: &str,
        type_id: u8,
        access_flags: u32,
    ) -> Result<FieldHandle, ParseError> {
        let c_name = CString::new(name).expect("name contains null byte");
        let idx = unsafe {
            abcd_file_sys::abc_builder_class_add_field(
                self.inner,
                class_handle.0,
                c_name.as_ptr(),
                type_id,
                access_flags,
            )
        };
        if idx == u32::MAX {
            return Err(ParseError::Io("failed to add field".into()));
        }
        Ok(FieldHandle(idx))
    }

    /// Add a u8 item to a literal array (used for tags and small values).
    pub fn literal_array_add_u8(&mut self, handle: LiteralArrayHandle, val: u8) {
        unsafe {
            abcd_file_sys::abc_builder_literal_array_add_u8(self.inner, handle.0, val);
        }
    }

    /// Add a u16 item to a literal array.
    pub fn literal_array_add_u16(&mut self, handle: LiteralArrayHandle, val: u16) {
        unsafe {
            abcd_file_sys::abc_builder_literal_array_add_u16(self.inner, handle.0, val);
        }
    }

    /// Add a u32 item to a literal array.
    pub fn literal_array_add_u32(&mut self, handle: LiteralArrayHandle, val: u32) {
        unsafe {
            abcd_file_sys::abc_builder_literal_array_add_u32(self.inner, handle.0, val);
        }
    }

    /// Add a u64 item to a literal array.
    pub fn literal_array_add_u64(&mut self, handle: LiteralArrayHandle, val: u64) {
        unsafe {
            abcd_file_sys::abc_builder_literal_array_add_u64(self.inner, handle.0, val);
        }
    }

    /// Finalize the builder and produce the ABC binary data.
    ///
    /// The returned `Vec<u8>` is a complete, valid ABC file that can be
    /// parsed by `AbcFile::parse()`.
    pub fn finalize(self) -> Result<Vec<u8>, ParseError> {
        let mut out_len: u32 = 0;
        let ptr = unsafe { abcd_file_sys::abc_builder_finalize(self.inner, &mut out_len) };
        if ptr.is_null() {
            return Err(ParseError::Io("builder finalize failed".into()));
        }
        let data = unsafe { std::slice::from_raw_parts(ptr, out_len as usize) };
        Ok(data.to_vec())
    }
}

impl Default for AbcWriter {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for AbcWriter {
    fn drop(&mut self) {
        if !self.inner.is_null() {
            unsafe {
                abcd_file_sys::abc_builder_free(self.inner);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::AbcFile;
    use crate::class::ClassData;
    use crate::method::MethodData;

    #[test]
    fn basic_roundtrip() {
        let mut w = AbcWriter::new();

        let cls = w.add_class("L_GLOBAL;");
        // returnundefined opcode = 0xa0
        let code = [0xa0u8];
        let _m = w
            .add_method(cls, "func_main_0", 0x0001, &code, 1, 0)
            .unwrap();

        let data = w.finalize().unwrap();
        assert!(!data.is_empty());

        // Parse the output back
        let abc = AbcFile::parse(data).unwrap();
        assert!(abc.header.num_classes > 0);
    }

    #[test]
    fn roundtrip_multiple_methods() {
        let mut w = AbcWriter::new();
        let cls = w.add_class("L_GLOBAL;");

        let code = [0xa0u8]; // returnundefined
        w.add_method(cls, "func_main_0", 0x0001, &code, 1, 0)
            .unwrap();
        w.add_method(cls, "helper", 0x0001, &code, 2, 1).unwrap();
        w.add_method(cls, "init", 0x0009, &code, 0, 0) // PUBLIC | STATIC
            .unwrap();

        let data = w.finalize().unwrap();
        let abc = AbcFile::parse(data).unwrap();

        // Find our class and verify method count
        let class_off = abc.class_offsets().next().unwrap();
        let cls_data = ClassData::parse(abc.data(), class_off).unwrap();
        assert_eq!(cls_data.name, "L_GLOBAL;");
        assert_eq!(cls_data.num_methods, 3);
    }

    #[test]
    fn roundtrip_with_field() {
        let mut w = AbcWriter::new();
        let cls = w.add_class("L_GLOBAL;");

        let code = [0xa0u8];
        w.add_method(cls, "func_main_0", 0x0001, &code, 1, 0)
            .unwrap();
        // type_id 0x0d = TAGGED
        w.add_field(cls, "myField", 0x0d, 0x0001).unwrap();

        let data = w.finalize().unwrap();
        let abc = AbcFile::parse(data).unwrap();

        let class_off = abc.class_offsets().next().unwrap();
        let cls_data = ClassData::parse(abc.data(), class_off).unwrap();
        assert_eq!(cls_data.num_fields, 1);
    }

    #[test]
    fn roundtrip_with_strings() {
        let mut w = AbcWriter::new();
        w.add_string("hello");
        w.add_string("world");

        let cls = w.add_class("L_GLOBAL;");
        let code = [0xa0u8];
        w.add_method(cls, "func_main_0", 0x0001, &code, 1, 0)
            .unwrap();

        let data = w.finalize().unwrap();
        let abc = AbcFile::parse(data).unwrap();
        // File should parse without error; strings are in the string table
        assert!(abc.header.num_classes > 0);
    }

    #[test]
    fn roundtrip_with_literal_array() {
        let mut w = AbcWriter::new();
        let cls = w.add_class("L_GLOBAL;");
        let code = [0xa0u8];
        w.add_method(cls, "func_main_0", 0x0001, &code, 1, 0)
            .unwrap();

        let _la = w.add_literal_array("0");
        // Empty literal array — no items added

        let data = w.finalize().unwrap();
        let abc = AbcFile::parse(data).unwrap();
        assert!(abc.header.num_literalarrays > 0);
    }

    #[test]
    fn roundtrip_method_names_preserved() {
        let mut w = AbcWriter::new();
        let cls = w.add_class("L_GLOBAL;");
        let code = [0xa0u8];

        let names = ["func_main_0", "alpha", "beta"];
        for name in &names {
            w.add_method(cls, name, 0x0001, &code, 1, 0).unwrap();
        }

        let data = w.finalize().unwrap();
        let abc = AbcFile::parse(data).unwrap();

        let class_off = abc.class_offsets().next().unwrap();
        let cls_data = ClassData::parse(abc.data(), class_off).unwrap();

        // Parse each method and collect names
        let mut found_names: Vec<String> = cls_data
            .method_offsets
            .iter()
            .map(|&off| MethodData::parse(abc.data(), off as u32).unwrap().name)
            .collect();
        found_names.sort();

        let mut expected: Vec<&str> = names.to_vec();
        expected.sort();
        assert_eq!(found_names, expected);
    }

    #[test]
    fn finalize_produces_valid_magic() {
        let mut w = AbcWriter::new();
        let cls = w.add_class("L_GLOBAL;");
        let code = [0xa0u8];
        w.add_method(cls, "func_main_0", 0x0001, &code, 1, 0)
            .unwrap();

        let data = w.finalize().unwrap();
        // ABC magic: "PANDA\0\0\0"
        assert_eq!(&data[..8], b"PANDA\0\0\0");
    }
}
