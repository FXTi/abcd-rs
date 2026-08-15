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

/// Handle for an annotation item.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AnnotationHandle(u32);

/// Handle for a proto (function signature).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProtoHandle(pub(crate) u32);

/// Handle for a standalone code item.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CodeHandle(u32);

/// Handle for a debug info item.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DebugInfoHandle(u32);

/// Handle for a line number program.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LnpHandle(u32);

/// Definition of an annotation element for `create_annotation`.
#[repr(C)]
pub struct AnnotationElemDef {
    pub name_string_handle: u32,
    pub tag: u8,
    pub value: u32,
}

/// Definition of a catch block for `code_add_try_block`.
pub struct CatchBlockDef {
    /// Class handle for the exception type, or `u32::MAX` for catch-all.
    pub type_class_handle: u32,
    pub handler_pc: u32,
    pub code_size: u32,
}

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
        let proto = self.create_proto(0x0d, &[]);
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
        proto_handle: ProtoHandle,
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
                proto_handle.0,
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

    // ---- Proto ----

    /// Create a proto (function signature) with the given return type and parameter types.
    ///
    /// Type IDs use the ArkCompiler encoding (e.g. 0x0d = TAGGED).
    pub fn create_proto(&mut self, return_type: u8, param_types: &[u8]) -> ProtoHandle {
        let (ptr, len) = if param_types.is_empty() {
            (std::ptr::null(), 0)
        } else {
            (param_types.as_ptr(), param_types.len() as u32)
        };
        let idx =
            unsafe { abcd_file_sys::abc_builder_create_proto(self.inner, return_type, ptr, len) };
        ProtoHandle(idx)
    }

    // ---- Class configuration ----

    /// Set access flags on a class.
    pub fn class_set_access_flags(&mut self, class: ClassHandle, flags: u32) {
        unsafe {
            abcd_file_sys::abc_builder_class_set_access_flags(self.inner, class.0, flags);
        }
    }

    /// Set the source language for a class.
    pub fn class_set_source_lang(&mut self, class: ClassHandle, lang: u8) {
        unsafe {
            abcd_file_sys::abc_builder_class_set_source_lang(self.inner, class.0, lang);
        }
    }

    /// Set the super class. `super_handle` uses the tagged convention:
    /// high bit 0x80000000 = foreign class handle, otherwise regular class handle.
    pub fn class_set_super_class(&mut self, class: ClassHandle, super_handle: u32) {
        unsafe {
            abcd_file_sys::abc_builder_class_set_super_class(self.inner, class.0, super_handle);
        }
    }

    /// Add an interface to a class. `iface_handle` uses the same tagged convention
    /// as `class_set_super_class`.
    pub fn class_add_interface(&mut self, class: ClassHandle, iface_handle: u32) {
        unsafe {
            abcd_file_sys::abc_builder_class_add_interface(self.inner, class.0, iface_handle);
        }
    }

    /// Set the source file for a class (string handle from `add_string`).
    pub fn class_set_source_file(&mut self, class: ClassHandle, string_handle: u32) {
        unsafe {
            abcd_file_sys::abc_builder_class_set_source_file(self.inner, class.0, string_handle);
        }
    }

    // ---- Method configuration ----

    /// Set the source language for a method.
    pub fn method_set_source_lang(&mut self, method: MethodHandle, lang: u8) {
        unsafe {
            abcd_file_sys::abc_builder_method_set_source_lang(self.inner, method.0, lang);
        }
    }

    /// Set the function kind for a method.
    pub fn method_set_function_kind(&mut self, method: MethodHandle, kind: u8) {
        unsafe {
            abcd_file_sys::abc_builder_method_set_function_kind(self.inner, method.0, kind);
        }
    }

    /// Attach a code item to a method.
    pub fn method_set_code(&mut self, method: MethodHandle, code: CodeHandle) {
        unsafe {
            abcd_file_sys::abc_builder_method_set_code(self.inner, method.0, code.0);
        }
    }

    /// Attach debug info to a method.
    pub fn method_set_debug_info(&mut self, method: MethodHandle, debug: DebugInfoHandle) {
        unsafe {
            abcd_file_sys::abc_builder_method_set_debug_info(self.inner, method.0, debug.0);
        }
    }

    // ---- Field initial values ----

    /// Set an i32 initial value on a field.
    pub fn field_set_value_i32(&mut self, field: FieldHandle, val: i32) {
        unsafe {
            abcd_file_sys::abc_builder_field_set_value_i32(self.inner, field.0, val);
        }
    }

    /// Set an i64 initial value on a field.
    pub fn field_set_value_i64(&mut self, field: FieldHandle, val: i64) {
        unsafe {
            abcd_file_sys::abc_builder_field_set_value_i64(self.inner, field.0, val);
        }
    }

    /// Set an f32 initial value on a field.
    pub fn field_set_value_f32(&mut self, field: FieldHandle, val: f32) {
        unsafe {
            abcd_file_sys::abc_builder_field_set_value_f32(self.inner, field.0, val);
        }
    }

    /// Set an f64 initial value on a field.
    pub fn field_set_value_f64(&mut self, field: FieldHandle, val: f64) {
        unsafe {
            abcd_file_sys::abc_builder_field_set_value_f64(self.inner, field.0, val);
        }
    }

    // ---- Code + Try blocks ----

    /// Create a standalone code item.
    pub fn create_code(&mut self, bytecode: &[u8], num_vregs: u32, num_args: u32) -> CodeHandle {
        let (ptr, len) = if bytecode.is_empty() {
            (std::ptr::null(), 0)
        } else {
            (bytecode.as_ptr(), bytecode.len() as u32)
        };
        let idx = unsafe {
            abcd_file_sys::abc_builder_create_code(self.inner, num_vregs, num_args, ptr, len)
        };
        CodeHandle(idx)
    }

    /// Add a try block with catch handlers to a code item.
    pub fn code_add_try_block(
        &mut self,
        code: CodeHandle,
        start_pc: u32,
        length: u32,
        catches: &[CatchBlockDef],
    ) {
        let c_catches: Vec<abcd_file_sys::AbcCatchBlockDef> = catches
            .iter()
            .map(|c| abcd_file_sys::AbcCatchBlockDef {
                type_class_handle: c.type_class_handle,
                handler_pc: c.handler_pc,
                code_size: c.code_size,
            })
            .collect();
        unsafe {
            abcd_file_sys::abc_builder_code_add_try_block(
                self.inner,
                code.0,
                start_pc,
                length,
                c_catches.as_ptr(),
                c_catches.len() as u32,
            );
        }
    }

    // ---- Debug info + LNP ----

    /// Create a line number program.
    pub fn create_lnp(&mut self) -> LnpHandle {
        let idx = unsafe { abcd_file_sys::abc_builder_create_lnp(self.inner) };
        LnpHandle(idx)
    }

    /// Create a debug info item attached to a line number program.
    pub fn create_debug_info(
        &mut self,
        lnp: LnpHandle,
        line_number: u32,
    ) -> Result<DebugInfoHandle, ParseError> {
        let idx =
            unsafe { abcd_file_sys::abc_builder_create_debug_info(self.inner, lnp.0, line_number) };
        if idx == u32::MAX {
            return Err(ParseError::Io("failed to create debug info".into()));
        }
        Ok(DebugInfoHandle(idx))
    }

    /// Add a parameter name to debug info.
    pub fn debug_add_param(&mut self, debug: DebugInfoHandle, name_string_handle: u32) {
        unsafe {
            abcd_file_sys::abc_builder_debug_add_param(self.inner, debug.0, name_string_handle);
        }
    }

    /// Emit an "end" opcode in the line number program.
    pub fn lnp_emit_end(&mut self, lnp: LnpHandle) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_end(self.inner, lnp.0);
        }
    }

    /// Emit an "advance PC" opcode.
    pub fn lnp_emit_advance_pc(&mut self, lnp: LnpHandle, debug: DebugInfoHandle, value: u32) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_advance_pc(self.inner, lnp.0, debug.0, value);
        }
    }

    /// Emit an "advance line" opcode.
    pub fn lnp_emit_advance_line(&mut self, lnp: LnpHandle, debug: DebugInfoHandle, value: i32) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_advance_line(self.inner, lnp.0, debug.0, value);
        }
    }

    /// Emit a column opcode.
    pub fn lnp_emit_column(
        &mut self,
        lnp: LnpHandle,
        debug: DebugInfoHandle,
        pc_inc: u32,
        column: u32,
    ) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_column(self.inner, lnp.0, debug.0, pc_inc, column);
        }
    }

    /// Emit a "start local" opcode.
    pub fn lnp_emit_start_local(
        &mut self,
        lnp: LnpHandle,
        debug: DebugInfoHandle,
        reg: i32,
        name_handle: u32,
        type_handle: u32,
    ) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_start_local(
                self.inner,
                lnp.0,
                debug.0,
                reg,
                name_handle,
                type_handle,
            );
        }
    }

    /// Emit an "end local" opcode.
    pub fn lnp_emit_end_local(&mut self, lnp: LnpHandle, reg: i32) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_end_local(self.inner, lnp.0, reg);
        }
    }

    /// Emit a "set file" opcode.
    pub fn lnp_emit_set_file(
        &mut self,
        lnp: LnpHandle,
        debug: DebugInfoHandle,
        source_file_handle: u32,
    ) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_set_file(
                self.inner,
                lnp.0,
                debug.0,
                source_file_handle,
            );
        }
    }

    /// Emit a "set source code" opcode.
    pub fn lnp_emit_set_source_code(
        &mut self,
        lnp: LnpHandle,
        debug: DebugInfoHandle,
        source_code_handle: u32,
    ) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_set_source_code(
                self.inner,
                lnp.0,
                debug.0,
                source_code_handle,
            );
        }
    }

    // ---- Annotations ----

    /// Create an annotation item.
    pub fn create_annotation(
        &mut self,
        class_handle: u32,
        elements: &[AnnotationElemDef],
    ) -> Result<AnnotationHandle, ParseError> {
        let c_elems: Vec<abcd_file_sys::AbcAnnotationElemDef> = elements
            .iter()
            .map(|e| abcd_file_sys::AbcAnnotationElemDef {
                name_string_handle: e.name_string_handle,
                tag: e.tag as std::ffi::c_char,
                value: e.value,
            })
            .collect();
        let idx = unsafe {
            abcd_file_sys::abc_builder_create_annotation(
                self.inner,
                class_handle,
                c_elems.as_ptr(),
                c_elems.len() as u32,
            )
        };
        if idx == u32::MAX {
            return Err(ParseError::Io("failed to create annotation".into()));
        }
        Ok(AnnotationHandle(idx))
    }

    /// Add an annotation to a class.
    pub fn class_add_annotation(&mut self, class: ClassHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_class_add_annotation(self.inner, class.0, ann.0);
        }
    }

    /// Add a runtime annotation to a class.
    pub fn class_add_runtime_annotation(&mut self, class: ClassHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_class_add_runtime_annotation(self.inner, class.0, ann.0);
        }
    }

    /// Add a type annotation to a class.
    pub fn class_add_type_annotation(&mut self, class: ClassHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_class_add_type_annotation(self.inner, class.0, ann.0);
        }
    }

    /// Add a runtime type annotation to a class.
    pub fn class_add_runtime_type_annotation(&mut self, class: ClassHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_class_add_runtime_type_annotation(
                self.inner, class.0, ann.0,
            );
        }
    }

    /// Add an annotation to a method.
    pub fn method_add_annotation(&mut self, method: MethodHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_method_add_annotation(self.inner, method.0, ann.0);
        }
    }

    /// Add a runtime annotation to a method.
    pub fn method_add_runtime_annotation(&mut self, method: MethodHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_method_add_runtime_annotation(self.inner, method.0, ann.0);
        }
    }

    /// Add a type annotation to a method.
    pub fn method_add_type_annotation(&mut self, method: MethodHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_method_add_type_annotation(self.inner, method.0, ann.0);
        }
    }

    /// Add a runtime type annotation to a method.
    pub fn method_add_runtime_type_annotation(
        &mut self,
        method: MethodHandle,
        ann: AnnotationHandle,
    ) {
        unsafe {
            abcd_file_sys::abc_builder_method_add_runtime_type_annotation(
                self.inner, method.0, ann.0,
            );
        }
    }

    /// Add an annotation to a field.
    pub fn field_add_annotation(&mut self, field: FieldHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_field_add_annotation(self.inner, field.0, ann.0);
        }
    }

    /// Add a runtime annotation to a field.
    pub fn field_add_runtime_annotation(&mut self, field: FieldHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_field_add_runtime_annotation(self.inner, field.0, ann.0);
        }
    }

    /// Add a type annotation to a field.
    pub fn field_add_type_annotation(&mut self, field: FieldHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_field_add_type_annotation(self.inner, field.0, ann.0);
        }
    }

    /// Add a runtime type annotation to a field.
    pub fn field_add_runtime_type_annotation(&mut self, field: FieldHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_field_add_runtime_type_annotation(
                self.inner, field.0, ann.0,
            );
        }
    }

    // ---- Foreign items ----

    /// Add a foreign field.
    pub fn add_foreign_field(
        &mut self,
        class_handle: u32,
        name: &str,
        type_id: u8,
    ) -> Result<u32, ParseError> {
        let c_name = CString::new(name).expect("name contains null byte");
        let idx = unsafe {
            abcd_file_sys::abc_builder_add_foreign_field(
                self.inner,
                class_handle,
                c_name.as_ptr(),
                type_id,
            )
        };
        if idx == u32::MAX {
            return Err(ParseError::Io("failed to add foreign field".into()));
        }
        Ok(idx)
    }

    /// Add a foreign method.
    pub fn add_foreign_method(
        &mut self,
        class_handle: u32,
        name: &str,
        proto: ProtoHandle,
        access_flags: u32,
    ) -> Result<u32, ParseError> {
        let c_name = CString::new(name).expect("name contains null byte");
        let idx = unsafe {
            abcd_file_sys::abc_builder_add_foreign_method(
                self.inner,
                class_handle,
                c_name.as_ptr(),
                proto.0,
                access_flags,
            )
        };
        if idx == u32::MAX {
            return Err(ParseError::Io("failed to add foreign method".into()));
        }
        Ok(idx)
    }

    // ---- Deduplication ----

    /// Deduplicate items in the container.
    pub fn deduplicate(&mut self) {
        unsafe {
            abcd_file_sys::abc_builder_deduplicate(self.inner);
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
