//! ABC file builder (writer).

use crate::annotation::AnnotationTag;
use crate::error::Error;
use crate::types::{FunctionKind, SourceLang, TypeId};
use std::ffi::CString;

/// Opaque handle for a class being built.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClassHandle(pub(crate) u32);

/// Opaque handle for a foreign class being built.
/// The raw value does NOT include the high-bit tag; use [`AnyClassHandle`] for APIs
/// that accept both regular and foreign classes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ForeignClassHandle(pub(crate) u32);

/// A class handle that can be either regular or foreign.
/// Used in APIs like `class_set_super_class` and `class_add_interface`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AnyClassHandle {
    Regular(ClassHandle),
    Foreign(ForeignClassHandle),
}

impl AnyClassHandle {
    /// Get the raw tagged handle value for the C bridge.
    /// Foreign classes have the high bit (0x80000000) set.
    pub(crate) fn raw(&self) -> u32 {
        match self {
            AnyClassHandle::Regular(h) => h.0,
            AnyClassHandle::Foreign(h) => h.0 | 0x8000_0000,
        }
    }
}

impl From<ClassHandle> for AnyClassHandle {
    fn from(h: ClassHandle) -> Self {
        AnyClassHandle::Regular(h)
    }
}

impl From<ForeignClassHandle> for AnyClassHandle {
    fn from(h: ForeignClassHandle) -> Self {
        AnyClassHandle::Foreign(h)
    }
}

/// Opaque handle for a method being built.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MethodHandle(pub(crate) u32);

/// Opaque handle for a field being built.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FieldHandle(pub(crate) u32);

/// Opaque handle for a proto being built.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProtoHandle(pub(crate) u32);

/// Opaque handle for a code item being built.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CodeHandle(pub(crate) u32);

/// Opaque handle for a literal array being built.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LiteralArrayHandle(pub(crate) u32);

/// Opaque handle for a string being built.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StringHandle(pub(crate) u32);

/// Opaque handle for a line number program being built.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LnpHandle(pub(crate) u32);

/// Opaque handle for a debug info entry being built.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DebugHandle(pub(crate) u32);

/// Opaque handle for an annotation being built.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AnnotationHandle(pub(crate) u32);

/// A catch block definition for try-catch building.
#[derive(Debug, Clone)]
pub struct CatchBlockDef {
    /// Class handle for the exception type, or `None` for catch-all.
    pub type_class: Option<ClassHandle>,
    pub handler_pc: u32,
    pub code_size: u32,
}

/// An annotation element definition.
#[derive(Debug, Clone)]
pub struct AnnotationElemDef {
    pub name: StringHandle,
    pub tag: AnnotationTag,
    pub value: u32,
}

/// Value for an extended annotation element: either a scalar or an array.
#[derive(Debug, Clone)]
pub enum AnnotationElemValue {
    Scalar(u32),
    Array(Vec<u32>),
}

/// An extended annotation element definition supporting array values.
#[derive(Debug, Clone)]
pub struct AnnotationElemDefEx {
    pub name: StringHandle,
    pub tag: AnnotationTag,
    pub value: AnnotationElemValue,
}

/// A proto parameter with reference type support.
#[derive(Debug, Clone, Copy)]
pub struct ProtoParam {
    pub type_id: TypeId,
    pub class_handle: AnyClassHandle,
}

/// ABC file builder.
pub struct Builder {
    inner: *mut abcd_file_sys::AbcBuilder,
}

/// Convert a `&str` to `CString`, mapping null-byte errors to `Error::Ffi`.
fn to_cstring(s: &str) -> Result<CString, Error> {
    CString::new(s).map_err(|_| Error::Ffi("string contains interior null byte".into()))
}

/// Convert a `usize` to `u32`, panicking if the value exceeds `u32::MAX`.
fn to_u32(len: usize) -> u32 {
    u32::try_from(len).expect("slice length exceeds u32::MAX")
}

impl Builder {
    pub fn new() -> Result<Self, Error> {
        let inner = unsafe { abcd_file_sys::abc_builder_new() };
        if inner.is_null() {
            return Err(Error::Ffi("abc_builder_new returned null".into()));
        }
        Ok(Self { inner })
    }

    // --- API version ---

    pub fn set_api(&mut self, api: u8, sub_api: &str) -> Result<(), Error> {
        let c = to_cstring(sub_api)?;
        unsafe { abcd_file_sys::abc_builder_set_api(self.inner, api, c.as_ptr()) };
        Ok(())
    }

    // --- Create / get items ---

    pub fn add_string(&mut self, s: &str) -> Result<StringHandle, Error> {
        let c = to_cstring(s)?;
        Ok(StringHandle(unsafe {
            abcd_file_sys::abc_builder_add_string(self.inner, c.as_ptr())
        }))
    }

    pub fn add_class(&mut self, descriptor: &str) -> Result<ClassHandle, Error> {
        let c = to_cstring(descriptor)?;
        Ok(ClassHandle(unsafe {
            abcd_file_sys::abc_builder_add_class(self.inner, c.as_ptr())
        }))
    }

    pub fn add_foreign_class(&mut self, descriptor: &str) -> Result<ForeignClassHandle, Error> {
        let c = to_cstring(descriptor)?;
        Ok(ForeignClassHandle(unsafe {
            abcd_file_sys::abc_builder_add_foreign_class(self.inner, c.as_ptr())
        }))
    }

    pub fn add_global_class(&mut self) -> ClassHandle {
        ClassHandle(unsafe { abcd_file_sys::abc_builder_add_global_class(self.inner) })
    }

    pub fn add_literal_array(&mut self, id: &str) -> Result<LiteralArrayHandle, Error> {
        let c = to_cstring(id)?;
        Ok(LiteralArrayHandle(unsafe {
            abcd_file_sys::abc_builder_add_literal_array(self.inner, c.as_ptr())
        }))
    }

    // --- Class fields ---

    pub fn class_add_field(
        &mut self,
        class: ClassHandle,
        name: &str,
        type_id: TypeId,
        access_flags: u32,
    ) -> Result<FieldHandle, Error> {
        let c = to_cstring(name)?;
        Ok(FieldHandle(unsafe {
            abcd_file_sys::abc_builder_class_add_field(
                self.inner,
                class.0,
                c.as_ptr(),
                type_id as u8,
                access_flags,
            )
        }))
    }

    pub fn class_add_field_ex(
        &mut self,
        class: ClassHandle,
        name: &str,
        type_id: TypeId,
        ref_class: AnyClassHandle,
        access_flags: u32,
    ) -> Result<FieldHandle, Error> {
        let c = to_cstring(name)?;
        Ok(FieldHandle(unsafe {
            abcd_file_sys::abc_builder_class_add_field_ex(
                self.inner,
                class.0,
                c.as_ptr(),
                type_id as u8,
                ref_class.raw(),
                access_flags,
            )
        }))
    }

    // --- Literal array items ---

    pub fn literal_array_add_u8(&mut self, lit: LiteralArrayHandle, val: u8) {
        unsafe { abcd_file_sys::abc_builder_literal_array_add_u8(self.inner, lit.0, val) };
    }

    pub fn literal_array_add_u16(&mut self, lit: LiteralArrayHandle, val: u16) {
        unsafe { abcd_file_sys::abc_builder_literal_array_add_u16(self.inner, lit.0, val) };
    }

    pub fn literal_array_add_u32(&mut self, lit: LiteralArrayHandle, val: u32) {
        unsafe { abcd_file_sys::abc_builder_literal_array_add_u32(self.inner, lit.0, val) };
    }

    pub fn literal_array_add_u64(&mut self, lit: LiteralArrayHandle, val: u64) {
        unsafe { abcd_file_sys::abc_builder_literal_array_add_u64(self.inner, lit.0, val) };
    }

    pub fn literal_array_add_bool(&mut self, lit: LiteralArrayHandle, val: bool) {
        unsafe { abcd_file_sys::abc_builder_literal_array_add_bool(self.inner, lit.0, val as u8) };
    }

    pub fn literal_array_add_f32(&mut self, lit: LiteralArrayHandle, val: f32) {
        unsafe { abcd_file_sys::abc_builder_literal_array_add_f32(self.inner, lit.0, val) };
    }

    pub fn literal_array_add_f64(&mut self, lit: LiteralArrayHandle, val: f64) {
        unsafe { abcd_file_sys::abc_builder_literal_array_add_f64(self.inner, lit.0, val) };
    }

    pub fn literal_array_add_string(&mut self, lit: LiteralArrayHandle, s: StringHandle) {
        unsafe { abcd_file_sys::abc_builder_literal_array_add_string(self.inner, lit.0, s.0) };
    }

    pub fn literal_array_add_method(&mut self, lit: LiteralArrayHandle, m: MethodHandle) {
        unsafe { abcd_file_sys::abc_builder_literal_array_add_method(self.inner, lit.0, m.0) };
    }

    pub fn literal_array_add_literalarray(
        &mut self,
        lit: LiteralArrayHandle,
        r: LiteralArrayHandle,
    ) {
        unsafe {
            abcd_file_sys::abc_builder_literal_array_add_literalarray(self.inner, lit.0, r.0)
        };
    }

    // --- Proto ---

    pub fn create_proto(&mut self, ret_type_id: TypeId, param_type_ids: &[TypeId]) -> ProtoHandle {
        let raw: Vec<u8> = param_type_ids.iter().map(|t| *t as u8).collect();
        let ptr = if raw.is_empty() {
            std::ptr::null()
        } else {
            raw.as_ptr()
        };
        ProtoHandle(unsafe {
            abcd_file_sys::abc_builder_create_proto(
                self.inner,
                ret_type_id as u8,
                ptr,
                to_u32(raw.len()),
            )
        })
    }

    pub fn create_proto_ex(
        &mut self,
        ret_type_id: TypeId,
        ret_class: AnyClassHandle,
        params: &[ProtoParam],
    ) -> ProtoHandle {
        let defs: Vec<abcd_file_sys::AbcProtoParam> = params
            .iter()
            .map(|p| abcd_file_sys::AbcProtoParam {
                type_id: p.type_id as u8,
                class_handle: p.class_handle.raw(),
            })
            .collect();
        let ptr = if defs.is_empty() {
            std::ptr::null()
        } else {
            defs.as_ptr()
        };
        ProtoHandle(unsafe {
            abcd_file_sys::abc_builder_create_proto_ex(
                self.inner,
                ret_type_id as u8,
                ret_class.raw(),
                ptr,
                to_u32(defs.len()),
            )
        })
    }

    pub fn class_add_method_with_proto(
        &mut self,
        class: ClassHandle,
        name: &str,
        proto: ProtoHandle,
        access_flags: u32,
        code: &[u8],
        num_vregs: u32,
        num_args: u32,
    ) -> Result<MethodHandle, Error> {
        let c = to_cstring(name)?;
        let code_ptr = if code.is_empty() {
            std::ptr::null()
        } else {
            code.as_ptr()
        };
        Ok(MethodHandle(unsafe {
            abcd_file_sys::abc_builder_class_add_method_with_proto(
                self.inner,
                class.0,
                c.as_ptr(),
                proto.0,
                access_flags,
                code_ptr,
                to_u32(code.len()),
                num_vregs,
                num_args,
            )
        }))
    }

    // --- Class configuration ---

    pub fn class_set_access_flags(&mut self, class: ClassHandle, flags: u32) {
        unsafe { abcd_file_sys::abc_builder_class_set_access_flags(self.inner, class.0, flags) };
    }

    pub fn class_set_source_lang(&mut self, class: ClassHandle, lang: SourceLang) {
        unsafe {
            abcd_file_sys::abc_builder_class_set_source_lang(self.inner, class.0, lang as u8)
        };
    }

    pub fn class_set_super_class(
        &mut self,
        class: ClassHandle,
        super_class: impl Into<AnyClassHandle>,
    ) {
        unsafe {
            abcd_file_sys::abc_builder_class_set_super_class(
                self.inner,
                class.0,
                super_class.into().raw(),
            )
        };
    }

    pub fn class_add_interface(&mut self, class: ClassHandle, iface: impl Into<AnyClassHandle>) {
        unsafe {
            abcd_file_sys::abc_builder_class_add_interface(self.inner, class.0, iface.into().raw())
        };
    }

    pub fn class_set_source_file(&mut self, class: ClassHandle, string: StringHandle) {
        unsafe { abcd_file_sys::abc_builder_class_set_source_file(self.inner, class.0, string.0) };
    }

    // --- Method configuration ---

    pub fn method_set_source_lang(&mut self, method: MethodHandle, lang: SourceLang) {
        unsafe {
            abcd_file_sys::abc_builder_method_set_source_lang(self.inner, method.0, lang as u8)
        };
    }

    pub fn method_set_function_kind(&mut self, method: MethodHandle, kind: FunctionKind) {
        unsafe {
            abcd_file_sys::abc_builder_method_set_function_kind(self.inner, method.0, kind as u8)
        };
    }

    pub fn method_set_debug_info(&mut self, method: MethodHandle, debug: DebugHandle) {
        unsafe { abcd_file_sys::abc_builder_method_set_debug_info(self.inner, method.0, debug.0) };
    }

    pub fn method_set_code(&mut self, method: MethodHandle, code: CodeHandle) {
        unsafe { abcd_file_sys::abc_builder_method_set_code(self.inner, method.0, code.0) };
    }

    // --- Field configuration ---

    pub fn field_set_value_i32(&mut self, field: FieldHandle, value: i32) {
        unsafe { abcd_file_sys::abc_builder_field_set_value_i32(self.inner, field.0, value) };
    }

    pub fn field_set_value_i64(&mut self, field: FieldHandle, value: i64) {
        unsafe { abcd_file_sys::abc_builder_field_set_value_i64(self.inner, field.0, value) };
    }

    pub fn field_set_value_f32(&mut self, field: FieldHandle, value: f32) {
        unsafe { abcd_file_sys::abc_builder_field_set_value_f32(self.inner, field.0, value) };
    }

    pub fn field_set_value_f64(&mut self, field: FieldHandle, value: f64) {
        unsafe { abcd_file_sys::abc_builder_field_set_value_f64(self.inner, field.0, value) };
    }

    // --- Code ---

    pub fn create_code(
        &mut self,
        num_vregs: u32,
        num_args: u32,
        instructions: &[u8],
    ) -> CodeHandle {
        let ptr = if instructions.is_empty() {
            std::ptr::null()
        } else {
            instructions.as_ptr()
        };
        CodeHandle(unsafe {
            abcd_file_sys::abc_builder_create_code(
                self.inner,
                num_vregs,
                num_args,
                ptr,
                to_u32(instructions.len()),
            )
        })
    }

    pub fn code_add_try_block(
        &mut self,
        code: CodeHandle,
        start_pc: u32,
        length: u32,
        catches: &[CatchBlockDef],
    ) {
        let defs: Vec<abcd_file_sys::AbcCatchBlockDef> = catches
            .iter()
            .map(|c| abcd_file_sys::AbcCatchBlockDef {
                type_class_handle: c.type_class.map_or(u32::MAX, |h| h.0),
                handler_pc: c.handler_pc,
                code_size: c.code_size,
            })
            .collect();
        let ptr = if defs.is_empty() {
            std::ptr::null()
        } else {
            defs.as_ptr()
        };
        unsafe {
            abcd_file_sys::abc_builder_code_add_try_block(
                self.inner,
                code.0,
                start_pc,
                length,
                ptr,
                to_u32(defs.len()),
            );
        }
    }

    // --- Debug info ---

    pub fn create_lnp(&mut self) -> LnpHandle {
        LnpHandle(unsafe { abcd_file_sys::abc_builder_create_lnp(self.inner) })
    }

    pub fn lnp_emit_end(&mut self, lnp: LnpHandle) {
        unsafe { abcd_file_sys::abc_builder_lnp_emit_end(self.inner, lnp.0) };
    }

    pub fn lnp_emit_advance_pc(&mut self, lnp: LnpHandle, debug: DebugHandle, value: u32) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_advance_pc(self.inner, lnp.0, debug.0, value)
        };
    }

    pub fn lnp_emit_advance_line(&mut self, lnp: LnpHandle, debug: DebugHandle, value: i32) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_advance_line(self.inner, lnp.0, debug.0, value)
        };
    }

    pub fn lnp_emit_column(
        &mut self,
        lnp: LnpHandle,
        debug: DebugHandle,
        pc_inc: u32,
        column: u32,
    ) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_column(self.inner, lnp.0, debug.0, pc_inc, column)
        };
    }

    pub fn lnp_emit_start_local(
        &mut self,
        lnp: LnpHandle,
        debug: DebugHandle,
        reg: i32,
        name: StringHandle,
        type_handle: StringHandle,
    ) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_start_local(
                self.inner,
                lnp.0,
                debug.0,
                reg,
                name.0,
                type_handle.0,
            );
        }
    }

    pub fn lnp_emit_end_local(&mut self, lnp: LnpHandle, reg: i32) {
        unsafe { abcd_file_sys::abc_builder_lnp_emit_end_local(self.inner, lnp.0, reg) };
    }

    pub fn lnp_emit_set_file(
        &mut self,
        lnp: LnpHandle,
        debug: DebugHandle,
        source_file: StringHandle,
    ) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_set_file(self.inner, lnp.0, debug.0, source_file.0)
        };
    }

    pub fn lnp_emit_set_source_code(
        &mut self,
        lnp: LnpHandle,
        debug: DebugHandle,
        source_code: StringHandle,
    ) {
        unsafe {
            abcd_file_sys::abc_builder_lnp_emit_set_source_code(
                self.inner,
                lnp.0,
                debug.0,
                source_code.0,
            );
        }
    }

    pub fn create_debug_info(&mut self, lnp: LnpHandle, line_number: u32) -> DebugHandle {
        DebugHandle(unsafe {
            abcd_file_sys::abc_builder_create_debug_info(self.inner, lnp.0, line_number)
        })
    }

    pub fn debug_add_param(&mut self, debug: DebugHandle, name: StringHandle) {
        unsafe { abcd_file_sys::abc_builder_debug_add_param(self.inner, debug.0, name.0) };
    }

    // --- Annotations ---

    pub fn create_annotation(
        &mut self,
        class: ClassHandle,
        elements: &[AnnotationElemDef],
    ) -> AnnotationHandle {
        let defs: Vec<abcd_file_sys::AbcAnnotationElemDef> = elements
            .iter()
            .map(|e| abcd_file_sys::AbcAnnotationElemDef {
                name_string_handle: e.name.0,
                tag: e.tag.to_byte() as std::ffi::c_char,
                value: e.value,
            })
            .collect();
        let ptr = if defs.is_empty() {
            std::ptr::null()
        } else {
            defs.as_ptr()
        };
        AnnotationHandle(unsafe {
            abcd_file_sys::abc_builder_create_annotation(
                self.inner,
                class.0,
                ptr,
                to_u32(defs.len()),
            )
        })
    }

    pub fn create_annotation_ex(
        &mut self,
        class: ClassHandle,
        elements: &[AnnotationElemDefEx],
    ) -> AnnotationHandle {
        // SAFETY: The `defs` vector holds `array_values` pointers that borrow from
        // `elements`. Both `defs` and `elements` are alive for the duration of the
        // FFI call. The C++ side must copy the array data synchronously — it must
        // not retain these pointers beyond the call.
        let defs: Vec<abcd_file_sys::AbcAnnotationElemDefEx> = elements
            .iter()
            .map(|e| {
                let (is_array, scalar_value, array_ptr, array_count) = match &e.value {
                    AnnotationElemValue::Scalar(v) => (0, *v, std::ptr::null(), 0),
                    AnnotationElemValue::Array(arr) => (
                        1,
                        0,
                        if arr.is_empty() {
                            std::ptr::null()
                        } else {
                            arr.as_ptr()
                        },
                        to_u32(arr.len()),
                    ),
                };
                abcd_file_sys::AbcAnnotationElemDefEx {
                    name_string_handle: e.name.0,
                    tag: e.tag.to_byte() as std::ffi::c_char,
                    is_array,
                    scalar_value,
                    array_values: array_ptr,
                    array_count,
                }
            })
            .collect();
        let ptr = if defs.is_empty() {
            std::ptr::null()
        } else {
            defs.as_ptr()
        };
        AnnotationHandle(unsafe {
            abcd_file_sys::abc_builder_create_annotation_ex(
                self.inner,
                class.0,
                ptr,
                to_u32(defs.len()),
            )
        })
    }

    pub fn class_add_annotation(&mut self, class: ClassHandle, ann: AnnotationHandle) {
        unsafe { abcd_file_sys::abc_builder_class_add_annotation(self.inner, class.0, ann.0) };
    }

    pub fn class_add_runtime_annotation(&mut self, class: ClassHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_class_add_runtime_annotation(self.inner, class.0, ann.0)
        };
    }

    pub fn class_add_type_annotation(&mut self, class: ClassHandle, ann: AnnotationHandle) {
        unsafe { abcd_file_sys::abc_builder_class_add_type_annotation(self.inner, class.0, ann.0) };
    }

    pub fn class_add_runtime_type_annotation(&mut self, class: ClassHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_class_add_runtime_type_annotation(self.inner, class.0, ann.0)
        };
    }

    pub fn method_add_annotation(&mut self, method: MethodHandle, ann: AnnotationHandle) {
        unsafe { abcd_file_sys::abc_builder_method_add_annotation(self.inner, method.0, ann.0) };
    }

    pub fn method_add_runtime_annotation(&mut self, method: MethodHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_method_add_runtime_annotation(self.inner, method.0, ann.0)
        };
    }

    pub fn method_add_type_annotation(&mut self, method: MethodHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_method_add_type_annotation(self.inner, method.0, ann.0)
        };
    }

    pub fn method_add_runtime_type_annotation(
        &mut self,
        method: MethodHandle,
        ann: AnnotationHandle,
    ) {
        unsafe {
            abcd_file_sys::abc_builder_method_add_runtime_type_annotation(
                self.inner, method.0, ann.0,
            )
        };
    }

    pub fn field_add_annotation(&mut self, field: FieldHandle, ann: AnnotationHandle) {
        unsafe { abcd_file_sys::abc_builder_field_add_annotation(self.inner, field.0, ann.0) };
    }

    pub fn field_add_runtime_annotation(&mut self, field: FieldHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_field_add_runtime_annotation(self.inner, field.0, ann.0)
        };
    }

    pub fn field_add_type_annotation(&mut self, field: FieldHandle, ann: AnnotationHandle) {
        unsafe { abcd_file_sys::abc_builder_field_add_type_annotation(self.inner, field.0, ann.0) };
    }

    pub fn field_add_runtime_type_annotation(&mut self, field: FieldHandle, ann: AnnotationHandle) {
        unsafe {
            abcd_file_sys::abc_builder_field_add_runtime_type_annotation(self.inner, field.0, ann.0)
        };
    }

    // --- Foreign items ---

    pub fn add_foreign_field(
        &mut self,
        class: impl Into<AnyClassHandle>,
        name: &str,
        type_id: TypeId,
    ) -> Result<FieldHandle, Error> {
        let c = to_cstring(name)?;
        Ok(FieldHandle(unsafe {
            abcd_file_sys::abc_builder_add_foreign_field(
                self.inner,
                class.into().raw(),
                c.as_ptr(),
                type_id as u8,
            )
        }))
    }

    pub fn add_foreign_method(
        &mut self,
        class: impl Into<AnyClassHandle>,
        name: &str,
        proto: ProtoHandle,
        access_flags: u32,
    ) -> Result<MethodHandle, Error> {
        let c = to_cstring(name)?;
        Ok(MethodHandle(unsafe {
            abcd_file_sys::abc_builder_add_foreign_method(
                self.inner,
                class.into().raw(),
                c.as_ptr(),
                proto.0,
                access_flags,
            )
        }))
    }

    // --- Deduplication ---

    pub fn deduplicate(&mut self) {
        unsafe { abcd_file_sys::abc_builder_deduplicate(self.inner) };
    }

    pub fn deduplicate_code_and_debug_info(&mut self) {
        unsafe { abcd_file_sys::abc_builder_deduplicate_code_and_debug_info(self.inner) };
    }

    pub fn deduplicate_annotations(&mut self) {
        unsafe { abcd_file_sys::abc_builder_deduplicate_annotations(self.inner) };
    }

    // --- Finalize ---

    /// Finalize the builder and return the ABC file bytes.
    ///
    /// This method can be called multiple times. Each call re-serializes the
    /// current builder state and returns a fresh copy of the output bytes.
    pub fn finalize(&mut self) -> Result<Vec<u8>, Error> {
        let mut out_len = 0u32;
        let ptr = unsafe { abcd_file_sys::abc_builder_finalize(self.inner, &mut out_len) };
        if ptr.is_null() {
            return Err(Error::Ffi("abc_builder_finalize failed".into()));
        }
        let slice = unsafe { std::slice::from_raw_parts(ptr, out_len as usize) };
        Ok(slice.to_vec())
    }
}

impl Default for Builder {
    fn default() -> Self {
        Self::new().expect("abc_builder_new returned null")
    }
}

impl Drop for Builder {
    fn drop(&mut self) {
        if !self.inner.is_null() {
            unsafe { abcd_file_sys::abc_builder_free(self.inner) };
        }
    }
}

impl std::fmt::Debug for Builder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Builder").finish_non_exhaustive()
    }
}
