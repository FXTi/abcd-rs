use std::collections::HashMap;
use std::ffi::CString;

use abcd_file_sys as sys;

use crate::annotation::AnnotationValue;
use crate::error::Error;
use crate::literal::LiteralTag;
use crate::model::*;
use crate::types::{AccessFlags, FunctionKind, SourceLang, Type};

macro_rules! handle_type {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $name(u32);

        impl $name {
            /// Raw handle value (index into the builder's tables).
            pub fn as_raw(self) -> u32 {
                self.0
            }
        }
    };
}

handle_type!(StringHandle);
handle_type!(ClassHandle);
handle_type!(MethodHandle);
handle_type!(FieldHandle);
handle_type!(ProtoHandle);
handle_type!(CodeHandle);
handle_type!(LiteralArrayHandle);
handle_type!(LnpHandle);
handle_type!(DebugInfoHandle);
handle_type!(AnnotationHandle);
handle_type!(ParamHandle);
handle_type!(MethodHandleItemHandle);

/// Safe catch block definition for the builder.
pub struct CatchBlockDef {
    /// Class handle for the exception type, or `None` for catch-all.
    pub type_class: Option<ClassHandle>,
    pub handler_pc: u32,
    pub code_size: u32,
}

/// Simple annotation element definition.
pub struct AnnotationElemDef {
    pub name: StringHandle,
    pub tag: u8,
    pub value: u32,
}

/// Extended annotation element definition (supports arrays).
pub struct AnnotationElemDefEx {
    pub name: StringHandle,
    pub tag: u8,
    pub value: AnnotationElemValue,
}

/// Value of an extended annotation element.
pub enum AnnotationElemValue {
    Scalar(u32),
    Scalar64(u64),
    Array(Vec<u32>),
    /// Entity reference: handle index resolved by tag on C++ side (is_array=3).
    EntityRef(u32),
    /// Array of entity references: handle indices resolved by tag (is_array=4).
    EntityArray(Vec<u32>),
}

/// ABC file builder.
pub struct Builder {
    raw: *mut sys::AbcBuilder,
}

impl Builder {
    /// Create a new builder.
    pub fn new() -> Self {
        // SAFETY: no preconditions.
        let raw = unsafe { sys::abc_builder_new() };
        assert!(!raw.is_null(), "abc_builder_new returned null");
        Self { raw }
    }

    /// Set the API version.
    pub fn set_api(&mut self, version: u8, sub_api: &str) {
        let c_sub = CString::new(sub_api).expect("sub_api contains NUL");
        unsafe { sys::abc_builder_set_api(self.raw, version, c_sub.as_ptr()) };
    }

    // --- Strings ---

    /// Add a string, returning its handle.
    pub fn add_string(&mut self, s: &str) -> StringHandle {
        let c_str = CString::new(s).expect("string contains NUL");
        StringHandle(unsafe { sys::abc_builder_add_string(self.raw, c_str.as_ptr()) })
    }

    // --- Classes ---

    /// Add a class with the given descriptor (e.g. `"LMyClass;"`).
    pub fn add_class(&mut self, descriptor: &str) -> ClassHandle {
        let c_desc = CString::new(descriptor).expect("descriptor contains NUL");
        ClassHandle(unsafe { sys::abc_builder_add_class(self.raw, c_desc.as_ptr()) })
    }

    /// Add a foreign (external) class.
    pub fn add_foreign_class(&mut self, descriptor: &str) -> ClassHandle {
        let c_desc = CString::new(descriptor).expect("descriptor contains NUL");
        ClassHandle(unsafe { sys::abc_builder_add_foreign_class(self.raw, c_desc.as_ptr()) })
    }

    /// Add the global class (`L_GLOBAL;`).
    pub fn add_global_class(&mut self) -> ClassHandle {
        ClassHandle(unsafe { sys::abc_builder_add_global_class(self.raw) })
    }

    pub fn class_set_access_flags(&mut self, cls: ClassHandle, flags: AccessFlags) {
        unsafe { sys::abc_builder_class_set_access_flags(self.raw, cls.0, flags.bits()) };
    }

    pub fn class_set_source_lang(&mut self, cls: ClassHandle, lang: SourceLang) {
        unsafe { sys::abc_builder_class_set_source_lang(self.raw, cls.0, lang as u8) };
    }

    pub fn class_set_super_class(&mut self, cls: ClassHandle, super_cls: ClassHandle) {
        unsafe { sys::abc_builder_class_set_super_class(self.raw, cls.0, super_cls.0) };
    }

    pub fn class_add_interface(&mut self, cls: ClassHandle, iface: ClassHandle) {
        unsafe { sys::abc_builder_class_add_interface(self.raw, cls.0, iface.0) };
    }

    pub fn class_set_source_file(&mut self, cls: ClassHandle, file: StringHandle) {
        unsafe { sys::abc_builder_class_set_source_file(self.raw, cls.0, file.0) };
    }

    // --- Proto ---

    /// Create a proto (method signature) with type descriptors.
    pub fn create_proto(&mut self, ret_type: Type, args: &[Type]) -> ProtoHandle {
        let arg_bytes: Vec<u8> = args.iter().map(|t| t.as_raw_u8()).collect();
        let ptr = if arg_bytes.is_empty() {
            std::ptr::null()
        } else {
            arg_bytes.as_ptr()
        };
        ProtoHandle(unsafe {
            sys::abc_builder_create_proto(self.raw, ret_type.as_raw_u8(), ptr, args.len() as u32)
        })
    }

    /// Create a proto with reference type support.
    ///
    /// `class_map` resolves reference type descriptors to ClassHandles.
    pub fn create_proto_ex(
        &mut self,
        ret_type: &Type,
        ret_class: Option<ClassHandle>,
        args: &[Type],
        arg_classes: &[Option<ClassHandle>],
    ) -> ProtoHandle {
        let params: Vec<sys::AbcProtoParam> = args
            .iter()
            .zip(arg_classes.iter())
            .map(|(ty, cls)| sys::AbcProtoParam {
                type_id: ty.as_raw_u8(),
                class_handle: cls.map_or(0, |h| h.0),
            })
            .collect();
        let ptr = if params.is_empty() {
            std::ptr::null()
        } else {
            params.as_ptr()
        };
        ProtoHandle(unsafe {
            sys::abc_builder_create_proto_ex(
                self.raw,
                ret_type.as_raw_u8(),
                ret_class.map_or(0, |h| h.0),
                ptr,
                params.len() as u32,
            )
        })
    }

    // --- Methods ---

    /// Add a method to a class with inline code.
    #[allow(clippy::too_many_arguments)]
    pub fn class_add_method(
        &mut self,
        cls: ClassHandle,
        name: &str,
        proto: ProtoHandle,
        flags: AccessFlags,
        code: &[u8],
        num_vregs: u32,
        num_args: u32,
    ) -> MethodHandle {
        let c_name = CString::new(name).expect("name contains NUL");
        MethodHandle(unsafe {
            sys::abc_builder_class_add_method_with_proto(
                self.raw,
                cls.0,
                c_name.as_ptr(),
                proto.0,
                flags.bits(),
                code.as_ptr(),
                code.len() as u32,
                num_vregs,
                num_args,
            )
        })
    }

    /// Add a foreign method.
    pub fn add_foreign_method(
        &mut self,
        cls: ClassHandle,
        name: &str,
        proto: ProtoHandle,
        flags: AccessFlags,
    ) -> MethodHandle {
        let c_name = CString::new(name).expect("name contains NUL");
        MethodHandle(unsafe {
            sys::abc_builder_add_foreign_method(
                self.raw,
                cls.0,
                c_name.as_ptr(),
                proto.0,
                flags.bits(),
            )
        })
    }

    pub fn method_set_source_lang(&mut self, m: MethodHandle, lang: SourceLang) {
        unsafe { sys::abc_builder_method_set_source_lang(self.raw, m.0, lang as u8) };
    }

    pub fn method_set_function_kind(&mut self, m: MethodHandle, kind: FunctionKind) {
        unsafe { sys::abc_builder_method_set_function_kind(self.raw, m.0, kind as u8) };
    }

    pub fn method_set_debug_info(&mut self, m: MethodHandle, debug: DebugInfoHandle) {
        unsafe { sys::abc_builder_method_set_debug_info(self.raw, m.0, debug.0) };
    }

    pub fn method_set_code(&mut self, m: MethodHandle, code: CodeHandle) {
        unsafe { sys::abc_builder_method_set_code(self.raw, m.0, code.0) };
    }

    pub fn method_add_param(&mut self, m: MethodHandle, ty: Type) -> ParamHandle {
        ParamHandle(unsafe { sys::abc_builder_method_add_param(self.raw, m.0, ty.as_raw_u8()) })
    }

    // --- Fields ---

    /// Add a field to a class.
    pub fn class_add_field(
        &mut self,
        cls: ClassHandle,
        name: &str,
        ty: Type,
        flags: AccessFlags,
    ) -> FieldHandle {
        let c_name = CString::new(name).expect("name contains NUL");
        FieldHandle(unsafe {
            sys::abc_builder_class_add_field(
                self.raw,
                cls.0,
                c_name.as_ptr(),
                ty.as_raw_u8(),
                flags.bits(),
            )
        })
    }

    /// Add a field with a reference type.
    pub fn class_add_field_ex(
        &mut self,
        cls: ClassHandle,
        name: &str,
        ty: Type,
        ref_class: ClassHandle,
        flags: AccessFlags,
    ) -> FieldHandle {
        let c_name = CString::new(name).expect("name contains NUL");
        FieldHandle(unsafe {
            sys::abc_builder_class_add_field_ex(
                self.raw,
                cls.0,
                c_name.as_ptr(),
                ty.as_raw_u8(),
                ref_class.0,
                flags.bits(),
            )
        })
    }

    /// Add a foreign field.
    pub fn add_foreign_field(&mut self, cls: ClassHandle, name: &str, ty: Type) -> FieldHandle {
        let c_name = CString::new(name).expect("name contains NUL");
        FieldHandle(unsafe {
            sys::abc_builder_add_foreign_field(self.raw, cls.0, c_name.as_ptr(), ty.as_raw_u8())
        })
    }

    pub fn field_set_value_i32(&mut self, f: FieldHandle, value: i32) {
        unsafe { sys::abc_builder_field_set_value_i32(self.raw, f.0, value) };
    }

    pub fn field_set_value_i64(&mut self, f: FieldHandle, value: i64) {
        unsafe { sys::abc_builder_field_set_value_i64(self.raw, f.0, value) };
    }

    pub fn field_set_value_f32(&mut self, f: FieldHandle, value: f32) {
        unsafe { sys::abc_builder_field_set_value_f32(self.raw, f.0, value) };
    }

    pub fn field_set_value_f64(&mut self, f: FieldHandle, value: f64) {
        unsafe { sys::abc_builder_field_set_value_f64(self.raw, f.0, value) };
    }

    // --- Code ---

    /// Create a standalone code item.
    pub fn create_code(&mut self, insns: &[u8], num_vregs: u32, num_args: u32) -> CodeHandle {
        CodeHandle(unsafe {
            sys::abc_builder_create_code(
                self.raw,
                num_vregs,
                num_args,
                insns.as_ptr(),
                insns.len() as u32,
            )
        })
    }

    /// Add a try-catch block to a code item.
    pub fn code_add_try_block(
        &mut self,
        code: CodeHandle,
        start_pc: u32,
        length: u32,
        catches: &[CatchBlockDef],
    ) {
        let ffi_catches: Vec<sys::AbcCatchBlockDef> = catches
            .iter()
            .map(|c| sys::AbcCatchBlockDef {
                type_class_handle: c.type_class.map_or(u32::MAX, |h| h.0),
                handler_pc: c.handler_pc,
                code_size: c.code_size,
            })
            .collect();
        unsafe {
            sys::abc_builder_code_add_try_block(
                self.raw,
                code.0,
                start_pc,
                length,
                ffi_catches.as_ptr(),
                ffi_catches.len() as u32,
            );
        }
    }

    // --- Literal arrays ---

    /// Create a literal array with the given ID string.
    pub fn add_literal_array(&mut self, id: &str) -> LiteralArrayHandle {
        let c_id = CString::new(id).expect("id contains NUL");
        LiteralArrayHandle(unsafe { sys::abc_builder_add_literal_array(self.raw, c_id.as_ptr()) })
    }

    // The literal-array section stores pairs of items: a one-byte tag followed
    // by the encoded value, and the section count is the total number of
    // items (2 per logical literal). The typed conveniences below therefore
    // emit a complete `[tag][value]` pair; the `add_u*` methods are the raw
    // single-item primitives used to build those pairs.

    /// Append a raw one-byte item. Combine with a preceding tag item (e.g.
    /// `literal_array_add_u8(la, LiteralTag::Accessor as u8)`) to form a
    /// complete literal.
    pub fn literal_array_add_u8(&mut self, la: LiteralArrayHandle, val: u8) {
        unsafe { sys::abc_builder_literal_array_add_u8(self.raw, la.0, val) };
    }

    /// Append a raw two-byte item; see [`Self::literal_array_add_u8`].
    pub fn literal_array_add_u16(&mut self, la: LiteralArrayHandle, val: u16) {
        unsafe { sys::abc_builder_literal_array_add_u16(self.raw, la.0, val) };
    }

    /// Append a raw four-byte item; see [`Self::literal_array_add_u8`].
    pub fn literal_array_add_u32(&mut self, la: LiteralArrayHandle, val: u32) {
        unsafe { sys::abc_builder_literal_array_add_u32(self.raw, la.0, val) };
    }

    /// Append a raw eight-byte item; see [`Self::literal_array_add_u8`].
    pub fn literal_array_add_u64(&mut self, la: LiteralArrayHandle, val: u64) {
        unsafe { sys::abc_builder_literal_array_add_u64(self.raw, la.0, val) };
    }

    /// Append a complete `BOOL` literal (`[tag][value]` pair).
    pub fn literal_array_add_bool(&mut self, la: LiteralArrayHandle, val: bool) {
        self.literal_array_add_u8(la, LiteralTag::Bool as u8);
        self.literal_array_add_raw_bool(la, val);
    }

    /// Append a complete `FLOAT` literal (`[tag][value]` pair).
    pub fn literal_array_add_f32(&mut self, la: LiteralArrayHandle, val: f32) {
        self.literal_array_add_u8(la, LiteralTag::Float as u8);
        self.literal_array_add_u32(la, val.to_bits());
    }

    /// Append a complete `INTEGER` literal (`[tag][value]` pair).
    pub fn literal_array_add_integer(&mut self, la: LiteralArrayHandle, val: u32) {
        self.literal_array_add_u8(la, LiteralTag::Integer as u8);
        self.literal_array_add_u32(la, val);
    }

    /// Append a complete `DOUBLE` literal (`[tag][value]` pair).
    pub fn literal_array_add_f64(&mut self, la: LiteralArrayHandle, val: f64) {
        self.literal_array_add_u8(la, LiteralTag::Double as u8);
        self.literal_array_add_u64(la, val.to_bits());
    }

    /// Append a complete `STRING` literal (`[tag][value]` pair).
    pub fn literal_array_add_string(&mut self, la: LiteralArrayHandle, s: StringHandle) {
        self.literal_array_add_u8(la, LiteralTag::String as u8);
        self.literal_array_add_raw_string(la, s);
    }

    /// Append a complete `METHOD` literal (`[tag][value]` pair).
    pub fn literal_array_add_method(&mut self, la: LiteralArrayHandle, m: MethodHandle) {
        self.literal_array_add_u8(la, LiteralTag::Method as u8);
        self.literal_array_add_raw_method(la, m);
    }

    /// Append a complete `LITERALARRAY` literal (`[tag][value]` pair).
    pub fn literal_array_add_literalarray(
        &mut self,
        la: LiteralArrayHandle,
        ref_la: LiteralArrayHandle,
    ) {
        self.literal_array_add_u8(la, LiteralTag::LiteralArray as u8);
        self.literal_array_add_raw_literalarray(la, ref_la);
    }

    // Raw value items without a tag. Callers that already emitted the tag
    // item (e.g. the model-driven literal encoder) use these directly.
    pub(crate) fn literal_array_add_raw_bool(&mut self, la: LiteralArrayHandle, val: bool) {
        unsafe { sys::abc_builder_literal_array_add_bool(self.raw, la.0, val as u8) };
    }

    pub(crate) fn literal_array_add_raw_string(&mut self, la: LiteralArrayHandle, s: StringHandle) {
        unsafe { sys::abc_builder_literal_array_add_string(self.raw, la.0, s.0) };
    }

    pub(crate) fn literal_array_add_raw_method(&mut self, la: LiteralArrayHandle, m: MethodHandle) {
        unsafe { sys::abc_builder_literal_array_add_method(self.raw, la.0, m.0) };
    }

    pub(crate) fn literal_array_add_raw_literalarray(
        &mut self,
        la: LiteralArrayHandle,
        ref_la: LiteralArrayHandle,
    ) {
        unsafe { sys::abc_builder_literal_array_add_literalarray(self.raw, la.0, ref_la.0) };
    }

    // --- MethodHandle items ---

    /// Create a method handle item.
    /// `handle_type`: 0-3 = field ops, 4-8 = method ops.
    /// `entity_handle`: field or method handle (high bit = foreign).
    pub fn create_method_handle(
        &mut self,
        handle_type: u8,
        entity_handle: u32,
    ) -> MethodHandleItemHandle {
        MethodHandleItemHandle(unsafe {
            sys::abc_builder_create_method_handle(self.raw, handle_type, entity_handle)
        })
    }

    // --- Debug info ---

    /// Create a line number program.
    pub fn create_lnp(&mut self) -> LnpHandle {
        LnpHandle(unsafe { sys::abc_builder_create_lnp(self.raw) })
    }

    pub fn lnp_emit_end(&mut self, lnp: LnpHandle) {
        unsafe { sys::abc_builder_lnp_emit_end(self.raw, lnp.0) };
    }

    pub fn lnp_emit_advance_pc(&mut self, lnp: LnpHandle, debug: DebugInfoHandle, value: u32) {
        unsafe { sys::abc_builder_lnp_emit_advance_pc(self.raw, lnp.0, debug.0, value) };
    }

    pub fn lnp_emit_advance_line(&mut self, lnp: LnpHandle, debug: DebugInfoHandle, value: i32) {
        unsafe { sys::abc_builder_lnp_emit_advance_line(self.raw, lnp.0, debug.0, value) };
    }

    pub fn lnp_emit_column(
        &mut self,
        lnp: LnpHandle,
        debug: DebugInfoHandle,
        pc_inc: u32,
        column: u32,
    ) {
        unsafe { sys::abc_builder_lnp_emit_column(self.raw, lnp.0, debug.0, pc_inc, column) };
    }

    pub fn lnp_emit_start_local(
        &mut self,
        lnp: LnpHandle,
        debug: DebugInfoHandle,
        reg: i32,
        name: StringHandle,
        type_handle: StringHandle,
    ) {
        unsafe {
            sys::abc_builder_lnp_emit_start_local(
                self.raw,
                lnp.0,
                debug.0,
                reg,
                name.0,
                type_handle.0,
            );
        }
    }

    pub fn lnp_emit_start_local_extended(
        &mut self,
        lnp: LnpHandle,
        debug: DebugInfoHandle,
        reg: i32,
        name: StringHandle,
        type_handle: StringHandle,
        type_sig: StringHandle,
    ) {
        unsafe {
            sys::abc_builder_lnp_emit_start_local_extended(
                self.raw,
                lnp.0,
                debug.0,
                reg,
                name.0,
                type_handle.0,
                type_sig.0,
            );
        }
    }

    pub fn lnp_emit_end_local(&mut self, lnp: LnpHandle, reg: i32) {
        unsafe { sys::abc_builder_lnp_emit_end_local(self.raw, lnp.0, reg) };
    }

    pub fn lnp_emit_set_file(
        &mut self,
        lnp: LnpHandle,
        debug: DebugInfoHandle,
        source_file: StringHandle,
    ) {
        unsafe { sys::abc_builder_lnp_emit_set_file(self.raw, lnp.0, debug.0, source_file.0) };
    }

    pub fn lnp_emit_set_source_code(
        &mut self,
        lnp: LnpHandle,
        debug: DebugInfoHandle,
        source_code: StringHandle,
    ) {
        unsafe {
            sys::abc_builder_lnp_emit_set_source_code(self.raw, lnp.0, debug.0, source_code.0);
        }
    }

    /// Create a debug info item.
    pub fn create_debug_info(&mut self, lnp: LnpHandle, line_number: u32) -> DebugInfoHandle {
        DebugInfoHandle(unsafe { sys::abc_builder_create_debug_info(self.raw, lnp.0, line_number) })
    }

    /// Add a parameter name to a debug info item.
    pub fn debug_add_param(&mut self, debug: DebugInfoHandle, name: StringHandle) {
        unsafe { sys::abc_builder_debug_add_param(self.raw, debug.0, name.0) };
    }

    // --- Annotations ---

    /// Create an annotation with simple elements.
    pub fn create_annotation(
        &mut self,
        cls: ClassHandle,
        elements: &[AnnotationElemDef],
    ) -> AnnotationHandle {
        let ffi_elems: Vec<sys::AbcAnnotationElemDef> = elements
            .iter()
            .map(|e| sys::AbcAnnotationElemDef {
                name_string_handle: e.name.0,
                tag: e.tag as std::os::raw::c_char,
                value: e.value,
            })
            .collect();
        AnnotationHandle(unsafe {
            sys::abc_builder_create_annotation(
                self.raw,
                cls.0,
                ffi_elems.as_ptr(),
                ffi_elems.len() as u32,
            )
        })
    }

    /// Create an annotation with extended elements (array support).
    pub fn create_annotation_ex(
        &mut self,
        cls: ClassHandle,
        elements: &[AnnotationElemDefEx],
    ) -> AnnotationHandle {
        let ffi_elems: Vec<sys::AbcAnnotationElemDefEx> = elements
            .iter()
            .map(|e| match &e.value {
                AnnotationElemValue::Scalar(v) => sys::AbcAnnotationElemDefEx {
                    name_string_handle: e.name.0,
                    tag: e.tag as std::os::raw::c_char,
                    is_array: 0,
                    scalar_value: *v,
                    scalar_value_64: 0,
                    array_values: std::ptr::null(),
                    array_count: 0,
                },
                AnnotationElemValue::Scalar64(v) => sys::AbcAnnotationElemDefEx {
                    name_string_handle: e.name.0,
                    tag: e.tag as std::os::raw::c_char,
                    is_array: 2,
                    scalar_value: 0,
                    scalar_value_64: *v,
                    array_values: std::ptr::null(),
                    array_count: 0,
                },
                AnnotationElemValue::Array(arr) => sys::AbcAnnotationElemDefEx {
                    name_string_handle: e.name.0,
                    tag: e.tag as std::os::raw::c_char,
                    is_array: 1,
                    scalar_value: 0,
                    scalar_value_64: 0,
                    array_values: arr.as_ptr(),
                    array_count: arr.len() as u32,
                },
                AnnotationElemValue::EntityRef(h) => sys::AbcAnnotationElemDefEx {
                    name_string_handle: e.name.0,
                    tag: e.tag as std::os::raw::c_char,
                    is_array: 3,
                    scalar_value: *h,
                    scalar_value_64: 0,
                    array_values: std::ptr::null(),
                    array_count: 0,
                },
                AnnotationElemValue::EntityArray(arr) => sys::AbcAnnotationElemDefEx {
                    name_string_handle: e.name.0,
                    tag: e.tag as std::os::raw::c_char,
                    is_array: 4,
                    scalar_value: 0,
                    scalar_value_64: 0,
                    array_values: arr.as_ptr(),
                    array_count: arr.len() as u32,
                },
            })
            .collect();
        AnnotationHandle(unsafe {
            sys::abc_builder_create_annotation_ex(
                self.raw,
                cls.0,
                ffi_elems.as_ptr(),
                ffi_elems.len() as u32,
            )
        })
    }

    // Annotation attachment helpers
    pub fn class_add_annotation(&mut self, cls: ClassHandle, ann: AnnotationHandle) {
        unsafe { sys::abc_builder_class_add_annotation(self.raw, cls.0, ann.0) };
    }
    pub fn class_add_runtime_annotation(&mut self, cls: ClassHandle, ann: AnnotationHandle) {
        unsafe { sys::abc_builder_class_add_runtime_annotation(self.raw, cls.0, ann.0) };
    }
    pub fn class_add_type_annotation(&mut self, cls: ClassHandle, ann: AnnotationHandle) {
        unsafe { sys::abc_builder_class_add_type_annotation(self.raw, cls.0, ann.0) };
    }
    pub fn class_add_runtime_type_annotation(&mut self, cls: ClassHandle, ann: AnnotationHandle) {
        unsafe { sys::abc_builder_class_add_runtime_type_annotation(self.raw, cls.0, ann.0) };
    }

    pub fn method_add_annotation(&mut self, m: MethodHandle, ann: AnnotationHandle) {
        unsafe { sys::abc_builder_method_add_annotation(self.raw, m.0, ann.0) };
    }
    pub fn method_add_runtime_annotation(&mut self, m: MethodHandle, ann: AnnotationHandle) {
        unsafe { sys::abc_builder_method_add_runtime_annotation(self.raw, m.0, ann.0) };
    }
    pub fn method_add_type_annotation(&mut self, m: MethodHandle, ann: AnnotationHandle) {
        unsafe { sys::abc_builder_method_add_type_annotation(self.raw, m.0, ann.0) };
    }
    pub fn method_add_runtime_type_annotation(&mut self, m: MethodHandle, ann: AnnotationHandle) {
        unsafe { sys::abc_builder_method_add_runtime_type_annotation(self.raw, m.0, ann.0) };
    }

    pub fn method_param_add_annotation(
        &mut self,
        m: MethodHandle,
        param: ParamHandle,
        ann: AnnotationHandle,
    ) {
        unsafe { sys::abc_builder_method_param_add_annotation(self.raw, m.0, param.0, ann.0) };
    }
    pub fn method_param_add_runtime_annotation(
        &mut self,
        m: MethodHandle,
        param: ParamHandle,
        ann: AnnotationHandle,
    ) {
        unsafe {
            sys::abc_builder_method_param_add_runtime_annotation(self.raw, m.0, param.0, ann.0);
        }
    }
    pub fn method_param_add_type_annotation(
        &mut self,
        m: MethodHandle,
        param: ParamHandle,
        ann: AnnotationHandle,
    ) {
        unsafe {
            sys::abc_builder_method_param_add_type_annotation(self.raw, m.0, param.0, ann.0);
        }
    }
    pub fn method_param_add_runtime_type_annotation(
        &mut self,
        m: MethodHandle,
        param: ParamHandle,
        ann: AnnotationHandle,
    ) {
        unsafe {
            sys::abc_builder_method_param_add_runtime_type_annotation(
                self.raw, m.0, param.0, ann.0,
            );
        }
    }

    pub fn field_add_annotation(&mut self, f: FieldHandle, ann: AnnotationHandle) {
        unsafe { sys::abc_builder_field_add_annotation(self.raw, f.0, ann.0) };
    }
    pub fn field_add_runtime_annotation(&mut self, f: FieldHandle, ann: AnnotationHandle) {
        unsafe { sys::abc_builder_field_add_runtime_annotation(self.raw, f.0, ann.0) };
    }
    pub fn field_add_type_annotation(&mut self, f: FieldHandle, ann: AnnotationHandle) {
        unsafe { sys::abc_builder_field_add_type_annotation(self.raw, f.0, ann.0) };
    }
    pub fn field_add_runtime_type_annotation(&mut self, f: FieldHandle, ann: AnnotationHandle) {
        unsafe { sys::abc_builder_field_add_runtime_type_annotation(self.raw, f.0, ann.0) };
    }

    // --- Deduplication ---

    pub fn deduplicate(&mut self) {
        unsafe { sys::abc_builder_deduplicate(self.raw) };
    }

    pub fn deduplicate_code_and_debug_info(&mut self) {
        unsafe { sys::abc_builder_deduplicate_code_and_debug_info(self.raw) };
    }

    pub fn deduplicate_annotations(&mut self) {
        unsafe { sys::abc_builder_deduplicate_annotations(self.raw) };
    }

    // --- Finalize ---

    /// Finalize the builder and return the serialized ABC file bytes.
    pub fn finalize(&mut self) -> Result<Vec<u8>, Error> {
        let mut out_len: u32 = 0;
        // SAFETY: raw is valid; out_len is stack-allocated.
        let ptr = unsafe { sys::abc_builder_finalize(self.raw, &mut out_len) };
        if ptr.is_null() {
            return Err(Error::Finalize);
        }
        // SAFETY: ptr points to out_len bytes owned by the builder; copy before free.
        let data = unsafe { std::slice::from_raw_parts(ptr, out_len as usize) }.to_vec();
        Ok(data)
    }
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for Builder {
    fn drop(&mut self) {
        // SAFETY: raw was allocated by abc_builder_new.
        unsafe { sys::abc_builder_free(self.raw) };
    }
}

// ---------------------------------------------------------------------------
// High-level encode
// ---------------------------------------------------------------------------

use crate::{StringId, StringPool};

/// Handles of encoded methods/fields, resolvable from decoded reference
/// payloads.
///
/// References inside a decoded file carry entity offsets (method/field item
/// offsets) or interned names. Names are not unique — two classes routinely
/// define a method of the same name — so the offset map is authoritative and
/// the name map only serves hand-built models whose entities all carry
/// offset 0.
#[derive(Default)]
struct EntityHandles {
    methods_by_offset: HashMap<u32, MethodHandle>,
    methods_by_name: HashMap<StringId, MethodHandle>,
    fields_by_offset: HashMap<u32, FieldHandle>,
    fields_by_name: HashMap<StringId, FieldHandle>,
}

impl EntityHandles {
    fn insert_method(&mut self, m: &Method, h: MethodHandle) {
        self.methods_by_name.insert(m.name, h);
        if m.offset != 0 {
            self.methods_by_offset.insert(m.offset, h);
        }
    }

    fn insert_field(&mut self, f: &Field, h: FieldHandle) {
        self.fields_by_name.insert(f.name, h);
        if f.offset != 0 {
            self.fields_by_offset.insert(f.offset, h);
        }
    }

    /// Resolve a method reference. A non-zero offset is the entity's unique
    /// identity; the name map is only a fallback for hand-built models.
    fn resolve_method(&self, name: StringId, offset: u32) -> Option<MethodHandle> {
        if offset != 0
            && let Some(&h) = self.methods_by_offset.get(&offset)
        {
            return Some(h);
        }
        self.methods_by_name.get(&name).copied()
    }

    /// Resolve a field reference (see [`Self::resolve_method`]).
    fn resolve_field(&self, name: StringId, offset: u32) -> Option<FieldHandle> {
        if offset != 0
            && let Some(&h) = self.fields_by_offset.get(&offset)
        {
            return Some(h);
        }
        self.fields_by_name.get(&name).copied()
    }
}

/// Encode a decoded [`File`] back to ABC bytes.
///
/// The output is a valid ABC file that can be decoded again. Checksums will
/// differ from the original but all semantic content is preserved.
///
/// Note: `ParamInfo::signature` is not preserved (C++ writer limitation).
pub fn encode(file: &File) -> Result<Vec<u8>, Error> {
    let mut b = Builder::new();
    let pool = &file.strings;

    // Helper: resolve a StringId to &str, panicking on invalid ids.
    let rs = |id: StringId| -> &str { pool.resolve(id).expect("dangling StringId in file") };

    // --- Collect all strings and build handle map ---
    let mut string_handles: HashMap<StringId, StringHandle> = HashMap::new();

    // --- Create classes (foreign first, then normal) ---
    let mut class_handles: HashMap<StringId, ClassHandle> = HashMap::new();
    let mut entities = EntityHandles::default();
    let mut ann_la_counter: u32 = 0;

    // First pass: foreign classes
    for (&desc, cls) in &file.classes {
        if cls.is_external {
            let h = b.add_foreign_class(rs(desc));
            class_handles.insert(desc, h);
        }
    }
    // Second pass: normal classes
    for (&desc, cls) in &file.classes {
        if !cls.is_external {
            let desc_str = rs(desc);
            let h = if desc_str == "L_GLOBAL;" {
                b.add_global_class()
            } else {
                b.add_class(desc_str)
            };
            class_handles.insert(desc, h);
        }
    }

    // Helper: resolve a descriptor StringId to a ClassHandle (may need to create foreign).
    let resolve_class_id = |b: &mut Builder,
                            map: &mut HashMap<StringId, ClassHandle>,
                            pool: &StringPool,
                            desc: StringId|
     -> ClassHandle {
        if let Some(&h) = map.get(&desc) {
            return h;
        }
        let desc_str = pool.resolve(desc).expect("dangling StringId");
        let h = b.add_foreign_class(desc_str);
        map.insert(desc, h);
        h
    };

    // --- Configure each class ---
    for (&desc, cls) in &file.classes {
        let cls_h = class_handles[&desc];

        b.class_set_access_flags(cls_h, cls.access_flags);
        b.class_set_source_lang(cls_h, cls.source_lang);

        if let Some(sf) = cls.source_file {
            let sh = get_or_add_string_id(&mut b, &mut string_handles, pool, sf);
            b.class_set_source_file(cls_h, sh);
        }
        if let Some(sup) = cls.super_class {
            let sup_h = resolve_class_id(&mut b, &mut class_handles, pool, sup);
            b.class_set_super_class(cls_h, sup_h);
        }
        for &iface in &cls.interfaces {
            let iface_h = resolve_class_id(&mut b, &mut class_handles, pool, iface);
            b.class_add_interface(cls_h, iface_h);
        }

        // --- Methods ---
        for method in &cls.methods {
            let method_name_str = rs(method.name);
            let ret_type = method.return_type.unwrap_or(Type::Void);
            let ret_class = if let Type::Reference(d) = ret_type {
                Some(resolve_class_id(&mut b, &mut class_handles, pool, d))
            } else {
                None
            };
            let arg_classes: Vec<Option<ClassHandle>> = method
                .arg_types
                .iter()
                .map(|t| {
                    if let Type::Reference(d) = t {
                        Some(resolve_class_id(&mut b, &mut class_handles, pool, *d))
                    } else {
                        None
                    }
                })
                .collect();

            let proto = b.create_proto_ex(&ret_type, ret_class, &method.arg_types, &arg_classes);

            let method_h = if method.is_external {
                b.add_foreign_method(cls_h, method_name_str, proto, method.access_flags)
            } else {
                // Encode bytecodes
                let (code_bytes, byte_offsets) = if let Some(ref body) = method.body {
                    abcd_isa::encode(&body.bytecodes)
                        .map_err(|e| Error::BytecodeEncode(e.to_string()))?
                } else {
                    (Vec::new(), Vec::new())
                };

                let (num_vregs, num_args) = method
                    .body
                    .as_ref()
                    .map_or((0, method.arg_types.len() as u32), |b| {
                        (b.num_vregs, b.num_args)
                    });

                let has_try_blocks = method
                    .body
                    .as_ref()
                    .is_some_and(|b| !b.try_blocks.is_empty());

                // When try-blocks exist, pass empty code to class_add_method
                // and attach a separate CodeHandle with try-blocks via method_set_code.
                // This avoids creating an orphaned code item.
                let inline_code = if has_try_blocks { &[][..] } else { &code_bytes };
                let m_h = b.class_add_method(
                    cls_h,
                    method_name_str,
                    proto,
                    method.access_flags,
                    inline_code,
                    num_vregs,
                    num_args,
                );

                // Try blocks
                if let Some(ref body) = method.body
                    && !body.try_blocks.is_empty()
                {
                    let code_h = b.create_code(&code_bytes, num_vregs, num_args);
                    for tb in &body.try_blocks {
                        let catches: Vec<CatchBlockDef> = tb
                            .catches
                            .iter()
                            .map(|cb| {
                                let type_class = if cb.type_idx == u32::MAX {
                                    None
                                } else {
                                    file.resolve_entity(cb.type_idx).map(|d| {
                                        resolve_class_id(&mut b, &mut class_handles, pool, d)
                                    })
                                };
                                let handler_pc =
                                    byte_offsets.get(cb.handler as usize).copied().unwrap_or(0);
                                let end = cb.handler + cb.len;
                                let end_pc = byte_offsets
                                    .get(end as usize)
                                    .copied()
                                    .unwrap_or(code_bytes.len() as u32);
                                CatchBlockDef {
                                    type_class,
                                    handler_pc,
                                    code_size: end_pc - handler_pc,
                                }
                            })
                            .collect();
                        let start_pc = byte_offsets.get(tb.start as usize).copied().unwrap_or(0);
                        let end = tb.start + tb.len;
                        let end_pc = byte_offsets
                            .get(end as usize)
                            .copied()
                            .unwrap_or(code_bytes.len() as u32);
                        b.code_add_try_block(code_h, start_pc, end_pc - start_pc, &catches);
                    }
                    b.method_set_code(m_h, code_h);
                }

                // Debug info
                if let Some(ref dbg) = method.debug {
                    encode_debug_info(
                        &mut b,
                        &mut string_handles,
                        pool,
                        m_h,
                        dbg,
                        &byte_offsets,
                        code_bytes.len() as u32,
                    );
                }

                m_h
            };

            b.method_set_source_lang(method_h, method.source_lang);
            b.method_set_function_kind(method_h, method.function_kind);

            // Track method handle for literal array method references.
            entities.insert_method(method, method_h);

            // Method annotations
            {
                let mut ctx = AnnotationEncodeCtx {
                    string_handles: &mut string_handles,
                    class_handles: &mut class_handles,
                    entities: &entities,
                    ann_la_counter: &mut ann_la_counter,
                    pool,
                };
                encode_annotations_on(
                    &mut b,
                    &mut ctx,
                    &method.annotations,
                    AnnotationTarget::Method(method_h),
                );
            }
        }

        // --- Fields ---
        for field in &cls.fields {
            let field_name_str = rs(field.name);
            let ty = field.field_type;
            let field_h = if field.is_external {
                b.add_foreign_field(cls_h, field_name_str, ty)
            } else if let Type::Reference(d) = ty {
                let ref_cls = resolve_class_id(&mut b, &mut class_handles, pool, d);
                b.class_add_field_ex(cls_h, field_name_str, ty, ref_cls, field.access_flags)
            } else {
                b.class_add_field(cls_h, field_name_str, ty, field.access_flags)
            };

            // Track field handle for annotation references.
            entities.insert_field(field, field_h);

            // Initial value
            match field.initial_value {
                Some(FieldValue::I32(v)) => b.field_set_value_i32(field_h, v),
                Some(FieldValue::I64(v)) => b.field_set_value_i64(field_h, v),
                Some(FieldValue::F32(v)) => b.field_set_value_f32(field_h, v),
                Some(FieldValue::F64(v)) => b.field_set_value_f64(field_h, v),
                None => {}
            }

            // Field annotations
            {
                let mut ctx = AnnotationEncodeCtx {
                    string_handles: &mut string_handles,
                    class_handles: &mut class_handles,
                    entities: &entities,
                    ann_la_counter: &mut ann_la_counter,
                    pool,
                };
                encode_annotations_on(
                    &mut b,
                    &mut ctx,
                    &field.annotations,
                    AnnotationTarget::Field(field_h),
                );
            }
        }

        // Class annotations
        {
            let mut ctx = AnnotationEncodeCtx {
                string_handles: &mut string_handles,
                class_handles: &mut class_handles,
                entities: &entities,
                ann_la_counter: &mut ann_la_counter,
                pool,
            };
            encode_annotations_on(
                &mut b,
                &mut ctx,
                &cls.annotations,
                AnnotationTarget::Class(cls_h),
            );
        }
    }

    // --- Literal arrays ---
    for (i, la) in file.literal_arrays.iter().enumerate() {
        let id = format!("{i}");
        let la_h = b.add_literal_array(&id);
        for val in &la.values {
            encode_literal_value(
                &mut b,
                &mut string_handles,
                pool,
                la_h,
                val,
                &file.entity_map,
                &entities,
            );
        }
    }

    // --- Deduplicate and finalize ---
    // DeduplicateItems computes a layout pass first: its hash computation
    // reads per-item index ranges that only ComputeLayout populates.
    b.deduplicate();
    b.finalize()
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

enum AnnotationTarget {
    Class(ClassHandle),
    Method(MethodHandle),
    Field(FieldHandle),
}

/// Shared mutable state for annotation encoding.
struct AnnotationEncodeCtx<'a> {
    string_handles: &'a mut HashMap<StringId, StringHandle>,
    class_handles: &'a mut HashMap<StringId, ClassHandle>,
    entities: &'a EntityHandles,
    ann_la_counter: &'a mut u32,
    pool: &'a StringPool,
}

#[allow(clippy::type_complexity)]
fn encode_annotations_on(
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
    anns: &Annotations,
    target: AnnotationTarget,
) {
    let groups: [(
        &[Annotation],
        fn(&mut Builder, &AnnotationTarget, AnnotationHandle),
    ); 4] = [
        (&anns.compile_time, |b, t, a| match t {
            AnnotationTarget::Class(h) => b.class_add_annotation(*h, a),
            AnnotationTarget::Method(h) => b.method_add_annotation(*h, a),
            AnnotationTarget::Field(h) => b.field_add_annotation(*h, a),
        }),
        (&anns.runtime, |b, t, a| match t {
            AnnotationTarget::Class(h) => b.class_add_runtime_annotation(*h, a),
            AnnotationTarget::Method(h) => b.method_add_runtime_annotation(*h, a),
            AnnotationTarget::Field(h) => b.field_add_runtime_annotation(*h, a),
        }),
        (&anns.compile_time_type, |b, t, a| match t {
            AnnotationTarget::Class(h) => b.class_add_type_annotation(*h, a),
            AnnotationTarget::Method(h) => b.method_add_type_annotation(*h, a),
            AnnotationTarget::Field(h) => b.field_add_type_annotation(*h, a),
        }),
        (&anns.runtime_type, |b, t, a| match t {
            AnnotationTarget::Class(h) => b.class_add_runtime_type_annotation(*h, a),
            AnnotationTarget::Method(h) => b.method_add_runtime_type_annotation(*h, a),
            AnnotationTarget::Field(h) => b.field_add_runtime_type_annotation(*h, a),
        }),
    ];

    for (ann_list, attach_fn) in &groups {
        for ann in *ann_list {
            let ann_cls =
                resolve_class_for_ann(b, ctx.class_handles, ctx.pool, ann.class_descriptor);

            let elems: Vec<AnnotationElemDefEx> = ann
                .elements
                .iter()
                .map(|e| {
                    let name = get_or_add_string_id(b, ctx.string_handles, ctx.pool, e.name);
                    let (tag, value) = annotation_value_to_raw(&e.value, b, ctx);
                    AnnotationElemDefEx { name, tag, value }
                })
                .collect();

            let ann_h = b.create_annotation_ex(ann_cls, &elems);
            attach_fn(b, &target, ann_h);
        }
    }
}

fn annotation_value_to_raw(
    val: &AnnotationValue,
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
) -> (u8, AnnotationElemValue) {
    match val {
        AnnotationValue::Bool(v) => (b'1', AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::I8(v) => (b'2', AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::U8(v) => (b'3', AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::I16(v) => (b'4', AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::U16(v) => (b'5', AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::I32(v) => (b'6', AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::U32(v) => (b'7', AnnotationElemValue::Scalar(*v)),
        AnnotationValue::I64(v) => (b'8', AnnotationElemValue::Scalar64(*v as u64)),
        AnnotationValue::U64(v) => (b'9', AnnotationElemValue::Scalar64(*v)),
        AnnotationValue::F32(v) => (b'A', AnnotationElemValue::Scalar(v.to_bits())),
        AnnotationValue::F64(v) => (b'B', AnnotationElemValue::Scalar64(v.to_bits())),
        AnnotationValue::String(sid) => {
            let h = get_or_add_string_id(b, ctx.string_handles, ctx.pool, *sid);
            (b'C', AnnotationElemValue::EntityRef(h.0))
        }
        AnnotationValue::Record(sid) => {
            let h = resolve_class_for_ann(b, ctx.class_handles, ctx.pool, *sid);
            (b'D', AnnotationElemValue::EntityRef(h.0))
        }
        AnnotationValue::Method { name, offset } => {
            if let Some(mh) = ctx.entities.resolve_method(*name, *offset) {
                (b'E', AnnotationElemValue::EntityRef(mh.0))
            } else {
                (b'E', AnnotationElemValue::Scalar(0))
            }
        }
        AnnotationValue::Enum { name, offset } => {
            if let Some(fh) = ctx.entities.resolve_field(*name, *offset) {
                (b'F', AnnotationElemValue::EntityRef(fh.0))
            } else {
                (b'F', AnnotationElemValue::Scalar(0))
            }
        }
        AnnotationValue::Annotation(nested) => {
            let ann_cls =
                resolve_class_for_ann(b, ctx.class_handles, ctx.pool, nested.class_descriptor);
            let elems: Vec<AnnotationElemDefEx> = nested
                .elements
                .iter()
                .map(|e| {
                    let name = get_or_add_string_id(b, ctx.string_handles, ctx.pool, e.name);
                    let (tag, value) = annotation_value_to_raw(&e.value, b, ctx);
                    AnnotationElemDefEx { name, tag, value }
                })
                .collect();
            let ann_h = b.create_annotation_ex(ann_cls, &elems);
            (b'G', AnnotationElemValue::EntityRef(ann_h.0))
        }
        AnnotationValue::MethodHandle(mh) => {
            let entity_handle = if mh.handle_type.is_field_op() {
                ctx.entities
                    .resolve_field(mh.entity, mh.entity_offset)
                    .map(|h| h.0)
                    .unwrap_or(u32::MAX)
            } else {
                ctx.entities
                    .resolve_method(mh.entity, mh.entity_offset)
                    .map(|h| h.0)
                    .unwrap_or(u32::MAX)
            };
            if entity_handle != u32::MAX {
                let mh_item = b.create_method_handle(mh.handle_type as u8, entity_handle);
                (b'J', AnnotationElemValue::EntityRef(mh_item.0))
            } else {
                (b'J', AnnotationElemValue::Scalar(0))
            }
        }
        AnnotationValue::LiteralArray(values) => {
            let id = format!("ann_la_{}", *ctx.ann_la_counter);
            *ctx.ann_la_counter += 1;
            let la_h = b.add_literal_array(&id);
            for val in values {
                encode_literal_value_simple(b, ctx.string_handles, ctx.pool, la_h, val);
            }
            (b'#', AnnotationElemValue::EntityRef(la_h.0))
        }
        AnnotationValue::Void => (b'I', AnnotationElemValue::Scalar(0)),
        AnnotationValue::StringNullptr => (b'*', AnnotationElemValue::Scalar(0)),
        AnnotationValue::Array { tag, values } => {
            let handles: Vec<u32> = values
                .iter()
                .map(|v| {
                    annotation_array_elem_to_handle(
                        v,
                        b,
                        ctx.string_handles,
                        ctx.class_handles,
                        ctx.pool,
                    )
                })
                .collect();
            if is_entity_array_tag(*tag) {
                (*tag, AnnotationElemValue::EntityArray(handles))
            } else {
                (*tag, AnnotationElemValue::Array(handles))
            }
        }
    }
}

/// Returns true if the annotation array tag refers to entity-reference
/// elements. Tag chars follow upstream pandasm::Value::GetArrayTypeAsChar:
/// K..U are scalar arrays (K=U1 … T=F32, U=F64), V=String, W=Record,
/// X=Method, Y=Enum, Z=Annotation, @=MethodHandle (audit finding #B1).
fn is_entity_array_tag(tag: u8) -> bool {
    matches!(tag, b'V' | b'W' | b'X' | b'Y' | b'Z' | b'@')
}

/// Convert a single annotation array element to a u32 handle/value for the builder.
fn annotation_array_elem_to_handle(
    val: &AnnotationValue,
    b: &mut Builder,
    string_handles: &mut HashMap<StringId, StringHandle>,
    class_handles: &mut HashMap<StringId, ClassHandle>,
    pool: &StringPool,
) -> u32 {
    match val {
        AnnotationValue::Bool(v) => *v as u32,
        AnnotationValue::I8(v) => *v as u32,
        AnnotationValue::U8(v) => *v as u32,
        AnnotationValue::I16(v) => *v as u32,
        AnnotationValue::U16(v) => *v as u32,
        AnnotationValue::I32(v) => *v as u32,
        AnnotationValue::U32(v) => *v,
        AnnotationValue::I64(v) => *v as u32,
        AnnotationValue::U64(v) => *v as u32,
        AnnotationValue::F32(v) => v.to_bits(),
        AnnotationValue::F64(v) => v.to_bits() as u32,
        AnnotationValue::String(sid) => {
            let h = get_or_add_string_id(b, string_handles, pool, *sid);
            h.0
        }
        AnnotationValue::Record(sid) => {
            let h = resolve_class_for_ann(b, class_handles, pool, *sid);
            h.0
        }
        _ => 0,
    }
}

/// Resolve a class descriptor for annotation encoding.
fn resolve_class_for_ann(
    b: &mut Builder,
    class_handles: &mut HashMap<StringId, ClassHandle>,
    pool: &StringPool,
    desc: StringId,
) -> ClassHandle {
    if let Some(&h) = class_handles.get(&desc) {
        return h;
    }
    let desc_str = pool.resolve(desc).expect("dangling StringId");
    let h = b.add_foreign_class(desc_str);
    class_handles.insert(desc, h);
    h
}

/// Simplified literal value encoding for annotation-embedded literal arrays.
/// Does not resolve method entity offsets (no entity_map available).
fn encode_literal_value_simple(
    b: &mut Builder,
    string_handles: &mut HashMap<StringId, StringHandle>,
    pool: &StringPool,
    la: LiteralArrayHandle,
    val: &LiteralValue,
) {
    use crate::literal::LiteralTag;
    match val {
        LiteralValue::Bool(v) => {
            b.literal_array_add_u8(la, LiteralTag::Bool as u8);
            b.literal_array_add_u8(la, *v as u8);
        }
        LiteralValue::Integer8(v) => {
            b.literal_array_add_u8(la, LiteralTag::TagValue as u8);
            b.literal_array_add_u8(la, *v);
        }
        LiteralValue::Integer(v) => {
            b.literal_array_add_u8(la, LiteralTag::Integer as u8);
            b.literal_array_add_u32(la, *v);
        }
        LiteralValue::Float(v) => {
            b.literal_array_add_u8(la, LiteralTag::Float as u8);
            b.literal_array_add_u32(la, v.to_bits());
        }
        LiteralValue::Double(v) => {
            b.literal_array_add_u8(la, LiteralTag::Double as u8);
            b.literal_array_add_u64(la, v.to_bits());
        }
        LiteralValue::String(sid) => {
            b.literal_array_add_u8(la, LiteralTag::String as u8);
            let sh = get_or_add_string_id(b, string_handles, pool, *sid);
            b.literal_array_add_raw_string(la, sh);
        }
        LiteralValue::Method(off)
        | LiteralValue::GeneratorMethod(off)
        | LiteralValue::AsyncGeneratorMethod(off)
        | LiteralValue::Getter(off)
        | LiteralValue::Setter(off) => {
            let tag = match val {
                LiteralValue::Method(_) => LiteralTag::Method,
                LiteralValue::GeneratorMethod(_) => LiteralTag::GeneratorMethod,
                LiteralValue::AsyncGeneratorMethod(_) => LiteralTag::AsyncGeneratorMethod,
                LiteralValue::Getter(_) => LiteralTag::Getter,
                LiteralValue::Setter(_) => LiteralTag::Setter,
                _ => unreachable!(),
            };
            b.literal_array_add_u8(la, tag as u8);
            b.literal_array_add_u32(la, *off);
        }
        LiteralValue::Accessor(v) => {
            b.literal_array_add_u8(la, LiteralTag::Accessor as u8);
            b.literal_array_add_u8(la, *v);
        }
        LiteralValue::MethodAffiliate(v) => {
            b.literal_array_add_u8(la, LiteralTag::MethodAffiliate as u8);
            b.literal_array_add_u16(la, *v);
        }
        LiteralValue::LiteralArray(idx) => {
            b.literal_array_add_u8(la, LiteralTag::LiteralArray as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::LiteralBufferIndex(idx) => {
            b.literal_array_add_u8(la, LiteralTag::LiteralBufferIndex as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::BuiltinTypeIndex(v) => {
            b.literal_array_add_u8(la, LiteralTag::BuiltinTypeIndex as u8);
            b.literal_array_add_u8(la, *v);
        }
        LiteralValue::EtsImplements(sid) => {
            b.literal_array_add_u8(la, LiteralTag::EtsImplements as u8);
            let sh = get_or_add_string_id(b, string_handles, pool, *sid);
            b.literal_array_add_raw_string(la, sh);
        }
        LiteralValue::NullValue(v) => {
            b.literal_array_add_u8(la, LiteralTag::NullValue as u8);
            b.literal_array_add_u8(la, *v);
        }
        LiteralValue::ArrayU1(idx)
        | LiteralValue::ArrayU8(idx)
        | LiteralValue::ArrayI8(idx)
        | LiteralValue::ArrayU16(idx)
        | LiteralValue::ArrayI16(idx)
        | LiteralValue::ArrayU32(idx)
        | LiteralValue::ArrayI32(idx)
        | LiteralValue::ArrayU64(idx)
        | LiteralValue::ArrayI64(idx)
        | LiteralValue::ArrayF32(idx)
        | LiteralValue::ArrayF64(idx)
        | LiteralValue::ArrayString(idx) => {
            let tag = match val {
                LiteralValue::ArrayU1(_) => LiteralTag::ArrayU1,
                LiteralValue::ArrayU8(_) => LiteralTag::ArrayU8,
                LiteralValue::ArrayI8(_) => LiteralTag::ArrayI8,
                LiteralValue::ArrayU16(_) => LiteralTag::ArrayU16,
                LiteralValue::ArrayI16(_) => LiteralTag::ArrayI16,
                LiteralValue::ArrayU32(_) => LiteralTag::ArrayU32,
                LiteralValue::ArrayI32(_) => LiteralTag::ArrayI32,
                LiteralValue::ArrayU64(_) => LiteralTag::ArrayU64,
                LiteralValue::ArrayI64(_) => LiteralTag::ArrayI64,
                LiteralValue::ArrayF32(_) => LiteralTag::ArrayF32,
                LiteralValue::ArrayF64(_) => LiteralTag::ArrayF64,
                LiteralValue::ArrayString(_) => LiteralTag::ArrayString,
                _ => unreachable!(),
            };
            b.literal_array_add_u8(la, tag as u8);
            b.literal_array_add_u32(la, idx.0);
        }
    }
}

fn encode_debug_info(
    b: &mut Builder,
    string_handles: &mut HashMap<StringId, StringHandle>,
    pool: &StringPool,
    method_h: MethodHandle,
    dbg: &MethodDebugInfo,
    byte_offsets: &[u32],
    code_len: u32,
) {
    // Skip if debug info is completely empty (no meaningful content).
    let has_content = !dbg.line_table.is_empty()
        || !dbg.column_table.is_empty()
        || !dbg.local_vars.is_empty()
        || !dbg.params.is_empty()
        || dbg.source_file.is_some()
        || dbg.source_code.is_some();
    if !has_content {
        return;
    }

    let lnp = b.create_lnp();
    let first_line = dbg.line_table.first().map_or(0, |e| e.line);
    let debug_h = b.create_debug_info(lnp, first_line);

    // Source file / source code
    if let Some(sf) = dbg.source_file {
        let sf_str = pool.resolve(sf).unwrap_or("");
        if !sf_str.is_empty() {
            let sh = get_or_add_string_id(b, string_handles, pool, sf);
            b.lnp_emit_set_file(lnp, debug_h, sh);
        }
    }
    if let Some(sc) = dbg.source_code {
        let sc_str = pool.resolve(sc).unwrap_or("");
        if !sc_str.is_empty() {
            let sh = get_or_add_string_id(b, string_handles, pool, sc);
            b.lnp_emit_set_source_code(lnp, debug_h, sh);
        }
    }

    // Params (signature not preserved — C++ writer limitation)
    for p in &dbg.params {
        let nh = get_or_add_string_id(b, string_handles, pool, p.name);
        b.debug_add_param(debug_h, nh);
    }

    // Line table — emit as (advance_pc, advance_line) deltas
    let mut prev_pc: u32 = 0;
    let mut prev_line: u32 = first_line;
    for entry in &dbg.line_table {
        let pc = index_to_offset(byte_offsets, entry.index, code_len);
        let pc_delta = pc.saturating_sub(prev_pc);
        let line_delta = entry.line as i32 - prev_line as i32;
        if pc_delta > 0 {
            b.lnp_emit_advance_pc(lnp, debug_h, pc_delta);
        }
        if line_delta != 0 {
            b.lnp_emit_advance_line(lnp, debug_h, line_delta);
        }
        prev_pc = pc;
        prev_line = entry.line;
    }

    // Column table
    let mut prev_pc: u32 = 0;
    for entry in &dbg.column_table {
        let pc = index_to_offset(byte_offsets, entry.index, code_len);
        let pc_delta = pc.saturating_sub(prev_pc);
        b.lnp_emit_column(lnp, debug_h, pc_delta, entry.column);
        prev_pc = pc;
    }

    // Local variables
    for lv in &dbg.local_vars {
        let name_h = get_or_add_string_id(b, string_handles, pool, lv.name);
        let type_h = get_or_add_string_id(b, string_handles, pool, lv.type_name);
        let sig_str = pool.resolve(lv.type_signature).unwrap_or("");
        if !sig_str.is_empty() {
            let sig_h = get_or_add_string_id(b, string_handles, pool, lv.type_signature);
            b.lnp_emit_start_local_extended(lnp, debug_h, lv.reg_number, name_h, type_h, sig_h);
        } else {
            b.lnp_emit_start_local(lnp, debug_h, lv.reg_number, name_h, type_h);
        }
        // Emit end_local at the end offset
        b.lnp_emit_end_local(lnp, lv.reg_number);
    }

    b.lnp_emit_end(lnp);
    b.method_set_debug_info(method_h, debug_h);
}

fn encode_literal_value(
    b: &mut Builder,
    string_handles: &mut HashMap<StringId, StringHandle>,
    pool: &StringPool,
    la: LiteralArrayHandle,
    val: &LiteralValue,
    entity_map: &HashMap<u32, StringId>,
    entities: &EntityHandles,
) {
    // Helper: resolve a method entity offset to a MethodHandle. The offset
    // is the unique entity identity; the name lookup via entity_map is only
    // a fallback for hand-built models (offset 0).
    let resolve_method = |off: u32| -> Option<MethodHandle> {
        if off != 0
            && let Some(&mh) = entities.methods_by_offset.get(&off)
        {
            return Some(mh);
        }
        let sid = entity_map.get(&off)?;
        entities.methods_by_name.get(sid).copied()
    };

    // Literal arrays are stored as flat (tag_u8, value) pairs.
    match val {
        LiteralValue::Bool(v) => {
            b.literal_array_add_u8(la, LiteralTag::Bool as u8);
            b.literal_array_add_u8(la, *v as u8);
        }
        LiteralValue::Integer8(v) => {
            b.literal_array_add_u8(la, LiteralTag::TagValue as u8);
            b.literal_array_add_u8(la, *v);
        }
        LiteralValue::Integer(v) => {
            b.literal_array_add_u8(la, LiteralTag::Integer as u8);
            b.literal_array_add_u32(la, *v);
        }
        LiteralValue::Float(v) => {
            b.literal_array_add_u8(la, LiteralTag::Float as u8);
            b.literal_array_add_u32(la, v.to_bits());
        }
        LiteralValue::Double(v) => {
            b.literal_array_add_u8(la, LiteralTag::Double as u8);
            b.literal_array_add_u64(la, v.to_bits());
        }
        LiteralValue::String(sid) => {
            b.literal_array_add_u8(la, LiteralTag::String as u8);
            let sh = get_or_add_string_id(b, string_handles, pool, *sid);
            b.literal_array_add_raw_string(la, sh);
        }
        LiteralValue::Method(off) => {
            if let Some(mh) = resolve_method(*off) {
                b.literal_array_add_u8(la, LiteralTag::Method as u8);
                b.literal_array_add_raw_method(la, mh);
            } else {
                b.literal_array_add_u8(la, LiteralTag::Method as u8);
                b.literal_array_add_u32(la, *off);
            }
        }
        LiteralValue::GeneratorMethod(off) => {
            if let Some(mh) = resolve_method(*off) {
                b.literal_array_add_u8(la, LiteralTag::GeneratorMethod as u8);
                b.literal_array_add_raw_method(la, mh);
            } else {
                b.literal_array_add_u8(la, LiteralTag::GeneratorMethod as u8);
                b.literal_array_add_u32(la, *off);
            }
        }
        LiteralValue::AsyncGeneratorMethod(off) => {
            if let Some(mh) = resolve_method(*off) {
                b.literal_array_add_u8(la, LiteralTag::AsyncGeneratorMethod as u8);
                b.literal_array_add_raw_method(la, mh);
            } else {
                b.literal_array_add_u8(la, LiteralTag::AsyncGeneratorMethod as u8);
                b.literal_array_add_u32(la, *off);
            }
        }
        LiteralValue::Getter(off) => {
            if let Some(mh) = resolve_method(*off) {
                b.literal_array_add_u8(la, LiteralTag::Getter as u8);
                b.literal_array_add_raw_method(la, mh);
            } else {
                b.literal_array_add_u8(la, LiteralTag::Getter as u8);
                b.literal_array_add_u32(la, *off);
            }
        }
        LiteralValue::Setter(off) => {
            if let Some(mh) = resolve_method(*off) {
                b.literal_array_add_u8(la, LiteralTag::Setter as u8);
                b.literal_array_add_raw_method(la, mh);
            } else {
                b.literal_array_add_u8(la, LiteralTag::Setter as u8);
                b.literal_array_add_u32(la, *off);
            }
        }
        LiteralValue::Accessor(v) => {
            b.literal_array_add_u8(la, LiteralTag::Accessor as u8);
            b.literal_array_add_u8(la, *v);
        }
        LiteralValue::MethodAffiliate(v) => {
            b.literal_array_add_u8(la, LiteralTag::MethodAffiliate as u8);
            b.literal_array_add_u16(la, *v);
        }
        LiteralValue::LiteralArray(idx) => {
            b.literal_array_add_u8(la, LiteralTag::LiteralArray as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::LiteralBufferIndex(idx) => {
            b.literal_array_add_u8(la, LiteralTag::LiteralBufferIndex as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::BuiltinTypeIndex(v) => {
            b.literal_array_add_u8(la, LiteralTag::BuiltinTypeIndex as u8);
            b.literal_array_add_u8(la, *v);
        }
        LiteralValue::EtsImplements(sid) => {
            b.literal_array_add_u8(la, LiteralTag::EtsImplements as u8);
            let sh = get_or_add_string_id(b, string_handles, pool, *sid);
            b.literal_array_add_raw_string(la, sh);
        }
        LiteralValue::NullValue(v) => {
            b.literal_array_add_u8(la, LiteralTag::NullValue as u8);
            b.literal_array_add_u8(la, *v);
        }
        LiteralValue::ArrayU1(idx) => {
            b.literal_array_add_u8(la, LiteralTag::ArrayU1 as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::ArrayU8(idx) => {
            b.literal_array_add_u8(la, LiteralTag::ArrayU8 as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::ArrayI8(idx) => {
            b.literal_array_add_u8(la, LiteralTag::ArrayI8 as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::ArrayU16(idx) => {
            b.literal_array_add_u8(la, LiteralTag::ArrayU16 as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::ArrayI16(idx) => {
            b.literal_array_add_u8(la, LiteralTag::ArrayI16 as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::ArrayU32(idx) => {
            b.literal_array_add_u8(la, LiteralTag::ArrayU32 as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::ArrayI32(idx) => {
            b.literal_array_add_u8(la, LiteralTag::ArrayI32 as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::ArrayU64(idx) => {
            b.literal_array_add_u8(la, LiteralTag::ArrayU64 as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::ArrayI64(idx) => {
            b.literal_array_add_u8(la, LiteralTag::ArrayI64 as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::ArrayF32(idx) => {
            b.literal_array_add_u8(la, LiteralTag::ArrayF32 as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::ArrayF64(idx) => {
            b.literal_array_add_u8(la, LiteralTag::ArrayF64 as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::ArrayString(idx) => {
            b.literal_array_add_u8(la, LiteralTag::ArrayString as u8);
            b.literal_array_add_u32(la, idx.0);
        }
    }
}

/// Convert an instruction index to a byte offset using the offset table.
fn index_to_offset(byte_offsets: &[u32], index: u32, code_len: u32) -> u32 {
    byte_offsets
        .get(index as usize)
        .copied()
        .unwrap_or(code_len)
}

/// Resolve a StringId through the pool and add it to the builder's string table.
fn get_or_add_string_id(
    b: &mut Builder,
    string_handles: &mut HashMap<StringId, StringHandle>,
    pool: &StringPool,
    sid: StringId,
) -> StringHandle {
    if let Some(&h) = string_handles.get(&sid) {
        return h;
    }
    let s = pool.resolve(sid).expect("dangling StringId");
    let h = b.add_string(s);
    string_handles.insert(sid, h);
    h
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::AccessFlags;

    fn method(pool: &mut StringPool, name: &str, offset: u32) -> Method {
        Method {
            name: pool.get_or_intern(name),
            offset,
            access_flags: AccessFlags::empty(),
            function_kind: FunctionKind::None,
            source_lang: SourceLang::EcmaScript,
            is_external: false,
            return_type: None,
            arg_types: Vec::new(),
            body: None,
            annotations: Annotations::default(),
            debug: None,
        }
    }

    fn field(pool: &mut StringPool, name: &str, offset: u32) -> Field {
        Field {
            name: pool.get_or_intern(name),
            offset,
            field_type: Type::Tagged,
            access_flags: AccessFlags::empty(),
            is_external: false,
            initial_value: None,
            annotations: Annotations::default(),
        }
    }

    #[test]
    fn handles_resolve_by_offset_when_names_collide() {
        // Same name in two classes; only the offset disambiguates.
        let mut pool = StringPool::default();
        let name = pool.get_or_intern("foo");
        let mut entities = EntityHandles::default();

        entities.insert_method(&method(&mut pool, "foo", 100), MethodHandle(1));
        entities.insert_method(&method(&mut pool, "foo", 200), MethodHandle(2));
        entities.insert_field(&field(&mut pool, "foo", 300), FieldHandle(3));
        entities.insert_field(&field(&mut pool, "foo", 400), FieldHandle(4));

        assert_eq!(entities.resolve_method(name, 100), Some(MethodHandle(1)));
        assert_eq!(entities.resolve_method(name, 200), Some(MethodHandle(2)));
        assert_eq!(entities.resolve_field(name, 300), Some(FieldHandle(3)));
        assert_eq!(entities.resolve_field(name, 400), Some(FieldHandle(4)));
    }

    #[test]
    fn handles_fall_back_to_name_for_offsetless_models() {
        // Hand-built models carry offset 0; name lookup (last insert wins)
        // must still work, preserving pre-#6 behavior.
        let mut pool = StringPool::default();
        let name = pool.get_or_intern("bar");
        let mut entities = EntityHandles::default();

        entities.insert_method(&method(&mut pool, "bar", 0), MethodHandle(10));
        entities.insert_field(&field(&mut pool, "bar", 0), FieldHandle(20));

        assert_eq!(entities.resolve_method(name, 0), Some(MethodHandle(10)));
        assert_eq!(entities.resolve_field(name, 0), Some(FieldHandle(20)));
        // Unknown offsets on an offset-carrying resolver do not resolve.
        assert_eq!(entities.resolve_method(name, 999), Some(MethodHandle(10)));
    }
}
