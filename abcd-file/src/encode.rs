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

/// Convert a Rust UTF-8 string to MUTF-8 (modified UTF-8) bytes in a CString.
///
/// MUTF-8 encodes U+0000 as the two-byte overlong sequence `C0 80`, so the
/// result never contains a `0x00` byte regardless of the input; astral
/// characters keep their standard 4-byte UTF-8 encoding (panda's MUTF-8
/// differs from UTF-8 only in the NUL rule — upstream utf.cpp:131-138).
fn c_mutf8(s: &str) -> CString {
    let mut bytes = Vec::with_capacity(s.len());
    for ch in s.chars() {
        if ch == '\0' {
            bytes.extend_from_slice(&[0xC0, 0x80]);
        } else {
            let mut buf = [0u8; 4];
            bytes.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
        }
    }
    // Unreachable: MUTF-8 output contains no 0x00 byte by construction.
    CString::new(bytes).expect("MUTF-8 contains no NUL")
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

/// A symbolic builder target for a bytecode entity operand.
pub enum CodeEntity {
    String(StringHandle),
    Method(MethodHandle),
    LiteralArray(LiteralArrayHandle),
    Class(ClassHandle),
    Field(FieldHandle),
}

unsafe extern "C" fn update_code_id(
    code: *mut u8,
    size: usize,
    byte_offset: u32,
    operand: u32,
    new_id: u32,
) -> std::ffi::c_int {
    if code.is_null() || byte_offset as usize >= size {
        return 0;
    }
    // SAFETY: the builder owns this buffer and grants exclusive access for
    // this synchronous callback. No Rust reference into it survives the call.
    let bytes = unsafe { std::slice::from_raw_parts_mut(code, size) };
    abcd_isa::relocate_entity_id(
        &mut bytes[byte_offset as usize..],
        operand,
        abcd_isa::EntityId(new_id),
    )
    .is_ok() as std::ffi::c_int
}

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

/// Handle-based module record for [`Builder::literal_array_add_module_data`].
///
/// Variants correspond to the vendored `panda_file::ModuleTag` kinds; the
/// wire tag values come from bindgen (`ModuleTag_*`), not hand mirrors.
#[derive(Clone, Copy, Debug)]
pub enum ModuleRecordDef {
    RegularImport {
        local_name: StringHandle,
        import_name: StringHandle,
        module_request_idx: u16,
    },
    NamespaceImport {
        local_name: StringHandle,
        module_request_idx: u16,
    },
    LocalExport {
        local_name: StringHandle,
        export_name: StringHandle,
    },
    IndirectExport {
        export_name: StringHandle,
        import_name: StringHandle,
        module_request_idx: u16,
    },
    StarExport {
        module_request_idx: u16,
    },
}

impl ModuleRecordDef {
    /// Convert to the FFI record; `u32::MAX` marks an absent name handle
    /// (bridge sentinel convention).
    fn as_raw(&self) -> sys::AbcModuleRecordDef {
        use ModuleRecordDef::*;
        match *self {
            RegularImport {
                local_name,
                import_name,
                module_request_idx,
            } => sys::AbcModuleRecordDef {
                tag: sys::ModuleTag_REGULAR_IMPORT,
                export_name_handle: u32::MAX,
                module_request_idx: module_request_idx as u32,
                import_name_handle: import_name.as_raw(),
                local_name_handle: local_name.as_raw(),
            },
            NamespaceImport {
                local_name,
                module_request_idx,
            } => sys::AbcModuleRecordDef {
                tag: sys::ModuleTag_NAMESPACE_IMPORT,
                export_name_handle: u32::MAX,
                module_request_idx: module_request_idx as u32,
                import_name_handle: u32::MAX,
                local_name_handle: local_name.as_raw(),
            },
            LocalExport {
                local_name,
                export_name,
            } => sys::AbcModuleRecordDef {
                tag: sys::ModuleTag_LOCAL_EXPORT,
                export_name_handle: export_name.as_raw(),
                module_request_idx: 0,
                import_name_handle: u32::MAX,
                local_name_handle: local_name.as_raw(),
            },
            IndirectExport {
                export_name,
                import_name,
                module_request_idx,
            } => sys::AbcModuleRecordDef {
                tag: sys::ModuleTag_INDIRECT_EXPORT,
                export_name_handle: export_name.as_raw(),
                module_request_idx: module_request_idx as u32,
                import_name_handle: import_name.as_raw(),
                local_name_handle: u32::MAX,
            },
            StarExport { module_request_idx } => sys::AbcModuleRecordDef {
                tag: sys::ModuleTag_STAR_EXPORT,
                export_name_handle: u32::MAX,
                module_request_idx: module_request_idx as u32,
                import_name_handle: u32::MAX,
                local_name_handle: u32::MAX,
            },
        }
    }
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

    /// Set the API policy before adding items.
    pub fn set_api(&mut self, version: u8, sub_api: &str) {
        let c_sub = c_mutf8(sub_api);
        unsafe { sys::abc_builder_set_api(self.raw, version, c_sub.as_ptr()) };
    }

    /// Select an exact output version using the vendored writer's version
    /// policy. Call before adding items. An unsupported version leaves the
    /// existing selection unchanged.
    pub fn set_file_version(&mut self, version: crate::Version) -> Result<(), Error> {
        // SAFETY: the builder is live and as_bytes provides all four bytes.
        if unsafe { sys::abc_builder_set_file_version(self.raw, version.as_bytes().as_ptr()) } == 0
        {
            return Err(Error::UnsupportedOutputVersion(version));
        }
        Ok(())
    }

    // --- Strings ---

    /// Add a string, returning its handle.
    pub fn add_string(&mut self, s: &str) -> StringHandle {
        let c_str = c_mutf8(s);
        StringHandle(unsafe { sys::abc_builder_add_string(self.raw, c_str.as_ptr()) })
    }

    // --- Classes ---

    /// Add a class with the given descriptor (e.g. `"LMyClass;"`).
    pub fn add_class(&mut self, descriptor: &str) -> ClassHandle {
        let c_desc = c_mutf8(descriptor);
        ClassHandle(unsafe { sys::abc_builder_add_class(self.raw, c_desc.as_ptr()) })
    }

    /// Add a foreign (external) class.
    pub fn add_foreign_class(&mut self, descriptor: &str) -> ClassHandle {
        let c_desc = c_mutf8(descriptor);
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
        let c_name = c_mutf8(name);
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
        let c_name = c_mutf8(name);
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

    /// Add a typed parameter with reference-type support.
    pub fn method_add_param_ex(
        &mut self,
        m: MethodHandle,
        ty: Type,
        class: Option<ClassHandle>,
    ) -> ParamHandle {
        ParamHandle(unsafe {
            sys::abc_builder_method_add_param_ex(
                self.raw,
                m.0,
                ty.as_raw_u8(),
                class.map_or(0, |h| h.0),
            )
        })
    }

    /// Seal staged param annotations into a ParamAnnotationsItem
    /// (`is_runtime`: false = compile-time, true = runtime). The vendored
    /// MethodParamItem keeps a single annotation vector per param; sealing
    /// snapshots whatever is staged at that moment.
    pub fn method_seal_param_annotations(&mut self, m: MethodHandle, is_runtime: bool) {
        unsafe { sys::abc_builder_method_seal_param_annotations(self.raw, m.0, is_runtime as i32) };
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
        let c_name = c_mutf8(name);
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
        let c_name = c_mutf8(name);
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
        let c_name = c_mutf8(name);
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

    /// Set a field's initial value to a literal-array item reference.
    ///
    /// The vendored writer stores the item's LAYOUT offset inline
    /// (`ScalarValueItem` Type::ID → `FieldTag::VALUE` + u32), so the
    /// reference relocates with the item automatically. This is how es2abc
    /// stores `_ESModuleRecord` / `_ESScopeNamesRecord` field values.
    pub fn field_set_value_literalarray(
        &mut self,
        f: FieldHandle,
        la: LiteralArrayHandle,
    ) -> Result<(), Error> {
        // SAFETY: the builder is live; the bridge validates both handles.
        if unsafe { sys::abc_builder_field_set_value_literalarray(self.raw, f.0, la.0) } != 0 {
            return Err(Error::ModuleData(
                "field_set_value_literalarray: invalid field or literal-array handle".into(),
            ));
        }
        Ok(())
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
        let c_id = c_mutf8(id);
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

    /// Append a complete `METHODAFFILIATE` literal (`[tag][value]` pair) —
    /// used by the module-record encoding for module request indices.
    pub fn literal_array_add_method_affiliate(&mut self, la: LiteralArrayHandle, val: u16) {
        self.literal_array_add_u8(la, LiteralTag::MethodAffiliate as u8);
        self.literal_array_add_u16(la, val);
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

    /// Stage a complete module-record blob (the UNTAGGED vendored
    /// `ModuleDataAccessor` layout: request count + request strings, then
    /// per-tag section counts and entries) into a literal array created by
    /// [`Self::add_literal_array`]. The vendored writer emits the u32
    /// item-count header itself. Nothing is staged if any input is invalid.
    pub fn literal_array_add_module_data(
        &mut self,
        la: LiteralArrayHandle,
        requests: &[StringHandle],
        records: &[ModuleRecordDef],
    ) -> Result<(), Error> {
        let raw_requests: Vec<u32> = requests.iter().map(|h| h.as_raw()).collect();
        let raw_records: Vec<sys::AbcModuleRecordDef> =
            records.iter().map(ModuleRecordDef::as_raw).collect();
        // SAFETY: the builder is live; both slices outlive the call; the
        // bridge validates all handles and record fields before staging.
        let rc = unsafe {
            sys::abc_builder_literal_array_add_module_data(
                self.raw,
                la.0,
                raw_requests.as_ptr(),
                raw_requests.len() as u32,
                raw_records.as_ptr(),
                raw_records.len() as u32,
            )
        };
        if rc != 0 {
            return Err(Error::ModuleData(format!(
                "module-record blob staging rejected ({records} records)",
                records = records.len()
            )));
        }
        Ok(())
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

    /// Resolve an instruction's ID operand after the upstream writer assigns
    /// method-local indices. `byte_offset` is an instruction start and
    /// `operand` is its ID ordinal (excluding register/immediate operands).
    pub fn relocate_code_id(
        &mut self,
        method: MethodHandle,
        byte_offset: u32,
        operand: u32,
        target: CodeEntity,
    ) -> Result<(), Error> {
        use sys::{
            AbcCodeEntityKind_ABC_CODE_CLASS as CLASS, AbcCodeEntityKind_ABC_CODE_FIELD as FIELD,
            AbcCodeEntityKind_ABC_CODE_LITERAL_ARRAY as LITERAL,
            AbcCodeEntityKind_ABC_CODE_METHOD as METHOD,
            AbcCodeEntityKind_ABC_CODE_STRING as STRING,
        };
        let (kind, handle) = match target {
            CodeEntity::String(h) => (STRING, h.0),
            CodeEntity::Method(h) => (METHOD, h.0),
            CodeEntity::LiteralArray(h) => (LITERAL, h.0),
            CodeEntity::Class(h) => (CLASS, h.0),
            CodeEntity::Field(h) => (FIELD, h.0),
        };
        // SAFETY: builder handle lives for the duration of this call. C++
        // validates ownership and stores only pointers owned by the builder.
        let ok = unsafe {
            sys::abc_builder_relocate_code_id(
                self.raw,
                method.0,
                byte_offset,
                operand,
                kind,
                handle,
            )
        };
        if ok == 0 {
            return Err(Error::CodeRelocation(format!(
                "invalid builder target or code location at {byte_offset:#x}"
            )));
        }
        Ok(())
    }

    /// Finalize the builder and return the serialized ABC file bytes.
    pub fn finalize(&mut self) -> Result<Vec<u8>, Error> {
        let mut out_len: u32 = 0;
        // SAFETY: raw is valid; out_len is stack-allocated.
        let ptr = unsafe {
            sys::abc_builder_finalize_with_code_ids(self.raw, &mut out_len, Some(update_code_id))
        };
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
/// Source entity operands are resolved through each method body's index map
/// and relocated after the upstream writer assigns new indices. The output
/// is checked by this crate's decoder before being returned. This readback
/// check does not prove runtime equivalence or complete metadata preservation.
///
/// Note: `ParamInfo::signature` is not preserved (C++ writer limitation).
pub fn encode(file: &File) -> Result<Vec<u8>, Error> {
    validate_annotation_arrays(file)?;
    let mut b = Builder::new();
    b.set_file_version(file.version)?;
    let pool = &file.strings;

    // Helper: resolve a StringId to &str, erroring on invalid ids.
    let rs = |id: StringId| -> Result<&str, Error> {
        pool.resolve(id).ok_or_else(|| Error::Malformed {
            field: "string_id",
            context: format!("dangling StringId {id:?} in file"),
        })
    };

    // --- Collect all strings and build handle map ---
    let mut string_handles: HashMap<StringId, StringHandle> = HashMap::new();

    // --- Create classes (foreign first, then normal) ---
    let mut class_handles: HashMap<StringId, ClassHandle> = HashMap::new();
    let mut entities = EntityHandles::default();
    let mut code_references = Vec::new();
    // Field values that reference literal-array items (module-record blobs,
    // scope-names arrays), wired up after the literal-array section exists.
    let mut deferred_field_values: Vec<(FieldHandle, &FieldValue)> = Vec::new();
    let mut ann_la_counter: u32 = 0;
    // Number of annotation-embedded literal arrays that will be created
    // while classes are configured. Model literal arrays are only created
    // afterwards (creation order is significant to the vendored writer), so
    // their builder handles start at this offset — used to resolve nested
    // `LiteralValue::LiteralArray` references on the annotation path (#8).
    let ann_la_base = count_annotation_literal_arrays(file);

    // First pass: foreign classes
    for (&desc, cls) in &file.classes {
        if cls.is_external {
            let h = b.add_foreign_class(rs(desc)?);
            class_handles.insert(desc, h);
        }
    }
    // Second pass: normal classes
    for (&desc, cls) in &file.classes {
        if !cls.is_external {
            let desc_str = rs(desc)?;
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
     -> Result<ClassHandle, Error> {
        if let Some(&h) = map.get(&desc) {
            return Ok(h);
        }
        let desc_str = pool.resolve(desc).ok_or_else(|| Error::Malformed {
            field: "string_id",
            context: format!("dangling StringId {desc:?} for class descriptor"),
        })?;
        let h = b.add_foreign_class(desc_str);
        map.insert(desc, h);
        Ok(h)
    };

    // --- Configure each class ---
    for (&desc, cls) in &file.classes {
        let cls_h = class_handles[&desc];

        b.class_set_access_flags(cls_h, cls.access_flags);
        b.class_set_source_lang(cls_h, cls.source_lang);

        if let Some(sf) = cls.source_file {
            let sh = get_or_add_string_id(&mut b, &mut string_handles, pool, sf)?;
            b.class_set_source_file(cls_h, sh);
        }
        if let Some(sup) = cls.super_class {
            let sup_h = resolve_class_id(&mut b, &mut class_handles, pool, sup)?;
            b.class_set_super_class(cls_h, sup_h);
        }
        for &iface in &cls.interfaces {
            let iface_h = resolve_class_id(&mut b, &mut class_handles, pool, iface)?;
            b.class_add_interface(cls_h, iface_h);
        }

        // --- Methods ---
        for method in &cls.methods {
            let method_name_str = rs(method.name)?;
            let ret_type = method.return_type.unwrap_or(Type::Void);
            let ret_class = if let Type::Reference(d) = ret_type {
                Some(resolve_class_id(&mut b, &mut class_handles, pool, d)?)
            } else {
                None
            };
            let arg_classes: Vec<Option<ClassHandle>> = method
                .arg_types
                .iter()
                .map(|t| {
                    if let Type::Reference(d) = t {
                        resolve_class_id(&mut b, &mut class_handles, pool, *d).map(Some)
                    } else {
                        Ok(None)
                    }
                })
                .collect::<Result<_, Error>>()?;

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
                                    file.resolve_entity(cb.type_idx)
                                        .map(|d| {
                                            resolve_class_id(&mut b, &mut class_handles, pool, d)
                                        })
                                        .transpose()?
                                };
                                let handler_pc =
                                    byte_offsets.get(cb.handler as usize).copied().unwrap_or(0);
                                let end = cb.handler + cb.len;
                                let end_pc = byte_offsets
                                    .get(end as usize)
                                    .copied()
                                    .unwrap_or(code_bytes.len() as u32);
                                Ok(CatchBlockDef {
                                    type_class,
                                    handler_pc,
                                    code_size: end_pc - handler_pc,
                                })
                            })
                            .collect::<Result<_, Error>>()?;
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
                    )?;
                }

                if let Some(body) = &method.body {
                    code_references.push((m_h, byte_offsets, body));
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
                    ann_la_base,
                    literal_array_count: file.literal_arrays.len(),
                    pool,
                };
                encode_annotations_on(
                    &mut b,
                    &mut ctx,
                    &method.annotations,
                    AnnotationTarget::Method(method_h),
                )?;
            }

            // --- Parameter annotations ---
            // Contract (maintainer ruling, same precedent as the annotation
            // category fold, review finding #9): decode keeps both buckets;
            // encode folds them. The vendored MethodParamItem has a single
            // annotation vector per param and sealing snapshots it
            // (ParamAnnotationsItem ctor, vendor file_items.cpp:424), so the
            // fold stages the per-param union of both buckets through the
            // compile-time adder and seals ONCE as compile-time — unless the
            // compile-time bucket is empty, in which case the runtime bucket
            // is staged alone and sealed as runtime.
            let pa = &method.param_annotations;
            let has_compile = pa.compile_time.iter().any(|v| !v.is_empty());
            let has_runtime = pa.runtime.iter().any(|v| !v.is_empty());
            if !method.is_external && (has_compile || has_runtime) {
                // Params must exist before annotations can attach to them
                // (the bridge drops out-of-range param indices). Hand-built
                // models may carry param annotations without arg_types; pad
                // with TAGGED params.
                let num_params = method
                    .arg_types
                    .len()
                    .max(pa.compile_time.len())
                    .max(pa.runtime.len());
                let mut param_handles = Vec::with_capacity(num_params);
                for i in 0..num_params {
                    let ty = method.arg_types.get(i).copied().unwrap_or(Type::Tagged);
                    let ref_cls = if let Type::Reference(d) = ty {
                        Some(resolve_class_id(&mut b, &mut class_handles, pool, d)?)
                    } else {
                        None
                    };
                    param_handles.push(b.method_add_param_ex(method_h, ty, ref_cls));
                }

                let seal_as_runtime = !has_compile;
                let mut ctx = AnnotationEncodeCtx {
                    string_handles: &mut string_handles,
                    class_handles: &mut class_handles,
                    entities: &entities,
                    ann_la_counter: &mut ann_la_counter,
                    ann_la_base,
                    literal_array_count: file.literal_arrays.len(),
                    pool,
                };
                for (idx, param_h) in param_handles.iter().enumerate() {
                    // Per-param union of both buckets; the runtime bucket may
                    // already contain compile-time annotations (vendor seal
                    // snapshots the shared vector), so dedup by value.
                    let staged: Vec<&Annotation> = if seal_as_runtime {
                        pa.runtime.get(idx).into_iter().flatten().collect()
                    } else {
                        pa.compile_time
                            .get(idx)
                            .into_iter()
                            .flatten()
                            .chain(pa.runtime.get(idx).into_iter().flatten().filter(|ra| {
                                !pa.compile_time.get(idx).is_some_and(|c| c.contains(*ra))
                            }))
                            .collect()
                    };
                    for ann in staged {
                        let ann_h = encode_single_annotation(&mut b, &mut ctx, ann)?;
                        b.method_param_add_annotation(method_h, *param_h, ann_h);
                    }
                }
                b.method_seal_param_annotations(method_h, seal_as_runtime);
            }
        }

        // --- Fields ---
        for field in &cls.fields {
            let field_name_str = rs(field.name)?;
            let ty = field.field_type;
            let field_h = if field.is_external {
                b.add_foreign_field(cls_h, field_name_str, ty)
            } else if let Type::Reference(d) = ty {
                let ref_cls = resolve_class_id(&mut b, &mut class_handles, pool, d)?;
                b.class_add_field_ex(cls_h, field_name_str, ty, ref_cls, field.access_flags)
            } else {
                b.class_add_field(cls_h, field_name_str, ty, field.access_flags)
            };

            // Track field handle for annotation references.
            entities.insert_field(field, field_h);

            // Initial value. Offset-reference values (module-record and
            // scope-names blobs) are deferred: their literal-array items are
            // only created after class configuration (creation order is
            // significant to the vendored writer), and the field value must
            // reference the item so the writer relocates it at layout time.
            match &field.initial_value {
                Some(FieldValue::I32(v)) => b.field_set_value_i32(field_h, *v),
                Some(FieldValue::I64(v)) => b.field_set_value_i64(field_h, *v),
                Some(FieldValue::F32(v)) => b.field_set_value_f32(field_h, *v),
                Some(FieldValue::F64(v)) => b.field_set_value_f64(field_h, *v),
                Some(FieldValue::ModuleData(_)) | Some(FieldValue::LiteralArrayRef(_)) => {
                    deferred_field_values.push((
                        field_h,
                        field.initial_value.as_ref().expect("deferred value"),
                    ))
                }
                None => {}
            }

            // Field annotations
            {
                let mut ctx = AnnotationEncodeCtx {
                    string_handles: &mut string_handles,
                    class_handles: &mut class_handles,
                    entities: &entities,
                    ann_la_counter: &mut ann_la_counter,
                    ann_la_base,
                    literal_array_count: file.literal_arrays.len(),
                    pool,
                };
                encode_annotations_on(
                    &mut b,
                    &mut ctx,
                    &field.annotations,
                    AnnotationTarget::Field(field_h),
                )?;
            }
        }

        // Class annotations
        {
            let mut ctx = AnnotationEncodeCtx {
                string_handles: &mut string_handles,
                class_handles: &mut class_handles,
                entities: &entities,
                ann_la_counter: &mut ann_la_counter,
                ann_la_base,
                literal_array_count: file.literal_arrays.len(),
                pool,
            };
            encode_annotations_on(
                &mut b,
                &mut ctx,
                &cls.annotations,
                AnnotationTarget::Class(cls_h),
            )?;
        }
    }

    // --- Literal array contents ---
    // Model literal arrays are created after class configuration, so their
    // builder handles start after every annotation-embedded (`ann_la_*`)
    // array: handle(i) = ann_la_base + i.
    let literal_handles: Vec<_> = (0..file.literal_arrays.len())
        .map(|index| b.add_literal_array(&index.to_string()))
        .collect();
    for (i, (la, &la_h)) in file.literal_arrays.iter().zip(&literal_handles).enumerate() {
        debug_assert_eq!(
            la_h.as_raw(),
            ann_la_base + i as u32,
            "model literal-array handles must follow annotation-embedded ones"
        );
        for val in &la.values {
            encode_literal_value(
                &mut b,
                &mut string_handles,
                pool,
                la_h,
                val,
                &file.entity_map,
                &entities,
                &literal_handles,
            )?;
        }
    }

    // --- Module-record blobs and scope-names field references ---
    // These literal arrays are created at the same point as model literal
    // arrays (after all class configuration; creation order is significant
    // to the vendored writer — F-new-1), so their handles follow the model
    // arrays and never disturb the `ann_la_base` handle arithmetic above.
    let mut module_la_counter: u32 = 0;
    for (field_h, value) in deferred_field_values {
        match value {
            FieldValue::ModuleData(md) => {
                let la_h = b.add_literal_array(&format!("module_la_{module_la_counter}"));
                module_la_counter += 1;
                let requests: Vec<StringHandle> = md
                    .requests
                    .iter()
                    .map(|&sid| get_or_add_string_id(&mut b, &mut string_handles, pool, sid))
                    .collect::<Result<_, _>>()?;
                let records: Vec<ModuleRecordDef> = md
                    .records
                    .iter()
                    .map(|rec| module_record_def(rec, &mut b, &mut string_handles, pool))
                    .collect::<Result<_, _>>()?;
                b.literal_array_add_module_data(la_h, &requests, &records)?;
                b.field_set_value_literalarray(field_h, la_h)?;
            }
            FieldValue::LiteralArrayRef(source_offset) => {
                let index =
                    *file
                        .literal_array_offsets
                        .get(source_offset)
                        .ok_or_else(|| {
                            Error::ModuleData(format!(
                                "scope-names literal array at source offset {source_offset:#x} was not decoded"
                            ))
                        })?;
                let la_h = *literal_handles.get(index as usize).ok_or_else(|| {
                    Error::ModuleData(format!(
                        "scope-names literal array index {index} out of range"
                    ))
                })?;
                b.field_set_value_literalarray(field_h, la_h)?;
            }
            _ => unreachable!("only offset-reference field values are deferred"),
        }
    }

    // All entities now have handles, including forward method/literal refs.
    // Register dependencies AND deferred operand updates; upstream owns the
    // final method-local index ordering, which may differ from the input.
    for (owner, offsets, body) in code_references {
        for (instruction, &byte_offset) in body.bytecodes.iter().zip(&offsets) {
            for (ordinal, (kind, id)) in instruction.entity_operands().into_iter().enumerate() {
                use abcd_isa::EntityKind;
                let unresolved = || {
                    Error::CodeRelocation(format!(
                        "{:?} index {} at byte {byte_offset:#x}",
                        kind, id.0
                    ))
                };
                let offset = *body
                    .entity_offsets
                    .get(&(kind, id.0))
                    .ok_or_else(unresolved)?;
                let target = match kind {
                    EntityKind::StringId => {
                        let sid = *file.entity_map.get(&offset).ok_or_else(unresolved)?;
                        CodeEntity::String(get_or_add_string_id(
                            &mut b,
                            &mut string_handles,
                            pool,
                            sid,
                        )?)
                    }
                    EntityKind::MethodId => CodeEntity::Method(
                        *entities
                            .methods_by_offset
                            .get(&offset)
                            .ok_or_else(unresolved)?,
                    ),
                    EntityKind::LiteralarrayId => {
                        let index = *file
                            .literal_array_offsets
                            .get(&offset)
                            .ok_or_else(unresolved)?;
                        CodeEntity::LiteralArray(
                            *literal_handles.get(index as usize).ok_or_else(unresolved)?,
                        )
                    }
                };
                b.relocate_code_id(owner, byte_offset, ordinal as u32, target)?;
            }
        }
    }

    // --- Deduplicate and finalize ---
    // DeduplicateItems computes a layout pass first: its hash computation
    // reads per-item index ranges that only ComputeLayout populates.
    b.deduplicate();
    let output = b.finalize()?;
    crate::decode(&output).map_err(|e| Error::FinalizeValidation(e.to_string()))?;
    Ok(output)
}

fn validate_annotation_arrays(file: &File) -> Result<(), Error> {
    fn annotations(a: &Annotations) -> impl Iterator<Item = &Annotation> {
        a.compile_time
            .iter()
            .chain(a.runtime.iter())
            .chain(a.compile_time_type.iter())
            .chain(a.runtime_type.iter())
    }
    fn value(v: &AnnotationValue) -> Result<(), Error> {
        match v {
            AnnotationValue::Array { tag, values } => {
                if values.iter().any(|item| {
                    matches!(
                        item,
                        AnnotationValue::I64(_) | AnnotationValue::U64(_) | AnnotationValue::F64(_)
                    )
                }) {
                    return Err(Error::UnsupportedAnnotationArrayType { tag: *tag });
                }
                for item in values {
                    value(item)?;
                }
                Ok(())
            }
            AnnotationValue::Annotation(a) => {
                for e in &a.elements {
                    value(&e.value)?;
                }
                Ok(())
            }
            AnnotationValue::LiteralArray(values) => {
                let _ = values;
                Ok(())
            }
            _ => Ok(()),
        }
    }
    for class in file.classes.values() {
        for ann in annotations(&class.annotations) {
            for e in &ann.elements {
                value(&e.value)?;
            }
        }
        for method in &class.methods {
            for ann in annotations(&method.annotations) {
                for e in &ann.elements {
                    value(&e.value)?;
                }
            }
        }
        for field in &class.fields {
            for ann in annotations(&field.annotations) {
                for e in &ann.elements {
                    value(&e.value)?;
                }
            }
        }
    }
    Ok(())
}

/// Count the literal arrays that annotation encoding will create: exactly
/// one `ann_la_*` builder array per `AnnotationValue::LiteralArray` element,
/// recursing into nested annotations and array elements (both are handled by
/// paths that create such arrays).
///
/// The count determines the builder handle of every model literal array
/// (created after class configuration): `handle(i) = count + i`.
fn count_annotation_literal_arrays(file: &File) -> u32 {
    fn in_value(v: &AnnotationValue) -> u32 {
        match v {
            AnnotationValue::LiteralArray(_) => 1,
            AnnotationValue::Annotation(a) => a.elements.iter().map(|e| in_value(&e.value)).sum(),
            AnnotationValue::Array { values, .. } => values.iter().map(in_value).sum(),
            _ => 0,
        }
    }
    fn in_annotations(a: &Annotations) -> u32 {
        a.compile_time
            .iter()
            .chain(a.runtime.iter())
            .chain(a.compile_time_type.iter())
            .chain(a.runtime_type.iter())
            .flat_map(|ann| ann.elements.iter())
            .map(|e| in_value(&e.value))
            .sum()
    }
    file.classes
        .values()
        .map(|class| {
            in_annotations(&class.annotations)
                + class
                    .methods
                    .iter()
                    .map(|m| in_annotations(&m.annotations))
                    .sum::<u32>()
                + class
                    .fields
                    .iter()
                    .map(|f| in_annotations(&f.annotations))
                    .sum::<u32>()
        })
        .sum()
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
    /// Handle of the first model literal array (= number of
    /// annotation-embedded arrays, which are created first), plus the model
    /// table length. Nested `LiteralValue::LiteralArray` references resolve
    /// to `LiteralArrayHandle(ann_la_base + idx)`.
    ann_la_base: u32,
    literal_array_count: usize,
    pool: &'a StringPool,
}

#[allow(clippy::type_complexity)]
fn encode_annotations_on(
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
    anns: &Annotations,
    target: AnnotationTarget,
) -> Result<(), Error> {
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
            let ann_h = encode_single_annotation(b, ctx, ann)?;
            attach_fn(b, &target, ann_h);
        }
    }
    Ok(())
}

/// Encode one annotation (class reference + elements) into a builder handle.
fn encode_single_annotation(
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
    ann: &Annotation,
) -> Result<AnnotationHandle, Error> {
    let ann_cls = resolve_class_for_ann(b, ctx.class_handles, ctx.pool, ann.class_descriptor)?;

    let elems: Vec<AnnotationElemDefEx> = ann
        .elements
        .iter()
        .map(|e| {
            let name = get_or_add_string_id(b, ctx.string_handles, ctx.pool, e.name)?;
            let (tag, value) = annotation_value_to_raw(&e.value, b, ctx)?;
            Ok(AnnotationElemDefEx { name, tag, value })
        })
        .collect::<Result<_, Error>>()?;

    Ok(b.create_annotation_ex(ann_cls, &elems))
}

fn annotation_value_to_raw(
    val: &AnnotationValue,
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
) -> Result<(u8, AnnotationElemValue), Error> {
    use sys::AnnotationValueType as AVT;

    // Unresolvable entity references (e.g. foreign members, which never
    // enter EntityHandles) must fail loudly — writing Scalar(0) would
    // silently produce a different annotation (audit findings #6/#7).
    let unresolved = |kind: &str, name: StringId, offset: u32| {
        Error::CodeRelocation(format!(
            "annotation {kind} reference '{}' at offset {offset:#x} cannot be resolved",
            ctx.pool.resolve(name).unwrap_or("<unknown>")
        ))
    };

    let raw = match val {
        AnnotationValue::Bool(v) => (AVT::U1 as u8, AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::I8(v) => (AVT::I8 as u8, AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::U8(v) => (AVT::U8 as u8, AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::I16(v) => (AVT::I16 as u8, AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::U16(v) => (AVT::U16 as u8, AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::I32(v) => (AVT::I32 as u8, AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::U32(v) => (AVT::U32 as u8, AnnotationElemValue::Scalar(*v)),
        AnnotationValue::I64(v) => (AVT::I64 as u8, AnnotationElemValue::Scalar64(*v as u64)),
        AnnotationValue::U64(v) => (AVT::U64 as u8, AnnotationElemValue::Scalar64(*v)),
        AnnotationValue::F32(v) => (AVT::F32 as u8, AnnotationElemValue::Scalar(v.to_bits())),
        AnnotationValue::F64(v) => (AVT::F64 as u8, AnnotationElemValue::Scalar64(v.to_bits())),
        AnnotationValue::String(sid) => {
            let h = get_or_add_string_id(b, ctx.string_handles, ctx.pool, *sid)?;
            (AVT::String as u8, AnnotationElemValue::EntityRef(h.0))
        }
        AnnotationValue::Record(sid) => {
            let h = resolve_class_for_ann(b, ctx.class_handles, ctx.pool, *sid)?;
            (AVT::Record as u8, AnnotationElemValue::EntityRef(h.0))
        }
        AnnotationValue::Method { name, offset } => {
            let mh = ctx
                .entities
                .resolve_method(*name, *offset)
                .ok_or_else(|| unresolved("method", *name, *offset))?;
            (AVT::Method as u8, AnnotationElemValue::EntityRef(mh.0))
        }
        AnnotationValue::Enum { name, offset } => {
            let fh = ctx
                .entities
                .resolve_field(*name, *offset)
                .ok_or_else(|| unresolved("enum", *name, *offset))?;
            (AVT::Enum as u8, AnnotationElemValue::EntityRef(fh.0))
        }
        AnnotationValue::Annotation(nested) => {
            let ann_cls =
                resolve_class_for_ann(b, ctx.class_handles, ctx.pool, nested.class_descriptor)?;
            let elems: Vec<AnnotationElemDefEx> = nested
                .elements
                .iter()
                .map(|e| {
                    let name = get_or_add_string_id(b, ctx.string_handles, ctx.pool, e.name)?;
                    let (tag, value) = annotation_value_to_raw(&e.value, b, ctx)?;
                    Ok(AnnotationElemDefEx { name, tag, value })
                })
                .collect::<Result<_, Error>>()?;
            let ann_h = b.create_annotation_ex(ann_cls, &elems);
            (
                AVT::Annotation as u8,
                AnnotationElemValue::EntityRef(ann_h.0),
            )
        }
        AnnotationValue::MethodHandle(mh) => {
            let entity_handle = if mh.handle_type.is_field_op() {
                ctx.entities
                    .resolve_field(mh.entity, mh.entity_offset)
                    .map(|h| h.0)
            } else {
                ctx.entities
                    .resolve_method(mh.entity, mh.entity_offset)
                    .map(|h| h.0)
            }
            .ok_or_else(|| unresolved("method-handle", mh.entity, mh.entity_offset))?;
            let mh_item = b.create_method_handle(mh.handle_type as u8, entity_handle);
            (
                AVT::MethodHandle as u8,
                AnnotationElemValue::EntityRef(mh_item.0),
            )
        }
        AnnotationValue::LiteralArray(values) => {
            let id = format!("ann_la_{}", *ctx.ann_la_counter);
            *ctx.ann_la_counter += 1;
            let la_h = b.add_literal_array(&id);
            for val in values {
                encode_literal_value_simple(
                    b,
                    ctx.string_handles,
                    ctx.pool,
                    la_h,
                    val,
                    ctx.ann_la_base,
                    ctx.literal_array_count,
                )?;
            }
            (
                AVT::LiteralArray as u8,
                AnnotationElemValue::EntityRef(la_h.0),
            )
        }
        AnnotationValue::Void => (AVT::Void as u8, AnnotationElemValue::Scalar(0)),
        AnnotationValue::StringNullptr => {
            (AVT::StringNullptr as u8, AnnotationElemValue::Scalar(0))
        }
        AnnotationValue::Array { tag, values } => {
            let handles: Vec<u32> = values
                .iter()
                .map(|v| annotation_array_elem_to_handle(v, *tag, b, ctx))
                .collect::<Result<_, Error>>()?;
            if is_entity_array_tag(*tag) {
                (*tag, AnnotationElemValue::EntityArray(handles))
            } else {
                (*tag, AnnotationElemValue::Array(handles))
            }
        }
    };
    Ok(raw)
}

/// Returns true if the annotation array tag refers to entity-reference
/// elements. Tag chars follow upstream pandasm::Value::GetArrayTypeAsChar
/// (audit finding #B1): K..U are scalar arrays (K=U1 … T=F32, U=F64),
/// V=String, W=Record, X=Method, Y=Enum, Z=Annotation, @=MethodHandle;
/// '#' (LiteralArray) is also an entity reference.
fn is_entity_array_tag(tag: u8) -> bool {
    use sys::AnnotationValueType as AVT;
    matches!(
        AVT::try_from(tag),
        Ok(AVT::ArrayString
            | AVT::ArrayRecord
            | AVT::ArrayMethod
            | AVT::ArrayEnum
            | AVT::ArrayAnnotation
            | AVT::ArrayMethodHandle
            | AVT::LiteralArray)
    )
}

/// Convert a single annotation array element to a u32 handle/value for the builder.
///
/// `tag` is the enclosing array's element tag, used only for error reporting.
/// Entity elements (Method/Enum/Annotation/MethodHandle/LiteralArray) are
/// resolved to real builder handles; unresolvable references fail instead of
/// writing 0 (audit finding #7).
fn annotation_array_elem_to_handle(
    val: &AnnotationValue,
    tag: u8,
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
) -> Result<u32, Error> {
    let raw = match val {
        AnnotationValue::Bool(v) => *v as u32,
        AnnotationValue::I8(v) => *v as u32,
        AnnotationValue::U8(v) => *v as u32,
        AnnotationValue::I16(v) => *v as u32,
        AnnotationValue::U16(v) => *v as u32,
        AnnotationValue::I32(v) => *v as u32,
        AnnotationValue::U32(v) => *v,
        // The C bridge's array ABI currently accepts only 32-bit elements.
        // Silently truncating these values produces a different annotation;
        // fail explicitly until a 64-bit array ABI is available.
        AnnotationValue::I64(_) | AnnotationValue::U64(_) | AnnotationValue::F64(_) => {
            return Err(Error::UnsupportedAnnotationArrayType { tag });
        }
        AnnotationValue::F32(v) => v.to_bits(),
        AnnotationValue::String(sid) => {
            let h = get_or_add_string_id(b, ctx.string_handles, ctx.pool, *sid)?;
            h.0
        }
        AnnotationValue::Record(sid) => {
            let h = resolve_class_for_ann(b, ctx.class_handles, ctx.pool, *sid)?;
            h.0
        }
        AnnotationValue::Method { name, offset } => {
            ctx.entities
                .resolve_method(*name, *offset)
                .ok_or_else(|| {
                    Error::CodeRelocation(format!(
                        "annotation array method reference '{}' at offset {offset:#x} cannot be resolved",
                        ctx.pool.resolve(*name).unwrap_or("<unknown>")
                    ))
                })?
                .0
        }
        AnnotationValue::Enum { name, offset } => {
            ctx.entities
                .resolve_field(*name, *offset)
                .ok_or_else(|| {
                    Error::CodeRelocation(format!(
                        "annotation array enum reference '{}' at offset {offset:#x} cannot be resolved",
                        ctx.pool.resolve(*name).unwrap_or("<unknown>")
                    ))
                })?
                .0
        }
        AnnotationValue::MethodHandle(mh) => {
            let entity_handle = if mh.handle_type.is_field_op() {
                ctx.entities
                    .resolve_field(mh.entity, mh.entity_offset)
                    .map(|h| h.0)
            } else {
                ctx.entities
                    .resolve_method(mh.entity, mh.entity_offset)
                    .map(|h| h.0)
            }
            .ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "annotation array method-handle reference '{}' at offset {:#x} cannot be resolved",
                    ctx.pool.resolve(mh.entity).unwrap_or("<unknown>"),
                    mh.entity_offset
                ))
            })?;
            b.create_method_handle(mh.handle_type as u8, entity_handle).0
        }
        // Nested annotations and literal arrays encode as entity references;
        // reuse the scalar conversion path.
        AnnotationValue::Annotation(_) | AnnotationValue::LiteralArray(_) => {
            match annotation_value_to_raw(val, b, ctx)? {
                (_, AnnotationElemValue::EntityRef(h)) => h,
                _ => unreachable!("annotation/literal-array values encode as entity refs"),
            }
        }
        AnnotationValue::Void | AnnotationValue::StringNullptr => 0,
        AnnotationValue::Array { .. } => {
            return Err(Error::CodeRelocation(
                "nested annotation arrays are not supported by the builder ABI".into(),
            ));
        }
    };
    Ok(raw)
}

/// Resolve a class descriptor for annotation encoding.
fn resolve_class_for_ann(
    b: &mut Builder,
    class_handles: &mut HashMap<StringId, ClassHandle>,
    pool: &StringPool,
    desc: StringId,
) -> Result<ClassHandle, Error> {
    if let Some(&h) = class_handles.get(&desc) {
        return Ok(h);
    }
    let desc_str = pool.resolve(desc).ok_or_else(|| Error::Malformed {
        field: "string_id",
        context: format!("dangling StringId {desc:?} for annotation class descriptor"),
    })?;
    let h = b.add_foreign_class(desc_str);
    class_handles.insert(desc, h);
    Ok(h)
}

/// Simplified literal value encoding for annotation-embedded literal arrays.
/// Does not resolve method entity offsets (no entity_map available).
///
/// Nested `LiteralValue::LiteralArray` references carry a model table index
/// into `File::literal_arrays`. Model arrays are created after all
/// annotation-embedded ones, so the builder handle is
/// `ann_la_base + idx` (`literal_array_count` bounds-checks `idx`).
fn encode_literal_value_simple(
    b: &mut Builder,
    string_handles: &mut HashMap<StringId, StringHandle>,
    pool: &StringPool,
    la: LiteralArrayHandle,
    val: &LiteralValue,
    ann_la_base: u32,
    literal_array_count: usize,
) -> Result<(), Error> {
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
            let sh = get_or_add_string_id(b, string_handles, pool, *sid)?;
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
            // idx is a model table index into File::literal_arrays, NOT a
            // builder handle: annotation-embedded arrays occupy the low
            // handle slots. Model arrays are created right after them, so
            // the target handle is ann_la_base + idx. Route it through the
            // reference API so the writer stores the array's final file
            // offset.
            if idx.0 as usize >= literal_array_count {
                return Err(Error::CodeRelocation(format!(
                    "nested literal array index {} out of bounds",
                    idx.0
                )));
            }
            let target = LiteralArrayHandle(ann_la_base + idx.0);
            b.literal_array_add_literalarray(la, target);
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
            let sh = get_or_add_string_id(b, string_handles, pool, *sid)?;
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
    Ok(())
}

fn encode_debug_info(
    b: &mut Builder,
    string_handles: &mut HashMap<StringId, StringHandle>,
    pool: &StringPool,
    method_h: MethodHandle,
    dbg: &MethodDebugInfo,
    byte_offsets: &[u32],
    code_len: u32,
) -> Result<(), Error> {
    // Skip if debug info is completely empty (no meaningful content).
    let has_content = !dbg.line_table.is_empty()
        || !dbg.column_table.is_empty()
        || !dbg.local_vars.is_empty()
        || !dbg.params.is_empty()
        || dbg.source_file.is_some()
        || dbg.source_code.is_some();
    if !has_content {
        return Ok(());
    }

    let lnp = b.create_lnp();
    let first_line = dbg.line_table.first().map_or(0, |e| e.line);
    let debug_h = b.create_debug_info(lnp, first_line);

    // Source file / source code
    if let Some(sf) = dbg.source_file {
        let sf_str = pool.resolve(sf).unwrap_or("");
        if !sf_str.is_empty() {
            let sh = get_or_add_string_id(b, string_handles, pool, sf)?;
            b.lnp_emit_set_file(lnp, debug_h, sh);
        }
    }
    if let Some(sc) = dbg.source_code {
        let sc_str = pool.resolve(sc).unwrap_or("");
        if !sc_str.is_empty() {
            let sh = get_or_add_string_id(b, string_handles, pool, sc)?;
            b.lnp_emit_set_source_code(lnp, debug_h, sh);
        }
    }

    // Params (signature not preserved — C++ writer limitation)
    for p in &dbg.params {
        let nh = get_or_add_string_id(b, string_handles, pool, p.name)?;
        b.debug_add_param(debug_h, nh);
    }

    // Line table — emit as (advance_pc, advance_line) deltas.
    // `cur_pc` tracks the LNP program counter across the whole program;
    // the line table, column table, and local variables share one stream.
    let mut cur_pc: u32 = 0;
    let mut prev_line: u32 = first_line;
    for entry in &dbg.line_table {
        let pc = index_to_offset(byte_offsets, entry.index, code_len);
        let pc_delta = pc.saturating_sub(cur_pc);
        let line_delta = entry.line as i32 - prev_line as i32;
        if pc_delta > 0 {
            b.lnp_emit_advance_pc(lnp, debug_h, pc_delta);
            cur_pc = pc;
        }
        if line_delta != 0 {
            b.lnp_emit_advance_line(lnp, debug_h, line_delta);
        }
        prev_line = entry.line;
    }

    // Column table
    let mut prev_col_pc: u32 = 0;
    for entry in &dbg.column_table {
        let pc = index_to_offset(byte_offsets, entry.index, code_len);
        let pc_delta = pc.saturating_sub(prev_col_pc);
        b.lnp_emit_column(lnp, debug_h, pc_delta, entry.column);
        prev_col_pc = pc;
        cur_pc = cur_pc.saturating_add(pc_delta);
    }

    // Local variables — advance the program counter to each scope boundary
    // so start_local/end_local span the variable's live range (the line and
    // column tables above have already moved the pc past zero).
    for lv in &dbg.local_vars {
        let name_h = get_or_add_string_id(b, string_handles, pool, lv.name)?;
        let type_h = get_or_add_string_id(b, string_handles, pool, lv.type_name)?;
        let start_pc = index_to_offset(byte_offsets, lv.start, code_len);
        let start_delta = start_pc.saturating_sub(cur_pc);
        if start_delta > 0 {
            b.lnp_emit_advance_pc(lnp, debug_h, start_delta);
            cur_pc = start_pc;
        }
        let sig_str = pool.resolve(lv.type_signature).unwrap_or("");
        if !sig_str.is_empty() {
            let sig_h = get_or_add_string_id(b, string_handles, pool, lv.type_signature)?;
            b.lnp_emit_start_local_extended(lnp, debug_h, lv.reg_number, name_h, type_h, sig_h);
        } else {
            b.lnp_emit_start_local(lnp, debug_h, lv.reg_number, name_h, type_h);
        }
        let end_pc = index_to_offset(byte_offsets, lv.end, code_len);
        let end_delta = end_pc.saturating_sub(cur_pc);
        if end_delta > 0 {
            b.lnp_emit_advance_pc(lnp, debug_h, end_delta);
            cur_pc = end_pc;
        }
        b.lnp_emit_end_local(lnp, lv.reg_number);
    }

    b.lnp_emit_end(lnp);
    b.method_set_debug_info(method_h, debug_h);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn encode_literal_value(
    b: &mut Builder,
    string_handles: &mut HashMap<StringId, StringHandle>,
    pool: &StringPool,
    la: LiteralArrayHandle,
    val: &LiteralValue,
    entity_map: &HashMap<u32, StringId>,
    entities: &EntityHandles,
    literal_handles: &[LiteralArrayHandle],
) -> Result<(), Error> {
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
            let sh = get_or_add_string_id(b, string_handles, pool, *sid)?;
            b.literal_array_add_raw_string(la, sh);
        }
        // Method references: an unresolvable offset must fail loudly —
        // falling back to writing the source-file offset into the new
        // file's different layout silently corrupts the array (#6).
        LiteralValue::Method(off) => {
            let mh = resolve_method(*off).ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "literal array method reference at offset {off:#x} cannot be resolved"
                ))
            })?;
            b.literal_array_add_u8(la, LiteralTag::Method as u8);
            b.literal_array_add_raw_method(la, mh);
        }
        LiteralValue::GeneratorMethod(off) => {
            let mh = resolve_method(*off).ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "literal array generator-method reference at offset {off:#x} cannot be resolved"
                ))
            })?;
            b.literal_array_add_u8(la, LiteralTag::GeneratorMethod as u8);
            b.literal_array_add_raw_method(la, mh);
        }
        LiteralValue::AsyncGeneratorMethod(off) => {
            let mh = resolve_method(*off).ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "literal array async-generator-method reference at offset {off:#x} cannot be resolved"
                ))
            })?;
            b.literal_array_add_u8(la, LiteralTag::AsyncGeneratorMethod as u8);
            b.literal_array_add_raw_method(la, mh);
        }
        LiteralValue::Getter(off) => {
            let mh = resolve_method(*off).ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "literal array getter reference at offset {off:#x} cannot be resolved"
                ))
            })?;
            b.literal_array_add_u8(la, LiteralTag::Getter as u8);
            b.literal_array_add_raw_method(la, mh);
        }
        LiteralValue::Setter(off) => {
            let mh = resolve_method(*off).ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "literal array setter reference at offset {off:#x} cannot be resolved"
                ))
            })?;
            b.literal_array_add_u8(la, LiteralTag::Setter as u8);
            b.literal_array_add_raw_method(la, mh);
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
            // idx is a model table index into File::literal_arrays, NOT a
            // builder handle: annotation-embedded arrays occupy other handle
            // slots. Resolve through the handle table and route the result
            // through the reference API so the writer stores the array's
            // final file offset.
            let target = literal_handles.get(idx.0 as usize).ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "nested literal array index {} out of bounds",
                    idx.0
                ))
            })?;
            b.literal_array_add_literalarray(la, *target);
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
            let sh = get_or_add_string_id(b, string_handles, pool, *sid)?;
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
    Ok(())
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
) -> Result<StringHandle, Error> {
    if let Some(&h) = string_handles.get(&sid) {
        return Ok(h);
    }
    let s = pool.resolve(sid).ok_or_else(|| Error::Malformed {
        field: "string_id",
        context: format!("dangling StringId {sid:?} in string table"),
    })?;
    let h = b.add_string(s);
    string_handles.insert(sid, h);
    Ok(h)
}

/// Convert a decoded module record into the handle-based builder form,
/// interning its name strings into the output file.
fn module_record_def(
    rec: &ModuleRecord,
    b: &mut Builder,
    string_handles: &mut HashMap<StringId, StringHandle>,
    pool: &StringPool,
) -> Result<ModuleRecordDef, Error> {
    let mut gs =
        |b: &mut Builder, sid: StringId| get_or_add_string_id(b, string_handles, pool, sid);
    let idx = |v: u32| -> Result<u16, Error> {
        u16::try_from(v).map_err(|_| {
            Error::ModuleData(format!(
                "module request index {v} exceeds the vendored u16 slot"
            ))
        })
    };
    Ok(match rec {
        ModuleRecord::RegularImport {
            local_name,
            import_name,
            module_request_idx,
        } => ModuleRecordDef::RegularImport {
            local_name: gs(b, *local_name)?,
            import_name: gs(b, *import_name)?,
            module_request_idx: idx(*module_request_idx)?,
        },
        ModuleRecord::NamespaceImport {
            local_name,
            module_request_idx,
        } => ModuleRecordDef::NamespaceImport {
            local_name: gs(b, *local_name)?,
            module_request_idx: idx(*module_request_idx)?,
        },
        ModuleRecord::LocalExport {
            local_name,
            export_name,
        } => ModuleRecordDef::LocalExport {
            local_name: gs(b, *local_name)?,
            export_name: gs(b, *export_name)?,
        },
        ModuleRecord::IndirectExport {
            export_name,
            import_name,
            module_request_idx,
        } => ModuleRecordDef::IndirectExport {
            export_name: gs(b, *export_name)?,
            import_name: gs(b, *import_name)?,
            module_request_idx: idx(*module_request_idx)?,
        },
        ModuleRecord::StarExport { module_request_idx } => ModuleRecordDef::StarExport {
            module_request_idx: idx(*module_request_idx)?,
        },
    })
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
            param_annotations: ParamAnnotations::default(),
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
