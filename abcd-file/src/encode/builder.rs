//! Handle-based programmatic `.abc` builder wrapping the `abcd-file-sys`
//! C99 writer bridge.

use std::ffi::CString;

use abcd_file_sys as sys;

use crate::error::Error;
use crate::literal::LiteralTag;
use crate::types::{AccessFlags, FunctionKind, SourceLang, Type};

macro_rules! handle_type {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $name(pub(super) u32);

        impl $name {
            /// Raw handle value (index into the builder's tables).
            pub fn as_raw(self) -> u32 {
                self.0
            }
        }
    };
}

/// Convert a Rust UTF-8 string to canonical MUTF-8 (`C0 80` for U+0000,
/// 6-byte CESU-8 surrogate pairs for U+10000+) wrapped in a [`CString`].
fn c_mutf8(s: &str) -> CString {
    let mut bytes = crate::string_pool::mutf8_encode_cow(s).into_owned();
    bytes.push(0);
    // SAFETY: `mutf8_encode_cow` encodes every `\0` as `0xC0 0x80` and never
    // emits a `0x00` byte, so the trailing byte pushed above is the sole NUL.
    unsafe { CString::from_vec_with_nul_unchecked(bytes) }
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
    /// Array of 64-bit scalar values — I64/U64 raw bits or F64::to_bits() (is_array=1).
    Array64(Vec<u64>),
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
        // SAFETY: `abc_builder_new` has no pointer preconditions.
        let raw = unsafe { sys::abc_builder_new() };
        assert!(!raw.is_null(), "abc_builder_new returned null");
        Self { raw }
    }

    fn mutf8_of(&self, s: &str) -> CString {
        c_mutf8(s)
    }

    pub(super) fn mutf8_cstr(raw: &[u8]) -> Result<CString, Error> {
        if raw.iter().any(|&b| b >= 0xF0)
            && let Some(decoded) = crate::string_pool::mutf8_decode_utf8(raw)
        {
            return Ok(c_mutf8(&decoded));
        }
        CString::new(raw.to_vec()).map_err(|_| Error::Malformed {
            field: "string",
            context: "raw MUTF-8 bytes contain an embedded NUL".to_owned(),
        })
    }

    /// Set the API policy before adding items.
    pub fn set_api(&mut self, version: u8, sub_api: &str) {
        let c_sub = self.mutf8_of(sub_api);
        // SAFETY: `self.raw` is a live `AbcBuilder` and `c_sub` is NUL-terminated.
        unsafe { sys::abc_builder_set_api(self.raw, version, c_sub.as_ptr()) };
    }

    /// Select an exact output version using the vendored writer's version
    /// policy. Call before adding items. An unsupported version leaves the
    /// existing selection unchanged.
    pub fn set_file_version(&mut self, version: crate::Version) -> Result<(), Error> {
        // SAFETY: `self.raw` is live and `as_bytes` provides all four version bytes.
        if unsafe { sys::abc_builder_set_file_version(self.raw, version.as_bytes().as_ptr()) } == 0
        {
            return Err(Error::UnsupportedOutputVersion(version));
        }
        Ok(())
    }

    // --- Strings ---

    /// Add a string, returning its handle.
    pub fn add_string(&mut self, s: &str) -> StringHandle {
        let c_str = self.mutf8_of(s);
        // SAFETY: `self.raw` is live and `c_str` is a valid NUL-terminated MUTF-8 string.
        StringHandle(unsafe { sys::abc_builder_add_string(self.raw, c_str.as_ptr()) })
    }

    /// Add a raw MUTF-8 string (e.g. lone-surrogate wire bytes, #30).
    pub fn add_string_mutf8(&mut self, raw: &[u8]) -> Result<StringHandle, Error> {
        let c_str = Self::mutf8_cstr(raw)?;
        // SAFETY: `self.raw` is live and `c_str` is NUL-terminated.
        Ok(StringHandle(unsafe {
            sys::abc_builder_add_string(self.raw, c_str.as_ptr())
        }))
    }

    // --- Classes ---

    /// Add a class with the given descriptor (e.g. `"LMyClass;"`).
    pub fn add_class(&mut self, descriptor: &str) -> ClassHandle {
        let c_desc = self.mutf8_of(descriptor);
        // SAFETY: `self.raw` is live and `c_desc` is NUL-terminated.
        ClassHandle(unsafe { sys::abc_builder_add_class(self.raw, c_desc.as_ptr()) })
    }

    pub(crate) fn add_class_cstr(&mut self, c_desc: &CString) -> ClassHandle {
        // SAFETY: `self.raw` is live and `c_desc` is NUL-terminated.
        ClassHandle(unsafe { sys::abc_builder_add_class(self.raw, c_desc.as_ptr()) })
    }

    /// Add a foreign (external) class.
    pub fn add_foreign_class(&mut self, descriptor: &str) -> ClassHandle {
        let c_desc = self.mutf8_of(descriptor);
        // SAFETY: `self.raw` is live and `c_desc` is NUL-terminated.
        ClassHandle(unsafe { sys::abc_builder_add_foreign_class(self.raw, c_desc.as_ptr()) })
    }

    /// Add a foreign class from raw MUTF-8 descriptor bytes (#30).
    pub fn add_foreign_class_mutf8(&mut self, raw: &[u8]) -> Result<ClassHandle, Error> {
        let c_desc = Self::mutf8_cstr(raw)?;
        // SAFETY: `self.raw` is live and `c_desc` is NUL-terminated.
        Ok(ClassHandle(unsafe {
            sys::abc_builder_add_foreign_class(self.raw, c_desc.as_ptr())
        }))
    }

    pub(crate) fn add_foreign_class_cstr(&mut self, c_desc: &CString) -> ClassHandle {
        // SAFETY: `self.raw` is live and `c_desc` is NUL-terminated.
        ClassHandle(unsafe { sys::abc_builder_add_foreign_class(self.raw, c_desc.as_ptr()) })
    }

    /// Add the global class (`L_GLOBAL;`).
    pub fn add_global_class(&mut self) -> ClassHandle {
        // SAFETY: `self.raw` is a live `AbcBuilder`.
        ClassHandle(unsafe { sys::abc_builder_add_global_class(self.raw) })
    }

    pub fn class_set_access_flags(&mut self, cls: ClassHandle, flags: AccessFlags) {
        // SAFETY: `self.raw` is live; `cls.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_class_set_access_flags(self.raw, cls.0, flags.bits()) };
    }

    pub fn class_set_source_lang(&mut self, cls: ClassHandle, lang: SourceLang) {
        // SAFETY: `self.raw` is live; `cls.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_class_set_source_lang(self.raw, cls.0, lang as u8) };
    }

    pub fn class_set_super_class(&mut self, cls: ClassHandle, super_cls: ClassHandle) {
        // SAFETY: `self.raw` is live; both class handles are bounds-checked in C++.
        unsafe { sys::abc_builder_class_set_super_class(self.raw, cls.0, super_cls.0) };
    }

    pub fn class_add_interface(&mut self, cls: ClassHandle, iface: ClassHandle) {
        // SAFETY: `self.raw` is live; both class handles are bounds-checked in C++.
        unsafe { sys::abc_builder_class_add_interface(self.raw, cls.0, iface.0) };
    }

    pub fn class_set_source_file(&mut self, cls: ClassHandle, file: StringHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
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
        // SAFETY: `self.raw` is live; `ptr` is null when `args` is empty or valid
        // for `args.len()` bytes for the duration of the call.
        ProtoHandle(unsafe {
            sys::abc_builder_create_proto(self.raw, ret_type.as_raw_u8(), ptr, args.len() as u32)
        })
    }

    /// Create a proto with reference type support.
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
        // SAFETY: `self.raw` is live; `ptr` is null when `params` is empty or valid
        // for `params.len()` elements for the duration of the call.
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
    #[expect(
        clippy::too_many_arguments,
        reason = "builder method creation mirrors the C bridge entry point"
    )]
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
        let c_name = self.mutf8_of(name);
        self.class_add_method_cstr(cls, &c_name, proto, flags, code, num_vregs, num_args)
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "builder method creation mirrors the C bridge entry point"
    )]
    pub(crate) fn class_add_method_cstr(
        &mut self,
        cls: ClassHandle,
        c_name: &CString,
        proto: ProtoHandle,
        flags: AccessFlags,
        code: &[u8],
        num_vregs: u32,
        num_args: u32,
    ) -> MethodHandle {
        // SAFETY: `self.raw` is live, `c_name` is NUL-terminated, and `code` is
        // valid for `code.len()` bytes during the call.
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
        let c_name = self.mutf8_of(name);
        self.add_foreign_method_cstr(cls, &c_name, proto, flags)
    }

    pub(crate) fn add_foreign_method_cstr(
        &mut self,
        cls: ClassHandle,
        c_name: &CString,
        proto: ProtoHandle,
        flags: AccessFlags,
    ) -> MethodHandle {
        // SAFETY: `self.raw` is live and `c_name` is NUL-terminated.
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
        // SAFETY: `self.raw` is live; `m.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_method_set_source_lang(self.raw, m.0, lang as u8) };
    }

    pub fn method_set_function_kind(&mut self, m: MethodHandle, kind: FunctionKind) {
        self.method_set_function_kind_raw(m, kind as u8);
    }

    pub(crate) fn method_set_function_kind_raw(&mut self, m: MethodHandle, raw_kind: u8) {
        // SAFETY: `self.raw` is live; `m.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_method_set_function_kind(self.raw, m.0, raw_kind) };
    }

    pub fn method_set_debug_info(&mut self, m: MethodHandle, debug: DebugInfoHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_method_set_debug_info(self.raw, m.0, debug.0) };
    }

    pub fn method_set_code(&mut self, m: MethodHandle, code: CodeHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_method_set_code(self.raw, m.0, code.0) };
    }

    pub fn method_add_param(&mut self, m: MethodHandle, ty: Type) -> ParamHandle {
        // SAFETY: `self.raw` is live; `m.0` is bounds-checked in C++.
        ParamHandle(unsafe { sys::abc_builder_method_add_param(self.raw, m.0, ty.as_raw_u8()) })
    }

    /// Add a typed parameter with reference-type support.
    pub fn method_add_param_ex(
        &mut self,
        m: MethodHandle,
        ty: Type,
        class: Option<ClassHandle>,
    ) -> ParamHandle {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        ParamHandle(unsafe {
            sys::abc_builder_method_add_param_ex(
                self.raw,
                m.0,
                ty.as_raw_u8(),
                class.map_or(0, |h| h.0),
            )
        })
    }

    /// Seal staged param annotations into a `ParamAnnotationsItem`
    /// (`is_runtime`: `false` = compile-time `PARAM_ANNOTATION`, `true` =
    /// runtime `RUNTIME_PARAM_ANNOTATION`). `AbcBuilder` maintains independent
    /// staging buckets for compile-time vs. runtime parameter annotations.
    pub fn method_seal_param_annotations(
        &mut self,
        m: MethodHandle,
        is_runtime: bool,
    ) -> Result<(), Error> {
        // SAFETY: `self.raw` is live; `m.0` is bounds-checked in C++.
        if unsafe {
            sys::abc_builder_method_seal_param_annotations(self.raw, m.0, is_runtime as i32)
        } == 0
        {
            return Err(Error::Malformed {
                field: "param_annotations",
                context: format!(
                    "invalid method handle {} when sealing param annotations",
                    m.0
                ),
            });
        }
        Ok(())
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
        let c_name = self.mutf8_of(name);
        self.class_add_field_cstr(cls, &c_name, ty, flags)
    }

    pub(crate) fn class_add_field_cstr(
        &mut self,
        cls: ClassHandle,
        c_name: &CString,
        ty: Type,
        flags: AccessFlags,
    ) -> FieldHandle {
        // SAFETY: `self.raw` is live and `c_name` is NUL-terminated.
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
        let c_name = self.mutf8_of(name);
        self.class_add_field_ex_cstr(cls, &c_name, ty, ref_class, flags)
    }

    pub(crate) fn class_add_field_ex_cstr(
        &mut self,
        cls: ClassHandle,
        c_name: &CString,
        ty: Type,
        ref_class: ClassHandle,
        flags: AccessFlags,
    ) -> FieldHandle {
        // SAFETY: `self.raw` is live and `c_name` is NUL-terminated.
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
        let c_name = self.mutf8_of(name);
        self.add_foreign_field_cstr(cls, &c_name, ty)
    }

    pub(crate) fn add_foreign_field_cstr(
        &mut self,
        cls: ClassHandle,
        c_name: &CString,
        ty: Type,
    ) -> FieldHandle {
        // SAFETY: `self.raw` is live and `c_name` is NUL-terminated.
        FieldHandle(unsafe {
            sys::abc_builder_add_foreign_field(self.raw, cls.0, c_name.as_ptr(), ty.as_raw_u8())
        })
    }

    pub fn field_set_value_i32(&mut self, f: FieldHandle, value: i32) {
        // SAFETY: `self.raw` is live; `f.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_field_set_value_i32(self.raw, f.0, value) };
    }

    pub fn field_set_value_i64(&mut self, f: FieldHandle, value: i64) {
        // SAFETY: `self.raw` is live; `f.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_field_set_value_i64(self.raw, f.0, value) };
    }

    pub fn field_set_value_f32(&mut self, f: FieldHandle, value: f32) {
        // SAFETY: `self.raw` is live; `f.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_field_set_value_f32(self.raw, f.0, value) };
    }

    pub fn field_set_value_f64(&mut self, f: FieldHandle, value: f64) {
        // SAFETY: `self.raw` is live; `f.0` is bounds-checked in C++.
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

    /// Set a field's initial value to a string item reference.
    ///
    /// Emits `ScalarValueItem` `Type::ID` over `StringItem`, so the writer
    /// stores the string item's layout offset inline (`FieldTag::VALUE` + u32)
    /// and relocates it automatically (`--merge-abc` `jsonFileContent`).
    pub fn field_set_value_string(&mut self, f: FieldHandle, s: StringHandle) -> Result<(), Error> {
        // SAFETY: the builder is live; the bridge validates both handles.
        if unsafe { sys::abc_builder_field_set_value_string(self.raw, f.0, s.0) } != 0 {
            return Err(Error::ModuleData(
                "field_set_value_string: invalid field or string handle".into(),
            ));
        }
        Ok(())
    }

    // --- Code ---

    /// Create a standalone code item.
    pub fn create_code(&mut self, insns: &[u8], num_vregs: u32, num_args: u32) -> CodeHandle {
        // SAFETY: `self.raw` is live and `insns` is valid for `insns.len()` bytes.
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
        // SAFETY: `self.raw` is live and `ffi_catches` is valid for `ffi_catches.len()` items.
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
        let c_id = self.mutf8_of(id);
        // SAFETY: `self.raw` is live and `c_id` is NUL-terminated.
        LiteralArrayHandle(unsafe { sys::abc_builder_add_literal_array(self.raw, c_id.as_ptr()) })
    }

    /// Append a raw one-byte item. Combine with a preceding tag item (e.g.
    /// `literal_array_add_u8(la, LiteralTag::Accessor as u8)`) to form a
    /// complete literal.
    pub fn literal_array_add_u8(&mut self, la: LiteralArrayHandle, val: u8) {
        // SAFETY: `self.raw` is live; `la.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_literal_array_add_u8(self.raw, la.0, val) };
    }

    /// Append a raw two-byte item; see [`Self::literal_array_add_u8`].
    pub fn literal_array_add_u16(&mut self, la: LiteralArrayHandle, val: u16) {
        // SAFETY: `self.raw` is live; `la.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_literal_array_add_u16(self.raw, la.0, val) };
    }

    /// Append a raw four-byte item; see [`Self::literal_array_add_u8`].
    pub fn literal_array_add_u32(&mut self, la: LiteralArrayHandle, val: u32) {
        // SAFETY: `self.raw` is live; `la.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_literal_array_add_u32(self.raw, la.0, val) };
    }

    /// Append a raw eight-byte item; see [`Self::literal_array_add_u8`].
    pub fn literal_array_add_u64(&mut self, la: LiteralArrayHandle, val: u64) {
        // SAFETY: `self.raw` is live; `la.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_literal_array_add_u64(self.raw, la.0, val) };
    }

    /// Append a complete `BOOL` literal (`[tag][value]` pair).
    pub fn literal_array_add_bool(&mut self, la: LiteralArrayHandle, val: bool) {
        self.literal_array_add_u8(la, LiteralTag::Bool as u8);
        self.literal_array_add_raw_bool(la, val);
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

    pub(crate) fn literal_array_add_raw_bool(&mut self, la: LiteralArrayHandle, val: bool) {
        // SAFETY: `self.raw` is live; `la.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_literal_array_add_bool(self.raw, la.0, val as u8) };
    }

    pub(crate) fn literal_array_add_raw_string(&mut self, la: LiteralArrayHandle, s: StringHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_literal_array_add_string(self.raw, la.0, s.0) };
    }

    pub(crate) fn literal_array_add_raw_method(&mut self, la: LiteralArrayHandle, m: MethodHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_literal_array_add_method(self.raw, la.0, m.0) };
    }

    pub(crate) fn literal_array_add_raw_literalarray(
        &mut self,
        la: LiteralArrayHandle,
        ref_la: LiteralArrayHandle,
    ) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
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

    /// Stage a module-request-phase blob: one raw u8 lazy flag per module
    /// request after the u32 item-count header the vendored writer emits
    /// itself. UNtagged — matches the vendored runtime reader
    /// (`ModuleLazyImportFlagAccessor`); do not add LiteralTag bytes.
    pub fn literal_array_add_module_request_phase(
        &mut self,
        la: LiteralArrayHandle,
        flags: &[u8],
    ) -> Result<(), Error> {
        // SAFETY: the builder is live; the slice outlives the call.
        let rc = unsafe {
            sys::abc_builder_literal_array_add_module_request_phase(
                self.raw,
                la.0,
                flags.as_ptr(),
                flags.len() as u32,
            )
        };
        if rc != 0 {
            return Err(Error::ModuleData(format!(
                "module-request-phase blob staging rejected ({flags} flags)",
                flags = flags.len()
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
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        MethodHandleItemHandle(unsafe {
            sys::abc_builder_create_method_handle(self.raw, handle_type, entity_handle)
        })
    }

    // --- Debug info ---

    /// Create a line number program.
    pub fn create_lnp(&mut self) -> LnpHandle {
        // SAFETY: `self.raw` is a live `AbcBuilder`.
        LnpHandle(unsafe { sys::abc_builder_create_lnp(self.raw) })
    }

    pub fn lnp_emit_end(&mut self, lnp: LnpHandle) {
        // SAFETY: `self.raw` is live; `lnp.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_lnp_emit_end(self.raw, lnp.0) };
    }

    pub fn lnp_emit_advance_pc(&mut self, lnp: LnpHandle, debug: DebugInfoHandle, value: u32) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_lnp_emit_advance_pc(self.raw, lnp.0, debug.0, value) };
    }

    pub fn lnp_emit_advance_line(&mut self, lnp: LnpHandle, debug: DebugInfoHandle, value: i32) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_lnp_emit_advance_line(self.raw, lnp.0, debug.0, value) };
    }

    /// Emit a DWARF special opcode (or `ADVANCE_PC` + `ADVANCE_LINE` +
    /// `EmitSpecialOpcode(0, 0)` fallback when the delta exceeds the compact
    /// single-byte range), recording a `(pc, line)` row in the line table.
    pub fn lnp_emit_special_opcode(
        &mut self,
        lnp: LnpHandle,
        debug: DebugInfoHandle,
        pc_inc: u32,
        line_inc: i32,
    ) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe {
            sys::abc_builder_lnp_emit_special_opcode(self.raw, lnp.0, debug.0, pc_inc, line_inc);
        }
    }

    pub fn lnp_emit_column(
        &mut self,
        lnp: LnpHandle,
        debug: DebugInfoHandle,
        pc_inc: u32,
        column: u32,
    ) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
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
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
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
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
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
        // SAFETY: `self.raw` is live; `lnp.0` is bounds-checked in C++.
        unsafe { sys::abc_builder_lnp_emit_end_local(self.raw, lnp.0, reg) };
    }

    pub fn lnp_emit_set_file(
        &mut self,
        lnp: LnpHandle,
        debug: DebugInfoHandle,
        source_file: StringHandle,
    ) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_lnp_emit_set_file(self.raw, lnp.0, debug.0, source_file.0) };
    }

    pub fn lnp_emit_set_source_code(
        &mut self,
        lnp: LnpHandle,
        debug: DebugInfoHandle,
        source_code: StringHandle,
    ) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe {
            sys::abc_builder_lnp_emit_set_source_code(self.raw, lnp.0, debug.0, source_code.0);
        }
    }

    /// Create a debug info item.
    pub fn create_debug_info(&mut self, lnp: LnpHandle, line_number: u32) -> DebugInfoHandle {
        // SAFETY: `self.raw` is live; `lnp.0` is bounds-checked in C++.
        DebugInfoHandle(unsafe { sys::abc_builder_create_debug_info(self.raw, lnp.0, line_number) })
    }

    /// Add a parameter name to a debug info item.
    pub fn debug_add_param(&mut self, debug: DebugInfoHandle, name: StringHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
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
        // SAFETY: `self.raw` is live and `ffi_elems` is valid for `ffi_elems.len()` items.
        AnnotationHandle(unsafe {
            sys::abc_builder_create_annotation(
                self.raw,
                cls.0,
                ffi_elems.as_ptr(),
                ffi_elems.len() as u32,
            )
        })
    }

    /// Create an annotation with extended elements (array and 64-bit support).
    pub fn create_annotation_ex(
        &mut self,
        cls: ClassHandle,
        elements: &[AnnotationElemDefEx],
    ) -> AnnotationHandle {
        let mut widened_arrays: Vec<Vec<u64>> = Vec::new();
        let mut ffi_elems: Vec<sys::AbcAnnotationElemDefEx> = Vec::with_capacity(elements.len());
        for e in elements {
            let elem = match &e.value {
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
                AnnotationElemValue::Array(arr) => {
                    let widened: Vec<u64> = arr.iter().map(|&x| u64::from(x)).collect();
                    let ptr = widened.as_ptr();
                    let len = widened.len() as u32;
                    widened_arrays.push(widened);
                    sys::AbcAnnotationElemDefEx {
                        name_string_handle: e.name.0,
                        tag: e.tag as std::os::raw::c_char,
                        is_array: 1,
                        scalar_value: 0,
                        scalar_value_64: 0,
                        array_values: ptr,
                        array_count: len,
                    }
                }
                AnnotationElemValue::Array64(arr) => sys::AbcAnnotationElemDefEx {
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
                AnnotationElemValue::EntityArray(arr) => {
                    let widened: Vec<u64> = arr.iter().map(|&x| u64::from(x)).collect();
                    let ptr = widened.as_ptr();
                    let len = widened.len() as u32;
                    widened_arrays.push(widened);
                    sys::AbcAnnotationElemDefEx {
                        name_string_handle: e.name.0,
                        tag: e.tag as std::os::raw::c_char,
                        is_array: 4,
                        scalar_value: 0,
                        scalar_value_64: 0,
                        array_values: ptr,
                        array_count: len,
                    }
                }
            };
            ffi_elems.push(elem);
        }
        // SAFETY: `self.raw` is live; `ffi_elems`, `widened_arrays`, and `elements`
        // all remain alive until after `abc_builder_create_annotation_ex` returns.
        let handle = AnnotationHandle(unsafe {
            sys::abc_builder_create_annotation_ex(
                self.raw,
                cls.0,
                ffi_elems.as_ptr(),
                ffi_elems.len() as u32,
            )
        });
        drop(widened_arrays);
        handle
    }

    // Annotation attachment helpers.
    // Note: upstream OpenHarmony `ItemContainer` (`ClassItem`, `MethodItem`,
    // `FieldItem`) stores a single unified `annotations_` vector emitted under
    // the `ANNOTATION` tag, so the runtime/type convenience methods below fold
    // into that list on serialization.

    /// Attach an annotation to a class (`ClassTag::ANNOTATION`).
    pub fn class_add_annotation(&mut self, cls: ClassHandle, ann: AnnotationHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_class_add_annotation(self.raw, cls.0, ann.0) };
    }
    /// Attach a runtime annotation to a class (folded into `ClassItem::AddAnnotation`
    /// by the vendored OpenHarmony `ItemContainer` writer).
    pub fn class_add_runtime_annotation(&mut self, cls: ClassHandle, ann: AnnotationHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_class_add_runtime_annotation(self.raw, cls.0, ann.0) };
    }
    /// Attach a type annotation to a class (folded into `ClassItem::AddAnnotation`
    /// by the vendored OpenHarmony `ItemContainer` writer).
    pub fn class_add_type_annotation(&mut self, cls: ClassHandle, ann: AnnotationHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_class_add_type_annotation(self.raw, cls.0, ann.0) };
    }
    /// Attach a runtime type annotation to a class (folded into
    /// `ClassItem::AddAnnotation` by the vendored OpenHarmony `ItemContainer` writer).
    pub fn class_add_runtime_type_annotation(&mut self, cls: ClassHandle, ann: AnnotationHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_class_add_runtime_type_annotation(self.raw, cls.0, ann.0) };
    }

    /// Attach an annotation to a method (`MethodTag::ANNOTATION`).
    pub fn method_add_annotation(&mut self, m: MethodHandle, ann: AnnotationHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_method_add_annotation(self.raw, m.0, ann.0) };
    }
    /// Attach a runtime annotation to a method (folded into `MethodItem::AddAnnotation`
    /// by the vendored OpenHarmony `ItemContainer` writer).
    pub fn method_add_runtime_annotation(&mut self, m: MethodHandle, ann: AnnotationHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_method_add_runtime_annotation(self.raw, m.0, ann.0) };
    }
    /// Attach a type annotation to a method (folded into `MethodItem::AddAnnotation`
    /// by the vendored OpenHarmony `ItemContainer` writer).
    pub fn method_add_type_annotation(&mut self, m: MethodHandle, ann: AnnotationHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_method_add_type_annotation(self.raw, m.0, ann.0) };
    }
    /// Attach a runtime type annotation to a method (folded into
    /// `MethodItem::AddAnnotation` by the vendored OpenHarmony `ItemContainer` writer).
    pub fn method_add_runtime_type_annotation(&mut self, m: MethodHandle, ann: AnnotationHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_method_add_runtime_type_annotation(self.raw, m.0, ann.0) };
    }

    /// Stage an annotation on a method parameter; call
    /// [`Self::method_seal_param_annotations`] to emit the table.
    pub fn method_param_add_annotation(
        &mut self,
        m: MethodHandle,
        param: ParamHandle,
        ann: AnnotationHandle,
    ) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_method_param_add_annotation(self.raw, m.0, param.0, ann.0) };
    }
    /// Stage a runtime parameter annotation (shares `MethodParamItem`'s staged
    /// annotation vector; select retention via [`Self::method_seal_param_annotations`]).
    pub fn method_param_add_runtime_annotation(
        &mut self,
        m: MethodHandle,
        param: ParamHandle,
        ann: AnnotationHandle,
    ) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe {
            sys::abc_builder_method_param_add_runtime_annotation(self.raw, m.0, param.0, ann.0);
        }
    }
    /// Stage a type parameter annotation (shares `MethodParamItem`'s staged
    /// annotation vector; select retention via [`Self::method_seal_param_annotations`]).
    pub fn method_param_add_type_annotation(
        &mut self,
        m: MethodHandle,
        param: ParamHandle,
        ann: AnnotationHandle,
    ) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe {
            sys::abc_builder_method_param_add_type_annotation(self.raw, m.0, param.0, ann.0);
        }
    }
    /// Stage a runtime type parameter annotation (shares `MethodParamItem`'s
    /// staged annotation vector; select retention via [`Self::method_seal_param_annotations`]).
    pub fn method_param_add_runtime_type_annotation(
        &mut self,
        m: MethodHandle,
        param: ParamHandle,
        ann: AnnotationHandle,
    ) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe {
            sys::abc_builder_method_param_add_runtime_type_annotation(
                self.raw, m.0, param.0, ann.0,
            );
        }
    }

    /// Attach an annotation to a field (`FieldTag::ANNOTATION`).
    pub fn field_add_annotation(&mut self, f: FieldHandle, ann: AnnotationHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_field_add_annotation(self.raw, f.0, ann.0) };
    }
    /// Attach a runtime annotation to a field (folded into `FieldItem::AddAnnotation`
    /// by the vendored OpenHarmony `ItemContainer` writer).
    pub fn field_add_runtime_annotation(&mut self, f: FieldHandle, ann: AnnotationHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_field_add_runtime_annotation(self.raw, f.0, ann.0) };
    }
    /// Attach a type annotation to a field (folded into `FieldItem::AddAnnotation`
    /// by the vendored OpenHarmony `ItemContainer` writer).
    pub fn field_add_type_annotation(&mut self, f: FieldHandle, ann: AnnotationHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_field_add_type_annotation(self.raw, f.0, ann.0) };
    }
    /// Attach a runtime type annotation to a field (folded into
    /// `FieldItem::AddAnnotation` by the vendored OpenHarmony `ItemContainer` writer).
    pub fn field_add_runtime_type_annotation(&mut self, f: FieldHandle, ann: AnnotationHandle) {
        // SAFETY: `self.raw` is live; handles are bounds-checked in C++.
        unsafe { sys::abc_builder_field_add_runtime_type_annotation(self.raw, f.0, ann.0) };
    }

    // --- Deduplication ---

    pub fn deduplicate(&mut self) {
        // SAFETY: `self.raw` is a live `AbcBuilder`.
        unsafe { sys::abc_builder_deduplicate(self.raw) };
    }

    pub fn deduplicate_code_and_debug_info(&mut self) {
        // SAFETY: `self.raw` is a live `AbcBuilder`.
        unsafe { sys::abc_builder_deduplicate_code_and_debug_info(self.raw) };
    }

    pub fn deduplicate_annotations(&mut self) {
        // SAFETY: `self.raw` is a live `AbcBuilder`.
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

#[cfg(test)]
mod tests {
    use super::c_mutf8;

    #[test]
    fn c_mutf8_encodes_nul_and_astral_without_panicking() {
        let cs = c_mutf8("a\0\u{1F600}z");
        assert_eq!(
            cs.as_bytes(),
            &[b'a', 0xC0, 0x80, 0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80, b'z']
        );
    }
}
