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

    fn mutf8_cstr(raw: &[u8]) -> Result<CString, Error> {
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
    /// runtime `RUNTIME_PARAM_ANNOTATION`). The vendored `MethodParamItem`
    /// keeps a single annotation vector per param; sealing snapshots whatever
    /// is staged at that moment.
    pub fn method_seal_param_annotations(&mut self, m: MethodHandle, is_runtime: bool) {
        // SAFETY: `self.raw` is live; `m.0` is bounds-checked in C++.
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

// ---------------------------------------------------------------------------
// High-level encode
// ---------------------------------------------------------------------------

use crate::{StringId, StringPool};

/// Configuration options for [`encode_with_options`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct EncodeOptions {
    /// When `true`, run [`crate::inspect_summary`] (`verify = true`) over the
    /// finalized `.abc` bytes before returning them, mapping any failure to
    /// [`Error::FinalizeValidation`]. Defaults to `false`.
    pub verify: bool,
}

/// Handles of encoded methods/fields, resolvable from decoded reference
/// payloads.
///
/// References inside a decoded file carry entity offsets (method/field item
/// offsets) or interned names. Names are not unique — two classes routinely
/// define a method of the same name — so a non-zero offset resolves solely
/// through the offset map, and the name map only serves hand-built models
/// whose references carry offset `0`.
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
    /// identity; the name map is ONLY consulted when `offset == 0`
    /// (hand-built models).
    fn resolve_method(&self, name: StringId, offset: u32) -> Option<MethodHandle> {
        if offset != 0 {
            return self.methods_by_offset.get(&offset).copied();
        }
        self.methods_by_name.get(&name).copied()
    }

    /// Resolve a field reference (see [`Self::resolve_method`]).
    fn resolve_field(&self, name: StringId, offset: u32) -> Option<FieldHandle> {
        if offset != 0 {
            return self.fields_by_offset.get(&offset).copied();
        }
        self.fields_by_name.get(&name).copied()
    }
}

/// Encode a decoded [`File`] back to ABC bytes using [`EncodeOptions::default`].
///
/// Source entity operands are resolved through each method body's index map
/// and relocated after the upstream writer assigns new indices. Pass
/// [`EncodeOptions { verify: true }`](EncodeOptions) to [`encode_with_options`]
/// when post-finalize readback verification is desired.
///
/// Note: `ParamInfo::signature` is derived from method prototypes on decode and
/// is not stored separately in `DebugInfoItem`.
pub fn encode(file: &File) -> Result<Vec<u8>, Error> {
    encode_with_options(file, EncodeOptions::default())
}

/// Encode a decoded [`File`] back to ABC bytes with explicit [`EncodeOptions`].
pub fn encode_with_options(file: &File, options: EncodeOptions) -> Result<Vec<u8>, Error> {
    if file.file_type != crate::FileType::Dynamic {
        return Err(Error::Malformed {
            field: "file_type",
            context: format!(
                "cannot encode {:?} file as dynamic ArkTS/JS bytecode",
                file.file_type
            ),
        });
    }
    validate_annotation_arrays(file)?;
    validate_literal_array_graph(&file.literal_arrays)?;
    let mut b = Builder::new();
    b.set_file_version(file.version)?;
    let pool = &file.strings;

    let rcstr = |id: StringId| -> Result<CString, Error> {
        let bytes = pool.to_mutf8_bytes(id).ok_or_else(|| Error::Malformed {
            field: "string_id",
            context: format!("dangling StringId {id:?} in file"),
        })?;
        Builder::mutf8_cstr(&bytes)
    };

    // Dense `StringId::index() -> Option<StringHandle>` table (zero hashing).
    let mut string_handles: Vec<Option<StringHandle>> = vec![None; pool.len()];

    // --- Create classes (foreign first, then normal) ---
    let mut class_handles: HashMap<StringId, ClassHandle> = HashMap::new();
    let mut entities = EntityHandles::default();
    let mut code_references = Vec::new();
    let mut deferred_field_values: Vec<(FieldHandle, &FieldValue)> = Vec::new();
    let mut deferred_ann_las: Vec<(LiteralArrayHandle, Vec<LiteralValue>)> = Vec::new();
    let mut ann_la_counter: u32 = 0;
    let ann_la_base = count_annotation_literal_arrays(file);

    // First pass: foreign classes
    for (&desc, cls) in &file.classes {
        if cls.is_external {
            let h = b.add_foreign_class_cstr(&rcstr(desc)?);
            class_handles.insert(desc, h);
        }
    }
    // Second pass: normal classes
    for (&desc, cls) in &file.classes {
        if !cls.is_external {
            let h = if pool.as_str(desc) == Some("L_GLOBAL;") {
                b.add_global_class()
            } else {
                b.add_class_cstr(&rcstr(desc)?)
            };
            class_handles.insert(desc, h);
        }
    }

    let resolve_class_id = |b: &mut Builder,
                            map: &mut HashMap<StringId, ClassHandle>,
                            pool: &StringPool,
                            desc: StringId|
     -> Result<ClassHandle, Error> {
        if let Some(&h) = map.get(&desc) {
            return Ok(h);
        }
        let bytes = pool.to_mutf8_bytes(desc).ok_or_else(|| Error::Malformed {
            field: "string_id",
            context: format!("dangling StringId {desc:?} for class descriptor"),
        })?;
        let h = b.add_foreign_class_cstr(&Builder::mutf8_cstr(&bytes)?);
        map.insert(desc, h);
        Ok(h)
    };

    // --- Configure each class ---
    for (&desc, cls) in &file.classes {
        let cls_h = class_handles
            .get(&desc)
            .copied()
            .ok_or_else(|| Error::Malformed {
                field: "class_descriptor",
                context: format!("missing class handle for {desc:?}"),
            })?;

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
            let method_name_cstr = rcstr(method.name)?;
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
                b.add_foreign_method_cstr(cls_h, &method_name_cstr, proto, method.access_flags)
            } else {
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

                let inline_code = if has_try_blocks { &[][..] } else { &code_bytes };
                let m_h = b.class_add_method_cstr(
                    cls_h,
                    &method_name_cstr,
                    proto,
                    method.access_flags,
                    inline_code,
                    num_vregs,
                    num_args,
                );

                // Try blocks (strictly validated against instruction indices).
                if let Some(ref body) = method.body
                    && !body.try_blocks.is_empty()
                {
                    let code_byte_len = code_bytes.len() as u32;
                    let method_label = pool.resolve(method.name).unwrap_or("<method>");
                    let checked_pc = |idx: u32, field: &'static str| -> Result<u32, Error> {
                        let i = idx as usize;
                        if let Some(&off) = byte_offsets.get(i) {
                            Ok(off)
                        } else if i == byte_offsets.len() {
                            Ok(code_byte_len)
                        } else {
                            Err(Error::Malformed {
                                field,
                                context: format!(
                                    "method {method_label}: instruction index {idx} out of bounds (insn count {})",
                                    byte_offsets.len()
                                ),
                            })
                        }
                    };
                    let code_h = b.create_code(&code_bytes, num_vregs, num_args);
                    for tb in &body.try_blocks {
                        let tb_end =
                            tb.start
                                .checked_add(tb.len)
                                .ok_or_else(|| Error::Malformed {
                                    field: "try_block",
                                    context: format!("method {method_label}: try span overflow"),
                                })?;
                        let start_pc = checked_pc(tb.start, "try_block")?;
                        let end_pc = checked_pc(tb_end, "try_block")?;
                        let catches: Vec<CatchBlockDef> = tb
                            .catches
                            .iter()
                            .map(|cb| {
                                let type_class = if cb.type_idx == u32::MAX {
                                    None
                                } else {
                                    let desc_sid = file.resolve_entity(cb.type_idx).ok_or_else(
                                        || {
                                            Error::CodeRelocation(format!(
                                                "method {method_label}: catch type offset {:#x} cannot be resolved",
                                                cb.type_idx
                                            ))
                                        },
                                    )?;
                                    Some(resolve_class_id(
                                        &mut b,
                                        &mut class_handles,
                                        pool,
                                        desc_sid,
                                    )?)
                                };
                                let cb_end = cb.handler.checked_add(cb.len).ok_or_else(|| {
                                    Error::Malformed {
                                        field: "catch_block",
                                        context: format!(
                                            "method {method_label}: catch span overflow"
                                        ),
                                    }
                                })?;
                                let handler_pc = checked_pc(cb.handler, "catch_block")?;
                                let handler_end_pc = checked_pc(cb_end, "catch_block")?;
                                Ok(CatchBlockDef {
                                    type_class,
                                    handler_pc,
                                    code_size: handler_end_pc.saturating_sub(handler_pc),
                                })
                            })
                            .collect::<Result<_, Error>>()?;
                        b.code_add_try_block(
                            code_h,
                            start_pc,
                            end_pc.saturating_sub(start_pc),
                            &catches,
                        );
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
            let raw_hi = ((method.access_flags.bits() >> 8) & 0xFF) as u8;
            let sendable = sys::FunctionKind_SENDABLE_FUNCTION;
            let raw_kind = if (raw_hi & !0x07) == sendable {
                let base = raw_hi & 0x07;
                if (method.function_kind == FunctionKind::SendableFunction
                    && base == sys::FunctionKind_FUNCTION)
                    || (base != 0
                        && base != sys::FunctionKind_CONCURRENT_FUNCTION
                        && (method.function_kind as u8) == base)
                {
                    raw_hi
                } else {
                    method.function_kind as u8
                }
            } else {
                method.function_kind as u8
            };
            b.method_set_function_kind_raw(method_h, raw_kind);

            entities.insert_method(method, method_h);

            // Method annotations
            {
                let synced_annotations;
                let annotations = match method.body.as_ref().and_then(|b| b.ic_size) {
                    Some(ic_size) => {
                        synced_annotations =
                            sync_slot_number_annotation(&method.annotations, pool, ic_size);
                        &synced_annotations
                    }
                    None => &method.annotations,
                };
                let mut ctx = AnnotationEncodeCtx {
                    string_handles: &mut string_handles,
                    class_handles: &mut class_handles,
                    entities: &entities,
                    ann_la_counter: &mut ann_la_counter,
                    deferred_ann_las: &mut deferred_ann_las,
                    pool,
                };
                encode_annotations_on(
                    &mut b,
                    &mut ctx,
                    annotations,
                    AnnotationTarget::Method(method_h),
                )?;
            }

            // --- Parameter annotations ---
            let pa = &method.param_annotations;
            let has_compile = pa.compile_time.iter().any(|v| !v.is_empty());
            let has_runtime = pa.runtime.iter().any(|v| !v.is_empty());
            if !method.is_external && (has_compile || has_runtime) {
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
                    deferred_ann_las: &mut deferred_ann_las,
                    pool,
                };
                for (idx, param_h) in param_handles.iter().enumerate() {
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
            let field_name_cstr = rcstr(field.name)?;
            let ty = field.field_type;
            let field_h = if field.is_external {
                b.add_foreign_field_cstr(cls_h, &field_name_cstr, ty)
            } else if let Type::Reference(d) = ty {
                let ref_cls = resolve_class_id(&mut b, &mut class_handles, pool, d)?;
                b.class_add_field_ex_cstr(cls_h, &field_name_cstr, ty, ref_cls, field.access_flags)
            } else {
                b.class_add_field_cstr(cls_h, &field_name_cstr, ty, field.access_flags)
            };

            entities.insert_field(field, field_h);

            match &field.initial_value {
                Some(FieldValue::I32(v)) => b.field_set_value_i32(field_h, *v),
                Some(FieldValue::I64(v)) => b.field_set_value_i64(field_h, *v),
                Some(FieldValue::F32(v)) => b.field_set_value_f32(field_h, *v),
                Some(FieldValue::F64(v)) => b.field_set_value_f64(field_h, *v),
                Some(FieldValue::JsonFileContent { content, .. }) => {
                    let sh = get_or_add_string_id(&mut b, &mut string_handles, pool, *content)?;
                    b.field_set_value_string(field_h, sh)?;
                }
                Some(
                    fv @ (FieldValue::ModuleData(_)
                    | FieldValue::LiteralArrayRef(_)
                    | FieldValue::ModuleRequestPhase(_)),
                ) => deferred_field_values.push((field_h, fv)),
                None => {}
            }

            // Field annotations
            {
                let mut ctx = AnnotationEncodeCtx {
                    string_handles: &mut string_handles,
                    class_handles: &mut class_handles,
                    entities: &entities,
                    ann_la_counter: &mut ann_la_counter,
                    deferred_ann_las: &mut deferred_ann_las,
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
                deferred_ann_las: &mut deferred_ann_las,
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
    let literal_handles: Vec<_> = (0..file.literal_arrays.len())
        .map(|index| b.add_literal_array(&index.to_string()))
        .collect();
    {
        let mut lit_ctx = LiteralEncodeCtx {
            string_handles: &mut string_handles,
            pool,
            entity_map: &file.entity_map,
            entities: &entities,
            literal_handles: &literal_handles,
        };
        for (la_h, values) in &deferred_ann_las {
            for val in values {
                encode_literal_value(&mut b, &mut lit_ctx, *la_h, val)?;
            }
        }
        for (i, (la, &la_h)) in file.literal_arrays.iter().zip(&literal_handles).enumerate() {
            debug_assert_eq!(
                la_h.as_raw(),
                ann_la_base + i as u32,
                "model literal-array handles must follow annotation-embedded ones"
            );
            for val in &la.values {
                encode_literal_value(&mut b, &mut lit_ctx, la_h, val)?;
            }
        }
    }

    // --- Module-record blobs and scope-names field references ---
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
            FieldValue::ModuleRequestPhase(phase) => {
                let la_h = b.add_literal_array(&format!("phase_la_{module_la_counter}"));
                module_la_counter += 1;
                b.literal_array_add_module_request_phase(la_h, &phase.flags)?;
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

    // Relocate bytecode entity operands.
    for (owner, offsets, body) in code_references {
        for (instruction, &byte_offset) in body.bytecodes.iter().zip(&offsets) {
            let (ops, len) = instruction.entity_operands_inline();
            for (ordinal, &(kind, id)) in ops[..len].iter().enumerate() {
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

    b.deduplicate();
    let output = b.finalize()?;
    if options.verify {
        crate::inspect_summary(&output, true)
            .map_err(|e| Error::FinalizeValidation(e.to_string()))?;
    }
    Ok(output)
}

/// Encode preflight over every annotation in the file (hard-errors rule):
/// reject out-of-bounds `LiteralValue::LiteralArray(idx)` inside an
/// annotation-embedded literal array (`CodeRelocation` with site/owner
/// context) BEFORE any bytes are emitted, using an explicit iterative
/// workstack.
fn validate_annotation_arrays(file: &File) -> Result<(), Error> {
    fn annotations(a: &Annotations) -> impl Iterator<Item = &Annotation> {
        a.compile_time
            .iter()
            .chain(a.runtime.iter())
            .chain(a.compile_time_type.iter())
            .chain(a.runtime_type.iter())
    }

    #[derive(Clone, Copy)]
    enum Owner {
        Class(StringId),
        Method(StringId, StringId),
        Field(StringId, StringId),
        MethodParam(StringId, StringId, usize),
    }

    #[derive(Clone, Copy)]
    struct Site {
        annotation: StringId,
        element: StringId,
    }

    fn resolve(pool: &StringPool, sid: StringId) -> &str {
        pool.resolve(sid).unwrap_or("<unknown>")
    }

    fn owner_string(pool: &StringPool, owner: Owner) -> String {
        match owner {
            Owner::Class(c) => format!("class {}", resolve(pool, c)),
            Owner::Method(c, m) => format!("method {}::{}", resolve(pool, c), resolve(pool, m)),
            Owner::Field(c, f) => format!("field {}::{}", resolve(pool, c), resolve(pool, f)),
            Owner::MethodParam(c, m, i) => format!(
                "parameter {i} of method {}::{}",
                resolve(pool, c),
                resolve(pool, m)
            ),
        }
    }

    fn validate_root<'a>(
        pool: &StringPool,
        literal_array_count: usize,
        owner: Owner,
        site: Site,
        root: &'a AnnotationValue,
        stack: &mut Vec<(Owner, Site, &'a AnnotationValue)>,
    ) -> Result<(), Error> {
        stack.clear();
        stack.push((owner, site, root));
        while let Some((cur_owner, cur_site, v)) = stack.pop() {
            match v {
                AnnotationValue::Array { values, .. } => {
                    for item in values.iter().rev() {
                        stack.push((cur_owner, cur_site, item));
                    }
                }
                AnnotationValue::Annotation(a) => {
                    for e in a.elements.iter().rev() {
                        stack.push((
                            cur_owner,
                            Site {
                                annotation: a.class_descriptor,
                                element: e.name,
                            },
                            &e.value,
                        ));
                    }
                }
                AnnotationValue::LiteralArray(values) => {
                    for (item_index, item) in values.iter().enumerate() {
                        if let LiteralValue::LiteralArray(idx) = item
                            && (idx.0 as usize) >= literal_array_count
                        {
                            return Err(Error::CodeRelocation(format!(
                                "annotation {} element '{}' on {}: nested literal array index {} at item {} out of bounds (table len {})",
                                resolve(pool, cur_site.annotation),
                                resolve(pool, cur_site.element),
                                owner_string(pool, cur_owner),
                                idx.0,
                                item_index,
                                literal_array_count,
                            )));
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    let pool = &file.strings;
    let literal_array_count = file.literal_arrays.len();
    let mut stack: Vec<(Owner, Site, &AnnotationValue)> = Vec::new();

    for class in file.classes.values() {
        for ann in annotations(&class.annotations) {
            for e in &ann.elements {
                validate_root(
                    pool,
                    literal_array_count,
                    Owner::Class(class.descriptor),
                    Site {
                        annotation: ann.class_descriptor,
                        element: e.name,
                    },
                    &e.value,
                    &mut stack,
                )?;
            }
        }
        for method in &class.methods {
            for ann in annotations(&method.annotations) {
                for e in &ann.elements {
                    validate_root(
                        pool,
                        literal_array_count,
                        Owner::Method(class.descriptor, method.name),
                        Site {
                            annotation: ann.class_descriptor,
                            element: e.name,
                        },
                        &e.value,
                        &mut stack,
                    )?;
                }
            }
            for bucket in [
                &method.param_annotations.compile_time,
                &method.param_annotations.runtime,
            ] {
                for (index, anns) in bucket.iter().enumerate() {
                    for ann in anns {
                        for e in &ann.elements {
                            validate_root(
                                pool,
                                literal_array_count,
                                Owner::MethodParam(class.descriptor, method.name, index),
                                Site {
                                    annotation: ann.class_descriptor,
                                    element: e.name,
                                },
                                &e.value,
                                &mut stack,
                            )?;
                        }
                    }
                }
            }
        }
        for field in &class.fields {
            for ann in annotations(&field.annotations) {
                for e in &ann.elements {
                    validate_root(
                        pool,
                        literal_array_count,
                        Owner::Field(class.descriptor, field.name),
                        Site {
                            annotation: ann.class_descriptor,
                            element: e.name,
                        },
                        &e.value,
                        &mut stack,
                    )?;
                }
            }
        }
    }
    Ok(())
}

fn validate_literal_array_graph(literal_arrays: &[LiteralArray]) -> Result<(), Error> {
    let len = literal_arrays.len();
    for la in literal_arrays {
        for item in &la.values {
            if let LiteralValue::LiteralArray(idx) = item
                && (idx.0 as usize) >= len
            {
                return Err(Error::CodeRelocation(format!(
                    "nested literal array index {} out of bounds",
                    idx.0
                )));
            }
        }
    }
    Ok(())
}

fn count_annotation_literal_arrays(file: &File) -> u32 {
    fn push_annotations<'a>(a: &'a Annotations, stack: &mut Vec<&'a AnnotationValue>) {
        for ann in a
            .compile_time
            .iter()
            .chain(a.runtime.iter())
            .chain(a.compile_time_type.iter())
            .chain(a.runtime_type.iter())
        {
            for e in &ann.elements {
                stack.push(&e.value);
            }
        }
    }

    let mut stack: Vec<&AnnotationValue> = Vec::new();

    for class in file.classes.values() {
        push_annotations(&class.annotations, &mut stack);
        for method in &class.methods {
            push_annotations(&method.annotations, &mut stack);
            let pa = &method.param_annotations;
            let has_compile = pa.compile_time.iter().any(|v| !v.is_empty());
            let has_runtime = pa.runtime.iter().any(|v| !v.is_empty());
            if !method.is_external && (has_compile || has_runtime) {
                let num_params = method
                    .arg_types
                    .len()
                    .max(pa.compile_time.len())
                    .max(pa.runtime.len());
                let seal_as_runtime = !has_compile;
                for idx in 0..num_params {
                    if seal_as_runtime {
                        for ann in pa.runtime.get(idx).into_iter().flatten() {
                            for e in &ann.elements {
                                stack.push(&e.value);
                            }
                        }
                    } else {
                        for ann in pa.compile_time.get(idx).into_iter().flatten().chain(
                            pa.runtime.get(idx).into_iter().flatten().filter(|ra| {
                                !pa.compile_time.get(idx).is_some_and(|c| c.contains(*ra))
                            }),
                        ) {
                            for e in &ann.elements {
                                stack.push(&e.value);
                            }
                        }
                    }
                }
            }
        }
        for field in &class.fields {
            push_annotations(&field.annotations, &mut stack);
        }
    }

    let mut count: u32 = 0;
    while let Some(v) = stack.pop() {
        match v {
            AnnotationValue::LiteralArray(_) => count += 1,
            AnnotationValue::Annotation(a) => {
                for e in &a.elements {
                    stack.push(&e.value);
                }
            }
            AnnotationValue::Array { values, .. } => {
                for item in values {
                    stack.push(item);
                }
            }
            _ => {}
        }
    }
    count
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

enum AnnotationTarget {
    Class(ClassHandle),
    Method(MethodHandle),
    Field(FieldHandle),
}

struct AnnotationEncodeCtx<'a> {
    string_handles: &'a mut [Option<StringHandle>],
    class_handles: &'a mut HashMap<StringId, ClassHandle>,
    entities: &'a EntityHandles,
    ann_la_counter: &'a mut u32,
    deferred_ann_las: &'a mut Vec<(LiteralArrayHandle, Vec<LiteralValue>)>,
    pool: &'a StringPool,
}

fn sync_slot_number_annotation(
    anns: &Annotations,
    pool: &crate::StringPool,
    ic_size: u32,
) -> Annotations {
    const ANNOTATION_CLASS: &str = "L_ESSlotNumberAnnotation;";
    const ELEMENT_NAME: &str = "SlotNumber";

    let mut synced = anns.clone();
    for bucket in [
        &mut synced.compile_time,
        &mut synced.runtime,
        &mut synced.compile_time_type,
        &mut synced.runtime_type,
    ] {
        for ann in bucket.iter_mut() {
            if pool.resolve(ann.class_descriptor) != Some(ANNOTATION_CLASS) {
                continue;
            }
            for elem in &mut ann.elements {
                if pool.resolve(elem.name) == Some(ELEMENT_NAME) {
                    elem.value = AnnotationValue::U32(ic_size);
                }
            }
        }
    }
    synced
}

type AttachAnnotationFn = fn(&mut Builder, &AnnotationTarget, AnnotationHandle);

fn encode_annotations_on(
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
    anns: &Annotations,
    target: AnnotationTarget,
) -> Result<(), Error> {
    let groups: [(&[Annotation], AttachAnnotationFn); 4] = [
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

enum PendingEncodeElem<'a> {
    Scalar {
        name: StringHandle,
    },
    Array {
        name: StringHandle,
        tag: u8,
        remaining: std::slice::Iter<'a, AnnotationValue>,
        handles: Vec<u64>,
    },
}

struct AnnEncodeFrame<'a> {
    ann_cls: ClassHandle,
    elems_iter: std::slice::Iter<'a, AnnotationElem>,
    encoded_elems: Vec<AnnotationElemDefEx>,
    pending: Option<PendingEncodeElem<'a>>,
}

fn encode_single_annotation(
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
    ann: &Annotation,
) -> Result<AnnotationHandle, Error> {
    use sys::AnnotationValueType as AVT;

    let root_cls = resolve_class_for_ann(b, ctx.class_handles, ctx.pool, ann.class_descriptor)?;
    let mut stack = vec![AnnEncodeFrame {
        ann_cls: root_cls,
        elems_iter: ann.elements.iter(),
        encoded_elems: Vec::with_capacity(ann.elements.len()),
        pending: None,
    }];
    let mut completed: Option<AnnotationHandle> = None;

    while let Some(frame) = stack.last_mut() {
        let mut next_child: Option<AnnEncodeFrame<'_>> = None;
        if let Some(child_h) = completed.take() {
            match frame.pending.take() {
                Some(PendingEncodeElem::Scalar { name }) => {
                    frame.encoded_elems.push(AnnotationElemDefEx {
                        name,
                        tag: AVT::Annotation as u8,
                        value: AnnotationElemValue::EntityRef(child_h.0),
                    });
                }
                Some(PendingEncodeElem::Array {
                    name,
                    tag,
                    mut remaining,
                    mut handles,
                }) => {
                    handles.push(u64::from(child_h.0));
                    for item in &mut remaining {
                        if let AnnotationValue::Annotation(nested) = item {
                            let child_cls = resolve_class_for_ann(
                                b,
                                ctx.class_handles,
                                ctx.pool,
                                nested.class_descriptor,
                            )?;
                            frame.pending = Some(PendingEncodeElem::Array {
                                name,
                                tag,
                                remaining,
                                handles: std::mem::take(&mut handles),
                            });
                            next_child = Some(AnnEncodeFrame {
                                ann_cls: child_cls,
                                elems_iter: nested.elements.iter(),
                                encoded_elems: Vec::with_capacity(nested.elements.len()),
                                pending: None,
                            });
                            break;
                        }
                        handles.push(annotation_array_leaf_to_handle(item, b, ctx)?);
                    }
                    if next_child.is_none() {
                        let value = if is_entity_array_tag(tag) {
                            AnnotationElemValue::EntityArray(
                                handles.into_iter().map(|h| h as u32).collect(),
                            )
                        } else {
                            AnnotationElemValue::Array64(handles)
                        };
                        frame
                            .encoded_elems
                            .push(AnnotationElemDefEx { name, tag, value });
                    }
                }
                None => {}
            }
        }
        if let Some(child_frame) = next_child {
            stack.push(child_frame);
            continue;
        }

        for e in &mut frame.elems_iter {
            let name = get_or_add_string_id(b, ctx.string_handles, ctx.pool, e.name)?;
            match &e.value {
                AnnotationValue::Annotation(nested) => {
                    let child_cls = resolve_class_for_ann(
                        b,
                        ctx.class_handles,
                        ctx.pool,
                        nested.class_descriptor,
                    )?;
                    frame.pending = Some(PendingEncodeElem::Scalar { name });
                    next_child = Some(AnnEncodeFrame {
                        ann_cls: child_cls,
                        elems_iter: nested.elements.iter(),
                        encoded_elems: Vec::with_capacity(nested.elements.len()),
                        pending: None,
                    });
                    break;
                }
                AnnotationValue::Array { tag, values } => {
                    let mut remaining = values.iter();
                    let mut handles = Vec::with_capacity(values.len());
                    for item in &mut remaining {
                        if let AnnotationValue::Annotation(nested) = item {
                            let child_cls = resolve_class_for_ann(
                                b,
                                ctx.class_handles,
                                ctx.pool,
                                nested.class_descriptor,
                            )?;
                            frame.pending = Some(PendingEncodeElem::Array {
                                name,
                                tag: *tag,
                                remaining,
                                handles: std::mem::take(&mut handles),
                            });
                            next_child = Some(AnnEncodeFrame {
                                ann_cls: child_cls,
                                elems_iter: nested.elements.iter(),
                                encoded_elems: Vec::with_capacity(nested.elements.len()),
                                pending: None,
                            });
                            break;
                        }
                        handles.push(annotation_array_leaf_to_handle(item, b, ctx)?);
                    }
                    if next_child.is_some() {
                        break;
                    }
                    let value = if is_entity_array_tag(*tag) {
                        AnnotationElemValue::EntityArray(
                            handles.into_iter().map(|h| h as u32).collect(),
                        )
                    } else {
                        AnnotationElemValue::Array64(handles)
                    };
                    frame.encoded_elems.push(AnnotationElemDefEx {
                        name,
                        tag: *tag,
                        value,
                    });
                }
                other => {
                    let (tag, value) = annotation_scalar_value_to_raw(other, b, ctx)?;
                    frame
                        .encoded_elems
                        .push(AnnotationElemDefEx { name, tag, value });
                }
            }
        }

        if let Some(child_frame) = next_child {
            stack.push(child_frame);
            continue;
        }

        let Some(finished) = stack.pop() else {
            break;
        };
        let ann_h = b.create_annotation_ex(finished.ann_cls, &finished.encoded_elems);
        if stack.is_empty() {
            return Ok(ann_h);
        }
        completed = Some(ann_h);
    }

    Err(Error::Finalize)
}

fn annotation_scalar_value_to_raw(
    val: &AnnotationValue,
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
) -> Result<(u8, AnnotationElemValue), Error> {
    use sys::AnnotationValueType as AVT;

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
            ctx.deferred_ann_las.push((la_h, values.clone()));
            (
                AVT::LiteralArray as u8,
                AnnotationElemValue::EntityRef(la_h.0),
            )
        }
        AnnotationValue::Void => (AVT::Void as u8, AnnotationElemValue::Scalar(0)),
        AnnotationValue::StringNullptr => {
            (AVT::StringNullptr as u8, AnnotationElemValue::Scalar(0))
        }
        AnnotationValue::Annotation(_) | AnnotationValue::Array { .. } => {
            unreachable!("compound annotation values are dispatched by encode_single_annotation")
        }
    };
    Ok(raw)
}

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

fn annotation_array_leaf_to_handle(
    val: &AnnotationValue,
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
) -> Result<u64, Error> {
    let raw = match val {
        AnnotationValue::Bool(v) => u64::from(*v),
        AnnotationValue::I8(v) => u64::from(*v as u32),
        AnnotationValue::U8(v) => u64::from(*v),
        AnnotationValue::I16(v) => u64::from(*v as u32),
        AnnotationValue::U16(v) => u64::from(*v),
        AnnotationValue::I32(v) => u64::from(*v as u32),
        AnnotationValue::U32(v) => u64::from(*v),
        AnnotationValue::I64(v) => *v as u64,
        AnnotationValue::U64(v) => *v,
        AnnotationValue::F32(v) => u64::from(v.to_bits()),
        AnnotationValue::F64(v) => v.to_bits(),
        AnnotationValue::String(sid) => {
            let h = get_or_add_string_id(b, ctx.string_handles, ctx.pool, *sid)?;
            u64::from(h.0)
        }
        AnnotationValue::Record(sid) => {
            let h = resolve_class_for_ann(b, ctx.class_handles, ctx.pool, *sid)?;
            u64::from(h.0)
        }
        AnnotationValue::Method { name, offset } => u64::from(
            ctx.entities
                .resolve_method(*name, *offset)
                .ok_or_else(|| {
                    Error::CodeRelocation(format!(
                        "annotation array method reference '{}' at offset {offset:#x} cannot be resolved",
                        ctx.pool.resolve(*name).unwrap_or("<unknown>")
                    ))
                })?
                .0,
        ),
        AnnotationValue::Enum { name, offset } => u64::from(
            ctx.entities
                .resolve_field(*name, *offset)
                .ok_or_else(|| {
                    Error::CodeRelocation(format!(
                        "annotation array enum reference '{}' at offset {offset:#x} cannot be resolved",
                        ctx.pool.resolve(*name).unwrap_or("<unknown>")
                    ))
                })?
                .0,
        ),
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
            u64::from(b.create_method_handle(mh.handle_type as u8, entity_handle).0)
        }
        AnnotationValue::LiteralArray(_) => {
            match annotation_scalar_value_to_raw(val, b, ctx)? {
                (_, AnnotationElemValue::EntityRef(h)) => u64::from(h),
                _ => unreachable!("literal-array values encode as entity refs"),
            }
        }
        AnnotationValue::Annotation(_) => {
            unreachable!(
                "nested annotations are dispatched iteratively by encode_single_annotation"
            )
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

fn resolve_class_for_ann(
    b: &mut Builder,
    class_handles: &mut HashMap<StringId, ClassHandle>,
    pool: &StringPool,
    desc: StringId,
) -> Result<ClassHandle, Error> {
    if let Some(&h) = class_handles.get(&desc) {
        return Ok(h);
    }
    let bytes = pool.to_mutf8_bytes(desc).ok_or_else(|| Error::Malformed {
        field: "string_id",
        context: format!("dangling StringId {desc:?} for annotation class descriptor"),
    })?;
    let h = b.add_foreign_class_cstr(&Builder::mutf8_cstr(&bytes)?);
    class_handles.insert(desc, h);
    Ok(h)
}

#[derive(Clone, Copy)]
enum LnpEventKind {
    EndLocal {
        reg: i32,
    },
    Line {
        line: u32,
    },
    Column {
        column: u32,
    },
    StartLocal {
        reg: i32,
        name: StringHandle,
        type_name: StringHandle,
        type_sig: Option<StringHandle>,
    },
}

impl LnpEventKind {
    const fn priority(&self) -> u8 {
        match self {
            Self::EndLocal { .. } => 0,
            Self::Line { .. } => 1,
            Self::Column { .. } => 2,
            Self::StartLocal { .. } => 3,
        }
    }
}

struct LnpEvent {
    pc: u32,
    seq: usize,
    kind: LnpEventKind,
}

fn encode_debug_info(
    b: &mut Builder,
    string_handles: &mut [Option<StringHandle>],
    pool: &StringPool,
    method_h: MethodHandle,
    dbg: &MethodDebugInfo,
    byte_offsets: &[u32],
    code_len: u32,
) -> Result<(), Error> {
    let non_empty = |sid: StringId| !pool.resolve(sid).unwrap_or("").is_empty();
    let has_content = !dbg.line_table.is_empty()
        || !dbg.column_table.is_empty()
        || !dbg.local_vars.is_empty()
        || !dbg.params.is_empty()
        || dbg.source_file.is_some_and(non_empty)
        || dbg.source_code.is_some_and(non_empty);
    if !has_content {
        return Ok(());
    }

    let lnp = b.create_lnp();
    let first_line = dbg.line_table.first().map_or(0, |e| e.line);
    let debug_h = b.create_debug_info(lnp, first_line);

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

    for p in &dbg.params {
        let nh = get_or_add_string_id(b, string_handles, pool, p.name)?;
        b.debug_add_param(debug_h, nh);
    }

    // `ProcessBegin()` in `DebugInfoExtractor` unconditionally pushes
    // `{ offset: 0, line: first_line }` before executing the first opcode.
    // Skip `line_table[0]` when it already sits at PC 0 so it is not duplicated.
    let skip_initial_line = dbg
        .line_table
        .first()
        .is_some_and(|first| index_to_offset(byte_offsets, first.index, code_len) == 0);
    let line_slice = if skip_initial_line {
        &dbg.line_table[1..]
    } else {
        &dbg.line_table[..]
    };

    // Determine the final PC so local variables spanning to the end of the
    // method close via `ProcessVars()` at `END_SEQUENCE` instead of emitting a
    // trailing `END_LOCAL` that could overwrite a nested inner variable on the
    // same register (`DebugInfoExtractor::HandleEndLocal` scans `rbegin()`
    // without skipping already-closed entries).
    let mut final_unclosed_pc = code_len;
    for entry in line_slice {
        final_unclosed_pc =
            final_unclosed_pc.max(index_to_offset(byte_offsets, entry.index, code_len));
    }
    for entry in &dbg.column_table {
        final_unclosed_pc =
            final_unclosed_pc.max(index_to_offset(byte_offsets, entry.index, code_len));
    }
    for lv in &dbg.local_vars {
        let s = index_to_offset(byte_offsets, lv.start, code_len);
        let e = index_to_offset(byte_offsets, lv.end, code_len).max(s);
        final_unclosed_pc = final_unclosed_pc.max(e);
    }

    let mut events =
        Vec::with_capacity(line_slice.len() + dbg.column_table.len() + dbg.local_vars.len() * 2);
    let mut seq = 0usize;

    for entry in line_slice {
        let pc = index_to_offset(byte_offsets, entry.index, code_len);
        events.push(LnpEvent {
            pc,
            seq,
            kind: LnpEventKind::Line { line: entry.line },
        });
        seq += 1;
    }

    for entry in &dbg.column_table {
        let pc = index_to_offset(byte_offsets, entry.index, code_len);
        events.push(LnpEvent {
            pc,
            seq,
            kind: LnpEventKind::Column {
                column: entry.column,
            },
        });
        seq += 1;
    }

    let mut has_implicit_end_local = false;
    for lv in &dbg.local_vars {
        let name_h = get_or_add_string_id(b, string_handles, pool, lv.name)?;
        let type_h = get_or_add_string_id(b, string_handles, pool, lv.type_name)?;
        let sig_h = if lv.type_signature == lv.type_name {
            None
        } else {
            Some(get_or_add_string_id(
                b,
                string_handles,
                pool,
                lv.type_signature,
            )?)
        };
        let start_pc = index_to_offset(byte_offsets, lv.start, code_len);
        let end_pc = index_to_offset(byte_offsets, lv.end, code_len).max(start_pc);

        if end_pc == start_pc {
            // Zero-length range: start then immediately end at `start_pc`
            // unless `end_pc == 0 == final_unclosed_pc` (empty program).
            events.push(LnpEvent {
                pc: start_pc,
                seq,
                kind: LnpEventKind::StartLocal {
                    reg: lv.reg_number,
                    name: name_h,
                    type_name: type_h,
                    type_sig: sig_h,
                },
            });
            seq += 1;
            if end_pc > 0 && end_pc < final_unclosed_pc {
                events.push(LnpEvent {
                    pc: end_pc,
                    seq,
                    kind: LnpEventKind::EndLocal { reg: lv.reg_number },
                });
                seq += 1;
            } else if end_pc > 0 {
                has_implicit_end_local = true;
            }
            continue;
        }

        events.push(LnpEvent {
            pc: start_pc,
            seq,
            kind: LnpEventKind::StartLocal {
                reg: lv.reg_number,
                name: name_h,
                type_name: type_h,
                type_sig: sig_h,
            },
        });
        seq += 1;

        if end_pc < final_unclosed_pc {
            events.push(LnpEvent {
                pc: end_pc,
                seq,
                kind: LnpEventKind::EndLocal { reg: lv.reg_number },
            });
            seq += 1;
        } else if end_pc > 0 {
            has_implicit_end_local = true;
        }
    }

    // Sort by `(pc, priority, seq)`: at any PC, `EndLocal` runs before
    // `StartLocal` (except zero-length `[pc, pc)` where `EndLocal` shares `pc`
    // — wait: for zero-length `[pc, pc)` with `pc > 0`, `StartLocal` must
    // precede its own `EndLocal`! Handle zero-length `EndLocal` via `seq` only
    // or emit after `StartLocal`).
    events.sort_by_key(|ev| (ev.pc, ev.kind.priority(), ev.seq));

    // Re-check zero-length `[pc, pc)` locals where `start_pc == end_pc < final_unclosed_pc`:
    // ensure no `EndLocal` precedes its matching `StartLocal` on an unstarted register.
    let mut active_regs: Vec<i32> = Vec::new();
    let mut deferred_same_pc_ends: Vec<i32> = Vec::new();
    let mut cur_pc: u32 = 0;
    let mut prev_line: u32 = first_line;
    let mut idx = 0usize;

    while idx < events.len() {
        let group_pc = events[idx].pc;
        let group_end = events[idx..]
            .iter()
            .position(|e| e.pc != group_pc)
            .map_or(events.len(), |off| idx + off);

        deferred_same_pc_ends.clear();
        for ev in &events[idx..group_end] {
            match ev.kind {
                LnpEventKind::EndLocal { reg } => {
                    if let Some(pos) = active_regs.iter().rposition(|&r| r == reg) {
                        if group_pc > cur_pc {
                            b.lnp_emit_advance_pc(lnp, debug_h, group_pc - cur_pc);
                            cur_pc = group_pc;
                        }
                        b.lnp_emit_end_local(lnp, reg);
                        active_regs.remove(pos);
                    } else {
                        deferred_same_pc_ends.push(reg);
                    }
                }
                LnpEventKind::Line { line } => {
                    let pc_delta = group_pc - cur_pc;
                    let line_delta = (line as i32).wrapping_sub(prev_line as i32);
                    b.lnp_emit_special_opcode(lnp, debug_h, pc_delta, line_delta);
                    cur_pc = group_pc;
                    prev_line = line;
                }
                LnpEventKind::Column { column } => {
                    let pc_delta = group_pc - cur_pc;
                    b.lnp_emit_column(lnp, debug_h, pc_delta, column);
                    cur_pc = group_pc;
                }
                LnpEventKind::StartLocal {
                    reg,
                    name,
                    type_name,
                    type_sig,
                } => {
                    if group_pc > cur_pc {
                        b.lnp_emit_advance_pc(lnp, debug_h, group_pc - cur_pc);
                        cur_pc = group_pc;
                    }
                    if let Some(sig) = type_sig {
                        b.lnp_emit_start_local_extended(lnp, debug_h, reg, name, type_name, sig);
                    } else {
                        b.lnp_emit_start_local(lnp, debug_h, reg, name, type_name);
                    }
                    active_regs.push(reg);
                }
            }
        }
        for &reg in &deferred_same_pc_ends {
            if let Some(pos) = active_regs.iter().rposition(|&r| r == reg) {
                if group_pc > cur_pc {
                    b.lnp_emit_advance_pc(lnp, debug_h, group_pc - cur_pc);
                    cur_pc = group_pc;
                }
                b.lnp_emit_end_local(lnp, reg);
                active_regs.remove(pos);
            }
        }

        idx = group_end;
    }

    if has_implicit_end_local && final_unclosed_pc > cur_pc {
        b.lnp_emit_advance_pc(lnp, debug_h, final_unclosed_pc - cur_pc);
    }

    b.lnp_emit_end(lnp);
    b.method_set_debug_info(method_h, debug_h);
    Ok(())
}

struct LiteralEncodeCtx<'a> {
    string_handles: &'a mut [Option<StringHandle>],
    pool: &'a StringPool,
    entity_map: &'a HashMap<u32, StringId>,
    entities: &'a EntityHandles,
    literal_handles: &'a [LiteralArrayHandle],
}

fn encode_literal_value(
    b: &mut Builder,
    ctx: &mut LiteralEncodeCtx<'_>,
    la: LiteralArrayHandle,
    val: &LiteralValue,
) -> Result<(), Error> {
    // A non-zero offset is the unique entity identity; the name lookup via
    // `entity_map` at offset `0` only serves hand-built offsetless models.
    let resolve_method = |off: u32| -> Option<MethodHandle> {
        if off != 0 {
            return ctx.entities.methods_by_offset.get(&off).copied();
        }
        let sid = ctx.entity_map.get(&0)?;
        ctx.entities.methods_by_name.get(sid).copied()
    };

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
            let sh = get_or_add_string_id(b, ctx.string_handles, ctx.pool, *sid)?;
            b.literal_array_add_raw_string(la, sh);
        }
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
            let target = ctx.literal_handles.get(idx.0 as usize).ok_or_else(|| {
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
            let sh = get_or_add_string_id(b, ctx.string_handles, ctx.pool, *sid)?;
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

fn index_to_offset(byte_offsets: &[u32], index: u32, code_len: u32) -> u32 {
    byte_offsets
        .get(index as usize)
        .copied()
        .unwrap_or(code_len)
}

fn get_or_add_string_id(
    b: &mut Builder,
    string_handles: &mut [Option<StringHandle>],
    pool: &StringPool,
    sid: StringId,
) -> Result<StringHandle, Error> {
    let idx = sid.index();
    if let Some(&Some(h)) = string_handles.get(idx) {
        return Ok(h);
    }
    let h = if let Some(raw) = pool.raw_mutf8(sid) {
        b.add_string_mutf8(raw)?
    } else {
        let s = pool.as_str(sid).ok_or_else(|| Error::Malformed {
            field: "string_id",
            context: format!("dangling StringId {sid:?} in string table"),
        })?;
        b.add_string(s)
    };
    if let Some(slot) = string_handles.get_mut(idx) {
        *slot = Some(h);
    }
    Ok(h)
}

fn module_record_def(
    rec: &ModuleRecord,
    b: &mut Builder,
    string_handles: &mut [Option<StringHandle>],
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
        assert_eq!(entities.resolve_method(name, 999), None);
        assert_eq!(entities.resolve_field(name, 999), None);
    }

    #[test]
    fn handles_fall_back_to_name_for_offsetless_models() {
        let mut pool = StringPool::default();
        let name = pool.get_or_intern("bar");
        let mut entities = EntityHandles::default();

        entities.insert_method(&method(&mut pool, "bar", 0), MethodHandle(10));
        entities.insert_field(&field(&mut pool, "bar", 0), FieldHandle(20));

        assert_eq!(entities.resolve_method(name, 0), Some(MethodHandle(10)));
        assert_eq!(entities.resolve_field(name, 0), Some(FieldHandle(20)));
        // Unknown non-zero offsets must never silently alias by name (#44 R1-H6 #7).
        assert_eq!(entities.resolve_method(name, 999), None);
        assert_eq!(entities.resolve_field(name, 999), None);
    }

    #[test]
    fn c_mutf8_encodes_nul_and_astral_without_panicking() {
        let cs = c_mutf8("a\0\u{1F600}z");
        assert_eq!(
            cs.as_bytes(),
            &[b'a', 0xC0, 0x80, 0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80, b'z']
        );
    }
}
