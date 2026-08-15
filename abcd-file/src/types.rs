use crate::Error;
use abcd_file_sys as sys;
use string_interner::Symbol;

bitflags::bitflags! {
    /// Access flags for classes, methods, and fields.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct AccessFlags: u32 {
        const PUBLIC       = sys::AbcAccessFlags_ABC_ACC_PUBLIC;
        const PRIVATE      = sys::AbcAccessFlags_ABC_ACC_PRIVATE;
        const PROTECTED    = sys::AbcAccessFlags_ABC_ACC_PROTECTED;
        const STATIC       = sys::AbcAccessFlags_ABC_ACC_STATIC;
        const FINAL        = sys::AbcAccessFlags_ABC_ACC_FINAL;
        const SUPER        = sys::AbcAccessFlags_ABC_ACC_SUPER;
        const SYNCHRONIZED = sys::AbcAccessFlags_ABC_ACC_SYNCHRONIZED;
        const BRIDGE       = sys::AbcAccessFlags_ABC_ACC_BRIDGE;
        const VOLATILE     = sys::AbcAccessFlags_ABC_ACC_VOLATILE;
        const TRANSIENT    = sys::AbcAccessFlags_ABC_ACC_TRANSIENT;
        const VARARGS      = sys::AbcAccessFlags_ABC_ACC_VARARGS;
        const NATIVE       = sys::AbcAccessFlags_ABC_ACC_NATIVE;
        const INTERFACE    = sys::AbcAccessFlags_ABC_ACC_INTERFACE;
        const ABSTRACT     = sys::AbcAccessFlags_ABC_ACC_ABSTRACT;
        const STRICT       = sys::AbcAccessFlags_ABC_ACC_STRICT;
        const SYNTHETIC    = sys::AbcAccessFlags_ABC_ACC_SYNTHETIC;
        const ANNOTATION   = sys::AbcAccessFlags_ABC_ACC_ANNOTATION;
        const ENUM         = sys::AbcAccessFlags_ABC_ACC_ENUM;
        const CONSTRUCTOR            = sys::AbcAccessFlags_ABC_ACC_CONSTRUCTOR;
        const HAS_DEFAULT_METHODS    = sys::AbcAccessFlags_ABC_ACC_HAS_DEFAULT_METHODS;
        const DEFAULT_INTERFACE_METHOD = sys::AbcAccessFlags_ABC_ACC_DEFAULT_INTERFACE_METHOD;
        const SINGLE_IMPL  = sys::AbcAccessFlags_ABC_ACC_SINGLE_IMPL;
        const INTRINSIC    = sys::AbcAccessFlags_ABC_ACC_INTRINSIC;
        const PROXY        = sys::AbcAccessFlags_ABC_ACC_PROXY;
        const FAST_NATIVE  = sys::AbcAccessFlags_ABC_ACC_FAST_NATIVE;
        const CRITICAL_NATIVE = sys::AbcAccessFlags_ABC_ACC_CRITICAL_NATIVE;
    }
}

/// Trait for types that carry [`AccessFlags`].
///
/// Provides default `is_*()` convenience methods for all known flags.
/// Not all flags are meaningful for every implementor (e.g. `is_volatile`
/// is only relevant for fields), but the methods are still safe to call —
/// they simply return `false` when the flag is not set.
pub trait HasAccessFlags {
    fn access_flags(&self) -> AccessFlags;

    fn is_public(&self) -> bool {
        self.access_flags().contains(AccessFlags::PUBLIC)
    }
    fn is_private(&self) -> bool {
        self.access_flags().contains(AccessFlags::PRIVATE)
    }
    fn is_protected(&self) -> bool {
        self.access_flags().contains(AccessFlags::PROTECTED)
    }
    fn is_static(&self) -> bool {
        self.access_flags().contains(AccessFlags::STATIC)
    }
    fn is_final(&self) -> bool {
        self.access_flags().contains(AccessFlags::FINAL)
    }
    fn is_super(&self) -> bool {
        self.access_flags().contains(AccessFlags::SUPER)
    }
    fn is_synchronized(&self) -> bool {
        self.access_flags().contains(AccessFlags::SYNCHRONIZED)
    }
    fn is_bridge(&self) -> bool {
        self.access_flags().contains(AccessFlags::BRIDGE)
    }
    fn is_volatile(&self) -> bool {
        self.access_flags().contains(AccessFlags::VOLATILE)
    }
    fn is_transient(&self) -> bool {
        self.access_flags().contains(AccessFlags::TRANSIENT)
    }
    fn is_varargs(&self) -> bool {
        self.access_flags().contains(AccessFlags::VARARGS)
    }
    fn is_native(&self) -> bool {
        self.access_flags().contains(AccessFlags::NATIVE)
    }
    fn is_interface(&self) -> bool {
        self.access_flags().contains(AccessFlags::INTERFACE)
    }
    fn is_abstract(&self) -> bool {
        self.access_flags().contains(AccessFlags::ABSTRACT)
    }
    fn is_strict(&self) -> bool {
        self.access_flags().contains(AccessFlags::STRICT)
    }
    fn is_synthetic(&self) -> bool {
        self.access_flags().contains(AccessFlags::SYNTHETIC)
    }
    fn is_annotation(&self) -> bool {
        self.access_flags().contains(AccessFlags::ANNOTATION)
    }
    fn is_enum(&self) -> bool {
        self.access_flags().contains(AccessFlags::ENUM)
    }
    fn is_constructor(&self) -> bool {
        self.access_flags().contains(AccessFlags::CONSTRUCTOR)
    }
    fn has_default_methods(&self) -> bool {
        self.access_flags()
            .contains(AccessFlags::HAS_DEFAULT_METHODS)
    }
    fn is_default_interface_method(&self) -> bool {
        self.access_flags()
            .contains(AccessFlags::DEFAULT_INTERFACE_METHOD)
    }
    fn is_single_impl(&self) -> bool {
        self.access_flags().contains(AccessFlags::SINGLE_IMPL)
    }
    fn is_intrinsic(&self) -> bool {
        self.access_flags().contains(AccessFlags::INTRINSIC)
    }
    fn is_proxy(&self) -> bool {
        self.access_flags().contains(AccessFlags::PROXY)
    }
    fn is_fast_native(&self) -> bool {
        self.access_flags().contains(AccessFlags::FAST_NATIVE)
    }
    fn is_critical_native(&self) -> bool {
        self.access_flags().contains(AccessFlags::CRITICAL_NATIVE)
    }
}

/// Resolved type used in method signatures.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Void,
    Bool,
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
    F32,
    F64,
    Tagged,
    Reference(crate::StringId),
}

impl Type {
    /// Convert a raw TypeId to a Type, consuming a reference descriptor if needed.
    pub(crate) fn from_raw(id: TypeId, ref_desc: Option<crate::StringId>) -> Result<Type, Error> {
        match id {
            TypeId::Void => Ok(Type::Void),
            TypeId::U1 => Ok(Type::Bool),
            TypeId::I8 => Ok(Type::I8),
            TypeId::U8 => Ok(Type::U8),
            TypeId::I16 => Ok(Type::I16),
            TypeId::U16 => Ok(Type::U16),
            TypeId::I32 => Ok(Type::I32),
            TypeId::U32 => Ok(Type::U32),
            TypeId::F32 => Ok(Type::F32),
            TypeId::F64 => Ok(Type::F64),
            TypeId::I64 => Ok(Type::I64),
            TypeId::U64 => Ok(Type::U64),
            TypeId::Tagged => Ok(Type::Tagged),
            TypeId::Reference => ref_desc.map(Type::Reference).ok_or(Error::Malformed {
                field: "reference_type",
                context: "missing descriptor for Reference type".into(),
            }),
        }
    }

    /// Parse a field type descriptor string into a `Type`.
    ///
    /// Primitive descriptors (`"u1"`, `"i32"`, `"f64"`, etc.) map to the
    /// corresponding variant.  Everything else becomes `Type::Reference(sid)`.
    pub fn from_descriptor(descriptor: &str, descriptor_id: crate::StringId) -> Type {
        match descriptor {
            "u1" => Type::Bool,
            "i8" => Type::I8,
            "u8" => Type::U8,
            "i16" => Type::I16,
            "u16" => Type::U16,
            "i32" => Type::I32,
            "u32" => Type::U32,
            "i64" => Type::I64,
            "u64" => Type::U64,
            "f32" => Type::F32,
            "f64" => Type::F64,
            "any" => Type::Tagged,
            _ => Type::Reference(descriptor_id),
        }
    }

    /// Extract the raw FFI type byte for the builder.
    pub(crate) fn as_raw_u8(&self) -> u8 {
        match self {
            Type::Void => sys::Type_TypeId_VOID,
            Type::Bool => sys::Type_TypeId_U1,
            Type::I8 => sys::Type_TypeId_I8,
            Type::U8 => sys::Type_TypeId_U8,
            Type::I16 => sys::Type_TypeId_I16,
            Type::U16 => sys::Type_TypeId_U16,
            Type::I32 => sys::Type_TypeId_I32,
            Type::U32 => sys::Type_TypeId_U32,
            Type::F32 => sys::Type_TypeId_F32,
            Type::F64 => sys::Type_TypeId_F64,
            Type::I64 => sys::Type_TypeId_I64,
            Type::U64 => sys::Type_TypeId_U64,
            Type::Tagged => sys::Type_TypeId_TAGGED,
            Type::Reference(_) => sys::Type_TypeId_REFERENCE,
        }
    }
}

/// Raw type discriminant for internal FFI use.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub(crate) enum TypeId {
    Void = sys::Type_TypeId_VOID,
    U1 = sys::Type_TypeId_U1,
    I8 = sys::Type_TypeId_I8,
    U8 = sys::Type_TypeId_U8,
    I16 = sys::Type_TypeId_I16,
    U16 = sys::Type_TypeId_U16,
    I32 = sys::Type_TypeId_I32,
    U32 = sys::Type_TypeId_U32,
    F32 = sys::Type_TypeId_F32,
    F64 = sys::Type_TypeId_F64,
    I64 = sys::Type_TypeId_I64,
    U64 = sys::Type_TypeId_U64,
    Reference = sys::Type_TypeId_REFERENCE,
    Tagged = sys::Type_TypeId_TAGGED,
}

impl TryFrom<u8> for TypeId {
    type Error = Error;
    fn try_from(v: u8) -> Result<Self, Error> {
        match v {
            x if x == Self::Void as u8 => Ok(Self::Void),
            x if x == Self::U1 as u8 => Ok(Self::U1),
            x if x == Self::I8 as u8 => Ok(Self::I8),
            x if x == Self::U8 as u8 => Ok(Self::U8),
            x if x == Self::I16 as u8 => Ok(Self::I16),
            x if x == Self::U16 as u8 => Ok(Self::U16),
            x if x == Self::I32 as u8 => Ok(Self::I32),
            x if x == Self::U32 as u8 => Ok(Self::U32),
            x if x == Self::F32 as u8 => Ok(Self::F32),
            x if x == Self::F64 as u8 => Ok(Self::F64),
            x if x == Self::I64 as u8 => Ok(Self::I64),
            x if x == Self::U64 as u8 => Ok(Self::U64),
            x if x == Self::Reference as u8 => Ok(Self::Reference),
            x if x == Self::Tagged as u8 => Ok(Self::Tagged),
            _ => Err(Error::UnknownTypeId(v)),
        }
    }
}

/// Source language of a class or method.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum SourceLang {
    EcmaScript = sys::SourceLang_ECMASCRIPT,
    PandaAssembly = sys::SourceLang_PANDA_ASSEMBLY,
    JavaScript = sys::SourceLang_JAVASCRIPT,
    TypeScript = sys::SourceLang_TYPESCRIPT,
    ArkTs = sys::SourceLang_ARKTS,
}

impl TryFrom<u8> for SourceLang {
    type Error = Error;
    fn try_from(v: u8) -> Result<Self, Error> {
        match v {
            x if x == Self::EcmaScript as u8 => Ok(Self::EcmaScript),
            x if x == Self::PandaAssembly as u8 => Ok(Self::PandaAssembly),
            x if x == Self::JavaScript as u8 => Ok(Self::JavaScript),
            x if x == Self::TypeScript as u8 => Ok(Self::TypeScript),
            x if x == Self::ArkTs as u8 => Ok(Self::ArkTs),
            _ => Err(Error::UnknownSourceLang(v)),
        }
    }
}

/// Function kind (arrow, generator, async, etc.).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum FunctionKind {
    None = sys::FunctionKind_NONE,
    Function = sys::FunctionKind_FUNCTION,
    NcFunction = sys::FunctionKind_NC_FUNCTION,
    GeneratorFunction = sys::FunctionKind_GENERATOR_FUNCTION,
    AsyncFunction = sys::FunctionKind_ASYNC_FUNCTION,
    AsyncGeneratorFunction = sys::FunctionKind_ASYNC_GENERATOR_FUNCTION,
    AsyncNcFunction = sys::FunctionKind_ASYNC_NC_FUNCTION,
    ConcurrentFunction = sys::FunctionKind_CONCURRENT_FUNCTION,
    SendableFunction = sys::FunctionKind_SENDABLE_FUNCTION,
}

impl TryFrom<u8> for FunctionKind {
    type Error = Error;
    fn try_from(v: u8) -> Result<Self, Error> {
        match v {
            x if x == Self::None as u8 => Ok(Self::None),
            x if x == Self::Function as u8 => Ok(Self::Function),
            x if x == Self::NcFunction as u8 => Ok(Self::NcFunction),
            x if x == Self::GeneratorFunction as u8 => Ok(Self::GeneratorFunction),
            x if x == Self::AsyncFunction as u8 => Ok(Self::AsyncFunction),
            x if x == Self::AsyncGeneratorFunction as u8 => Ok(Self::AsyncGeneratorFunction),
            x if x == Self::AsyncNcFunction as u8 => Ok(Self::AsyncNcFunction),
            x if x == Self::ConcurrentFunction as u8 => Ok(Self::ConcurrentFunction),
            x if x == Self::SendableFunction as u8 => Ok(Self::SendableFunction),
            _ => Err(Error::UnknownFunctionKind(v)),
        }
    }
}

// ─── Display impls ──────────────────────────────────────────────────────────

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Void => f.write_str("void"),
            Type::Bool => f.write_str("u1"),
            Type::I8 => f.write_str("i8"),
            Type::U8 => f.write_str("u8"),
            Type::I16 => f.write_str("i16"),
            Type::U16 => f.write_str("u16"),
            Type::I32 => f.write_str("i32"),
            Type::U32 => f.write_str("u32"),
            Type::I64 => f.write_str("i64"),
            Type::U64 => f.write_str("u64"),
            Type::F32 => f.write_str("f32"),
            Type::F64 => f.write_str("f64"),
            Type::Tagged => f.write_str("any"),
            // Reference types need a StringPool to display the descriptor;
            // fall back to the raw symbol index.
            Type::Reference(sid) => write!(f, "ref({})", sid.to_usize()),
        }
    }
}

impl std::fmt::Display for SourceLang {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SourceLang::EcmaScript => f.write_str("ecmascript"),
            SourceLang::PandaAssembly => f.write_str("panda_assembly"),
            SourceLang::JavaScript => f.write_str("javascript"),
            SourceLang::TypeScript => f.write_str("typescript"),
            SourceLang::ArkTs => f.write_str("arkts"),
        }
    }
}

impl std::fmt::Display for FunctionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FunctionKind::None => f.write_str("none"),
            FunctionKind::Function => f.write_str("function"),
            FunctionKind::NcFunction => f.write_str("nc_function"),
            FunctionKind::GeneratorFunction => f.write_str("generator"),
            FunctionKind::AsyncFunction => f.write_str("async"),
            FunctionKind::AsyncGeneratorFunction => f.write_str("async_generator"),
            FunctionKind::AsyncNcFunction => f.write_str("async_nc"),
            FunctionKind::ConcurrentFunction => f.write_str("concurrent"),
            FunctionKind::SendableFunction => f.write_str("sendable"),
        }
    }
}
