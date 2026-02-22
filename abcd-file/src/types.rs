//! Type enums and access flag constants for the ABC file format.

use std::fmt;

/// ArkCompiler type IDs (type.h).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum TypeId {
    Invalid = 0x00,
    Void = 0x01,
    U1 = 0x02,
    I8 = 0x03,
    U8 = 0x04,
    I16 = 0x05,
    U16 = 0x06,
    I32 = 0x07,
    U32 = 0x08,
    F32 = 0x09,
    F64 = 0x0a,
    I64 = 0x0b,
    U64 = 0x0c,
    Reference = 0x0d,
    Tagged = 0x0e,
}

impl TypeId {
    pub fn from_u8(v: u8) -> Option<Self> {
        match v {
            0x00 => Some(Self::Invalid),
            0x01 => Some(Self::Void),
            0x02 => Some(Self::U1),
            0x03 => Some(Self::I8),
            0x04 => Some(Self::U8),
            0x05 => Some(Self::I16),
            0x06 => Some(Self::U16),
            0x07 => Some(Self::I32),
            0x08 => Some(Self::U32),
            0x09 => Some(Self::F32),
            0x0a => Some(Self::F64),
            0x0b => Some(Self::I64),
            0x0c => Some(Self::U64),
            0x0d => Some(Self::Reference),
            0x0e => Some(Self::Tagged),
            _ => None,
        }
    }
}

impl From<TypeId> for u8 {
    #[inline]
    fn from(v: TypeId) -> Self {
        v as u8
    }
}

/// Source language.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum SourceLang {
    EcmaScript = 0,
    PandaAssembly = 1,
    JavaScript = 2,
    TypeScript = 3,
    ArkTS = 4,
}

impl SourceLang {
    pub fn from_u8(v: u8) -> Option<Self> {
        match v {
            0 => Some(Self::EcmaScript),
            1 => Some(Self::PandaAssembly),
            2 => Some(Self::JavaScript),
            3 => Some(Self::TypeScript),
            4 => Some(Self::ArkTS),
            _ => None,
        }
    }
}

impl From<SourceLang> for u8 {
    #[inline]
    fn from(v: SourceLang) -> Self {
        v as u8
    }
}

/// Function kind (file_items.h).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum FunctionKind {
    None = 0x0,
    Function = 0x1,
    NcFunction = 0x2,
    GeneratorFunction = 0x3,
    AsyncFunction = 0x4,
    AsyncGeneratorFunction = 0x5,
    AsyncNcFunction = 0x6,
    ConcurrentFunction = 0x7,
    SendableFunction = 0x8,
}

impl FunctionKind {
    pub fn from_u8(v: u8) -> Option<Self> {
        match v {
            0x0 => Some(Self::None),
            0x1 => Some(Self::Function),
            0x2 => Some(Self::NcFunction),
            0x3 => Some(Self::GeneratorFunction),
            0x4 => Some(Self::AsyncFunction),
            0x5 => Some(Self::AsyncGeneratorFunction),
            0x6 => Some(Self::AsyncNcFunction),
            0x7 => Some(Self::ConcurrentFunction),
            0x8 => Some(Self::SendableFunction),
            _ => None,
        }
    }
}

impl From<FunctionKind> for u8 {
    #[inline]
    fn from(v: FunctionKind) -> Self {
        v as u8
    }
}

/// Module record tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ModuleTag {
    RegularImport,
    NamespaceImport,
    LocalExport,
    IndirectExport,
    StarExport,
    Unknown(u8),
}

impl ModuleTag {
    pub fn from_u8(v: u8) -> Self {
        match v {
            0x00 => Self::RegularImport,
            0x01 => Self::NamespaceImport,
            0x02 => Self::LocalExport,
            0x03 => Self::IndirectExport,
            0x04 => Self::StarExport,
            _ => Self::Unknown(v),
        }
    }
}

// --- Display impls ---

impl fmt::Display for TypeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Invalid => "invalid",
            Self::Void => "void",
            Self::U1 => "u1",
            Self::I8 => "i8",
            Self::U8 => "u8",
            Self::I16 => "i16",
            Self::U16 => "u16",
            Self::I32 => "i32",
            Self::U32 => "u32",
            Self::F32 => "f32",
            Self::F64 => "f64",
            Self::I64 => "i64",
            Self::U64 => "u64",
            Self::Reference => "ref",
            Self::Tagged => "tagged",
        })
    }
}

impl fmt::Display for SourceLang {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::EcmaScript => "EcmaScript",
            Self::PandaAssembly => "PandaAssembly",
            Self::JavaScript => "JavaScript",
            Self::TypeScript => "TypeScript",
            Self::ArkTS => "ArkTS",
        })
    }
}

impl fmt::Display for FunctionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::None => "none",
            Self::Function => "function",
            Self::NcFunction => "nc_function",
            Self::GeneratorFunction => "generator",
            Self::AsyncFunction => "async",
            Self::AsyncGeneratorFunction => "async_generator",
            Self::AsyncNcFunction => "async_nc",
            Self::ConcurrentFunction => "concurrent",
            Self::SendableFunction => "sendable",
        })
    }
}

impl fmt::Display for ModuleTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RegularImport => f.write_str("regular_import"),
            Self::NamespaceImport => f.write_str("namespace_import"),
            Self::LocalExport => f.write_str("local_export"),
            Self::IndirectExport => f.write_str("indirect_export"),
            Self::StarExport => f.write_str("star_export"),
            Self::Unknown(v) => write!(f, "unknown({v:#x})"),
        }
    }
}

// Access flag constants (modifiers.h)

pub const ACC_PUBLIC: u32 = 0x0001;
pub const ACC_PRIVATE: u32 = 0x0002;
pub const ACC_PROTECTED: u32 = 0x0004;
pub const ACC_STATIC: u32 = 0x0008;
pub const ACC_FINAL: u32 = 0x0010;
/// Super — class.
pub const ACC_SUPER: u32 = 0x0020;
/// Synchronized — method (same bit as ACC_SUPER).
pub const ACC_SYNCHRONIZED: u32 = 0x0020;
/// Bridge method (same bit as ACC_VOLATILE).
pub const ACC_BRIDGE: u32 = 0x0040;
/// Volatile field (same bit as ACC_BRIDGE).
pub const ACC_VOLATILE: u32 = 0x0040;
/// Transient field (same bit as ACC_VARARGS).
pub const ACC_TRANSIENT: u32 = 0x0080;
/// Varargs method (same bit as ACC_TRANSIENT).
pub const ACC_VARARGS: u32 = 0x0080;
pub const ACC_NATIVE: u32 = 0x0100;
pub const ACC_INTERFACE: u32 = 0x0200;
pub const ACC_ABSTRACT: u32 = 0x0400;
pub const ACC_STRICT: u32 = 0x0800;
pub const ACC_SYNTHETIC: u32 = 0x1000;
pub const ACC_ANNOTATION: u32 = 0x2000;
pub const ACC_ENUM: u32 = 0x4000;
pub const ACC_FILE_MASK: u32 = 0xFFFF;
