/// Errors from ABC file operations.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// Failed to open or parse an ABC file (reason from the C++ side).
    #[error("failed to open ABC file: {0}")]
    Open(String),
    /// An entity offset does not point to a valid entity.
    #[error("invalid entity offset {0:#x}")]
    InvalidOffset(u32),
    /// String at the given offset could not be read.
    #[error("string at offset {0:#x} is invalid")]
    InvalidString(u32),
    /// Annotation element index is out of range.
    #[error("annotation element index {0} out of range")]
    AnnotationIndex(u32),
    /// Builder finalize failed.
    #[error("builder finalize failed")]
    Finalize,
    /// The builder produced bytes that the reader cannot decode.
    #[error("finalized ABC failed validation: {0}")]
    FinalizeValidation(String),
    #[error("cannot relocate code entity: {0}")]
    CodeRelocation(String),
    #[error("unsupported ABC output version {0}")]
    UnsupportedOutputVersion(crate::Version),
    /// Bytecode encoding failed during encode.
    #[error("bytecode encode error: {0}")]
    BytecodeEncode(String),
    /// A method body contains bytes that the vendored ISA cannot decode.
    #[error("bytecode decode error in method {method_offset:#x}: {source}")]
    BytecodeDecode {
        method_offset: u32,
        #[source]
        source: abcd_isa::DecodeError,
    },
    /// Annotation arrays whose element width cannot be represented by the
    /// current builder ABI.
    #[error("unsupported annotation array element type for tag {tag:#x}")]
    UnsupportedAnnotationArrayType { tag: u8 },
    /// Unknown source language discriminant.
    #[error("unknown source language {0}")]
    UnknownSourceLang(u8),
    /// Unknown type id discriminant.
    #[error("unknown type id {0}")]
    UnknownTypeId(u8),
    /// Unknown function kind discriminant.
    #[error("unknown function kind {0}")]
    UnknownFunctionKind(u8),
    /// Unknown literal tag discriminant.
    #[error("unknown literal tag {0}")]
    UnknownLiteralTag(u8),
    /// A required field is missing (malformed ABC file).
    #[error("missing required {field} in {context}")]
    Malformed {
        field: &'static str,
        context: String,
    },
    /// Module-record blob decode/encode failure (never a silent fallback).
    #[error("module data error: {0}")]
    ModuleData(String),
    /// A field named `typeSummaryOffset` was encountered (N8). Upstream
    /// (`libpandabase/utils/const_value.h:25` `TYPE_SUMMARY_FIELD_NAME`)
    /// defines the name, but its value is a NESTED file offset — it points
    /// to a literal array whose elements are themselves offsets
    /// (arkcompiler_runtime_core 2022-08-18 ISA changelog item 5) — and
    /// upstream has no producer (es2panda never emits it) and no consumer
    /// (`TYPE_SUMMARY_OFFSET_NOT_FOUND` is a dead constant; the
    /// disassembler excludes it). Relocation of the nested indirection is
    /// unsupported, so decode fails loudly instead of passing a raw scalar
    /// through to a dangling rewrite.
    #[error(
        "unsupported `typeSummaryOffset` field on {class_descriptor} at {field_off:#x}: value is a nested file offset (2022-08-18 ISA changelog item 5) with no upstream producer or consumer and relocation is unsupported — please report this file to the abcd-rs maintainers"
    )]
    TypeSummaryOffset {
        class_descriptor: String,
        field_off: u32,
    },
}
