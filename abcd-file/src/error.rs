/// Errors from ABC file operations.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// Failed to open or parse an ABC file.
    #[error("failed to open ABC file")]
    Open,
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
    /// Bytecode encoding failed during encode.
    #[error("bytecode encode error: {0}")]
    BytecodeEncode(String),
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
}
