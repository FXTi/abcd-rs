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
    /// A `LiteralValue::LiteralArray` nested inside an annotation-embedded
    /// literal array (c-COV W5 ruling). Upstream pandasm has no
    /// representation for this shape and the vendored writer/reader pair
    /// corrupts it on encode → decode: every item after the nested
    /// reference decodes shifted and the reference itself resolves to a
    /// wrong array. Encode rejects it before writing anything (hard-errors
    /// rule). Top-level (model) literal-array nesting is unaffected.
    #[error(
        "annotation {annotation} element '{element_name}' on {owner}: literal-array item {item_index} is a nested literal array (model table index {nested_index}), which has no representation inside annotation-embedded literal arrays"
    )]
    NestedLiteralArrayInAnnotation {
        /// Descriptor of the annotation class carrying the embedded array.
        annotation: String,
        /// Name of the annotation element carrying the embedded array.
        element_name: String,
        /// Entity the annotation is attached to (class, method, field, or
        /// method parameter).
        owner: String,
        /// Index of the offending item within the embedded literal array.
        item_index: usize,
        /// Model table index the nested reference points at.
        nested_index: u32,
    },
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
    /// A field named `typeSummaryOffset` cannot be REWRITTEN (N8, revised
    /// after the wild-OHOS sweep). Its value is a NESTED file offset — it
    /// points to a literal array whose elements are themselves offsets of
    /// the type literal arrays (arkcompiler_runtime_core 2022-08-18 ISA
    /// changelog item 5; name from vendored
    /// `libpandabase/utils/const_value.h:25` `TYPE_SUMMARY_FIELD_NAME`).
    /// Wild 4.x–5.x es2abc emits the field on AbilityStage/Application
    /// records, so DECODE models it opaquely
    /// ([`crate::FieldValue::TypeSummaryOffset`]); but relocation of the
    /// nested indirection is unsupported, so encode fails loudly instead
    /// of emitting a stale offset that would dangle in the rewritten file.
    #[error(
        "cannot rewrite `typeSummaryOffset` field on {class_descriptor} at {field_off:#x}: value is a nested file offset (2022-08-18 ISA changelog item 5) and relocation is unsupported — decode reads it opaquely, but the rewritten file would carry a dangling offset"
    )]
    TypeSummaryOffset {
        class_descriptor: String,
        field_off: u32,
    },
    /// The vendored debug-info extractor failed to initialize (N55,
    /// second half). The extractor throws `INVALID_FILE_OFFSET`
    /// (`GetSpanFromId`, vendored file.h:186-193) when a debug item's
    /// line program leaves `file_ = File::EntityId(0)` — e.g. a class
    /// carrying debug items but no source-file record
    /// (debug_info_extractor.cpp:252 `value_or(File::EntityId(0))` →
    /// `LineProgramState::GetFile`) — and the bridge swallows the
    /// exception, returning nullptr (`abc_debug_info_open`,
    /// file_bridge.cpp). A file with NO debug items never throws (the
    /// extractor skips methods without a debug_info_id), so null is
    /// never benign: previously decode treated it as "no debug info",
    /// silently dropping the WHOLE file's debug region. Hard error,
    /// never silent.
    #[error(
        "debug info extraction failed (N55): the vendored extractor threw during initialization (e.g. INVALID_FILE_OFFSET from a debug item with file_=EntityId(0)) — refusing to silently drop the whole file's debug region"
    )]
    DebugInfoExtraction,
}
