use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("File too small: {0} bytes")]
    FileTooSmall(usize),

    #[error("Invalid magic: expected PANDA\\0\\0\\0")]
    InvalidMagic,

    #[error("Unsupported version: {0}")]
    UnsupportedVersion(abcd_isa::Version),

    #[error("Offset {0:#x} out of bounds (file size: {1:#x})")]
    OffsetOutOfBounds(usize, usize),

    #[error("Invalid LEB128 encoding at offset {0:#x}")]
    InvalidLeb128(usize),

    #[error("Invalid MUTF-8 encoding at offset {0:#x}")]
    InvalidMutf8(usize),

    #[error("Invalid tagged value tag {0:#x} at offset {1:#x}")]
    InvalidTag(u8, usize),

    #[error("FFI call failed: {0}")]
    Ffi(String),

    #[error("I/O error: {0}")]
    Io(String),
}

pub type Result<T> = std::result::Result<T, Error>;
