/// Errors from container and ZIP operations.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// No end-of-central-directory record was found; the input is not a ZIP
    /// archive (or is truncated past recognition).
    #[error("not a ZIP archive (no end of central directory found)")]
    NotZip,
    /// A structure runs past the end of the input.
    #[error("truncated {context}")]
    Truncated {
        /// Which structure was being read when the input ran out.
        context: &'static str,
    },
    /// The central directory failed structural validation (bad signature,
    /// entry-count mismatch, or size mismatch against the EOCD).
    #[error("malformed central directory: {0}")]
    BadCentralDirectory(&'static str),
    /// An entry's declared sizes cannot be processed (offset arithmetic
    /// overflow or an allocation size that does not fit `usize`).
    #[error("entry {name} is too large to process")]
    EntryTooLarge {
        /// Entry name.
        name: String,
    },
    /// Compression method other than STORED (0) or DEFLATE (8).
    #[error("unsupported compression method {method} for entry {name}")]
    UnsupportedMethod {
        /// Entry name.
        name: String,
        /// Raw ZIP method number.
        method: u16,
    },
    /// The entry has the encryption flag set; encrypted archives are out of
    /// scope for the OpenHarmony container dialect.
    #[error("entry {name} is encrypted, which is not supported")]
    Encrypted {
        /// Entry name.
        name: String,
    },
    /// Multi-disk (spanned) archive markers were found; not supported.
    #[error("multi-disk (spanned) ZIP archives are not supported")]
    MultiDisk,
    /// ZIP64 markers were found (ZIP64 EOCD locator, or 0xFFFF/0xFFFFFFFF
    /// sentinel fields); not supported — reported cleanly instead of being
    /// mis-parsed as 32-bit values.
    #[error("ZIP64 archives are not supported")]
    Zip64,
    /// DEFLATE inflation failed for the named entry (corrupt stream, or the
    /// inflated size does not match the central directory).
    #[error("failed to inflate entry {name}: {reason}")]
    Inflate {
        /// Entry name.
        name: String,
        /// Failure detail.
        reason: String,
    },
    /// The container (or its nested modules) carries no `.abc` entry at all
    /// (neither `ets/modules.abc` nor any per-ability bytecode).
    #[error("no .abc entry found")]
    NoAbcEntry,
    /// `read()` was asked for an entry that does not exist.
    #[error("entry not found: {0}")]
    EntryNotFound(String),
}
