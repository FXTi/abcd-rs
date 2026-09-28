//! Hand-written ZIP central-directory reader for the restricted OpenHarmony
//! container dialect (no spanned archives, no encryption, no ZIP64, methods
//! {STORED, DEFLATE}).
//!
//! Layout of the reader (design §3.2):
//!
//! 1. Scan backwards at most 64 KiB + EOCD for `PK\x05\x06`; a candidate is
//!    only real if its comment length lands exactly on EOF *and* the central
//!    directory it points at walks cleanly — so a fake EOCD magic hidden in
//!    the comment cannot hijack the scan.
//! 2. Walk central headers `PK\x01\x02`: name, method, CRC, sizes,
//!    local-header offset. The walk must consume the declared CD size
//!    exactly.
//! 3. Per entry: seek the local header `PK\x03\x04`, skip name+extra using
//!    the *local* header's lengths, take `compressed_size` bytes of data.
//!
//! Every offset/size computation goes through checked slice access; no
//! input byte pattern can panic the parser.

use std::ops::Range;

use crate::Error;

/// ZIP compression method: stored (no compression).
pub const METHOD_STORED: u16 = 0;
/// ZIP compression method: raw DEFLATE.
pub const METHOD_DEFLATE: u16 = 8;

const LOCAL_SIG: &[u8; 4] = b"PK\x03\x04";
const CD_SIG: &[u8; 4] = b"PK\x01\x02";
const EOCD_SIG: &[u8; 4] = b"PK\x05\x06";
const ZIP64_LOCATOR_SIG: &[u8; 4] = b"PK\x06\x07";

const EOCD_LEN: usize = 22;
const CD_HEADER_LEN: usize = 46;
const LOCAL_HEADER_LEN: usize = 30;
const ZIP64_LOCATOR_LEN: usize = 20;
/// Longest legal EOCD comment; bounds the backward scan window.
const MAX_COMMENT_LEN: usize = 0xFFFF;

/// General-purpose flag bit 0: entry is encrypted.
const FLAG_ENCRYPTED: u16 = 0x1;

fn read_u16(bytes: &[u8], offset: usize) -> Option<u16> {
    let s = bytes.get(offset..offset.checked_add(2)?)?;
    Some(u16::from_le_bytes([s[0], s[1]]))
}

fn read_u32(bytes: &[u8], offset: usize) -> Option<u32> {
    let s = bytes.get(offset..offset.checked_add(4)?)?;
    Some(u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
}

fn sig_at(bytes: &[u8], offset: usize, sig: &[u8; 4]) -> bool {
    offset.checked_add(4).and_then(|end| bytes.get(offset..end)) == Some(&sig[..])
}

/// Metadata for one central-directory entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EntryMeta {
    /// Entry name (lossy-decoded; used as a lookup key only, never as a
    /// filesystem path).
    pub name: String,
    /// Raw ZIP compression method number (`METHOD_STORED` /
    /// `METHOD_DEFLATE`).
    pub method: u16,
    /// Raw general-purpose bit flags.
    pub flags: u16,
    /// CRC-32 as recorded in the central directory (not verified on read).
    pub crc32: u32,
    /// Compressed size in bytes.
    pub compressed_size: u64,
    /// Uncompressed size in bytes.
    pub uncompressed_size: u64,
    /// Absolute offset of the entry's local file header.
    pub local_header_offset: u64,
}

/// How an entry's data is stored; mirrors the design's `Compression`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Compression {
    /// STORED; `data_offset` is the absolute offset of the entry data within
    /// the archive (exposed as an alignment hint; not a container invariant).
    Stored {
        /// Absolute offset of the entry data within the archive bytes.
        data_offset: u64,
    },
    /// DEFLATE (raw deflate stream).
    Deflated,
}

/// Entry payload: borrowed for STORED entries, owned for DEFLATE.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EntryData<'a> {
    /// Zero-copy slice into the archive bytes (STORED entries).
    Borrowed(&'a [u8]),
    /// Inflated data (DEFLATE entries), or owned data lifted out of a nested
    /// container.
    Owned(Vec<u8>),
}

impl<'a> EntryData<'a> {
    /// View the payload as a byte slice.
    pub fn as_slice(&self) -> &[u8] {
        match self {
            EntryData::Borrowed(s) => s,
            EntryData::Owned(v) => v,
        }
    }

    /// Consume into an owned `Vec<u8>`.
    pub fn into_owned(self) -> Vec<u8> {
        match self {
            EntryData::Borrowed(s) => s.to_vec(),
            EntryData::Owned(v) => v,
        }
    }

    /// Lift into an `'static` owned payload (used for nested containers whose
    /// backing bytes do not outlive the caller's archive).
    pub(crate) fn into_static(self) -> EntryData<'static> {
        EntryData::Owned(self.into_owned())
    }
}

/// An in-memory ZIP archive: a parsed central-directory index over the
/// caller's byte slice.
#[derive(Clone, Debug)]
pub struct ZipArchive<'a> {
    data: &'a [u8],
    entries: Vec<EntryMeta>,
}

impl<'a> ZipArchive<'a> {
    /// Parse the central directory of a ZIP archive held in memory.
    ///
    /// Locates the EOCD by scanning backwards (at most 64 KiB plus the EOCD
    /// itself), rejects fake EOCD magics hidden in the comment by validating
    /// CD offset/size/count self-consistency, and tolerates signing-block
    /// junk between the last entry and the central directory.
    pub fn open(bytes: &'a [u8]) -> Result<Self, Error> {
        if bytes.len() < EOCD_LEN {
            return Err(Error::NotZip);
        }
        let window_start = bytes.len().saturating_sub(EOCD_LEN + MAX_COMMENT_LEN);
        // First error from a position-consistent EOCD candidate, nearest to
        // EOF: that is the most plausible real EOCD, so its failure mode is
        // the one worth reporting when no candidate validates.
        let mut candidate_error: Option<Error> = None;
        let mut pos = bytes.len() - EOCD_LEN;
        loop {
            if sig_at(bytes, pos, EOCD_SIG) {
                // Candidate filter: the comment must land exactly on EOF.
                // Magic bytes failing this (e.g. inside entry data) are not
                // EOCDs at all and must not influence error reporting.
                let position_consistent = read_u16(bytes, pos + 20)
                    .map(|cl| pos + EOCD_LEN + cl as usize == bytes.len())
                    .unwrap_or(false);
                if position_consistent {
                    match Self::try_open_at_eocd(bytes, pos) {
                        Ok(archive) => return Ok(archive),
                        Err(err) => {
                            if candidate_error.is_none() {
                                candidate_error = Some(err);
                            }
                        }
                    }
                }
            }
            if pos == window_start {
                break;
            }
            pos -= 1;
        }
        Err(candidate_error.unwrap_or(Error::NotZip))
    }

    /// Validate an EOCD candidate at `pos` (already known to be
    /// position-consistent) and, if self-consistent, walk the central
    /// directory it describes.
    fn try_open_at_eocd(bytes: &'a [u8], pos: usize) -> Result<Self, Error> {
        let disk_no = read_u16(bytes, pos + 4).ok_or(Error::NotZip)?;
        let cd_disk = read_u16(bytes, pos + 6).ok_or(Error::NotZip)?;
        if disk_no != 0 || cd_disk != 0 {
            return Err(Error::MultiDisk);
        }
        let count_on_disk = read_u16(bytes, pos + 8).ok_or(Error::NotZip)?;
        let count = read_u16(bytes, pos + 10).ok_or(Error::NotZip)?;
        let cd_size = read_u32(bytes, pos + 12).ok_or(Error::NotZip)?;
        let cd_offset = read_u32(bytes, pos + 16).ok_or(Error::NotZip)?;

        // ZIP64 sentinels: fail cleanly instead of mis-parsing 32-bit views
        // of 64-bit values.
        if count_on_disk == 0xFFFF
            || count == 0xFFFF
            || cd_size == u32::MAX
            || cd_offset == u32::MAX
        {
            return Err(Error::Zip64);
        }
        // A ZIP64 EOCD locator directly precedes the classic EOCD.
        if pos >= ZIP64_LOCATOR_LEN && sig_at(bytes, pos - ZIP64_LOCATOR_LEN, ZIP64_LOCATOR_SIG) {
            return Err(Error::Zip64);
        }
        if count_on_disk != count {
            return Err(Error::BadCentralDirectory(
                "per-disk and total entry counts differ",
            ));
        }

        let cd_start = cd_offset as usize;
        let cd_end =
            (cd_offset as u64)
                .checked_add(cd_size as u64)
                .ok_or(Error::BadCentralDirectory(
                    "central directory range overflows",
                ))?;
        if cd_end > pos as u64 {
            return Err(Error::BadCentralDirectory(
                "central directory overlaps or passes the EOCD",
            ));
        }
        Self::walk_central_directory(bytes, cd_start, cd_end as usize, count as usize)
    }

    /// Walk `count` central file headers starting at `cd_start`; the walk
    /// must consume the declared CD range exactly.
    fn walk_central_directory(
        bytes: &'a [u8],
        cd_start: usize,
        cd_end: usize,
        count: usize,
    ) -> Result<Self, Error> {
        let mut entries = Vec::with_capacity(count);
        let mut cursor = cd_start;
        for _ in 0..count {
            let fixed_end = cursor
                .checked_add(CD_HEADER_LEN)
                .ok_or(Error::BadCentralDirectory(
                    "central directory offset overflow",
                ))?;
            if fixed_end > cd_end {
                return Err(Error::BadCentralDirectory(
                    "central directory record overruns its declared size",
                ));
            }
            if bytes.get(cursor..fixed_end).is_none() {
                return Err(Error::Truncated {
                    context: "central directory record",
                });
            }
            if !sig_at(bytes, cursor, CD_SIG) {
                return Err(Error::BadCentralDirectory(
                    "bad central file header signature",
                ));
            }
            // Offsets within the fixed 46-byte record; bounds checked above.
            let flags = read_u16(bytes, cursor + 8).ok_or(Error::Truncated {
                context: "central directory record",
            })?;
            let method = read_u16(bytes, cursor + 10).ok_or(Error::Truncated {
                context: "central directory record",
            })?;
            let crc32 = read_u32(bytes, cursor + 16).ok_or(Error::Truncated {
                context: "central directory record",
            })?;
            let compressed_size = read_u32(bytes, cursor + 20).ok_or(Error::Truncated {
                context: "central directory record",
            })?;
            let uncompressed_size = read_u32(bytes, cursor + 24).ok_or(Error::Truncated {
                context: "central directory record",
            })?;
            let name_len = read_u16(bytes, cursor + 28).ok_or(Error::Truncated {
                context: "central directory record",
            })? as usize;
            let extra_len = read_u16(bytes, cursor + 30).ok_or(Error::Truncated {
                context: "central directory record",
            })? as usize;
            let comment_len = read_u16(bytes, cursor + 32).ok_or(Error::Truncated {
                context: "central directory record",
            })? as usize;
            let local_header_offset = read_u32(bytes, cursor + 42).ok_or(Error::Truncated {
                context: "central directory record",
            })?;

            // ZIP64 sentinels at entry level: the real values would live in
            // the extra field, which this dialect does not support.
            if compressed_size == u32::MAX
                || uncompressed_size == u32::MAX
                || local_header_offset == u32::MAX
            {
                return Err(Error::Zip64);
            }

            let record_len = CD_HEADER_LEN
                .checked_add(name_len)
                .and_then(|n| n.checked_add(extra_len))
                .and_then(|n| n.checked_add(comment_len))
                .ok_or(Error::BadCentralDirectory(
                    "central directory offset overflow",
                ))?;
            let record_end = cursor
                .checked_add(record_len)
                .ok_or(Error::BadCentralDirectory(
                    "central directory offset overflow",
                ))?;
            if record_end > cd_end {
                return Err(Error::BadCentralDirectory(
                    "central directory record overruns its declared size",
                ));
            }
            let name_bytes = bytes
                .get(cursor + CD_HEADER_LEN..cursor + CD_HEADER_LEN + name_len)
                .ok_or(Error::Truncated {
                    context: "central directory entry name",
                })?;
            let name = String::from_utf8_lossy(name_bytes).into_owned();

            entries.push(EntryMeta {
                name,
                method,
                flags,
                crc32,
                compressed_size: u64::from(compressed_size),
                uncompressed_size: u64::from(uncompressed_size),
                local_header_offset: u64::from(local_header_offset),
            });
            cursor = record_end;
        }
        if cursor != cd_end {
            return Err(Error::BadCentralDirectory(
                "central directory size mismatch",
            ));
        }
        Ok(ZipArchive {
            data: bytes,
            entries,
        })
    }

    /// Iterate over central-directory entries in archive order.
    pub fn entries(&self) -> impl Iterator<Item = &EntryMeta> {
        self.entries.iter()
    }

    /// Look up an entry by exact name.
    pub fn entry(&self, name: &str) -> Option<&EntryMeta> {
        self.entries.iter().find(|e| e.name == name)
    }

    /// Read (and inflate, if needed) an entry by name.
    pub fn read(&self, name: &str) -> Result<EntryData<'a>, Error> {
        let meta = self
            .entry(name)
            .ok_or_else(|| Error::EntryNotFound(name.to_string()))?;
        self.read_entry(meta)
    }

    /// Read (and inflate, if needed) an entry by metadata.
    ///
    /// CRC is not verified (design §3.3); the data is returned as recorded.
    pub fn read_entry(&self, meta: &EntryMeta) -> Result<EntryData<'a>, Error> {
        if meta.flags & FLAG_ENCRYPTED != 0 {
            return Err(Error::Encrypted {
                name: meta.name.clone(),
            });
        }
        match meta.method {
            METHOD_STORED => {
                let range = self.entry_data_range(meta)?;
                let data = self.data.get(range).ok_or(Error::Truncated {
                    context: "entry data",
                })?;
                Ok(EntryData::Borrowed(data))
            }
            METHOD_DEFLATE => {
                let range = self.entry_data_range(meta)?;
                let data = self.data.get(range).ok_or(Error::Truncated {
                    context: "entry data",
                })?;
                let limit =
                    usize::try_from(meta.uncompressed_size).map_err(|_| Error::EntryTooLarge {
                        name: meta.name.clone(),
                    })?;
                let inflated = miniz_oxide::inflate::decompress_to_vec_with_limit(data, limit)
                    .map_err(|e| Error::Inflate {
                        name: meta.name.clone(),
                        reason: format!("{e:?}"),
                    })?;
                if inflated.len() as u64 != meta.uncompressed_size {
                    return Err(Error::Inflate {
                        name: meta.name.clone(),
                        reason: format!(
                            "inflated size {} does not match central directory {}",
                            inflated.len(),
                            meta.uncompressed_size
                        ),
                    });
                }
                Ok(EntryData::Owned(inflated))
            }
            method => Err(Error::UnsupportedMethod {
                name: meta.name.clone(),
                method,
            }),
        }
    }

    /// Classify how the entry's data is stored; computes the absolute data
    /// offset for STORED entries by consulting the local file header.
    pub fn entry_compression(&self, meta: &EntryMeta) -> Result<Compression, Error> {
        match meta.method {
            METHOD_STORED => {
                let range = self.entry_data_range(meta)?;
                Ok(Compression::Stored {
                    data_offset: range.start as u64,
                })
            }
            METHOD_DEFLATE => Ok(Compression::Deflated),
            method => Err(Error::UnsupportedMethod {
                name: meta.name.clone(),
                method,
            }),
        }
    }

    /// Compute the entry data range from the local file header (whose
    /// name/extra lengths are authoritative and may differ from the CD
    /// record). The range may extend past the input; callers bounds-check at
    /// slice time and report `Truncated`.
    fn entry_data_range(&self, meta: &EntryMeta) -> Result<Range<usize>, Error> {
        let too_large = || Error::EntryTooLarge {
            name: meta.name.clone(),
        };
        let local = usize::try_from(meta.local_header_offset).map_err(|_| too_large())?;
        let fixed_end = local.checked_add(LOCAL_HEADER_LEN).ok_or_else(too_large)?;
        let header = self.data.get(local..fixed_end).ok_or(Error::Truncated {
            context: "local file header",
        })?;
        if header.get(..4) != Some(&LOCAL_SIG[..]) {
            return Err(Error::BadCentralDirectory(
                "local file header signature mismatch",
            ));
        }
        let name_len = read_u16(header, 26).ok_or(Error::Truncated {
            context: "local file header",
        })? as usize;
        let extra_len = read_u16(header, 28).ok_or(Error::Truncated {
            context: "local file header",
        })? as usize;
        let data_start = fixed_end
            .checked_add(name_len)
            .and_then(|n| n.checked_add(extra_len))
            .ok_or_else(too_large)?;
        let compressed = usize::try_from(meta.compressed_size).map_err(|_| too_large())?;
        let data_end = data_start.checked_add(compressed).ok_or_else(too_large)?;
        Ok(data_start..data_end)
    }
}
