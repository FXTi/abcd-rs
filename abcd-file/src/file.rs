//! Pure Safe Rust zero-copy `.abc` container reader (`#49`, `#72`).
//!
//! Replaces all C++ `libpandafile` reader FFI handles with bounds-checked
//! cursor readers over `&[u8]`, supporting dynamic (`0.0.0.2`, `0.0.0.3`,
//! `9.0.0.0`–`24.0.0.0`, 60-byte header) and static (`0.0.0.5` 64-byte header,
//! `0.0.0.6` 72-byte header, `0.1.0.7` 72-byte / 60-byte header) containers.

#![forbid(unsafe_code)]

use abcd_file_sys as sys;
use abcd_isa::Version;

use crate::error::Error;
use crate::string_pool::{StringId, StringPool};
use crate::types::{Dialect, TypeId, field_encoding_to_type_id};

const MAGIC: [u8; 8] = *b"PANDA\0\0\0";
const BASE_HEADER_SIZE: usize = 60;
const STATIC_V5_HEADER_SIZE: usize = 64;
const STATIC_V6_V7_HEADER_SIZE: usize = 72;
const INDEX_HEADER_BYTE_SIZE: u64 = 40;
const ABSENT_OFFSET: u32 = u32::MAX;

// ---------------------------------------------------------------------------
// Primitive Little-Endian & LEB128 Slice Readers
// ---------------------------------------------------------------------------

#[inline]
pub(crate) fn read_u8(sp: &mut &[u8]) -> Option<u8> {
    let (&b, rest) = sp.split_first()?;
    *sp = rest;
    Some(b)
}

#[inline]
pub(crate) fn read_u16_le(sp: &mut &[u8]) -> Option<u16> {
    if sp.len() < 2 {
        return None;
    }
    let v = u16::from_le_bytes([sp[0], sp[1]]);
    *sp = &sp[2..];
    Some(v)
}

#[inline]
pub(crate) fn read_u32_le(sp: &mut &[u8]) -> Option<u32> {
    if sp.len() < 4 {
        return None;
    }
    let v = u32::from_le_bytes([sp[0], sp[1], sp[2], sp[3]]);
    *sp = &sp[4..];
    Some(v)
}

#[inline]
pub(crate) fn read_u64_le(sp: &mut &[u8]) -> Option<u64> {
    if sp.len() < 8 {
        return None;
    }
    let v = u64::from_le_bytes([sp[0], sp[1], sp[2], sp[3], sp[4], sp[5], sp[6], sp[7]]);
    *sp = &sp[8..];
    Some(v)
}

#[inline]
pub(crate) fn read_u32_at(data: &[u8], off: usize) -> Option<u32> {
    let bytes = data.get(off..off.checked_add(4)?)?;
    Some(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
}

/// Read an unsigned 32-bit ULEB128 matching `panda::leb128::DecodeUnsigned<uint32_t>`.
#[inline]
pub(crate) fn read_uleb128(sp: &mut &[u8]) -> Option<u32> {
    let mut result = 0u32;
    for i in 0..5usize {
        let &b = sp.get(i)?;
        if i == 4 && b >= 0x10 {
            return None;
        }
        result |= u32::from(b & 0x7f) << (7 * i);
        if (b & 0x80) == 0 {
            *sp = &sp[i + 1..];
            return Some(result);
        }
    }
    None
}

/// Read a signed 32-bit SLEB128 matching `panda::leb128::DecodeSigned<int32_t>`.
#[inline]
pub(crate) fn read_sleb128_i32(sp: &mut &[u8]) -> Option<i32> {
    let mut result = 0u32;
    for i in 0..5usize {
        let &b = sp.get(i)?;
        if i == 4 {
            if (b & 0x80) != 0 {
                return None;
            }
            let top = b & 0x78;
            if top != 0 && top != 0x78 {
                return None;
            }
        }
        result |= u32::from(b & 0x7f) << (7 * i);
        if (b & 0x80) == 0 {
            let shift = 7 * (i + 1);
            if shift < 32 && (b & 0x40) != 0 {
                result |= !0u32 << shift;
            }
            *sp = &sp[i + 1..];
            return Some(result as i32);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Adler-32 Checksum & Standalone File-Type Detection
// ---------------------------------------------------------------------------

/// Compute upstream `panda_file::File` Adler-32 (seed `1`, modulo `65521`)
/// over `payload` (`&data[12..file_size]`, skipping 8-byte magic + 4-byte checksum).
#[must_use]
pub fn adler32_abc(payload: &[u8]) -> u32 {
    const MOD: u64 = 65_521;
    const NMAX: usize = 5_552;
    let mut a = 1u64;
    let mut b = 0u64;
    for chunk in payload.chunks(NMAX) {
        for &byte in chunk {
            a += u64::from(byte);
            b += a;
        }
        a %= MOD;
        b %= MOD;
    }
    ((b << 16) | a) as u32
}

/// Validate the header Adler-32 checksum of an `.abc` buffer (`data[8..12]`
/// vs. `adler32(1, &data[12..file_size])`).
#[must_use]
pub fn validate_checksum(data: &[u8]) -> bool {
    if data.len() < BASE_HEADER_SIZE || data[..8] != MAGIC {
        return false;
    }
    let Some(expected) = read_u32_at(data, 8) else {
        return false;
    };
    let Some(file_size) = read_u32_at(data, 16) else {
        return false;
    };
    let fsize = file_size as usize;
    if fsize < BASE_HEADER_SIZE || fsize > data.len() {
        return false;
    }
    adler32_abc(&data[12..fsize]) == expected
}

/// Quick header check returning the file type (`Dynamic`, `Static`, or `Invalid`)
/// without decoding container items (`#49`).
///
/// Validates magic, declared `file_size <= data.len()` (accepting trailing
/// zero-alignment padding as well as exact-length buffers), and header table
/// bounds across dynamic (`60B`) and static (`0.0.0.5` `64B`, `0.0.0.6` `72B`,
/// `0.1.0.7` `60B`/`72B`) layouts.
#[must_use]
pub fn file_type(data: &[u8]) -> sys::FileType {
    match AbcReader::open(data) {
        Ok(reader) => reader.file_type(),
        Err(_) => sys::FileType::Invalid,
    }
}

// ---------------------------------------------------------------------------
// Header & Index-Section Structures
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
struct IndexRegion {
    start: u32,
    end: u32,
    class_idx_size: u32,
    class_idx_off: u32,
    method_idx_size: u32,
    method_idx_off: u32,
    field_idx_size: u32,
    field_idx_off: u32,
    proto_idx_size: u32,
    proto_idx_off: u32,
}

#[derive(Clone, Copy, Debug)]
struct RawHeader {
    header_size: u32,
    checksum: u32,
    version: Version,
    file_size: u32,
    foreign_off: u32,
    foreign_size: u32,
    num_classes: u32,
    class_idx_off: u32,
    export_raw_size: u32,
    export_elem_size: u64,
    export_off: u32,
    num_lnps: u32,
    lnp_idx_off: u32,
    num_literalarrays: u32,
    literalarray_idx_off: u32,
    num_indexes: u32,
    index_section_off: u32,
}

#[inline]
fn check_table(
    off: u32,
    count: u32,
    elem_size: u64,
    align: u32,
    min_off: u32,
    fsize: u64,
    allow_sentinel: bool,
) -> bool {
    if allow_sentinel && count == u32::MAX {
        return true;
    }
    if count == 0 {
        if allow_sentinel && off == u32::MAX {
            return true;
        }
        return u64::from(off) <= fsize;
    }
    if off < min_off || (align > 1 && !off.is_multiple_of(align)) {
        return false;
    }
    let Some(byte_len) = u64::from(count).checked_mul(elem_size) else {
        return false;
    };
    byte_len <= fsize && u64::from(off) <= fsize - byte_len
}

fn parse_and_validate_layout(
    raw: &[u8],
    header_size: usize,
    export_elem_size: u64,
) -> Result<RawHeader, Error> {
    if raw.len() < header_size {
        return Err(Error::Open(format!(
            "buffer too small for .abc header ({} < {header_size} bytes)",
            raw.len()
        )));
    }
    let checksum = read_u32_at(raw, 8).ok_or_else(|| Error::Open("truncated header".into()))?;
    let version = Version::new(raw[12], raw[13], raw[14], raw[15]);
    let file_size = read_u32_at(raw, 16).ok_or_else(|| Error::Open("truncated header".into()))?;
    if (file_size as usize) < header_size || (file_size as usize) > raw.len() {
        return Err(Error::Open(format!(
            "declared file_size ({file_size}) out of range ({header_size}..={})",
            raw.len()
        )));
    }
    let foreign_off = read_u32_at(raw, 20).unwrap_or(0);
    let foreign_size = read_u32_at(raw, 24).unwrap_or(0);

    let (
        num_classes,
        class_idx_off,
        export_raw_size,
        export_off,
        num_lnps,
        lnp_idx_off,
        num_literalarrays,
        literalarray_idx_off,
        num_indexes,
        index_section_off,
    ) = match header_size {
        BASE_HEADER_SIZE => (
            read_u32_at(raw, 28).unwrap_or(0),
            read_u32_at(raw, 32).unwrap_or(0),
            0,
            0,
            read_u32_at(raw, 36).unwrap_or(0),
            read_u32_at(raw, 40).unwrap_or(0),
            read_u32_at(raw, 44).unwrap_or(0),
            read_u32_at(raw, 48).unwrap_or(0),
            read_u32_at(raw, 52).unwrap_or(0),
            read_u32_at(raw, 56).unwrap_or(0),
        ),
        STATIC_V5_HEADER_SIZE => (
            read_u32_at(raw, 32).unwrap_or(0),
            read_u32_at(raw, 36).unwrap_or(0),
            0,
            0,
            read_u32_at(raw, 40).unwrap_or(0),
            read_u32_at(raw, 44).unwrap_or(0),
            read_u32_at(raw, 48).unwrap_or(0),
            read_u32_at(raw, 52).unwrap_or(0),
            read_u32_at(raw, 56).unwrap_or(0),
            read_u32_at(raw, 60).unwrap_or(0),
        ),
        STATIC_V6_V7_HEADER_SIZE => (
            read_u32_at(raw, 32).unwrap_or(0),
            read_u32_at(raw, 36).unwrap_or(0),
            read_u32_at(raw, 40).unwrap_or(0),
            read_u32_at(raw, 44).unwrap_or(0),
            read_u32_at(raw, 48).unwrap_or(0),
            read_u32_at(raw, 52).unwrap_or(0),
            read_u32_at(raw, 56).unwrap_or(0),
            read_u32_at(raw, 60).unwrap_or(0),
            read_u32_at(raw, 64).unwrap_or(0),
            read_u32_at(raw, 68).unwrap_or(0),
        ),
        _ => unreachable!("unsupported header_size"),
    };

    let min_off = header_size as u32;
    let fsize = u64::from(file_size);

    if !check_table(foreign_off, foreign_size, 1, 1, min_off, fsize, false) {
        return Err(Error::Open("invalid foreign region in header".into()));
    }
    if !check_table(class_idx_off, num_classes, 4, 4, min_off, fsize, false) {
        return Err(Error::Open("invalid class index table in header".into()));
    }
    if header_size == STATIC_V6_V7_HEADER_SIZE
        && ((export_elem_size == 1
            && export_raw_size != u32::MAX
            && !export_raw_size.is_multiple_of(4))
            || !check_table(
                export_off,
                export_raw_size,
                export_elem_size,
                4,
                min_off,
                fsize,
                true,
            ))
    {
        return Err(Error::Open("invalid export table in static header".into()));
    }
    if !check_table(lnp_idx_off, num_lnps, 4, 4, min_off, fsize, false) {
        return Err(Error::Open("invalid lnp index table in header".into()));
    }
    if !check_table(
        literalarray_idx_off,
        num_literalarrays,
        4,
        4,
        min_off,
        fsize,
        true,
    ) {
        return Err(Error::Open(
            "invalid literalarray index table in header".into(),
        ));
    }
    if !check_table(
        index_section_off,
        num_indexes,
        INDEX_HEADER_BYTE_SIZE,
        4,
        min_off,
        fsize,
        false,
    ) {
        return Err(Error::Open("invalid index section table in header".into()));
    }

    Ok(RawHeader {
        header_size: min_off,
        checksum,
        version,
        file_size,
        foreign_off,
        foreign_size,
        num_classes,
        class_idx_off,
        export_raw_size,
        export_elem_size,
        export_off,
        num_lnps,
        lnp_idx_off,
        num_literalarrays,
        literalarray_idx_off,
        num_indexes,
        index_section_off,
    })
}

// ---------------------------------------------------------------------------
// Zero-Copy AbcReader
// ---------------------------------------------------------------------------

/// Pure Safe Rust zero-copy reader over a validated `.abc` byte slice.
pub(crate) struct AbcReader<'a> {
    data: &'a [u8],
    header: RawHeader,
    file_type: sys::FileType,
    index_regions: Vec<IndexRegion>,
}

impl<'a> AbcReader<'a> {
    /// Validate header and index-section subtables and open a zero-copy reader.
    pub fn open(raw: &'a [u8]) -> Result<Self, Error> {
        if raw.len() < BASE_HEADER_SIZE {
            return Err(Error::Open(format!(
                "buffer too small for .abc header ({} < {BASE_HEADER_SIZE} bytes)",
                raw.len()
            )));
        }
        if raw[..8] != MAGIC {
            return Err(Error::Open(
                "bad magic bytes (expected PANDA\\0\\0\\0)".into(),
            ));
        }

        let version = Version::new(raw[12], raw[13], raw[14], raw[15]);
        let header = match version.as_bytes() {
            [0, 0, 0, 5] => parse_and_validate_layout(raw, STATIC_V5_HEADER_SIZE, 0)?,
            [0, 0, 0, 6] => parse_and_validate_layout(raw, STATIC_V6_V7_HEADER_SIZE, 4)?,
            [0, 1, 0, 7] => {
                // Real HarmonyOS 7.0 `0.1.0.7` containers use a 72-byte header
                // (`export_raw_size` in bytes); synthetic L1 fixtures built by
                // patching `12..16` on a 60-byte dynamic header fall back cleanly.
                match parse_and_validate_layout(raw, STATIC_V6_V7_HEADER_SIZE, 1) {
                    Ok(h) => h,
                    Err(_) => parse_and_validate_layout(raw, BASE_HEADER_SIZE, 0)?,
                }
            }
            _ => parse_and_validate_layout(raw, BASE_HEADER_SIZE, 0)?,
        };

        let fsize = header.file_size as usize;
        let data = &raw[..fsize];
        let fsize_u64 = u64::from(header.file_size);

        let mut index_regions = Vec::with_capacity(header.num_indexes as usize);
        let base_ih = header.index_section_off as usize;
        for i in 0..(header.num_indexes as usize) {
            let pos = base_ih + i * (INDEX_HEADER_BYTE_SIZE as usize);
            let reg = IndexRegion {
                start: read_u32_at(data, pos).unwrap_or(0),
                end: read_u32_at(data, pos + 4).unwrap_or(0),
                class_idx_size: read_u32_at(data, pos + 8).unwrap_or(0),
                class_idx_off: read_u32_at(data, pos + 12).unwrap_or(0),
                method_idx_size: read_u32_at(data, pos + 16).unwrap_or(0),
                method_idx_off: read_u32_at(data, pos + 20).unwrap_or(0),
                field_idx_size: read_u32_at(data, pos + 24).unwrap_or(0),
                field_idx_off: read_u32_at(data, pos + 28).unwrap_or(0),
                proto_idx_size: read_u32_at(data, pos + 32).unwrap_or(0),
                proto_idx_off: read_u32_at(data, pos + 36).unwrap_or(0),
            };
            let check_sub = |off: u32, count: u32, allow_invalid: bool| -> bool {
                if allow_invalid && count == u32::MAX {
                    return true;
                }
                if count > 0 {
                    let Some(bytes) = u64::from(count).checked_mul(4) else {
                        return false;
                    };
                    if bytes > fsize_u64 || !off.is_multiple_of(4) {
                        return false;
                    }
                }
                true
            };
            if !check_sub(reg.class_idx_off, reg.class_idx_size, false)
                || !check_sub(reg.method_idx_off, reg.method_idx_size, false)
                || !check_sub(reg.field_idx_off, reg.field_idx_size, true)
                || !check_sub(reg.proto_idx_off, reg.proto_idx_size, true)
            {
                return Err(Error::Open("invalid index header subtable".into()));
            }
            index_regions.push(reg);
        }

        let file_type = if Dialect::is_static_version(version) {
            sys::FileType::Static
        } else {
            sys::FileType::Dynamic
        };

        Ok(Self {
            data,
            header,
            file_type,
            index_regions,
        })
    }

    #[inline]
    pub fn bytes(&self) -> &'a [u8] {
        self.data
    }

    #[inline]
    pub fn header_size(&self) -> u32 {
        self.header.header_size
    }

    #[inline]
    pub fn version(&self) -> Version {
        self.header.version
    }

    #[inline]
    pub fn checksum(&self) -> u32 {
        self.header.checksum
    }

    /// Compute Adler-32 over `data[12..file_size]` and compare against `header.checksum`.
    #[inline]
    pub fn compute_checksum(&self) -> u32 {
        adler32_abc(&self.data[12..])
    }

    #[inline]
    pub fn file_size(&self) -> u32 {
        self.header.file_size
    }

    #[inline]
    pub fn file_type(&self) -> sys::FileType {
        self.file_type
    }

    #[inline]
    pub fn get_span(&self, offset: u32) -> Option<&'a [u8]> {
        if offset <= self.header.header_size {
            return None;
        }
        let idx = offset as usize;
        if idx >= self.data.len() {
            return None;
        }
        Some(&self.data[idx..])
    }

    #[inline]
    pub fn is_external(&self, offset: u32) -> bool {
        offset >= self.header.foreign_off
            && (offset - self.header.foreign_off) < self.header.foreign_size
    }

    /// Read `name_off` (`u32` at `entity_off + 4`) of a `ForeignFieldItem` or
    /// `ForeignMethodItem` inside `foreign_off..foreign_off + foreign_size`.
    #[inline]
    pub fn foreign_item_name_off(&self, entity_off: u32) -> Option<u32> {
        if !self.is_external(entity_off) {
            return None;
        }
        let name_off = read_u32_at(self.data, (entity_off as usize).checked_add(4)?)?;
        (name_off != ABSENT_OFFSET).then_some(name_off)
    }

    #[inline]
    pub fn num_classes(&self) -> usize {
        self.header.num_classes as usize
    }

    #[inline]
    pub fn class_off_by_idx(&self, index: usize) -> Option<u32> {
        if index >= self.num_classes() {
            return None;
        }
        let pos = (self.header.class_idx_off as usize) + index * 4;
        read_u32_at(self.data, pos)
    }

    #[cfg(test)]
    pub fn class_offsets(&self) -> Vec<u32> {
        let count = self.num_classes();
        let mut out = Vec::with_capacity(count);
        for i in 0..count {
            if let Some(off) = self.class_off_by_idx(i) {
                out.push(off);
            }
        }
        out
    }

    #[inline]
    pub fn num_lnps(&self) -> usize {
        self.header.num_lnps as usize
    }

    #[inline]
    pub fn lnp_off_by_idx(&self, index: u32) -> Option<u32> {
        let idx = index as usize;
        if idx >= self.num_lnps() {
            return None;
        }
        let pos = (self.header.lnp_idx_off as usize) + idx * 4;
        read_u32_at(self.data, pos)
    }

    #[inline]
    pub fn has_valid_literalarray_table(&self) -> bool {
        if self.header.num_literalarrays == u32::MAX {
            return false;
        }
        check_table(
            self.header.literalarray_idx_off,
            self.header.num_literalarrays,
            4,
            4,
            self.header.header_size,
            u64::from(self.header.file_size),
            false,
        )
    }

    pub fn literal_array_offsets(&self) -> Vec<u32> {
        if !self.has_valid_literalarray_table() {
            return Vec::new();
        }
        let count = self.header.num_literalarrays as usize;
        let base = self.header.literalarray_idx_off as usize;
        let mut out = Vec::with_capacity(count);
        for i in 0..count {
            if let Some(off) = read_u32_at(self.data, base + i * 4) {
                out.push(off);
            }
        }
        out
    }

    /// Check whether `array_off` overlaps any top-level header table
    /// (`foreign`, `class_idx`, `lnp_idx`, `literalarray_idx`, `index_section`,
    /// or static `export_table`), matching `file_bridge.cpp:1747`.
    pub fn overlaps_header_tables(&self, array_off: u32) -> bool {
        let off = u64::from(array_off);
        let in_range = |base: u32, count: u32, elem_size: u64, sentinel: bool| -> bool {
            if sentinel && count == u32::MAX {
                return false;
            }
            if count == 0 {
                return false;
            }
            let b = u64::from(base);
            let Some(len) = u64::from(count).checked_mul(elem_size) else {
                return false;
            };
            off >= b && off < b.saturating_add(len)
        };
        let h = &self.header;
        in_range(h.foreign_off, h.foreign_size, 1, false)
            || in_range(h.class_idx_off, h.num_classes, 4, false)
            || (h.header_size == STATIC_V6_V7_HEADER_SIZE as u32
                && in_range(h.export_off, h.export_raw_size, h.export_elem_size, true))
            || in_range(h.lnp_idx_off, h.num_lnps, 4, false)
            || in_range(h.literalarray_idx_off, h.num_literalarrays, 4, true)
            || in_range(
                h.index_section_off,
                h.num_indexes,
                INDEX_HEADER_BYTE_SIZE,
                false,
            )
    }

    // -- Index-Region Resolution (`File::GetIndexHeader` & `Resolve*Index`) --

    #[inline]
    fn find_region(&self, entity_off: u32) -> Option<&IndexRegion> {
        self.index_regions
            .iter()
            .find(|r| r.start <= entity_off && entity_off < r.end)
    }

    #[inline]
    fn read_region_table(&self, table_off: u32, table_size: u32, idx: u16) -> Option<u32> {
        if table_size == u32::MAX || u32::from(idx) >= table_size {
            return None;
        }
        let fsize = u64::from(self.header.file_size);
        let byte_len = u64::from(table_size) * 4;
        if u64::from(table_off) > fsize
            || byte_len > fsize
            || u64::from(table_off) > fsize - byte_len
        {
            return None;
        }
        let pos = (table_off as usize) + usize::from(idx) * 4;
        read_u32_at(self.data, pos)
    }

    /// Raw `ResolveClassIndex`: returns `None` if `context_off` is outside all
    /// index regions or `idx` is out of bounds; returns `Some(entry)` (which may
    /// be `u32::MAX` or a primitive field encoding `<= 0x0c`) otherwise.
    #[inline]
    pub fn resolve_class_index_raw(&self, context_off: u32, idx: u16) -> Option<u32> {
        let reg = self.find_region(context_off)?;
        self.read_region_table(reg.class_idx_off, reg.class_idx_size, idx)
    }

    /// Resolve a 16-bit class index relative to `context_off`, mapping
    /// `u32::MAX` to `None`.
    #[inline]
    pub fn resolve_class_index(&self, context_off: u32, idx: u16) -> Option<u32> {
        self.resolve_class_index_raw(context_off, idx)
            .filter(|&off| off != ABSENT_OFFSET)
    }

    /// Resolve a 16-bit method/literalarray index relative to `context_off`,
    /// mapping `u32::MAX` to `None`.
    #[inline]
    pub fn resolve_method_index(&self, context_off: u32, idx: u16) -> Option<u32> {
        let reg = self.find_region(context_off)?;
        self.read_region_table(reg.method_idx_off, reg.method_idx_size, idx)
            .filter(|&off| off != ABSENT_OFFSET)
    }

    /// Resolve a 16-bit proto index relative to `context_off` (returns raw
    /// entry including `u32::MAX` when valid, or `None` if OOB / no region).
    #[inline]
    pub fn resolve_proto_index_raw(&self, context_off: u32, idx: u16) -> Option<u32> {
        let reg = self.find_region(context_off)?;
        self.read_region_table(reg.proto_idx_off, reg.proto_idx_size, idx)
    }

    // -- StringItem Decoding (`GetStringData` + `ConvertMUtf8ToUtf16Pair`) --

    /// Raw fallback matching `ClassDataAccessor` descriptor scan (`[uleb128][bytes][0x00]`)
    /// without validating `utf16_len` unit count.
    pub fn raw_cstr_at(&self, offset: u32) -> Option<&'a [u8]> {
        let mut sp = self.get_span(offset)?;
        let _tag = read_uleb128(&mut sp)?;
        let nul_pos = sp.iter().position(|&b| b == 0)?;
        Some(&sp[..nul_pos])
    }

    /// Strictly decode and validate a `StringItem` at `offset` matching
    /// `file_bridge.cpp` `abc_file_get_string_utf16`.
    pub fn read_string_item(
        &self,
        offset: u32,
        utf16_scratch: &mut Vec<u16>,
    ) -> Option<DecodedString<'a>> {
        let mut sp = self.get_span(offset)?;
        let tag_utf16_len = read_uleb128(&mut sp)?;
        let utf16_len = (tag_utf16_len >> 1) as usize;
        let nul_pos = sp.iter().position(|&b| b == 0)?;
        let raw = &sp[..nul_pos];

        if utf16_len == 0 {
            return raw.is_empty().then_some(DecodedString::Utf8Borrowed(""));
        }
        // In MUTF-8/UTF-8, 1 byte produces at most 1 UTF-16 code unit
        // (4-byte sequence produces at most 2 units).
        if utf16_len > raw.len() {
            return None;
        }
        // Zero-copy fast path for pure ASCII strings (>95% of real `.abc` pools):
        // `raw` contains no `0x00`, so every ASCII byte emits 1 UTF-16 unit.
        if raw.is_ascii() {
            if raw.len() != utf16_len {
                return None;
            }
            let s = std::str::from_utf8(raw).ok()?;
            return Some(DecodedString::Utf8Borrowed(s));
        }

        utf16_scratch.clear();
        utf16_scratch.reserve(utf16_len);
        let mut i = 0usize;
        while i < raw.len() {
            if utf16_scratch.len() >= utf16_len {
                return None;
            }
            let d0 = raw[i];
            let rem = raw.len() - i;
            if (d0 & 0x80) == 0 || rem < 2 {
                utf16_scratch.push(u16::from(d0));
                i += 1;
            } else if (d0 & 0x20) == 0 {
                let d1 = raw[i + 1];
                utf16_scratch.push((u16::from(d0 & 0x1f) << 6) | u16::from(d1 & 0x3f));
                i += 2;
            } else if rem < 3 {
                utf16_scratch.push(u16::from(d0));
                i += 1;
            } else if (d0 & 0x10) == 0 {
                let d1 = raw[i + 1];
                let d2 = raw[i + 2];
                utf16_scratch.push(
                    (u16::from(d0 & 0x0f) << 12)
                        | (u16::from(d1 & 0x3f) << 6)
                        | u16::from(d2 & 0x3f),
                );
                i += 3;
            } else if rem < 4 {
                utf16_scratch.push(u16::from(d0));
                i += 1;
            } else {
                let d1 = raw[i + 1];
                let d2 = raw[i + 2];
                let d3 = raw[i + 3];
                let cp = (u32::from(d0 & 0x0f) << 18)
                    | (u32::from(d1 & 0x3f) << 12)
                    | (u32::from(d2 & 0x3f) << 6)
                    | u32::from(d3 & 0x3f);
                let p_hi = ((cp >> 10).wrapping_add(0xd7c0) & 0xffff) as u16;
                let p_lo = ((cp & 0x03ff) | 0xdc00) as u16;
                if p_hi != 0 {
                    if utf16_scratch.len() + 1 >= utf16_len {
                        return None;
                    }
                    utf16_scratch.push(p_hi);
                }
                utf16_scratch.push(p_lo);
                i += 4;
            }
        }

        if utf16_scratch.len() != utf16_len {
            return None;
        }

        match String::from_utf16(utf16_scratch) {
            Ok(s) => Some(DecodedString::Utf8Owned(s)),
            Err(_) => Some(DecodedString::LossyRaw {
                raw,
                lossy: String::from_utf8_lossy(raw).into_owned(),
            }),
        }
    }

    // -- Container Item Accessors --

    /// Parse a non-external `ClassItem` header and tagged metadata stream at
    /// `class_off` (`ClassDataAccessor`).
    pub fn open_class(&self, class_off: u32) -> Option<RawClass<'a>> {
        if self.is_external(class_off) {
            return None;
        }
        let mut sp = self.get_span(class_off)?;
        let _desc_tag = read_uleb128(&mut sp)?;
        let nul_pos = sp.iter().position(|&b| b == 0)?;
        sp = &sp[nul_pos + 1..];

        let super_class_off = read_u32_le(&mut sp)?;
        let access_flags = read_uleb128(&mut sp)?;
        let num_fields = read_uleb128(&mut sp)?;
        let num_methods = read_uleb128(&mut sp)?;

        if sp.is_empty() {
            return None;
        }
        let mut ifaces_sp: &'a [u8] = &[];
        let mut ifaces_count = 0u32;
        while !sp.is_empty() && sp[0] != 0 && sp[0] < 2 {
            let tag = sp[0];
            sp = &sp[1..];
            if tag == 1 {
                let n = read_uleb128(&mut sp)?;
                let byte_len = (n as usize).checked_mul(2)?;
                if sp.len() < byte_len {
                    return None;
                }
                ifaces_sp = &sp[..byte_len];
                ifaces_count = n;
                sp = &sp[byte_len..];
            }
            if sp.is_empty() {
                return None;
            }
        }

        if sp.is_empty() {
            return None;
        }
        let source_lang = if sp[0] == 2 {
            if sp.len() < 2 {
                return None;
            }
            let lang = sp[1];
            sp = &sp[2..];
            Some(lang)
        } else {
            None
        };

        let runtime_annotations = read_tagged_u32_list(&mut sp, 3)?;
        let annotations = read_tagged_u32_list(&mut sp, 4)?;
        let runtime_type_annotations = read_tagged_u32_list(&mut sp, 5)?;
        let type_annotations = read_tagged_u32_list(&mut sp, 6)?;

        if sp.is_empty() {
            return None;
        }
        let source_file_off = if sp[0] == 7 {
            sp = &sp[1..];
            Some(read_u32_le(&mut sp)?)
        } else {
            None
        };

        // Advance past `ClassTag::NOTHING` (`TAG_SIZE == 1`) into `fields_sp_`.
        if sp.is_empty() {
            return None;
        }
        sp = &sp[1..];
        let fields_off = self.slice_offset(sp);

        Some(RawClass {
            class_off,
            super_class_off: (super_class_off != 0 && super_class_off != ABSENT_OFFSET)
                .then_some(super_class_off),
            access_flags,
            num_fields,
            num_methods,
            ifaces_sp,
            ifaces_count,
            source_lang,
            source_file_off: source_file_off.filter(|&o| o != 0 && o != ABSENT_OFFSET),
            annotations,
            runtime_annotations,
            type_annotations,
            runtime_type_annotations,
            fields_off,
        })
    }

    /// Enumerate `(field_offsets, method_offsets)` of `cls`, returning `Err(())`
    /// if any inline `FieldItem` or `MethodItem` is truncated or malformed.
    pub fn enumerate_class_members(
        &self,
        cls: &RawClass<'a>,
    ) -> Result<(Vec<RawField>, Vec<RawMethod>), ()> {
        let mut cur_off = cls.fields_off;
        let rem_for_fields = (self.data.len()).saturating_sub(cur_off as usize);
        if (cls.num_fields as usize) > rem_for_fields / 8 {
            return Err(());
        }
        let mut fields = Vec::with_capacity(cls.num_fields as usize);
        for _ in 0..cls.num_fields {
            let f = self.open_field(cur_off).ok_or(())?;
            cur_off = cur_off.checked_add(f.byte_size).ok_or(())?;
            fields.push(f);
        }

        let rem_for_methods = (self.data.len()).saturating_sub(cur_off as usize);
        if (cls.num_methods as usize) > rem_for_methods / 8 {
            return Err(());
        }
        let mut methods = Vec::with_capacity(cls.num_methods as usize);
        for _ in 0..cls.num_methods {
            let m = self.open_method(cur_off).ok_or(())?;
            cur_off = cur_off.checked_add(m.byte_size).ok_or(())?;
            methods.push(m);
        }

        Ok((fields, methods))
    }

    /// Parse a `FieldItem` at `field_off` (`FieldDataAccessor`).
    pub fn open_field(&self, field_off: u32) -> Option<RawField> {
        let start_sp = self.get_span(field_off)?;
        let mut sp = start_sp;
        let class_idx = read_u16_le(&mut sp)?;
        let type_idx = read_u16_le(&mut sp)?;
        let name_off = read_u32_le(&mut sp)?;

        // Match `FieldDataAccessor` ctor: `ResolveClassIndex` runs eagerly on
        // both `class_idx_` and `type_idx_` and throws if out of region bounds.
        let _class_off = self.resolve_class_index_raw(field_off, class_idx)?;
        let type_raw = self.resolve_class_index_raw(field_off, type_idx)?;
        let type_id = field_encoding_to_type_id(type_raw);
        let is_external = self.is_external(field_off);

        if is_external {
            return Some(RawField {
                offset: field_off,
                name_off,
                type_id,
                type_off: type_raw,
                access_flags: 0,
                is_external: true,
                raw_value: None,
                annotations: Vec::new(),
                runtime_annotations: Vec::new(),
                byte_size: 8,
            });
        }

        let access_flags = read_uleb128(&mut sp)?;
        if sp.is_empty() {
            return None;
        }

        let raw_value = match sp[0] {
            1 => {
                // `FieldTag::INT_VALUE`: SLEB128 i32 value.
                sp = &sp[1..];
                let v = read_sleb128_i32(&mut sp)?;
                Some(RawFieldValue::Int(v))
            }
            2 => {
                // `FieldTag::VALUE`: inline u32 or indirect u64 for 64-bit types.
                sp = &sp[1..];
                if matches!(type_id, TypeId::I64 | TypeId::U64 | TypeId::F64) {
                    let val_off = read_u32_le(&mut sp)?;
                    let mut val_sp = self.get_span(val_off)?;
                    let v64 = read_u64_le(&mut val_sp)?;
                    Some(RawFieldValue::Bits64(v64))
                } else {
                    let v32 = read_u32_le(&mut sp)?;
                    Some(RawFieldValue::Bits32(v32))
                }
            }
            _ => None,
        };

        let runtime_annotations = read_tagged_u32_list(&mut sp, 3)?;
        let annotations = read_tagged_u32_list(&mut sp, 4)?;
        // Note: upstream `FieldDataAccessor::Enumerate{Runtime,}TypeAnnotations`
        // also filters `FieldTag::ANNOTATION` (`0x04`), so type buckets stay empty
        // and `size_ = cur_off - field_off + 1` consumes the trailing tag byte.
        if sp.is_empty() {
            return None;
        }
        sp = &sp[1..];
        let byte_size = (start_sp.len() - sp.len()) as u32;

        Some(RawField {
            offset: field_off,
            name_off,
            type_id,
            type_off: type_raw,
            access_flags,
            is_external: false,
            raw_value,
            annotations,
            runtime_annotations,
            byte_size,
        })
    }

    /// Parse a `MethodItem` at `method_off` (`MethodDataAccessor`).
    pub fn open_method(&self, method_off: u32) -> Option<RawMethod> {
        let start_sp = self.get_span(method_off)?;
        let mut sp = start_sp;
        let _class_idx = read_u16_le(&mut sp)?;
        let proto_idx = read_u16_le(&mut sp)?;
        let name_off = read_u32_le(&mut sp)?;
        let access_flags = read_uleb128(&mut sp)?;
        let is_external = self.is_external(method_off);

        if is_external {
            let byte_size = (start_sp.len() - sp.len()) as u32;
            return Some(RawMethod {
                offset: method_off,
                proto_idx,
                name_off,
                access_flags,
                is_external: true,
                code_off: None,
                source_lang: None,
                debug_info_off: None,
                param_annotations_off: None,
                runtime_param_annotations_off: None,
                annotations: Vec::new(),
                runtime_annotations: Vec::new(),
                type_annotations: Vec::new(),
                runtime_type_annotations: Vec::new(),
                byte_size,
            });
        }

        let code_off = read_optional_tagged_u32(&mut sp, 1)?;
        let source_lang = read_optional_tagged_u8(&mut sp, 2)?;
        let runtime_annotations = read_tagged_u32_list(&mut sp, 3)?;
        let runtime_param_annotations_off = read_optional_tagged_u32(&mut sp, 4)?;
        let debug_info_off = read_optional_tagged_u32(&mut sp, 5)?;
        let annotations = read_tagged_u32_list(&mut sp, 6)?;
        let param_annotations_off = read_optional_tagged_u32(&mut sp, 7)?;
        let type_annotations = read_tagged_u32_list(&mut sp, 8)?;
        let runtime_type_annotations = read_tagged_u32_list(&mut sp, 9)?;

        // Consume trailing `MethodTag::NOTHING` byte (`size_ = cur - method_off + 1`).
        if sp.is_empty() {
            return None;
        }
        sp = &sp[1..];
        let byte_size = (start_sp.len() - sp.len()) as u32;

        Some(RawMethod {
            offset: method_off,
            proto_idx,
            name_off,
            access_flags,
            is_external: false,
            code_off: code_off.filter(|&o| o != ABSENT_OFFSET),
            source_lang,
            debug_info_off: debug_info_off.filter(|&o| o != ABSENT_OFFSET),
            param_annotations_off: param_annotations_off.filter(|&o| o != ABSENT_OFFSET),
            runtime_param_annotations_off: runtime_param_annotations_off
                .filter(|&o| o != ABSENT_OFFSET),
            annotations,
            runtime_annotations,
            type_annotations,
            runtime_type_annotations,
            byte_size,
        })
    }

    /// Resolve a `RawMethod`'s `ProtoItem` offset: returns `None` when
    /// `proto_idx == 0xFFFF` or resolves to `u32::MAX`; returns `Some(0)` if
    /// `proto_idx` is out of region bounds (matching `MethodDataAccessor::GetProtoId`
    /// -> `EntityId(0)` -> `Error::UnknownTypeId(0xFF)`).
    #[inline]
    pub fn method_proto_off(&self, m: &RawMethod) -> Option<u32> {
        if m.proto_idx == u16::MAX {
            return None;
        }
        let raw = self
            .resolve_proto_index_raw(m.offset, m.proto_idx)
            .unwrap_or(0);
        (raw != ABSENT_OFFSET).then_some(raw)
    }

    /// Parse a `ProtoItem` at `proto_off` (`ProtoDataAccessor`).
    ///
    /// Note: upstream `ProtoDataAccessor` ctor is lazy; if `proto_off` is invalid
    /// or its shorty stream is truncated, `open_proto` returns `None`, which
    /// callers map to `Error::UnknownTypeId(0xFF)` on return-type read.
    pub fn open_proto(&self, proto_off: u32) -> Option<RawProto<'a>> {
        let mut sp = self.get_span(proto_off)?;
        let mut shorty = Vec::with_capacity(4);
        let mut num_ref = 0usize;
        let mut v = read_u16_le(&mut sp)?;
        let mut elem_num = 0usize;
        while v != 0 {
            let shift = (elem_num % 4) * 4;
            let elem = ((v >> shift) & 0x0f) as u8;
            if elem == 0 {
                break;
            }
            shorty.push(elem);
            if elem == (TypeId::Reference as u8) {
                num_ref += 1;
            }
            elem_num += 1;
            if elem_num.is_multiple_of(4) {
                v = read_u16_le(&mut sp)?;
            }
        }
        if shorty.is_empty() {
            return None;
        }
        let ref_bytes = num_ref.checked_mul(2)?;
        let ref_types_sp = sp.get(..ref_bytes)?;
        Some(RawProto {
            proto_off,
            shorty,
            ref_types_sp,
        })
    }

    /// Parse a `CodeItem` header at `code_off` (`CodeDataAccessor`).
    pub fn open_code(&self, code_off: u32) -> Option<RawCode<'a>> {
        let mut sp = self.get_span(code_off)?;
        let num_vregs = read_uleb128(&mut sp)?;
        let num_args = read_uleb128(&mut sp)?;
        let code_size = read_uleb128(&mut sp)?;
        let tries_size = read_uleb128(&mut sp)?;
        let csize = code_size as usize;
        if sp.len() < csize {
            return None;
        }
        let insns_off = self.slice_offset(sp);
        let instructions = &sp[..csize];
        let try_blocks_sp = &sp[csize..];
        Some(RawCode {
            num_vregs,
            num_args,
            code_size,
            tries_size,
            insns_off,
            instructions,
            try_blocks_sp,
        })
    }

    /// Parse an `AnnotationItem` header at `ann_off` (`AnnotationDataAccessor`).
    pub fn open_annotation(&self, ann_off: u32) -> Option<RawAnnotation<'a>> {
        let sp = self.get_span(ann_off)?;
        if sp.len() < 4 {
            return None;
        }
        let class_idx = u16::from_le_bytes([sp[0], sp[1]]);
        let count = u16::from_le_bytes([sp[2], sp[3]]);
        let total = 4usize + usize::from(count) * 9;
        if sp.len() < total {
            return None;
        }
        let class_off = self
            .resolve_class_index_raw(ann_off, class_idx)
            .unwrap_or(0);
        let elems_end = 4 + usize::from(count) * 8;
        Some(RawAnnotation {
            class_off,
            count,
            elements_sp: &sp[4..elems_end],
            tags_sp: &sp[elems_end..total],
        })
    }

    /// Read an 8-byte indirect scalar (`I64` / `U64` / `F64`) at `value_off`.
    #[inline]
    pub fn read_scalar_u64(&self, value_off: u32) -> Option<u64> {
        let mut sp = self.get_span(value_off)?;
        read_u64_le(&mut sp)
    }

    /// Read a homogeneous annotation `ValueArray` at `entity_off`
    /// (`[uleb128 count][count * elem_size]`, `elem_size` in `{1, 2, 4, 8}`).
    pub fn read_annotation_array(&self, entity_off: u32, elem_size: usize) -> Option<Vec<u64>> {
        let mut sp = self.get_span(entity_off)?;
        let count = read_uleb128(&mut sp)? as usize;
        if count > sp.len() {
            return None;
        }
        let byte_len = count.checked_mul(elem_size)?;
        if byte_len > sp.len() {
            return None;
        }
        let mut out = Vec::with_capacity(count);
        for _ in 0..count {
            let v = match elem_size {
                1 => u64::from(read_u8(&mut sp)?),
                2 => u64::from(read_u16_le(&mut sp)?),
                4 => u64::from(read_u32_le(&mut sp)?),
                8 => read_u64_le(&mut sp)?,
                _ => return None,
            };
            out.push(v);
        }
        Some(out)
    }

    /// Read a `MethodHandleItem` at `mh_off` (`[u8 type][uleb128 entity_off]`).
    pub fn read_method_handle(&self, mh_off: u32) -> Option<(u8, u32)> {
        let mut sp = self.get_span(mh_off)?;
        if sp.len() < 2 {
            return None;
        }
        let mh_type = read_u8(&mut sp)?;
        if mh_type > sys::MethodHandleType_INVOKE_INTERFACE {
            return None;
        }
        let entity_off = read_uleb128(&mut sp)?;
        Some((mh_type, entity_off))
    }

    /// Enumerate `(param_index, annotation_offset)` pairs of a `ParamAnnotationsItem`
    /// at `item_off` (`ParamAnnotationsDataAccessor`).
    pub fn read_param_annotations(&self, item_off: u32) -> Option<Vec<(u32, u32)>> {
        let mut sp = self.get_span(item_off)?;
        let num_params = read_u32_le(&mut sp)?;
        if (num_params as usize) > sp.len() / 4 {
            return None;
        }
        let mut pairs = Vec::new();
        for param_idx in 0..num_params {
            let count = read_u32_le(&mut sp)?;
            let byte_len = (count as usize).checked_mul(4)?;
            if sp.len() < byte_len {
                return None;
            }
            for _ in 0..count {
                let ann_off = read_u32_le(&mut sp)?;
                pairs.push((param_idx, ann_off));
            }
        }
        Some(pairs)
    }

    /// Read a `ModuleLazyImportFlagAccessor` phase-flag blob at `offset`
    /// (`[u32 num_flags][num_flags * u8]`).
    pub fn read_module_request_phase(&self, offset: u32) -> Option<Vec<u8>> {
        let mut sp = self.get_span(offset)?;
        let count = read_u32_le(&mut sp)? as usize;
        let flags = sp.get(..count)?;
        Some(flags.to_vec())
    }

    /// Parse an untagged `ModuleDataAccessor` blob at `offset`.
    pub fn read_module_data(&self, offset: u32) -> Option<RawModuleData> {
        let mut sp = self.get_span(offset)?;
        let _literal_num = read_u32_le(&mut sp)?;
        let num_reqs = read_u32_le(&mut sp)? as usize;
        let req_bytes = num_reqs.checked_mul(4)?;
        if sp.len() < req_bytes {
            return None;
        }
        let mut request_offs = Vec::with_capacity(num_reqs);
        for _ in 0..num_reqs {
            request_offs.push(read_u32_le(&mut sp)?);
        }

        // 5 fixed sections in `module_data_accessor-inl.h` order:
        let mut records = Vec::new();

        // 0: REGULAR_IMPORT `[u32 local][u32 import][u16 req_idx]` (10 B)
        let reg_n = read_u32_le(&mut sp)? as usize;
        if sp.len() < reg_n.checked_mul(10)? {
            return None;
        }
        for _ in 0..reg_n {
            let local_off = read_u32_le(&mut sp)?;
            let import_off = read_u32_le(&mut sp)?;
            let req_idx = u32::from(read_u16_le(&mut sp)?);
            records.push(RawModuleRecord::RegularImport {
                local_off,
                import_off,
                req_idx,
            });
        }

        // 1: NAMESPACE_IMPORT `[u32 local][u16 req_idx]` (6 B)
        let ns_n = read_u32_le(&mut sp)? as usize;
        if sp.len() < ns_n.checked_mul(6)? {
            return None;
        }
        for _ in 0..ns_n {
            let local_off = read_u32_le(&mut sp)?;
            let req_idx = u32::from(read_u16_le(&mut sp)?);
            records.push(RawModuleRecord::NamespaceImport { local_off, req_idx });
        }

        // 2: LOCAL_EXPORT `[u32 local][u32 export]` (8 B)
        let le_n = read_u32_le(&mut sp)? as usize;
        if sp.len() < le_n.checked_mul(8)? {
            return None;
        }
        for _ in 0..le_n {
            let local_off = read_u32_le(&mut sp)?;
            let export_off = read_u32_le(&mut sp)?;
            records.push(RawModuleRecord::LocalExport {
                local_off,
                export_off,
            });
        }

        // 3: INDIRECT_EXPORT `[u32 export][u32 import][u16 req_idx]` (10 B)
        let ie_n = read_u32_le(&mut sp)? as usize;
        if sp.len() < ie_n.checked_mul(10)? {
            return None;
        }
        for _ in 0..ie_n {
            let export_off = read_u32_le(&mut sp)?;
            let import_off = read_u32_le(&mut sp)?;
            let req_idx = u32::from(read_u16_le(&mut sp)?);
            records.push(RawModuleRecord::IndirectExport {
                export_off,
                import_off,
                req_idx,
            });
        }

        // 4: STAR_EXPORT `[u16 req_idx]` (2 B)
        let se_n = read_u32_le(&mut sp)? as usize;
        if sp.len() < se_n.checked_mul(2)? {
            return None;
        }
        for _ in 0..se_n {
            let req_idx = u32::from(read_u16_le(&mut sp)?);
            records.push(RawModuleRecord::StarExport { req_idx });
        }

        Some(RawModuleData {
            request_offs,
            records,
        })
    }

    #[inline]
    fn slice_offset(&self, sub: &'a [u8]) -> u32 {
        (self.data.len() - sub.len()) as u32
    }
}

#[inline]
fn read_optional_tagged_u32(sp: &mut &[u8], tag: u8) -> Option<Option<u32>> {
    if sp.is_empty() {
        return Some(None);
    }
    if sp[0] != tag {
        return Some(None);
    }
    *sp = &sp[1..];
    read_u32_le(sp).map(Some)
}

#[inline]
fn read_optional_tagged_u8(sp: &mut &[u8], tag: u8) -> Option<Option<u8>> {
    if sp.is_empty() {
        return Some(None);
    }
    if sp[0] != tag {
        return Some(None);
    }
    *sp = &sp[1..];
    read_u8(sp).map(Some)
}

#[inline]
fn read_tagged_u32_list(sp: &mut &[u8], tag: u8) -> Option<Vec<u32>> {
    if sp.is_empty() {
        return None;
    }
    let mut out = Vec::new();
    while !sp.is_empty() && sp[0] == tag {
        *sp = &sp[1..];
        out.push(read_u32_le(sp)?);
    }
    Some(out)
}

// ---------------------------------------------------------------------------
// Decoded Container Item Views
// ---------------------------------------------------------------------------

pub(crate) enum DecodedString<'a> {
    Utf8Borrowed(&'a str),
    Utf8Owned(String),
    LossyRaw { raw: &'a [u8], lossy: String },
}

pub(crate) struct RawClass<'a> {
    pub class_off: u32,
    pub super_class_off: Option<u32>,
    pub access_flags: u32,
    pub num_fields: u32,
    pub num_methods: u32,
    pub ifaces_sp: &'a [u8],
    pub ifaces_count: u32,
    pub source_lang: Option<u8>,
    pub source_file_off: Option<u32>,
    pub annotations: Vec<u32>,
    pub runtime_annotations: Vec<u32>,
    pub type_annotations: Vec<u32>,
    pub runtime_type_annotations: Vec<u32>,
    pub fields_off: u32,
}

impl RawClass<'_> {
    pub fn interface_class_off(&self, reader: &AbcReader<'_>, idx: u32) -> Option<u32> {
        if idx >= self.ifaces_count {
            return None;
        }
        let pos = (idx as usize) * 2;
        let bytes = self.ifaces_sp.get(pos..pos + 2)?;
        let class_idx = u16::from_le_bytes([bytes[0], bytes[1]]);
        reader.resolve_class_index(self.class_off, class_idx)
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum RawFieldValue {
    Int(i32),
    Bits32(u32),
    Bits64(u64),
}

impl RawFieldValue {
    #[inline]
    pub fn as_i32(self) -> i32 {
        match self {
            Self::Int(v) => v,
            Self::Bits32(v) => v as i32,
            Self::Bits64(v) => v as i32,
        }
    }

    #[inline]
    pub fn as_u32(self) -> u32 {
        match self {
            Self::Int(v) => v as u32,
            Self::Bits32(v) => v,
            Self::Bits64(v) => v as u32,
        }
    }

    #[inline]
    pub fn as_i64(self) -> i64 {
        match self {
            Self::Int(v) => i64::from(v),
            Self::Bits32(v) => i64::from(v),
            Self::Bits64(v) => v as i64,
        }
    }

    #[inline]
    pub fn as_f32(self) -> f32 {
        match self {
            Self::Int(v) => v as f32,
            Self::Bits32(v) => f32::from_bits(v),
            Self::Bits64(v) => f32::from_bits(v as u32),
        }
    }

    #[inline]
    pub fn as_f64(self) -> f64 {
        match self {
            Self::Int(v) => f64::from(v),
            Self::Bits32(v) => f64::from_bits(u64::from(v)),
            Self::Bits64(v) => f64::from_bits(v),
        }
    }
}

pub(crate) struct RawField {
    pub offset: u32,
    pub name_off: u32,
    pub type_id: TypeId,
    pub type_off: u32,
    pub access_flags: u32,
    pub is_external: bool,
    pub raw_value: Option<RawFieldValue>,
    pub annotations: Vec<u32>,
    pub runtime_annotations: Vec<u32>,
    pub byte_size: u32,
}

pub(crate) struct RawMethod {
    pub offset: u32,
    pub proto_idx: u16,
    pub name_off: u32,
    pub access_flags: u32,
    pub is_external: bool,
    pub code_off: Option<u32>,
    pub source_lang: Option<u8>,
    pub debug_info_off: Option<u32>,
    pub param_annotations_off: Option<u32>,
    pub runtime_param_annotations_off: Option<u32>,
    pub annotations: Vec<u32>,
    pub runtime_annotations: Vec<u32>,
    pub type_annotations: Vec<u32>,
    pub runtime_type_annotations: Vec<u32>,
    pub byte_size: u32,
}

pub(crate) struct RawProto<'a> {
    pub proto_off: u32,
    pub shorty: Vec<u8>,
    pub ref_types_sp: &'a [u8],
}

impl RawProto<'_> {
    #[inline]
    pub fn return_type_raw(&self) -> u8 {
        self.shorty[0]
    }

    #[inline]
    pub fn num_args(&self) -> usize {
        self.shorty.len().saturating_sub(1)
    }

    #[inline]
    pub fn arg_type_raw(&self, idx: usize) -> u8 {
        self.shorty[idx + 1]
    }

    #[inline]
    pub fn reference_type_off(&self, reader: &AbcReader<'_>, ref_idx: usize) -> Option<u32> {
        let pos = ref_idx.checked_mul(2)?;
        let bytes = self.ref_types_sp.get(pos..pos + 2)?;
        let class_idx = u16::from_le_bytes([bytes[0], bytes[1]]);
        reader.resolve_class_index(self.proto_off, class_idx)
    }
}

pub(crate) struct RawCode<'a> {
    pub num_vregs: u32,
    pub num_args: u32,
    pub code_size: u32,
    pub tries_size: u32,
    pub insns_off: u32,
    pub instructions: &'a [u8],
    pub try_blocks_sp: &'a [u8],
}

impl<'a> RawCode<'a> {
    /// Parse all `tries_size` try/catch records from `try_blocks_sp`.
    pub fn read_try_blocks(&self) -> Option<Vec<RawTryBlock>> {
        let mut sp = self.try_blocks_sp;
        if (self.tries_size as usize) > sp.len() / 3 {
            return None;
        }
        let mut out = Vec::with_capacity(self.tries_size as usize);
        for _ in 0..self.tries_size {
            let start_pc = read_uleb128(&mut sp)?;
            let length = read_uleb128(&mut sp)?;
            let num_catches = read_uleb128(&mut sp)?;
            if (num_catches as usize) > sp.len() / 3 {
                return None;
            }
            let mut catches = Vec::with_capacity(num_catches as usize);
            for _ in 0..num_catches {
                let raw_type_idx = read_uleb128(&mut sp)?;
                // Wire `0` = catch-all (`None`); `> 0` = `idx - 1` in region `class_idx`.
                let type_idx = if raw_type_idx == 0 {
                    None
                } else {
                    u16::try_from(raw_type_idx - 1).ok()
                };
                if raw_type_idx != 0 && type_idx.is_none() {
                    return None;
                }
                let handler_pc = read_uleb128(&mut sp)?;
                let code_size = read_uleb128(&mut sp)?;
                catches.push(RawCatchBlock {
                    type_idx,
                    handler_pc,
                    code_size,
                });
            }
            out.push(RawTryBlock {
                start_pc,
                length,
                catches,
            });
        }
        Some(out)
    }
}

pub(crate) struct RawTryBlock {
    pub start_pc: u32,
    pub length: u32,
    pub catches: Vec<RawCatchBlock>,
}

pub(crate) struct RawCatchBlock {
    pub type_idx: Option<u16>,
    pub handler_pc: u32,
    pub code_size: u32,
}

pub(crate) struct RawAnnotation<'a> {
    pub class_off: u32,
    pub count: u16,
    pub elements_sp: &'a [u8],
    pub tags_sp: &'a [u8],
}

impl RawAnnotation<'_> {
    #[inline]
    pub fn element(&self, index: u16) -> Option<(u32, u8, u32)> {
        if index >= self.count {
            return None;
        }
        let idx = usize::from(index);
        let epos = idx * 8;
        let name_off = read_u32_at(self.elements_sp, epos)?;
        let value = read_u32_at(self.elements_sp, epos + 4)?;
        let tag = *self.tags_sp.get(idx)?;
        Some((name_off, tag, value))
    }
}

pub(crate) struct RawModuleData {
    pub request_offs: Vec<u32>,
    pub records: Vec<RawModuleRecord>,
}

pub(crate) enum RawModuleRecord {
    RegularImport {
        local_off: u32,
        import_off: u32,
        req_idx: u32,
    },
    NamespaceImport {
        local_off: u32,
        req_idx: u32,
    },
    LocalExport {
        local_off: u32,
        export_off: u32,
    },
    IndirectExport {
        export_off: u32,
        import_off: u32,
        req_idx: u32,
    },
    StarExport {
        req_idx: u32,
    },
}

// ---------------------------------------------------------------------------
// Unified Single-Map StringItemCache (`#72` P2)
// ---------------------------------------------------------------------------

const LOSSY_CACHE_BIT: u32 = 0x8000_0000;

/// Compact open-addressed `u32 offset -> packed u32` hash map (`0` = empty).
struct OffsetStringMap {
    keys: Vec<u32>,
    vals: Vec<u32>,
    mask: usize,
    len: usize,
}

impl OffsetStringMap {
    fn with_capacity(cap: usize) -> Self {
        let buckets = (cap.saturating_mul(2)).max(64).next_power_of_two();
        Self {
            keys: vec![0; buckets],
            vals: vec![0; buckets],
            mask: buckets - 1,
            len: 0,
        }
    }

    #[inline]
    fn hash_off(k: u32) -> usize {
        k.wrapping_mul(0x9E37_79B9) as usize
    }

    #[inline]
    fn get(&self, offset: u32) -> Option<u32> {
        if offset == 0 || offset == u32::MAX {
            return None;
        }
        let mut idx = Self::hash_off(offset) & self.mask;
        loop {
            let k = self.keys[idx];
            if k == offset {
                return Some(self.vals[idx]);
            }
            if k == 0 {
                return None;
            }
            idx = (idx + 1) & self.mask;
        }
    }

    fn insert(&mut self, offset: u32, packed: u32) {
        if offset == 0 || offset == u32::MAX {
            return;
        }
        if (self.len + 1) * 10 >= self.keys.len() * 7 {
            self.grow();
        }
        let mut idx = Self::hash_off(offset) & self.mask;
        loop {
            let k = self.keys[idx];
            if k == 0 {
                self.keys[idx] = offset;
                self.vals[idx] = packed;
                self.len += 1;
                return;
            }
            if k == offset {
                self.vals[idx] = packed;
                return;
            }
            idx = (idx + 1) & self.mask;
        }
    }

    fn grow(&mut self) {
        let new_buckets = self.keys.len() * 2;
        let new_mask = new_buckets - 1;
        let mut new_keys = vec![0u32; new_buckets];
        let mut new_vals = vec![0u32; new_buckets];
        for (&k, &v) in self.keys.iter().zip(&self.vals) {
            if k != 0 {
                let mut idx = Self::hash_off(k) & new_mask;
                while new_keys[idx] != 0 {
                    idx = (idx + 1) & new_mask;
                }
                new_keys[idx] = k;
                new_vals[idx] = v;
            }
        }
        self.keys = new_keys;
        self.vals = new_vals;
        self.mask = new_mask;
    }
}

/// Reusable per-decode string interning cache (`#72` P2: single unified
/// offset map + reusable UTF-16 validation scratch buffer).
pub(crate) struct StringItemCache {
    cache: OffsetStringMap,
    utf16_scratch: Vec<u16>,
}

impl StringItemCache {
    pub fn new() -> Self {
        Self {
            cache: OffsetStringMap::with_capacity(256),
            utf16_scratch: Vec::with_capacity(64),
        }
    }

    #[inline]
    fn pack_lossless(sid: StringId) -> Option<u32> {
        let raw = sid.index();
        (raw < (LOSSY_CACHE_BIT as usize)).then_some(raw as u32)
    }

    #[inline]
    fn pack_lossy(sid: StringId) -> Option<u32> {
        let raw = sid.index();
        (raw < (LOSSY_CACHE_BIT as usize)).then_some((raw as u32) | LOSSY_CACHE_BIT)
    }

    /// Read and intern a `StringItem` preserving exact MUTF-8 bytes for lone surrogates.
    pub fn intern_lossy(
        &mut self,
        reader: &AbcReader<'_>,
        offset: u32,
        strings: &mut StringPool,
    ) -> Option<StringId> {
        if offset == ABSENT_OFFSET {
            return None;
        }
        if let Some(packed) = self.cache.get(offset) {
            return Some(StringId::new(packed & !LOSSY_CACHE_BIT));
        }
        let decoded = reader.read_string_item(offset, &mut self.utf16_scratch)?;
        match decoded {
            DecodedString::Utf8Borrowed(s) => {
                let sid = strings.try_get_or_intern(s).ok()?;
                if let Some(p) = Self::pack_lossless(sid) {
                    self.cache.insert(offset, p);
                }
                Some(sid)
            }
            DecodedString::Utf8Owned(s) => {
                let sid = strings.try_get_or_intern(&s).ok()?;
                if let Some(p) = Self::pack_lossless(sid) {
                    self.cache.insert(offset, p);
                }
                Some(sid)
            }
            DecodedString::LossyRaw { raw, lossy } => {
                let sid = strings.try_intern_lossy_raw(&lossy, raw).ok()?;
                if let Some(p) = Self::pack_lossy(sid) {
                    self.cache.insert(offset, p);
                }
                Some(sid)
            }
        }
    }

    /// Read and intern a `StringItem` as lossless/display UTF-8 (`StringPool::get_or_intern`).
    pub fn intern_utf8(
        &mut self,
        reader: &AbcReader<'_>,
        offset: u32,
        strings: &mut StringPool,
    ) -> Option<StringId> {
        if offset == ABSENT_OFFSET {
            return None;
        }
        if let Some(packed) = self.cache.get(offset) {
            let sid = StringId::new(packed & !LOSSY_CACHE_BIT);
            if (packed & LOSSY_CACHE_BIT) == 0 {
                return Some(sid);
            }
            let display = strings.resolve(sid)?.to_owned();
            return strings.try_get_or_intern(&display).ok();
        }
        let decoded = reader.read_string_item(offset, &mut self.utf16_scratch)?;
        match decoded {
            DecodedString::Utf8Borrowed(s) => {
                let sid = strings.try_get_or_intern(s).ok()?;
                if let Some(p) = Self::pack_lossless(sid) {
                    self.cache.insert(offset, p);
                }
                Some(sid)
            }
            DecodedString::Utf8Owned(s) => {
                let sid = strings.try_get_or_intern(&s).ok()?;
                if let Some(p) = Self::pack_lossless(sid) {
                    self.cache.insert(offset, p);
                }
                Some(sid)
            }
            DecodedString::LossyRaw { lossy, .. } => strings.try_get_or_intern(&lossy).ok(),
        }
    }

    /// Read and intern a method's `name_off` (`non-empty` lossless UTF-16
    /// validation, matching `abc_method_get_name_utf16` + `String::from_utf16`).
    pub fn intern_method_name(
        &mut self,
        reader: &AbcReader<'_>,
        name_off: u32,
        strings: &mut StringPool,
    ) -> Option<StringId> {
        if name_off == ABSENT_OFFSET {
            return None;
        }
        if let Some(packed) = self.cache.get(name_off) {
            if (packed & LOSSY_CACHE_BIT) != 0 {
                return None;
            }
            let sid = StringId::new(packed);
            return strings.resolve(sid).filter(|s| !s.is_empty()).map(|_| sid);
        }
        let decoded = reader.read_string_item(name_off, &mut self.utf16_scratch)?;
        match decoded {
            DecodedString::Utf8Borrowed(s) if !s.is_empty() => {
                let sid = strings.try_get_or_intern(s).ok()?;
                if let Some(p) = Self::pack_lossless(sid) {
                    self.cache.insert(name_off, p);
                }
                Some(sid)
            }
            DecodedString::Utf8Owned(s) if !s.is_empty() => {
                let sid = strings.try_get_or_intern(&s).ok()?;
                if let Some(p) = Self::pack_lossless(sid) {
                    self.cache.insert(name_off, p);
                }
                Some(sid)
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encode::Builder;
    use crate::types::{AccessFlags, SourceLang, Type};

    fn minimal_abc() -> Vec<u8> {
        let mut b = Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let proto = b.create_proto(Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            AccessFlags::PUBLIC,
            &[0x65],
            1,
            0,
        );
        b.method_set_source_lang(m, SourceLang::EcmaScript);
        b.finalize().expect("finalize")
    }

    #[test]
    fn pure_rust_reader_opens_and_validates_checksum() {
        let data = minimal_abc();
        assert_eq!(file_type(&data), sys::FileType::Dynamic);
        assert!(validate_checksum(&data));
        let reader = AbcReader::open(&data).expect("open minimal abc");
        assert_eq!(reader.checksum(), reader.compute_checksum());
        assert_eq!(reader.num_classes(), 1);
    }

    #[test]
    fn zeropadded_buffer_opens_via_declared_file_size() {
        let expected_bytes = minimal_abc();
        let expected = AbcReader::open(&expected_bytes).expect("open exact");

        let mut padded = expected_bytes.clone();
        padded.resize(padded.len() + 4096, 0);
        assert_eq!(file_type(&padded), sys::FileType::Dynamic);
        let zf = AbcReader::open(&padded).expect("open zero-padded");
        assert_eq!(zf.version(), expected.version());
        assert_eq!(zf.checksum(), expected.checksum());
        assert_eq!(zf.file_size(), expected.file_size());
        assert_eq!(zf.class_offsets(), expected.class_offsets());
    }
}
