use crate::error::ParseError;
use crate::header::Header;

/// A region header describing a 16-bit index region.
#[derive(Debug, Clone)]
pub struct RegionHeader {
    pub start_off: u32,
    pub end_off: u32,
    pub class_idx_size: u32,
    pub class_idx_off: u32,
    pub method_idx_size: u32,
    pub method_idx_off: u32,
    pub field_idx_size: u32,
    pub field_idx_off: u32,
    pub proto_idx_size: u32,
    pub proto_idx_off: u32,
}

impl RegionHeader {
    pub const SIZE: usize = 40; // 10 * 4 bytes

    pub fn parse(data: &[u8], offset: usize) -> Result<Self, ParseError> {
        if offset + Self::SIZE > data.len() {
            return Err(ParseError::OffsetOutOfBounds(offset, data.len()));
        }

        let r = |off: usize| -> u32 { u32::from_le_bytes(data[off..off + 4].try_into().unwrap()) };

        Ok(Self {
            start_off: r(offset),
            end_off: r(offset + 4),
            class_idx_size: r(offset + 8),
            class_idx_off: r(offset + 12),
            method_idx_size: r(offset + 16),
            method_idx_off: r(offset + 20),
            field_idx_size: r(offset + 24),
            field_idx_off: r(offset + 28),
            proto_idx_size: r(offset + 32),
            proto_idx_off: r(offset + 36),
        })
    }
}

/// The index section containing all region headers.
#[derive(Debug, Clone)]
pub struct IndexSection {
    pub regions: Vec<RegionHeader>,
}

impl IndexSection {
    pub fn parse(data: &[u8], header: &Header) -> Result<Self, ParseError> {
        let mut regions = Vec::with_capacity(header.num_indexes as usize);
        let base = header.index_section_off as usize;

        for i in 0..header.num_indexes as usize {
            let offset = base + i * RegionHeader::SIZE;
            regions.push(RegionHeader::parse(data, offset)?);
        }

        Ok(Self { regions })
    }

    /// Find the region header that covers the given file offset.
    pub fn find_region(&self, offset: u32) -> Option<&RegionHeader> {
        self.regions
            .iter()
            .find(|r| offset >= r.start_off && offset < r.end_off)
    }

    /// Resolve a 16-bit bytecode ID to a 32-bit entity offset.
    ///
    /// This mirrors the C++ `File::ResolveOffsetByIndex` which uses the method
    /// index table for ALL 16-bit ID operands (string_id, method_id, literalarray_id, etc.).
    pub fn resolve_offset_by_index(
        &self,
        data: &[u8],
        method_offset: u32,
        idx: u16,
    ) -> Option<u32> {
        self.resolve_method_index(data, method_offset, idx)
    }

    /// Resolve a 16-bit method index to a 32-bit entity offset.
    pub fn resolve_method_index(&self, data: &[u8], method_offset: u32, idx: u16) -> Option<u32> {
        let region = self.find_region(method_offset)?;
        if (idx as u32) >= region.method_idx_size {
            return None;
        }
        let entry_off = region.method_idx_off as usize + (idx as usize) * 4;
        if entry_off + 4 > data.len() {
            return None;
        }
        Some(u32::from_le_bytes(
            data[entry_off..entry_off + 4].try_into().unwrap(),
        ))
    }

    /// Resolve a 16-bit class index to a 32-bit entity offset.
    pub fn resolve_class_index(&self, data: &[u8], context_offset: u32, idx: u16) -> Option<u32> {
        let region = self.find_region(context_offset)?;
        if (idx as u32) >= region.class_idx_size {
            return None;
        }
        let entry_off = region.class_idx_off as usize + (idx as usize) * 4;
        if entry_off + 4 > data.len() {
            return None;
        }
        Some(u32::from_le_bytes(
            data[entry_off..entry_off + 4].try_into().unwrap(),
        ))
    }
}
