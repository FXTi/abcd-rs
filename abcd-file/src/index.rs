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

    /// Resolve a 16-bit field index to a 32-bit entity offset.
    pub fn resolve_field_index(&self, data: &[u8], context_offset: u32, idx: u16) -> Option<u32> {
        let region = self.find_region(context_offset)?;
        if (idx as u32) >= region.field_idx_size {
            return None;
        }
        let entry_off = region.field_idx_off as usize + (idx as usize) * 4;
        if entry_off + 4 > data.len() {
            return None;
        }
        Some(u32::from_le_bytes(
            data[entry_off..entry_off + 4].try_into().unwrap(),
        ))
    }

    /// Resolve a 16-bit proto index to a 32-bit entity offset.
    pub fn resolve_proto_index(&self, data: &[u8], context_offset: u32, idx: u16) -> Option<u32> {
        let region = self.find_region(context_offset)?;
        if (idx as u32) >= region.proto_idx_size {
            return None;
        }
        let entry_off = region.proto_idx_off as usize + (idx as usize) * 4;
        if entry_off + 4 > data.len() {
            return None;
        }
        Some(u32::from_le_bytes(
            data[entry_off..entry_off + 4].try_into().unwrap(),
        ))
    }
}

#[cfg(test)]
mod tests {
    //! Tests for index section resolution, based on patterns from
    //! arkcompiler runtime_core/libpandafile/tests/file_items_test.cpp

    use super::*;

    /// Build a fake data buffer with a region header and index tables.
    fn make_test_index_section() -> (Vec<u8>, IndexSection) {
        // We'll create a 256-byte buffer.
        // Region covers offsets [0, 256).
        // class_idx: 2 entries at offset 100
        // method_idx: 3 entries at offset 108
        // field_idx: 1 entry at offset 120
        // proto_idx: 1 entry at offset 124
        let mut data = vec![0u8; 256];

        // Write class index entries at offset 100
        let class_entries: [u32; 2] = [0xAAAA, 0xBBBB];
        for (i, &val) in class_entries.iter().enumerate() {
            let off = 100 + i * 4;
            data[off..off + 4].copy_from_slice(&val.to_le_bytes());
        }

        // Write method index entries at offset 108
        let method_entries: [u32; 3] = [0x1111, 0x2222, 0x3333];
        for (i, &val) in method_entries.iter().enumerate() {
            let off = 108 + i * 4;
            data[off..off + 4].copy_from_slice(&val.to_le_bytes());
        }

        // Write field index entry at offset 120
        data[120..124].copy_from_slice(&0xDDDDu32.to_le_bytes());

        // Write proto index entry at offset 124
        data[124..128].copy_from_slice(&0xEEEEu32.to_le_bytes());

        let region = RegionHeader {
            start_off: 0,
            end_off: 256,
            class_idx_size: 2,
            class_idx_off: 100,
            method_idx_size: 3,
            method_idx_off: 108,
            field_idx_size: 1,
            field_idx_off: 120,
            proto_idx_size: 1,
            proto_idx_off: 124,
        };

        let section = IndexSection {
            regions: vec![region],
        };

        (data, section)
    }

    #[test]
    fn resolve_method_index_valid() {
        let (data, section) = make_test_index_section();
        assert_eq!(section.resolve_method_index(&data, 50, 0), Some(0x1111));
        assert_eq!(section.resolve_method_index(&data, 50, 1), Some(0x2222));
        assert_eq!(section.resolve_method_index(&data, 50, 2), Some(0x3333));
    }

    #[test]
    fn resolve_method_index_out_of_bounds() {
        let (data, section) = make_test_index_section();
        // idx 3 is out of range (size is 3)
        assert_eq!(section.resolve_method_index(&data, 50, 3), None);
    }

    #[test]
    fn resolve_class_index_valid() {
        let (data, section) = make_test_index_section();
        assert_eq!(section.resolve_class_index(&data, 50, 0), Some(0xAAAA));
        assert_eq!(section.resolve_class_index(&data, 50, 1), Some(0xBBBB));
    }

    #[test]
    fn resolve_class_index_out_of_bounds() {
        let (data, section) = make_test_index_section();
        assert_eq!(section.resolve_class_index(&data, 50, 2), None);
    }

    #[test]
    fn resolve_field_index_valid() {
        let (data, section) = make_test_index_section();
        assert_eq!(section.resolve_field_index(&data, 50, 0), Some(0xDDDD));
    }

    #[test]
    fn resolve_field_index_out_of_bounds() {
        let (data, section) = make_test_index_section();
        assert_eq!(section.resolve_field_index(&data, 50, 1), None);
    }

    #[test]
    fn resolve_proto_index_valid() {
        let (data, section) = make_test_index_section();
        assert_eq!(section.resolve_proto_index(&data, 50, 0), Some(0xEEEE));
    }

    #[test]
    fn resolve_proto_index_out_of_bounds() {
        let (data, section) = make_test_index_section();
        assert_eq!(section.resolve_proto_index(&data, 50, 1), None);
    }

    #[test]
    fn find_region_outside_range() {
        let (data, section) = make_test_index_section();
        // Offset 300 is outside the region [0, 256)
        assert_eq!(section.resolve_method_index(&data, 300, 0), None);
    }

    #[test]
    fn region_header_parse_roundtrip() {
        let region = RegionHeader {
            start_off: 10,
            end_off: 200,
            class_idx_size: 5,
            class_idx_off: 100,
            method_idx_size: 10,
            method_idx_off: 120,
            field_idx_size: 3,
            field_idx_off: 160,
            proto_idx_size: 2,
            proto_idx_off: 172,
        };

        let mut data = vec![0u8; RegionHeader::SIZE];
        let fields = [
            region.start_off,
            region.end_off,
            region.class_idx_size,
            region.class_idx_off,
            region.method_idx_size,
            region.method_idx_off,
            region.field_idx_size,
            region.field_idx_off,
            region.proto_idx_size,
            region.proto_idx_off,
        ];
        for (i, &val) in fields.iter().enumerate() {
            let off = i * 4;
            data[off..off + 4].copy_from_slice(&val.to_le_bytes());
        }

        let parsed = RegionHeader::parse(&data, 0).unwrap();
        assert_eq!(parsed.start_off, 10);
        assert_eq!(parsed.end_off, 200);
        assert_eq!(parsed.class_idx_size, 5);
        assert_eq!(parsed.method_idx_size, 10);
        assert_eq!(parsed.field_idx_size, 3);
        assert_eq!(parsed.proto_idx_size, 2);
    }

    #[test]
    fn region_header_parse_too_small() {
        let data = [0u8; 20]; // Less than RegionHeader::SIZE (40)
        assert!(RegionHeader::parse(&data, 0).is_err());
    }

    #[test]
    fn resolve_offset_by_index_delegates_to_method() {
        let (data, section) = make_test_index_section();
        // resolve_offset_by_index should give same result as resolve_method_index
        assert_eq!(
            section.resolve_offset_by_index(&data, 50, 1),
            section.resolve_method_index(&data, 50, 1)
        );
    }
}
