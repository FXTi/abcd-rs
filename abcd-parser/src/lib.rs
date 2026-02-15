//! ABC binary file format parser for ArkCompiler bytecode files.

pub mod annotation;
pub mod class;
pub mod code;
pub mod debug_info;
pub mod error;
pub mod header;
pub mod index;
pub mod leb128;
pub mod literal;
pub mod method;
pub mod module_record;
pub mod mutf8;
pub mod string_table;

use error::ParseError;
use header::Header;
use index::IndexSection;

/// A parsed ABC file providing access to all structures.
pub struct AbcFile {
    data: Vec<u8>,
    pub header: Header,
    index_section: IndexSection,
}

impl AbcFile {
    /// Open and parse an ABC file from a byte slice.
    pub fn parse(data: Vec<u8>) -> Result<Self, ParseError> {
        if data.len() < Header::SIZE {
            return Err(ParseError::FileTooSmall(data.len()));
        }

        let header = Header::parse(&data)?;
        let index_section = IndexSection::parse(&data, &header)?;

        Ok(Self {
            data,
            header,
            index_section,
        })
    }

    /// Open an ABC file from a path.
    pub fn open(path: &std::path::Path) -> Result<Self, ParseError> {
        let data = std::fs::read(path).map_err(|e| ParseError::Io(e.to_string()))?;
        Self::parse(data)
    }

    /// Get the raw file data.
    pub fn data(&self) -> &[u8] {
        &self.data
    }

    /// Get the index section for resolving 16-bit indexes.
    pub fn index_section(&self) -> &IndexSection {
        &self.index_section
    }

    /// Read a string at the given offset.
    pub fn get_string(&self, offset: u32) -> Result<String, ParseError> {
        string_table::read_string(&self.data, offset as usize)
    }

    /// Iterate over all class offsets in the class index.
    pub fn class_offsets(&self) -> impl Iterator<Item = u32> + '_ {
        let start = self.header.class_idx_off as usize;
        let count = self.header.num_classes as usize;
        (0..count).map(move |i| {
            let off = start + i * 4;
            u32::from_le_bytes([
                self.data[off],
                self.data[off + 1],
                self.data[off + 2],
                self.data[off + 3],
            ])
        })
    }

    /// Iterate over all literal array offsets.
    pub fn literal_array_offsets(&self) -> impl Iterator<Item = u32> + '_ {
        let start = self.header.literalarray_idx_off as usize;
        let count = self.header.num_literalarrays as usize;
        (0..count).map(move |i| {
            let off = start + i * 4;
            u32::from_le_bytes([
                self.data[off],
                self.data[off + 1],
                self.data[off + 2],
                self.data[off + 3],
            ])
        })
    }

    /// Check if an offset falls within the foreign region.
    pub fn is_foreign(&self, offset: u32) -> bool {
        offset >= self.header.foreign_off
            && offset < self.header.foreign_off + self.header.foreign_size
    }
}
