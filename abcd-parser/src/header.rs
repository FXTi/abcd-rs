use crate::error::ParseError;

pub const MAGIC: [u8; 8] = *b"PANDA\0\0\0";

/// ABC file header (fixed size, at offset 0).
#[derive(Debug, Clone)]
pub struct Header {
    pub magic: [u8; 8],
    pub checksum: u32,
    pub version: [u8; 4],
    pub file_size: u32,
    pub foreign_off: u32,
    pub foreign_size: u32,
    pub num_classes: u32,
    pub class_idx_off: u32,
    pub num_lnps: u32,
    pub lnp_idx_off: u32,
    pub num_literalarrays: u32,
    pub literalarray_idx_off: u32,
    pub num_indexes: u32,
    pub index_section_off: u32,
}

impl Header {
    /// Header size in bytes: 8 + 4 + 4 + 4*11 = 60 bytes
    pub const SIZE: usize = 60;

    pub fn parse(data: &[u8]) -> Result<Self, ParseError> {
        if data.len() < Self::SIZE {
            return Err(ParseError::FileTooSmall(data.len()));
        }

        let magic: [u8; 8] = data[0..8].try_into().unwrap();
        if magic != MAGIC {
            return Err(ParseError::InvalidMagic);
        }

        let r = |off: usize| -> u32 { u32::from_le_bytes(data[off..off + 4].try_into().unwrap()) };

        Ok(Self {
            magic,
            checksum: r(8),
            version: data[12..16].try_into().unwrap(),
            file_size: r(16),
            foreign_off: r(20),
            foreign_size: r(24),
            num_classes: r(28),
            class_idx_off: r(32),
            num_lnps: r(36),
            lnp_idx_off: r(40),
            num_literalarrays: r(44),
            literalarray_idx_off: r(48),
            num_indexes: r(52),
            index_section_off: r(56),
        })
    }
}
