use crate::error::ParseError;

pub const MAGIC: [u8; 8] = *b"PANDA\0\0\0";

/// Minimum supported ABC version.
pub const MIN_VERSION: [u8; 4] = [0, 0, 0, 2];

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

        let version: [u8; 4] = data[12..16].try_into().unwrap();
        if !Self::version_ge(&version, &MIN_VERSION) {
            return Err(ParseError::UnsupportedVersion(version));
        }

        let r = |off: usize| -> u32 { u32::from_le_bytes(data[off..off + 4].try_into().unwrap()) };

        let file_size = r(16);
        if (file_size as usize) > data.len() {
            return Err(ParseError::FileTooSmall(data.len()));
        }

        Ok(Self {
            magic,
            checksum: r(8),
            version,
            file_size,
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

    /// Compare two version tuples (major.minor.patch.build) as >= .
    fn version_ge(a: &[u8; 4], b: &[u8; 4]) -> bool {
        for i in 0..4 {
            if a[i] > b[i] {
                return true;
            }
            if a[i] < b[i] {
                return false;
            }
        }
        true // equal
    }

    /// Get version as a human-readable string.
    pub fn version_string(&self) -> String {
        format!(
            "{}.{}.{}.{}",
            self.version[0], self.version[1], self.version[2], self.version[3]
        )
    }
}

#[cfg(test)]
mod tests {
    //! Tests based on arkcompiler runtime_core/libpandafile/tests/file_test.cpp
    //! and file_item_container_test.cpp header validation patterns.

    use super::*;

    fn make_minimal_header() -> Vec<u8> {
        let mut data = vec![0u8; Header::SIZE];
        data[0..8].copy_from_slice(b"PANDA\0\0\0");
        data[12..16].copy_from_slice(&[0, 0, 0, 5]);
        let size = Header::SIZE as u32;
        data[16..20].copy_from_slice(&size.to_le_bytes());
        data
    }

    #[test]
    fn valid_header() {
        let h = Header::parse(&make_minimal_header()).unwrap();
        assert_eq!(h.magic, *b"PANDA\0\0\0");
        assert_eq!(h.version, [0, 0, 0, 5]);
        assert_eq!(h.file_size, Header::SIZE as u32);
    }

    #[test]
    fn invalid_magic() {
        let mut d = make_minimal_header();
        d[0] = b'X';
        assert!(matches!(Header::parse(&d), Err(ParseError::InvalidMagic)));
    }

    #[test]
    fn too_small() {
        assert!(matches!(
            Header::parse(&[0u8; 10]),
            Err(ParseError::FileTooSmall(_))
        ));
    }

    #[test]
    fn version_too_old() {
        let mut d = make_minimal_header();
        d[12..16].copy_from_slice(&[0, 0, 0, 1]);
        assert!(matches!(
            Header::parse(&d),
            Err(ParseError::UnsupportedVersion(_))
        ));
    }

    #[test]
    fn version_minimum_accepted() {
        let mut d = make_minimal_header();
        d[12..16].copy_from_slice(&MIN_VERSION);
        assert!(Header::parse(&d).is_ok());
    }

    #[test]
    fn file_size_exceeds_data() {
        let mut d = make_minimal_header();
        d[16..20].copy_from_slice(&99999u32.to_le_bytes());
        assert!(matches!(
            Header::parse(&d),
            Err(ParseError::FileTooSmall(_))
        ));
    }

    #[test]
    fn version_ge_comparisons() {
        assert!(Header::version_ge(&[0, 0, 0, 5], &[0, 0, 0, 2]));
        assert!(Header::version_ge(&[0, 0, 0, 2], &[0, 0, 0, 2]));
        assert!(!Header::version_ge(&[0, 0, 0, 1], &[0, 0, 0, 2]));
        assert!(Header::version_ge(&[1, 0, 0, 0], &[0, 9, 9, 9]));
    }

    #[test]
    fn version_string_format() {
        let h = Header::parse(&make_minimal_header()).unwrap();
        assert_eq!(h.version_string(), "0.0.0.5");
    }
}
