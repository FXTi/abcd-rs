//! Synthetic ZIP builder shared by abcd-hap integration tests.
//!
//! All container bytes are generated in code — no binary fixtures live in
//! the repo (design §3.5, option (a)). Low-level writers are public so
//! adversarial tests can compose malformed archives byte by byte.
#![allow(dead_code)]

pub const STORED: u16 = 0;
pub const DEFLATE: u16 = 8;

pub const LOCAL_SIG: u32 = 0x0403_4b50;
pub const CD_SIG: u32 = 0x0201_4b50;
pub const EOCD_SIG: u32 = 0x0605_4b50;
pub const ZIP64_EOCD_SIG: u32 = 0x0606_4b50;
pub const ZIP64_LOCATOR_SIG: u32 = 0x0706_4b50;

pub fn w16(out: &mut Vec<u8>, v: u16) {
    out.extend_from_slice(&v.to_le_bytes());
}

pub fn w32(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&v.to_le_bytes());
}

pub fn w64(out: &mut Vec<u8>, v: u64) {
    out.extend_from_slice(&v.to_le_bytes());
}

/// CRC-32 (ISO 3309 / ITU-T V.42, reflected) so synthesized entries carry
/// honest checksums unless a test deliberately corrupts them.
pub fn crc32(data: &[u8]) -> u32 {
    let mut crc = 0xFFFF_FFFFu32;
    for &b in data {
        crc ^= u32::from(b);
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
        }
    }
    !crc
}

/// One entry to place into a synthesized archive.
#[derive(Clone)]
pub struct ZipEntry {
    pub name: String,
    /// Uncompressed payload.
    pub data: Vec<u8>,
    pub method: u16,
    pub flags: u16,
    pub crc32: u32,
    /// Bytes that actually follow the local header (compressed form).
    pub compressed: Vec<u8>,
    /// Extra field bytes written to the *local* header only (the CD record
    /// gets none), mimicking real packers whose local/CD extras differ.
    pub extra_local: Vec<u8>,
}

impl ZipEntry {
    pub fn stored(name: &str, data: &[u8]) -> Self {
        ZipEntry {
            name: name.to_string(),
            data: data.to_vec(),
            method: STORED,
            flags: 0,
            crc32: crc32(data),
            compressed: data.to_vec(),
            extra_local: Vec::new(),
        }
    }

    pub fn deflated(name: &str, data: &[u8]) -> Self {
        ZipEntry {
            name: name.to_string(),
            data: data.to_vec(),
            method: DEFLATE,
            flags: 0,
            crc32: crc32(data),
            compressed: miniz_oxide::deflate::compress_to_vec(data, 6),
            extra_local: Vec::new(),
        }
    }

    /// Entry with an arbitrary method number and raw "compressed" bytes
    /// (for unsupported-method tests).
    pub fn raw(name: &str, data: &[u8], method: u16) -> Self {
        ZipEntry {
            name: name.to_string(),
            data: data.to_vec(),
            method,
            flags: 0,
            crc32: crc32(data),
            compressed: data.to_vec(),
            extra_local: Vec::new(),
        }
    }

    pub fn with_crc(mut self, crc32: u32) -> Self {
        self.crc32 = crc32;
        self
    }

    pub fn with_flags(mut self, flags: u16) -> Self {
        self.flags = flags;
        self
    }

    pub fn with_extra_local(mut self, extra: &[u8]) -> Self {
        self.extra_local = extra.to_vec();
        self
    }
}

/// A synthesized archive plus the offsets tests need to cut/patch it.
pub struct Built {
    pub bytes: Vec<u8>,
    pub cd_offset: usize,
    pub cd_size: usize,
    pub eocd_offset: usize,
    pub local_offsets: Vec<usize>,
}

pub fn build_zip(entries: &[ZipEntry]) -> Built {
    build_zip_ex(entries, &[], &[])
}

/// Build an archive. `junk_before_cd` models a signing block sitting between
/// the last entry's data and the central directory; `comment` is the EOCD
/// comment (may contain fake EOCD magics).
pub fn build_zip_ex(entries: &[ZipEntry], comment: &[u8], junk_before_cd: &[u8]) -> Built {
    let mut out = Vec::new();
    let mut local_offsets = Vec::with_capacity(entries.len());
    for e in entries {
        local_offsets.push(out.len());
        w32(&mut out, LOCAL_SIG);
        w16(&mut out, 20); // version needed
        w16(&mut out, e.flags);
        w16(&mut out, e.method);
        w16(&mut out, 0); // mod time
        w16(&mut out, 0); // mod date
        w32(&mut out, e.crc32);
        w32(&mut out, e.compressed.len() as u32);
        w32(&mut out, e.data.len() as u32);
        w16(&mut out, e.name.len() as u16);
        w16(&mut out, e.extra_local.len() as u16);
        out.extend_from_slice(e.name.as_bytes());
        out.extend_from_slice(&e.extra_local);
        out.extend_from_slice(&e.compressed);
    }
    out.extend_from_slice(junk_before_cd);
    let cd_offset = out.len();
    for (i, e) in entries.iter().enumerate() {
        w32(&mut out, CD_SIG);
        w16(&mut out, 20); // version made by
        w16(&mut out, 20); // version needed
        w16(&mut out, e.flags);
        w16(&mut out, e.method);
        w16(&mut out, 0); // mod time
        w16(&mut out, 0); // mod date
        w32(&mut out, e.crc32);
        w32(&mut out, e.compressed.len() as u32);
        w32(&mut out, e.data.len() as u32);
        w16(&mut out, e.name.len() as u16);
        w16(&mut out, 0); // extra len
        w16(&mut out, 0); // comment len
        w16(&mut out, 0); // disk start
        w16(&mut out, 0); // internal attrs
        w32(&mut out, 0); // external attrs
        w32(&mut out, local_offsets[i] as u32);
        out.extend_from_slice(e.name.as_bytes());
    }
    let cd_size = out.len() - cd_offset;
    let eocd_offset = out.len();
    push_eocd(
        &mut out,
        entries.len() as u16,
        cd_size as u32,
        cd_offset as u32,
        comment,
    );
    Built {
        bytes: out,
        cd_offset,
        cd_size,
        eocd_offset,
        local_offsets,
    }
}

/// Append a plain EOCD record.
pub fn push_eocd(out: &mut Vec<u8>, count: u16, cd_size: u32, cd_offset: u32, comment: &[u8]) {
    w32(out, EOCD_SIG);
    w16(out, 0); // disk number
    w16(out, 0); // disk with CD
    w16(out, count); // entries on this disk
    w16(out, count); // entries total
    w32(out, cd_size);
    w32(out, cd_offset);
    w16(out, comment.len() as u16);
    out.extend_from_slice(comment);
}

/// A 56-byte ZIP64 EOCD record followed by its 20-byte locator, to be
/// inserted immediately before the real EOCD.
pub fn zip64_eocd_and_locator(
    cd_offset: u64,
    cd_size: u64,
    count: u64,
    zip64_eocd_offset: u64,
) -> Vec<u8> {
    let mut out = Vec::new();
    w32(&mut out, ZIP64_EOCD_SIG);
    w64(&mut out, 44); // size of the remaining record
    w16(&mut out, 45); // version made by
    w16(&mut out, 45); // version needed
    w32(&mut out, 0); // disk number
    w32(&mut out, 0); // disk with CD
    w64(&mut out, count);
    w64(&mut out, count);
    w64(&mut out, cd_size);
    w64(&mut out, cd_offset);
    w32(&mut out, ZIP64_LOCATOR_SIG);
    w32(&mut out, 0); // disk with ZIP64 EOCD
    w64(&mut out, zip64_eocd_offset);
    w32(&mut out, 1); // total disks
    out
}

/// Deterministic xorshift64* PRNG for the no-panic fuzz sweep.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed | 1)
    }

    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    pub fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}
