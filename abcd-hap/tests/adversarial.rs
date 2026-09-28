//! Adversarial inputs: truncations, fake EOCDs, ZIP64 markers, overflow
//! sizes, and a deterministic no-panic fuzz sweep. The iron rule is that no
//! input byte pattern may panic the parser.

mod common;

use abcd_hap::{Error, ZipArchive};
use common::*;

fn two_entry_zip() -> Built {
    build_zip(&[
        ZipEntry::stored("first.txt", b"first payload"),
        ZipEntry::deflated("second.txt", &[9u8; 2048]),
    ])
}

#[test]
fn truncated_eocd_is_not_zip() {
    let built = two_entry_zip();
    // Cut the EOCD in half.
    let cut = &built.bytes[..built.bytes.len() - 10];
    assert_eq!(ZipArchive::open(cut).unwrap_err(), Error::NotZip);
    // Drop the EOCD entirely.
    let cut = &built.bytes[..built.eocd_offset];
    assert_eq!(ZipArchive::open(cut).unwrap_err(), Error::NotZip);
}

#[test]
fn every_truncation_point_fails_without_panic() {
    let built = two_entry_zip();
    for cut in (0..built.bytes.len()).step_by(3) {
        let input = &built.bytes[..cut];
        if let Ok(archive) = ZipArchive::open(input) {
            // A truncated archive that still parses must still read cleanly.
            for meta in archive.entries().cloned().collect::<Vec<_>>() {
                let _ = archive.read_entry(&meta);
            }
        }
    }
}

#[test]
fn corrupted_central_directory_signature_is_rejected() {
    let built = two_entry_zip();
    let mut bytes = built.bytes;
    // Break the second CD record's signature; EOCD stays intact.
    let second_cd = built.cd_offset + 46 + "first.txt".len();
    assert_eq!(&bytes[second_cd..second_cd + 4], b"PK\x01\x02");
    bytes[second_cd + 3] = 0x07;
    assert!(matches!(
        ZipArchive::open(&bytes),
        Err(Error::BadCentralDirectory(_))
    ));
}

#[test]
fn central_directory_record_overrunning_declared_size_is_rejected() {
    // Hand-compose: local entries + first CD record + *half* of the second,
    // then an EOCD honestly claiming the truncated CD size but 2 entries.
    let built = two_entry_zip();
    let mut bytes = built.bytes[..built.cd_offset].to_vec();
    let first_record_len = 46 + "first.txt".len();
    let half_second = (46 + "second.txt".len()) / 2;
    let cd_size = first_record_len + half_second;
    bytes.extend_from_slice(&built.bytes[built.cd_offset..built.cd_offset + cd_size]);
    let cd_offset = built.cd_offset as u32;
    push_eocd(&mut bytes, 2, cd_size as u32, cd_offset, &[]);
    assert!(matches!(
        ZipArchive::open(&bytes),
        Err(Error::BadCentralDirectory(_))
    ));
}

#[test]
fn entry_data_running_past_input_is_truncated_error() {
    let built = two_entry_zip();
    let mut bytes = built.bytes;
    // Inflate the second entry's compressed size in its CD record to a huge
    // (but non-sentinel) value; the data slice then runs past the input.
    let second_cd = built.cd_offset + 46 + "first.txt".len();
    bytes[second_cd + 20..second_cd + 24].copy_from_slice(&0x00FF_FFFFu32.to_le_bytes());
    let archive = ZipArchive::open(&bytes).expect("open: CD structure is still self-consistent");
    assert_eq!(
        archive.read("second.txt"),
        Err(Error::Truncated {
            context: "entry data"
        })
    );
    // The intact first entry still reads fine.
    assert_eq!(
        archive.read("first.txt").expect("read").as_slice(),
        b"first payload"
    );
}

#[test]
fn u32_max_sizes_are_zip64_sentinels_not_overflow() {
    let built = two_entry_zip();
    let mut bytes = built.bytes;
    // 0xFFFF_FFFF in CD size fields is the ZIP64 sentinel: clean error, no
    // mis-parse as a 4 GiB entry.
    let first_cd = built.cd_offset;
    bytes[first_cd + 20..first_cd + 24].copy_from_slice(&u32::MAX.to_le_bytes());
    assert_eq!(ZipArchive::open(&bytes).unwrap_err(), Error::Zip64);
}

#[test]
fn zip64_eocd_locator_before_eocd_is_rejected() {
    let built = two_entry_zip();
    let mut bytes = built.bytes[..built.eocd_offset].to_vec();
    let zip64 = zip64_eocd_and_locator(
        built.cd_offset as u64,
        built.cd_size as u64,
        2,
        built.eocd_offset as u64,
    );
    bytes.extend_from_slice(&zip64);
    push_eocd(
        &mut bytes,
        2,
        built.cd_size as u32,
        built.cd_offset as u32,
        &[],
    );
    assert_eq!(ZipArchive::open(&bytes).unwrap_err(), Error::Zip64);
}

#[test]
fn eocd_sentinel_fields_are_zip64_markers() {
    let built = two_entry_zip();
    let mut bytes = built.bytes;
    // Entry-count sentinel 0xFFFF in the EOCD.
    bytes[built.eocd_offset + 8..built.eocd_offset + 10].copy_from_slice(&0xFFFFu16.to_le_bytes());
    bytes[built.eocd_offset + 10..built.eocd_offset + 12].copy_from_slice(&0xFFFFu16.to_le_bytes());
    assert_eq!(ZipArchive::open(&bytes).unwrap_err(), Error::Zip64);
}

#[test]
fn fake_eocd_hidden_in_comment_does_not_hijack_the_scan() {
    // Craft a comment whose fake EOCD magic even passes the position check
    // (comment_len reaches EOF exactly). CD self-consistency must reject it
    // and the scan must fall through to the real EOCD.
    let fake_cd_offset = 0u32;
    let fake_cd_size = 16u32;
    let comment_len = 22 + 5; // fake EOCD record + filler
    let mut comment = Vec::new();
    w32(&mut comment, EOCD_SIG);
    w16(&mut comment, 0);
    w16(&mut comment, 0);
    w16(&mut comment, 1);
    w16(&mut comment, 1);
    w32(&mut comment, fake_cd_size);
    w32(&mut comment, fake_cd_offset);
    w16(&mut comment, (comment_len - 22) as u16); // passes the position check
    comment.extend_from_slice(b"PAD!!");
    assert_eq!(comment.len(), comment_len);

    let built = build_zip_ex(
        &[ZipEntry::stored("ets/modules.abc", b"real abc")],
        &comment,
        &[],
    );
    let archive = ZipArchive::open(&built.bytes).expect("real EOCD must win");
    assert_eq!(
        archive.read("ets/modules.abc").expect("read").as_slice(),
        b"real abc"
    );
}

#[test]
fn eocd_comment_does_not_confuse_the_scan() {
    // A longer, plausible comment with embedded magic fragments.
    let comment = b"signed by Example Corp PK\x05\x06 trailing bytes";
    let built = build_zip_ex(&[ZipEntry::stored("a", b"b")], comment, &[]);
    let archive = ZipArchive::open(&built.bytes).expect("open");
    assert_eq!(archive.entries().count(), 1);
}

/// Read every entry; must never panic, whatever `open` accepted.
fn read_all(archive: &ZipArchive<'_>, input: &[u8]) {
    for meta in archive.entries().cloned().collect::<Vec<_>>() {
        let _ = archive.read_entry(&meta);
        let _ = archive.entry_compression(&meta);
    }
    let _ = abcd_hap::abc_modules(input);
}

#[test]
fn fuzz_sweep_never_panics() {
    let mut rng = Rng::new(0xABCD_0001);
    let reference = two_entry_zip().bytes;

    // 1. Pure random garbage.
    for _ in 0..1500 {
        let len = rng.below(2048);
        let mut buf = vec![0u8; len];
        for b in buf.iter_mut() {
            *b = rng.next() as u8;
        }
        // Seed the magic numbers often enough to reach deep code paths.
        if len > 30 && rng.below(2) == 0 {
            let pos = rng.below(len - 22);
            buf[pos..pos + 4].copy_from_slice(b"PK\x05\x06");
        }
        if let Ok(archive) = ZipArchive::open(&buf) {
            read_all(&archive, &buf);
        }
    }

    // 2. Random corruptions of a valid archive.
    for _ in 0..1500 {
        let mut buf = reference.clone();
        match rng.below(3) {
            0 => {
                // Byte flips.
                for _ in 0..=rng.below(8) {
                    let pos = rng.below(buf.len());
                    buf[pos] ^= rng.next() as u8;
                }
            }
            1 => {
                // Truncation.
                buf.truncate(rng.below(buf.len()));
            }
            _ => {
                // Splice random bytes into the middle.
                let pos = rng.below(buf.len());
                let extra = rng.below(64);
                for _ in 0..extra {
                    buf.insert(pos, rng.next() as u8);
                }
            }
        }
        if let Ok(archive) = ZipArchive::open(&buf) {
            read_all(&archive, &buf);
        }
    }
}
