//! Adversarial inputs: truncations, fake EOCDs, ZIP64 markers, overflow
//! sizes, and a deterministic no-panic fuzz sweep. The iron rule is that no
//! input byte pattern may panic the parser.

use crate::common;
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

#[test]
fn spoofed_400mib_deflate_uncompressed_size_rejected_before_allocation() {
    let tiny_payload = b"sixteen-byte-msg";
    let built = build_zip(&[ZipEntry::deflated("bomb.abc", tiny_payload)]);
    let mut bytes = built.bytes;

    // 400 MiB is deliberately below Limits::DEFAULT.max_entry_bytes (512 MiB)
    // so the RFC 1951 1032x compression-ratio guard is what catches it before
    // miniz_oxide ever allocates an output buffer.
    let spoofed_size: u32 = 400 * 1024 * 1024;
    let local_off = built.local_offsets[0];
    bytes[local_off + 22..local_off + 26].copy_from_slice(&spoofed_size.to_le_bytes());
    let cd_off = built.cd_offset;
    bytes[cd_off + 24..cd_off + 28].copy_from_slice(&spoofed_size.to_le_bytes());

    let archive = ZipArchive::open(&bytes).expect("CD layout remains structurally valid");
    let err = archive
        .read("bomb.abc")
        .expect_err("spoofed 400 MiB ratio must fail");
    assert!(
        matches!(&err, Error::Inflate { name, reason } if name == "bomb.abc" && reason.contains("RFC 1951")),
        "unexpected error: {err:?}"
    );

    // Zero-byte compressed stream claiming non-zero uncompressed output is also rejected.
    let mut empty_deflate = ZipEntry::raw("empty_deflate.abc", b"non-empty", 8);
    empty_deflate.compressed.clear();
    let built_zero = build_zip(&[empty_deflate]);
    let zero_archive = ZipArchive::open(&built_zero.bytes).expect("open");
    assert!(matches!(
        zero_archive.read("empty_deflate.abc"),
        Err(Error::Inflate { .. })
    ));
}

#[test]
fn bogus_high_entry_count_on_tiny_buffer_fails_without_overalloc() {
    let mut bytes = vec![0u8; 64];
    bytes[0..4].copy_from_slice(b"PK\x01\x02");
    // Claim 65,534 entries inside a 64-byte CD span: O(1) pre-check must reject.
    push_eocd(&mut bytes, 0xFFFE, 64, 0, &[]);
    assert!(matches!(
        ZipArchive::open(&bytes),
        Err(Error::BadCentralDirectory(_))
    ));
}

#[test]
fn eocd_candidate_flood_is_capped_and_survives_256kib_stack() {
    // Construct > 1,000 back-to-back position-consistent fake EOCD records
    // pointing at a fake central directory that fails partway through.
    let fake_cd_entries = 128u16;
    let cd_record_len = 46usize;
    let fake_cd_size = usize::from(fake_cd_entries) * cd_record_len;
    let mut flood = vec![0u8; fake_cd_size];
    // Give the first 64 records valid PK\x01\x02 headers and corrupt record 64.
    for i in 0..64 {
        let off = i * cd_record_len;
        flood[off..off + 4].copy_from_slice(b"PK\x01\x02");
    }

    let num_fake_eocds = 1200usize;
    let total_tail = num_fake_eocds * 22;
    assert!(total_tail <= 0xFFFF);
    for idx in 0..num_fake_eocds {
        let remaining_after = (num_fake_eocds - 1 - idx) * 22;
        push_eocd(&mut flood, fake_cd_entries, fake_cd_size as u32, 0, &[]);
        // Patch comment_len so pos + 22 + comment_len == final EOF for EVERY fake EOCD!
        let comment_len_pos = flood.len() - 2;
        flood[comment_len_pos..comment_len_pos + 2]
            .copy_from_slice(&(remaining_after as u16).to_le_bytes());
    }

    // Build a nested .app bundle as well to exercise iterative container unpacking
    // under the Engineering Invariant #1 256 KiB stack budget.
    let inner_hap = build_zip(&[
        ZipEntry::stored("module.json", br#"{"module":{"name":"entry"}}"#),
        ZipEntry::stored("ets/modules.abc", b"PANDA\x00abc"),
    ])
    .bytes;
    let res_hsp = build_zip(&[ZipEntry::stored(
        "module.json",
        br#"{"module":{"name":"res"}}"#,
    )])
    .bytes;
    let app = build_zip(&[
        ZipEntry::deflated("res.hsp", &res_hsp),
        ZipEntry::deflated("entry.hap", &inner_hap),
    ])
    .bytes;

    let handle = std::thread::Builder::new()
        .name("hap-256k-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(move || {
            assert!(matches!(
                ZipArchive::open(&flood),
                Err(Error::BadCentralDirectory(_))
            ));
            let modules = abcd_hap::abc_modules(&app).expect("iterative app unpack");
            assert_eq!(modules.len(), 1);
            assert_eq!(modules[0].container_path, ["entry.hap".to_string()]);
        })
        .expect("spawn 256 KiB thread");
    handle.join().expect("256 KiB stack thread panicked");
}
