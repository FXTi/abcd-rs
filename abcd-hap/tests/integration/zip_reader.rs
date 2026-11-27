//! Low-level ZIP central-directory reader tests (synthesized archives only).

use std::borrow::Cow;

use crate::common;
use abcd_hap::{Compression, EntryData, Error, Limits, METHOD_DEFLATE, METHOD_STORED, ZipArchive};
use common::*;

#[test]
fn crc32_helper_is_honest() {
    // Well-known check value from the CRC-32 catalogue ("123456789").
    assert_eq!(crc32(b"123456789"), 0xCBF4_3926);
}

#[test]
fn stored_and_deflated_entries_roundtrip() {
    let stored_data = b"plain stored bytes";
    let deflated_data: Vec<u8> = (0..5000).map(|i| (i % 251) as u8).collect();
    let built = build_zip(&[
        ZipEntry::stored("a.txt", stored_data),
        ZipEntry::deflated("dir/b.txt", &deflated_data),
    ]);
    let archive = ZipArchive::open(&built.bytes).expect("open");

    let names: Vec<&str> = archive.entries().map(|e| e.name.as_ref()).collect();
    assert_eq!(names, ["a.txt", "dir/b.txt"]);

    let a = archive.entry("a.txt").expect("meta a");
    assert_eq!(a.method, METHOD_STORED);
    assert_eq!(a.compressed_size, stored_data.len() as u64);
    assert_eq!(a.uncompressed_size, stored_data.len() as u64);

    let b = archive.entry("dir/b.txt").expect("meta b");
    assert_eq!(b.method, METHOD_DEFLATE);
    assert_eq!(b.uncompressed_size, deflated_data.len() as u64);
    assert!(b.compressed_size < b.uncompressed_size);

    match archive.read("a.txt").expect("read a") {
        EntryData::Borrowed(s) => assert_eq!(s, stored_data),
        EntryData::Owned(_) => panic!("STORED entry must be returned as a borrowed slice"),
    }
    match archive.read("dir/b.txt").expect("read b") {
        EntryData::Owned(v) => assert_eq!(v.as_ref(), deflated_data.as_slice()),
        EntryData::Borrowed(_) => panic!("DEFLATE entry must be returned as owned bytes"),
    }
}

#[test]
fn stored_entry_is_zero_copy_into_input() {
    let data: Vec<u8> = (0..256).map(|i| i as u8).collect();
    let built = build_zip(&[ZipEntry::stored("payload.bin", &data)]);
    let archive = ZipArchive::open(&built.bytes).expect("open");
    let read = archive.read("payload.bin").expect("read");
    let EntryData::Borrowed(slice) = read else {
        panic!("expected borrow");
    };
    // The borrowed slice must point into the caller's buffer.
    let base = built.bytes.as_ptr() as usize;
    let ptr = slice.as_ptr() as usize;
    assert!(ptr >= base && ptr < base + built.bytes.len());
}

#[test]
fn entry_meta_name_is_zero_copy_borrowed_for_utf8_and_lossy_owned_for_invalid_bytes() {
    let utf8_name = "ets/模块/modules.abc";
    let built = build_zip(&[ZipEntry::stored(utf8_name, b"abc")]);
    let archive = ZipArchive::open(&built.bytes).expect("open");
    let meta = archive.entry(utf8_name).expect("utf8 meta");
    let Cow::Borrowed(borrowed_name) = meta.name else {
        panic!("valid UTF-8 entry name must be Cow::Borrowed");
    };
    let base = built.bytes.as_ptr() as usize;
    let ptr = borrowed_name.as_ptr() as usize;
    assert!(
        ptr >= base && ptr + borrowed_name.len() <= base + built.bytes.len(),
        "borrowed entry name slice must point into caller archive buffer"
    );

    // Patch one byte inside the central-directory entry name to invalid UTF-8 (0xFF).
    let mut raw = built.bytes.clone();
    let cd_name_start = built.cd_offset + 46;
    raw[cd_name_start + 4] = 0xFF;
    let lossy_archive = ZipArchive::open(&raw).expect("open with non-UTF-8 name");
    let lossy_meta = lossy_archive.entries().next().expect("entry");
    assert!(
        matches!(lossy_meta.name, Cow::Owned(_)),
        "invalid UTF-8 bytes must fall back cleanly to Cow::Owned"
    );
}

#[test]
fn entry_lookup_missing_is_none_and_read_errors() {
    let built = build_zip(&[ZipEntry::stored("a.txt", b"x")]);
    let archive = ZipArchive::open(&built.bytes).expect("open");
    assert!(archive.entry("nope").is_none());
    assert_eq!(
        archive.read("nope"),
        Err(Error::EntryNotFound("nope".to_string()))
    );
}

#[test]
fn local_extra_field_is_skipped_using_local_header_lengths() {
    // Local-header name/extra lengths are authoritative for finding the data
    // (they may differ from the CD record).
    let extra: Vec<u8> = (0..64).map(|i| i as u8).collect();
    let built = build_zip(&[ZipEntry::stored("x.bin", b"payload").with_extra_local(&extra)]);
    let archive = ZipArchive::open(&built.bytes).expect("open");
    assert_eq!(archive.read("x.bin").expect("read").as_slice(), b"payload");
}

#[test]
fn stored_data_offset_matches_actual_payload_position() {
    let data = b"find-me-payload-0123456789";
    let built = build_zip(&[
        ZipEntry::stored("first", b"aaaa"),
        ZipEntry::stored("second", data),
    ]);
    let archive = ZipArchive::open(&built.bytes).expect("open");
    let meta = archive.entry("second").expect("meta");
    match archive.entry_compression(meta).expect("compression") {
        Compression::Stored { data_offset } => {
            let at = &built.bytes[data_offset as usize..data_offset as usize + data.len()];
            assert_eq!(at, data);
        }
        Compression::Deflated => panic!("stored entry classified as deflated"),
    }
    assert_eq!(
        archive.entry_compression(archive.entry("first").unwrap()),
        archive.entry_compression(archive.entry("first").unwrap())
    );
}

#[test]
fn deflated_entry_reports_deflated_compression() {
    let built = build_zip(&[ZipEntry::deflated("d", &[7u8; 1000])]);
    let archive = ZipArchive::open(&built.bytes).expect("open");
    let meta = archive.entry("d").expect("meta");
    assert_eq!(archive.entry_compression(meta), Ok(Compression::Deflated));
}

#[test]
fn unsupported_method_is_a_clean_error_on_read() {
    let built = build_zip(&[ZipEntry::raw("weird.bin", b"data", 99)]);
    let archive = ZipArchive::open(&built.bytes).expect("open still works");
    assert_eq!(
        archive.read("weird.bin"),
        Err(Error::UnsupportedMethod {
            name: "weird.bin".to_string(),
            method: 99,
        })
    );
}

#[test]
fn encrypted_flag_is_a_clean_error_on_read() {
    let built = build_zip(&[ZipEntry::stored("secret", b"data").with_flags(0x1)]);
    let archive = ZipArchive::open(&built.bytes).expect("open still works");
    assert_eq!(
        archive.read("secret"),
        Err(Error::Encrypted {
            name: "secret".to_string()
        })
    );
}

#[test]
fn crc_mismatch_in_header_is_rejected() {
    let payload = b"real data";
    let built = build_zip(&[ZipEntry::stored("bad-crc", payload).with_crc(0xDEAD_BEEF)]);
    let archive = ZipArchive::open(&built.bytes).expect("open");
    let meta = archive.entry("bad-crc").expect("meta");
    assert_eq!(meta.crc32, 0xDEAD_BEEF);
    assert_eq!(
        archive.read("bad-crc"),
        Err(Error::CrcMismatch {
            name: "bad-crc".to_string(),
            expected: 0xDEAD_BEEF,
            actual: crc32(payload),
        })
    );
}

#[test]
fn stored_and_deflated_single_bit_payload_flips_fail_crc_verification() {
    // 1. STORED: flip one bit directly inside the stored payload bytes.
    let plain = b"stored payload guarded by IEEE CRC-32";
    let built_stored = build_zip(&[ZipEntry::stored("stored.abc", plain)]);
    let mut raw_stored = built_stored.bytes.clone();
    let archive_ref = ZipArchive::open(&built_stored.bytes).expect("open");
    let Compression::Stored { data_offset } = archive_ref
        .entry_compression(archive_ref.entry("stored.abc").unwrap())
        .unwrap()
    else {
        panic!("expected stored");
    };
    raw_stored[data_offset as usize + 5] ^= 0x01;
    let corrupt_stored = ZipArchive::open(&raw_stored).expect("open corrupt stored");
    let mut flipped_plain = plain.to_vec();
    flipped_plain[5] ^= 0x01;
    assert_eq!(
        corrupt_stored.read("stored.abc"),
        Err(Error::CrcMismatch {
            name: "stored.abc".to_string(),
            expected: crc32(plain),
            actual: crc32(&flipped_plain),
        })
    );

    // 2. DEFLATE: flip one bit in the uncompressed payload while keeping the
    //    original expected CRC-32, plus flip one bit in the raw deflate stream.
    let orig_deflate_plain: Vec<u8> = (0..1024).map(|i| (i * 7 % 251) as u8).collect();
    let mut flipped_deflate_plain = orig_deflate_plain.clone();
    flipped_deflate_plain[333] ^= 0x04;
    let spoofed_deflate = ZipEntry::deflated("deflated.abc", &flipped_deflate_plain)
        .with_crc(crc32(&orig_deflate_plain));
    let built_deflate = build_zip(&[spoofed_deflate]);
    let corrupt_deflate = ZipArchive::open(&built_deflate.bytes).expect("open spoofed deflate");
    assert_eq!(
        corrupt_deflate.read("deflated.abc"),
        Err(Error::CrcMismatch {
            name: "deflated.abc".to_string(),
            expected: crc32(&orig_deflate_plain),
            actual: crc32(&flipped_deflate_plain),
        })
    );

    // Raw stream bit flip must fail with either Inflate or CrcMismatch, never Ok.
    let clean_deflate = build_zip(&[ZipEntry::deflated("stream.abc", &orig_deflate_plain)]);
    let mut raw_stream = clean_deflate.bytes.clone();
    let stream_start = clean_deflate.local_offsets[0] + 30 + "stream.abc".len();
    raw_stream[stream_start + 2] ^= 0x02;
    let bitflipped_stream = ZipArchive::open(&raw_stream).expect("open");
    assert!(matches!(
        bitflipped_stream.read("stream.abc"),
        Err(Error::Inflate { .. } | Error::CrcMismatch { .. })
    ));
}

#[test]
fn read_with_limits_enforces_max_entry_bytes() {
    let payload = vec![0x5Au8; 4096];
    let built = build_zip(&[
        ZipEntry::stored("stored.bin", &payload),
        ZipEntry::deflated("deflated.bin", &payload),
    ]);
    let archive = ZipArchive::open(&built.bytes).expect("open");
    let tight = Limits {
        max_entry_bytes: 2048,
        max_total_bytes: 1024 * 1024,
    };
    assert_eq!(
        archive.read_with_limits("stored.bin", tight),
        Err(Error::EntryTooLarge {
            name: "stored.bin".to_string()
        })
    );
    assert_eq!(
        archive.read_with_limits("deflated.bin", tight),
        Err(Error::EntryTooLarge {
            name: "deflated.bin".to_string()
        })
    );
    assert_eq!(
        archive
            .read_with_limits("deflated.bin", Limits::default())
            .expect("within default limits")
            .as_slice(),
        payload.as_slice()
    );
}

#[test]
fn dotdot_entry_name_is_a_lookup_key_only() {
    // In-memory only: hostile names never touch the filesystem.
    let built = build_zip(&[ZipEntry::stored("../../etc/passwd", b"not a path")]);
    let archive = ZipArchive::open(&built.bytes).expect("open");
    let meta = archive.entry("../../etc/passwd").expect("lookup by key");
    assert_eq!(meta.name, "../../etc/passwd");
    assert_eq!(
        archive.read("../../etc/passwd").expect("read").as_slice(),
        b"not a path"
    );
}

#[test]
fn signing_block_junk_before_central_directory_is_tolerated() {
    // Signed haps carry a signing block between the last entry and the CD;
    // a CD-first reader with absolute offsets is unaffected.
    let junk = b"APK Sig Block 42------------garbage-garbage-garbage";
    let built = build_zip_ex(
        &[ZipEntry::stored("ets/modules.abc", b"abc-bytes")],
        &[],
        junk,
    );
    let archive = ZipArchive::open(&built.bytes).expect("open");
    assert_eq!(
        archive.read("ets/modules.abc").expect("read").as_slice(),
        b"abc-bytes"
    );
}

#[test]
fn empty_zip_opens_with_zero_entries() {
    let built = build_zip(&[]);
    let archive = ZipArchive::open(&built.bytes).expect("open");
    assert_eq!(archive.len(), 0);
    assert!(archive.is_empty());
    assert!(archive.entry_at(0).is_none());
    assert_eq!(archive.entries().count(), 0);
}

#[test]
fn entry_at_indexes_central_directory_ordinals_including_duplicate_names() {
    let built = build_zip(&[
        ZipEntry::stored("dup.bin", b"first-payload"),
        ZipEntry::deflated("dup.bin", b"second-payload-longer"),
        ZipEntry::stored("tail.txt", b"tail"),
    ]);
    let archive = ZipArchive::open(&built.bytes).expect("open");
    assert_eq!(archive.len(), 3);
    assert!(!archive.is_empty());
    assert!(archive.entry_at(3).is_none());

    let e0 = archive.entry_at(0).expect("ordinal 0");
    let e1 = archive.entry_at(1).expect("ordinal 1");
    let e2 = archive.entry_at(2).expect("ordinal 2");
    assert_eq!(e0.name, "dup.bin");
    assert_eq!(e1.name, "dup.bin");
    assert_eq!(e2.name, "tail.txt");
    assert_ne!(e0.local_header_offset, e1.local_header_offset);

    assert_eq!(
        archive.read_entry(e0).expect("read ordinal 0").as_slice(),
        b"first-payload"
    );
    assert_eq!(
        archive.read_entry(e1).expect("read ordinal 1").as_slice(),
        b"second-payload-longer"
    );
    assert_eq!(
        archive.read_entry(e2).expect("read ordinal 2").as_slice(),
        b"tail"
    );
}

#[test]
fn non_zip_inputs_are_rejected() {
    assert_eq!(ZipArchive::open(b"").unwrap_err(), Error::NotZip);
    assert_eq!(ZipArchive::open(b"PK").unwrap_err(), Error::NotZip);
    assert_eq!(
        ZipArchive::open(b"this is definitely not a zip archive at all").unwrap_err(),
        Error::NotZip
    );
    // A local file header alone is not an archive.
    let only_local = build_zip(&[ZipEntry::stored("a", b"b")]);
    let head = &only_local.bytes[..only_local.cd_offset];
    assert_eq!(ZipArchive::open(head).unwrap_err(), Error::NotZip);
}

#[test]
fn multi_disk_archive_is_a_clean_error() {
    let built = build_zip(&[ZipEntry::stored("a", b"b")]);
    let mut bytes = built.bytes;
    // EOCD disk-number field (offset +4) nonzero => spanned archive.
    let pos = built.eocd_offset + 4;
    bytes[pos] = 1;
    assert_eq!(ZipArchive::open(&bytes).unwrap_err(), Error::MultiDisk);
}
