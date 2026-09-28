//! Low-level ZIP central-directory reader tests (synthesized archives only).

mod common;

use abcd_hap::{Compression, EntryData, Error, METHOD_DEFLATE, METHOD_STORED, ZipArchive};
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

    let names: Vec<&str> = archive.entries().map(|e| e.name.as_str()).collect();
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
        EntryData::Owned(v) => assert_eq!(v, deflated_data),
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
fn crc_mismatch_is_not_checked_but_data_is_returned() {
    let built = build_zip(&[ZipEntry::stored("bad-crc", b"real data").with_crc(0xDEAD_BEEF)]);
    let archive = ZipArchive::open(&built.bytes).expect("open");
    assert_eq!(
        archive.read("bad-crc").expect("read").as_slice(),
        b"real data"
    );
    let meta = archive.entry("bad-crc").expect("meta");
    assert_eq!(meta.crc32, 0xDEAD_BEEF);
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
    assert_eq!(archive.entries().count(), 0);
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
