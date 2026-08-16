//! Regression tests for review finding #4 (file-type detection was stubbed
//! to always report Dynamic).

use abcd_file::{AccessFlags, Builder, SourceLang, Type, file_type};
use abcd_file_sys::FileType;

fn minimal_file() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.finalize().expect("finalize")
}

#[test]
fn built_file_is_dynamic() {
    let data = minimal_file();
    assert_eq!(file_type(&data), FileType::Dynamic);
}

#[test]
fn static_version_header_is_static() {
    // Hand-craft a header with magic + STATIC_VERSION {0,0,0,6} and a
    // consistent file_size — the rest of the file is irrelevant for typing.
    let mut data = vec![0u8; 60];
    data[..8].copy_from_slice(b"PANDA\0\0\0");
    data[12..16].copy_from_slice(&[0, 1, 0, 7]);
    data[16..20].copy_from_slice(&60u32.to_le_bytes());
    assert_eq!(file_type(&data), FileType::Static);
}

#[test]
fn invalid_inputs_are_rejected() {
    // Garbage magic.
    assert_eq!(file_type(&[0xAB; 100]), FileType::Invalid);
    // Too small for a header.
    assert_eq!(file_type(&[0x50, 0x41, 0x4E, 0x44]), FileType::Invalid);
    // Header file_size mismatch (append one byte).
    let mut data = minimal_file();
    data.push(0);
    assert_eq!(file_type(&data), FileType::Invalid);
    // Empty input.
    assert_eq!(file_type(&[]), FileType::Invalid);
}
