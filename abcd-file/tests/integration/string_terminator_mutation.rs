//! P0 regression tests (memory safety): a corrupted MUTF-8 NUL terminator
//! in a string item must surface as a clean structured decode error —
//! never a heap overflow.
//!
//! Root cause: the bridge sized the Rust destination buffer from the
//! string item's length tag (`vec![u16; utf16_length]`) but drove the
//! MUTF-8 -> UTF-16 conversion with `strlen()`. Flipping the terminator
//! byte made the conversion run into the neighboring items and write past
//! the prefix-sized buffer (observed downstream as hashbrown "Went past
//! end of probe sequence" / SIGABRT in the string interner).

use abcd_file::{AccessFlags, Builder, Error, SourceLang, Type, decode};

/// Minimal file with one method named `target`.
fn file_with_target_method() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "target",
        proto,
        AccessFlags::PUBLIC,
        &[0x65], // return-void
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.finalize().expect("finalize")
}

/// Offset of the unique `target` string payload (its NUL terminator
/// included in the window).
fn target_payload_offset(data: &[u8]) -> usize {
    let needle = b"target\0";
    let hits: Vec<usize> = data
        .windows(needle.len())
        .enumerate()
        .filter_map(|(i, w)| (w == needle).then_some(i))
        .collect();
    assert_eq!(hits.len(), 1, "the method-name string item must be unique");
    hits[0]
}

#[test]
fn unmutated_control_decodes() {
    let data = file_with_target_method();
    let file = decode(&data).expect("the unmutated file must decode");
    let names: Vec<&str> = file
        .classes
        .values()
        .flat_map(|c| c.methods.iter())
        .filter_map(|m| file.strings.resolve(m.name))
        .collect();
    assert!(names.contains(&"target"), "method names: {names:?}");
}

/// The fuzz reproducer: flip the NUL terminator of the method-name string
/// to a 3-byte MUTF-8 lead. Before the fix this overflowed the prefix-sized
/// UTF-16 buffer during decode; after the fix it must be a clean error.
#[test]
fn corrupted_string_terminator_is_a_clean_error() {
    let mut data = file_with_target_method();
    let pos = target_payload_offset(&data);
    data[pos + 6] = 0xe1; // destroy the NUL terminator of "target"

    let err = decode(&data)
        .expect_err("a corrupted string terminator must be a structured error, not a crash");
    assert!(
        matches!(err, Error::Malformed { .. } | Error::InvalidString(_)),
        "unexpected error variant: {err}"
    );
}
