//! Regression tests for review findings #7 (open validation) and #8
//! (no C++ exception may cross the FFI boundary).

use abcd_file::{AccessFlags, Builder, SourceLang, Type, decode};

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
fn bad_magic_rejected() {
    let err = decode(&[0xAB; 100]).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("bad magic"), "got: {msg}");
}

#[test]
fn too_small_rejected() {
    let err = decode(&[0x50, 0x41, 0x4E, 0x44]).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("too small"), "got: {msg}");
}

#[test]
fn truncated_file_does_not_abort() {
    let data = minimal_file();

    // Truncations at various points: every case must yield a Rust result —
    // never an FFI-crossing exception (SIGABRT). Partial decodes are fine
    // (graceful degradation); the invariant under test is process survival.
    let cuts = [60usize, 80, 120, data.len() / 2, data.len() - 1];
    for cut in cuts {
        let truncated = &data[..cut.min(data.len())];
        let _ = decode(truncated); // must terminate normally
    }
}

#[test]
fn corrupted_body_does_not_abort() {
    let mut data = minimal_file();
    // Scramble the region after the header.
    for b in data.iter_mut().skip(64) {
        *b ^= 0xFF;
    }
    // Must terminate with a Rust result, not a signal.
    let _ = decode(&data);
}
