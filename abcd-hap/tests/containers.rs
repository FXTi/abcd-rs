//! Container-level tests: sniffing, `.hap`/`.hsp`/`.hqf` extraction, and
//! `.app` nesting with provenance.

mod common;

use abcd_hap::{Compression, Container, EntryData, Error, MODULE_ABC, abc_modules};
use common::*;

const MODULE_JSON: &[u8] = br#"{"module":{"name":"entry","type":"entry"}}"#;
const PACK_INFO: &[u8] = br#"{"summary":{"modules":[{"name":"entry"}]}}"#;
const PATCH_JSON: &[u8] = br#"{"patch":{"name":"entry","type":"patch"}}"#;

fn abc_bytes(tag: u8) -> Vec<u8> {
    // Fake but recognizable abc payload.
    let mut v = b"PANDA\x00fake-abc".to_vec();
    v.extend(std::iter::repeat_n(tag, 4096));
    v
}

fn stored_hap(tag: u8) -> Vec<u8> {
    build_zip(&[
        ZipEntry::stored("module.json", MODULE_JSON),
        ZipEntry::stored(MODULE_ABC, &abc_bytes(tag)),
    ])
    .bytes
}

#[test]
fn minimal_hap_stored_roundtrip() {
    let abc = abc_bytes(0x11);
    let hap = build_zip(&[
        ZipEntry::stored("module.json", MODULE_JSON),
        ZipEntry::stored(MODULE_ABC, &abc),
    ])
    .bytes;

    match Container::sniff(&hap).expect("sniff") {
        Container::Module(_) => {}
        Container::App { .. } => panic!("hap misclassified as app"),
    }

    let modules = abc_modules(&hap).expect("abc_modules");
    assert_eq!(modules.len(), 1);
    let m = &modules[0];
    assert_eq!(m.entry_name, MODULE_ABC);
    assert_eq!(m.data.as_slice(), abc.as_slice());
    assert!(m.container_path.is_empty());
    match m.compression {
        Compression::Stored { data_offset } => {
            assert_eq!(&hap[data_offset as usize..][..abc.len()], abc.as_slice());
        }
        Compression::Deflated => panic!("stored abc classified as deflated"),
    }
    let module_json = m.module_json.as_ref().expect("module.json");
    assert_eq!(module_json.as_slice(), MODULE_JSON);
    assert!(m.patch_json.is_none());
}

#[test]
fn deflated_abc_roundtrip() {
    let abc = abc_bytes(0x22);
    let hap = build_zip(&[
        ZipEntry::deflated("module.json", MODULE_JSON),
        ZipEntry::deflated(MODULE_ABC, &abc),
    ])
    .bytes;

    let modules = abc_modules(&hap).expect("abc_modules");
    assert_eq!(modules.len(), 1);
    let m = &modules[0];
    assert_eq!(m.compression, Compression::Deflated);
    match &m.data {
        EntryData::Owned(v) => assert_eq!(v, &abc),
        EntryData::Borrowed(_) => panic!("deflated abc must be owned"),
    }
    assert_eq!(
        m.module_json.as_ref().expect("json").as_slice(),
        MODULE_JSON
    );
}

#[test]
fn hsp_is_a_module_container() {
    // An .hsp is layout-identical to a .hap (module.json says "shared"; the
    // JSON contents are the caller's business).
    let hsp = build_zip(&[
        ZipEntry::stored("module.json", br#"{"module":{"type":"shared"}}"#),
        ZipEntry::stored(MODULE_ABC, &abc_bytes(0x33)),
        ZipEntry::stored("pack.info", PACK_INFO),
    ])
    .bytes;

    match Container::sniff(&hsp).expect("sniff") {
        Container::Module(_) => {}
        Container::App { .. } => panic!("hsp misclassified as app"),
    }
    let modules = abc_modules(&hsp).expect("abc_modules");
    assert_eq!(modules.len(), 1);
    assert_eq!(modules[0].data.as_slice(), abc_bytes(0x33).as_slice());
}

#[test]
fn hqf_goes_down_module_path_and_exposes_patch_json() {
    let abc = abc_bytes(0x44);
    let hqf = build_zip(&[
        ZipEntry::stored("patch.json", PATCH_JSON),
        ZipEntry::deflated(MODULE_ABC, &abc),
        ZipEntry::stored("libs/arm64-v8a/libentry.so", b"\x7fELF-fake"),
    ])
    .bytes;

    match Container::sniff(&hqf).expect("sniff") {
        Container::Module(_) => {}
        Container::App { .. } => panic!("hqf misclassified as app"),
    }
    let modules = abc_modules(&hqf).expect("abc_modules");
    assert_eq!(modules.len(), 1);
    let m = &modules[0];
    assert_eq!(m.compression, Compression::Deflated);
    assert_eq!(m.data.as_slice(), abc.as_slice());
    assert_eq!(
        m.patch_json.as_ref().expect("patch.json").as_slice(),
        PATCH_JSON
    );
    // No module.json in a quick-fix package.
    assert!(m.module_json.is_none());
}

#[test]
fn fa_model_config_json_is_picked_up_as_module_json() {
    let hap = build_zip(&[
        ZipEntry::stored("config.json", br#"{"app":{"legacy":true}}"#),
        ZipEntry::stored(MODULE_ABC, &abc_bytes(0x55)),
    ])
    .bytes;
    let modules = abc_modules(&hap).expect("abc_modules");
    assert_eq!(modules.len(), 1);
    assert_eq!(
        modules[0]
            .module_json
            .as_ref()
            .expect("config.json")
            .as_slice(),
        br#"{"app":{"legacy":true}}"#
    );
}

#[test]
fn app_flattens_nested_hap_and_hsp_with_provenance() {
    let entry_hap = stored_hap(0x66);
    let shared_hsp = build_zip(&[
        ZipEntry::stored("module.json", br#"{"module":{"type":"shared"}}"#),
        ZipEntry::stored(MODULE_ABC, &abc_bytes(0x77)),
    ])
    .bytes;

    // Upstream packs nested haps DEFLATED inside the .app.
    let app = build_zip(&[
        ZipEntry::stored("pack.info", PACK_INFO),
        ZipEntry::deflated("entry.hap", &entry_hap),
        ZipEntry::deflated("shared.hsp", &shared_hsp),
    ])
    .bytes;

    let module_names = match Container::sniff(&app).expect("sniff") {
        Container::App { modules, .. } => modules,
        Container::Module(_) => panic!("app misclassified as module"),
    };
    assert_eq!(module_names, ["entry.hap", "shared.hsp"]);

    let modules = abc_modules(&app).expect("abc_modules");
    assert_eq!(modules.len(), 2);

    assert_eq!(modules[0].container_path, ["entry.hap".to_string()]);
    assert_eq!(modules[0].data.as_slice(), abc_bytes(0x66).as_slice());
    assert_eq!(
        modules[0].module_json.as_ref().expect("json").as_slice(),
        MODULE_JSON
    );

    assert_eq!(modules[1].container_path, ["shared.hsp".to_string()]);
    assert_eq!(modules[1].data.as_slice(), abc_bytes(0x77).as_slice());

    // Data lifted out of a nested container must be owned (the nested
    // archive bytes do not outlive the call), but the STORED data offset is
    // still reported relative to the nested archive.
    for m in &modules {
        match (&m.data, m.compression) {
            (EntryData::Owned(v), Compression::Stored { data_offset }) => {
                assert!(data_offset > 0);
                assert_eq!(v.len(), 4096 + b"PANDA\x00fake-abc".len());
            }
            _ => panic!("nested STORED abc must be owned with an offset hint"),
        }
    }
}

#[test]
fn app_with_only_packinfo_and_no_nested_modules_has_no_abc() {
    let app = build_zip(&[
        ZipEntry::stored("pack.info", PACK_INFO),
        ZipEntry::stored("README.md", b"nothing here"),
    ])
    .bytes;
    assert_eq!(abc_modules(&app).unwrap_err(), Error::NoAbcEntry);
}

#[test]
fn plain_zip_that_is_neither_module_nor_app_has_no_abc() {
    let zip = build_zip(&[
        ZipEntry::stored("foo.txt", b"foo"),
        ZipEntry::deflated("bar/baz.bin", &[1u8; 512]),
    ])
    .bytes;
    assert_eq!(abc_modules(&zip).unwrap_err(), Error::NoAbcEntry);
    assert!(matches!(Container::sniff(&zip), Err(Error::NoAbcEntry)));
}

#[test]
fn garbage_nested_hap_fails_cleanly() {
    let app = build_zip(&[
        ZipEntry::stored("pack.info", PACK_INFO),
        ZipEntry::deflated("broken.hap", b"this is not a zip"),
    ])
    .bytes;
    assert_eq!(abc_modules(&app).unwrap_err(), Error::NotZip);
}

#[test]
fn nested_app_is_not_recursed_into() {
    // Only *.hap / *.hsp entries are module candidates; an .app inside an
    // .app is out of the upstream nesting contract (depth cap = 2).
    let inner_app = build_zip(&[
        ZipEntry::stored("pack.info", PACK_INFO),
        ZipEntry::deflated("inner.hap", &stored_hap(0x88)),
    ])
    .bytes;
    let outer_app = build_zip(&[
        ZipEntry::stored("pack.info", PACK_INFO),
        ZipEntry::deflated("nested.app", &inner_app),
    ])
    .bytes;
    assert_eq!(abc_modules(&outer_app).unwrap_err(), Error::NoAbcEntry);
}

#[test]
fn nested_hap_without_abc_fails_cleanly() {
    let no_abc_hap = build_zip(&[ZipEntry::stored("module.json", MODULE_JSON)]).bytes;
    let app = build_zip(&[
        ZipEntry::stored("pack.info", PACK_INFO),
        ZipEntry::deflated("empty.hap", &no_abc_hap),
    ])
    .bytes;
    assert_eq!(abc_modules(&app).unwrap_err(), Error::NoAbcEntry);
}

#[test]
fn module_container_without_abc_entry_errors() {
    let hap = build_zip(&[ZipEntry::stored("module.json", MODULE_JSON)]).bytes;
    assert_eq!(abc_modules(&hap).unwrap_err(), Error::NoAbcEntry);
}
