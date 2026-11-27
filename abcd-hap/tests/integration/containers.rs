//! Container-level tests: sniffing, `.hap`/`.hsp`/`.hqf` extraction, and
//! `.app` nesting with provenance.

use std::sync::Arc;

use crate::common;
use abcd_hap::{
    Compression, Container, EntryData, Error, Limits, MODULE_ABC, ManifestSummary, abc_modules,
    abc_modules_with_limits,
};
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
        EntryData::Owned(v) => assert_eq!(v.as_ref(), abc.as_slice()),
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

fn entry_names<'a>(modules: &'a [abcd_hap::AbcModule<'a>]) -> Vec<&'a str> {
    modules.iter().map(|m| m.entry_name.as_str()).collect()
}

#[test]
fn modules_abc_stays_first_among_per_ability_entries() {
    // Wild layout: one shared modules.abc plus per-ability bytecode.
    let hap = build_zip(&[
        ZipEntry::stored("ets/Application/AbilityStage.abc", &abc_bytes(0xA1)),
        ZipEntry::stored("module.json", MODULE_JSON),
        ZipEntry::stored(MODULE_ABC, &abc_bytes(0xA2)),
        ZipEntry::stored(
            "ets/ServiceExtension/ServiceExtension.abc",
            &abc_bytes(0xA3),
        ),
    ])
    .bytes;

    match Container::sniff(&hap).expect("sniff") {
        Container::Module(_) => {}
        Container::App { .. } => panic!("hap misclassified as app"),
    }
    let modules = abc_modules(&hap).expect("abc_modules");
    assert_eq!(
        entry_names(&modules),
        [
            MODULE_ABC,
            "ets/Application/AbilityStage.abc",
            "ets/ServiceExtension/ServiceExtension.abc",
        ]
    );
    assert_eq!(modules[0].data.as_slice(), abc_bytes(0xA2).as_slice());
    assert_eq!(modules[1].data.as_slice(), abc_bytes(0xA1).as_slice());
    assert_eq!(modules[2].data.as_slice(), abc_bytes(0xA3).as_slice());
    // The hap-level manifest is shared: every module carries it.
    for m in &modules {
        assert!(m.container_path.is_empty());
        assert_eq!(
            m.module_json.as_ref().expect("module.json").as_slice(),
            MODULE_JSON
        );
    }
}

#[test]
fn per_ability_entries_without_modules_abc_yield_all_in_cd_order() {
    // 3.2-era wild layout: no ets/modules.abc at all, one abc per ability.
    let hap = build_zip(&[
        ZipEntry::stored("module.json", MODULE_JSON),
        ZipEntry::stored(
            "ets/UIExtAbility/BluetoothUIExtAbility.abc",
            &abc_bytes(0xB1),
        ),
        ZipEntry::stored("ets/extensionability/UserAuthAbility.abc", &abc_bytes(0xB2)),
        ZipEntry::stored("ets/Application/MyAbilityStage.abc", &abc_bytes(0xB3)),
    ])
    .bytes;

    // Sniff must accept the container as a module without modules.abc.
    match Container::sniff(&hap).expect("sniff") {
        Container::Module(_) => {}
        Container::App { .. } => panic!("per-ability hap misclassified as app"),
    }
    let modules = abc_modules(&hap).expect("abc_modules");
    assert_eq!(
        entry_names(&modules),
        [
            "ets/UIExtAbility/BluetoothUIExtAbility.abc",
            "ets/extensionability/UserAuthAbility.abc",
            "ets/Application/MyAbilityStage.abc",
        ]
    );
}

#[test]
fn fa_model_assets_js_app_abc_entries() {
    // FA-era wild layout: bytecode under assets/js/<ability>/app.abc with a
    // config.json manifest.
    let hap = build_zip(&[
        ZipEntry::stored("config.json", br#"{"app":{"legacy":true}}"#),
        ZipEntry::stored("assets/js/MainAbility/app.abc", &abc_bytes(0xC1)),
        ZipEntry::stored("assets/js/default/app.abc", &abc_bytes(0xC2)),
    ])
    .bytes;

    let modules = abc_modules(&hap).expect("abc_modules");
    assert_eq!(
        entry_names(&modules),
        ["assets/js/MainAbility/app.abc", "assets/js/default/app.abc"]
    );
    for m in &modules {
        assert_eq!(
            m.module_json.as_ref().expect("config.json").as_slice(),
            br#"{"app":{"legacy":true}}"#
        );
    }
}

#[test]
fn abc_entries_outside_ets_prefix_still_count() {
    // Enumeration is uniform: any entry whose name ends in .abc, wherever it
    // sits — the path is the identity, not a whitelist.
    let hap = build_zip(&[
        ZipEntry::stored("module.json", MODULE_JSON),
        ZipEntry::stored("foo.abc", &abc_bytes(0xD1)),
        ZipEntry::stored("res/raw/leftover.abc", &abc_bytes(0xD2)),
        ZipEntry::stored("docs/notes.ABC", &abc_bytes(0xD3)),
    ])
    .bytes;

    match Container::sniff(&hap).expect("sniff") {
        Container::Module(_) => {}
        Container::App { .. } => panic!("misclassified as app"),
    }
    let modules = abc_modules(&hap).expect("abc_modules");
    assert_eq!(
        entry_names(&modules),
        ["foo.abc", "res/raw/leftover.abc", "docs/notes.ABC"]
    );
    // Entry name is echoed back verbatim (case preserved).
    assert_eq!(modules[2].entry_name, "docs/notes.ABC");
}

#[test]
fn app_nested_hap_with_per_ability_layout_flattens() {
    let nested = build_zip(&[
        ZipEntry::stored("module.json", MODULE_JSON),
        ZipEntry::stored("ets/Application/AbilityStage.abc", &abc_bytes(0xE1)),
        ZipEntry::stored(
            "ets/ServiceExtension/ServiceExtension.abc",
            &abc_bytes(0xE2),
        ),
    ])
    .bytes;
    let app = build_zip(&[
        ZipEntry::stored("pack.info", PACK_INFO),
        ZipEntry::deflated("entry.hap", &nested),
    ])
    .bytes;

    let modules = abc_modules(&app).expect("abc_modules");
    assert_eq!(
        entry_names(&modules),
        [
            "ets/Application/AbilityStage.abc",
            "ets/ServiceExtension/ServiceExtension.abc",
        ]
    );
    for m in &modules {
        assert_eq!(m.container_path, ["entry.hap".to_string()]);
        assert!(matches!(m.data, EntryData::Owned(_)));
        assert_eq!(
            m.module_json.as_ref().expect("module.json").as_slice(),
            MODULE_JSON
        );
    }
    assert_eq!(modules[0].data.as_slice(), abc_bytes(0xE1).as_slice());
    assert_eq!(modules[1].data.as_slice(), abc_bytes(0xE2).as_slice());
}

#[test]
fn app_skips_resource_only_nested_hsp_and_hap_siblings() {
    let res_only_hsp = build_zip(&[
        ZipEntry::stored(
            "module.json",
            br#"{"module":{"name":"skin","type":"shared"}}"#,
        ),
        ZipEntry::stored("resources/base/media/icon.png", b"\x89PNG-fake"),
    ])
    .bytes;
    let entry_hap = stored_hap(0xF1);
    let native_only_hap = build_zip(&[
        ZipEntry::stored(
            "module.json",
            br#"{"module":{"name":"native","type":"feature"}}"#,
        ),
        ZipEntry::stored("libs/arm64-v8a/libnative.so", b"\x7fELF-fake"),
    ])
    .bytes;

    let app = build_zip(&[
        ZipEntry::stored("pack.info", PACK_INFO),
        ZipEntry::deflated("skin.hsp", &res_only_hsp),
        ZipEntry::deflated("entry.hap", &entry_hap),
        ZipEntry::deflated("native.hap", &native_only_hap),
    ])
    .bytes;

    let modules = abc_modules(&app).expect("resource-only nested siblings must be skipped");
    assert_eq!(modules.len(), 1);
    assert_eq!(modules[0].container_path, ["entry.hap".to_string()]);
    assert_eq!(modules[0].entry_name, MODULE_ABC);
    assert_eq!(modules[0].data.as_slice(), abc_bytes(0xF1).as_slice());

    // Real corruption in a sibling nested .hsp (e.g. bad outer CRC) must still propagate.
    let bad_app = build_zip(&[
        ZipEntry::stored("pack.info", PACK_INFO),
        ZipEntry::deflated("entry.hap", &entry_hap),
        ZipEntry::deflated("corrupt.hsp", &res_only_hsp).with_crc(0xBAD0_C0DE),
    ])
    .bytes;
    assert!(matches!(
        abc_modules(&bad_app),
        Err(Error::CrcMismatch { name, .. }) if name == "corrupt.hsp"
    ));
}

#[test]
fn abc_modules_with_limits_enforces_cumulative_max_total_bytes_across_app() {
    let hap_a = stored_hap(0x31);
    let hap_b = stored_hap(0x32);
    let app = build_zip(&[
        ZipEntry::stored("pack.info", PACK_INFO),
        ZipEntry::deflated("a.hap", &hap_a),
        ZipEntry::deflated("b.hap", &hap_b),
    ])
    .bytes;

    // Generous budget succeeds and extracts both modules.
    let all = abc_modules_with_limits(&app, Limits::DEFAULT).expect("within default limits");
    assert_eq!(all.len(), 2);

    // Budget sufficient for a.hap (~4.2 KiB archive + ~4.1 KiB .abc + json)
    // but exceeded once b.hap + its .abc are accumulated (~16.7 KiB total).
    let single_module_budget = Limits {
        max_entry_bytes: 64 * 1024,
        max_total_bytes: 10 * 1024,
    };
    assert!(matches!(
        abc_modules_with_limits(&app, single_module_budget),
        Err(Error::EntryTooLarge { .. })
    ));

    // Per-entry cap smaller than one .abc payload also rejects cleanly.
    let tiny_entry_budget = Limits {
        max_entry_bytes: 1024,
        max_total_bytes: 1024 * 1024,
    };
    assert!(matches!(
        abc_modules_with_limits(&app, tiny_entry_budget),
        Err(Error::EntryTooLarge { .. })
    ));
}

#[test]
fn multi_abc_shared_manifest_uses_single_arc_under_tight_limits() {
    // Construct large manifest payloads so per-module duplication would blow
    // the cumulative `max_total_bytes` budget.
    let mut big_manifest = br#"{"module":{"name":"shared_entry","type":"entry","pad":""#.to_vec();
    big_manifest.extend(std::iter::repeat_n(b'M', 32 * 1024));
    big_manifest.extend_from_slice(br#""}}"#);

    let mut big_patch = br#"{"patch":{"name":"hotfix","pad":""#.to_vec();
    big_patch.extend(std::iter::repeat_n(b'P', 16 * 1024));
    big_patch.extend_from_slice(br#""}}"#);

    let abc0 = abc_bytes(0x90);
    let abc1 = abc_bytes(0x91);
    let abc2 = abc_bytes(0x92);
    let abc3 = abc_bytes(0x93);

    // 1. Top-level container with DEFLATED manifests + 4 .abc modules.
    let top_hap = build_zip(&[
        ZipEntry::deflated("module.json", &big_manifest),
        ZipEntry::deflated("patch.json", &big_patch),
        ZipEntry::stored(MODULE_ABC, &abc0),
        ZipEntry::stored("ets/AbilityA.abc", &abc1),
        ZipEntry::stored("ets/AbilityB.abc", &abc2),
        ZipEntry::stored("ets/AbilityC.abc", &abc3),
    ])
    .bytes;

    let exact_inner_bytes =
        (big_manifest.len() + big_patch.len() + abc0.len() + abc1.len() + abc2.len() + abc3.len())
            as u64;
    let top_limits = Limits {
        max_entry_bytes: 64 * 1024,
        max_total_bytes: exact_inner_bytes,
    };
    let top_modules =
        abc_modules_with_limits(&top_hap, top_limits).expect("shared Arc fits exact budget");
    assert_eq!(top_modules.len(), 4);

    let EntryData::Owned(first_mod_arc) = top_modules[0].module_json.as_ref().expect("module.json")
    else {
        panic!("deflated module.json must be EntryData::Owned(Arc<[u8]>)");
    };
    let EntryData::Owned(first_patch_arc) = top_modules[0].patch_json.as_ref().expect("patch.json")
    else {
        panic!("deflated patch.json must be EntryData::Owned(Arc<[u8]>)");
    };
    for m in &top_modules[1..] {
        let EntryData::Owned(mod_arc) = m.module_json.as_ref().expect("module.json") else {
            panic!("expected owned Arc");
        };
        let EntryData::Owned(patch_arc) = m.patch_json.as_ref().expect("patch.json") else {
            panic!("expected owned Arc");
        };
        assert!(
            Arc::ptr_eq(first_mod_arc, mod_arc),
            "top-level deflated module.json must share a single Arc<[u8]> allocation"
        );
        assert!(
            Arc::ptr_eq(first_patch_arc, patch_arc),
            "top-level deflated patch.json must share a single Arc<[u8]> allocation"
        );
    }

    // 2. Nested .hap inside an .app with STORED manifests + 4 .abc modules:
    //    `coerce(..., true)` and `into_static()` must coerce once before the
    //    loop and preserve the single `Arc<[u8]>` in O(1) across all 4 modules.
    let nested_hap = build_zip(&[
        ZipEntry::stored("module.json", &big_manifest),
        ZipEntry::stored("patch.json", &big_patch),
        ZipEntry::stored(MODULE_ABC, &abc0),
        ZipEntry::stored("ets/AbilityA.abc", &abc1),
        ZipEntry::stored("ets/AbilityB.abc", &abc2),
        ZipEntry::stored("ets/AbilityC.abc", &abc3),
    ])
    .bytes;
    let app = build_zip(&[
        ZipEntry::stored("pack.info", PACK_INFO),
        ZipEntry::deflated("entry.hap", &nested_hap),
    ])
    .bytes;

    let exact_app_budget = nested_hap.len() as u64 + exact_inner_bytes;
    let app_limits = Limits {
        max_entry_bytes: 128 * 1024,
        max_total_bytes: exact_app_budget,
    };
    let app_modules = abc_modules_with_limits(&app, app_limits)
        .expect("nested multi-abc hap fits exact un-duplicated budget");
    assert_eq!(app_modules.len(), 4);

    let EntryData::Owned(nested_mod_arc) =
        app_modules[0].module_json.as_ref().expect("module.json")
    else {
        panic!("nested module.json must be EntryData::Owned(Arc<[u8]>)");
    };
    let EntryData::Owned(nested_patch_arc) =
        app_modules[0].patch_json.as_ref().expect("patch.json")
    else {
        panic!("nested patch.json must be EntryData::Owned(Arc<[u8]>)");
    };
    for m in &app_modules[1..] {
        let EntryData::Owned(mod_arc) = m.module_json.as_ref().expect("module.json") else {
            panic!("expected owned Arc");
        };
        let EntryData::Owned(patch_arc) = m.patch_json.as_ref().expect("patch.json") else {
            panic!("expected owned Arc");
        };
        assert!(
            Arc::ptr_eq(nested_mod_arc, mod_arc),
            "nested module.json must share a single Arc<[u8]> across into_static()"
        );
        assert!(
            Arc::ptr_eq(nested_patch_arc, patch_arc),
            "nested patch.json must share a single Arc<[u8]> across into_static()"
        );
    }

    // Consuming one clone via into_owned() leaves sibling Arcs intact.
    let owned_vec = app_modules[0]
        .module_json
        .clone()
        .expect("module.json")
        .into_owned();
    assert_eq!(owned_vec, big_manifest);
    assert_eq!(
        app_modules[3].manifest_summary(),
        Some(ManifestSummary {
            module_name: Some("shared_entry".to_string()),
            module_type: Some("entry".to_string()),
            is_stage_model: true,
        })
    );
}

#[test]
fn app_with_duplicate_named_hap_entries_extracts_both_payloads() {
    let hap_first = build_zip(&[
        ZipEntry::stored(
            "module.json",
            br#"{"module":{"name":"first_mod","type":"entry"}}"#,
        ),
        ZipEntry::stored(MODULE_ABC, &abc_bytes(0x71)),
    ])
    .bytes;
    let hap_second = build_zip(&[
        ZipEntry::stored(
            "module.json",
            br#"{"module":{"name":"second_mod","type":"feature"}}"#,
        ),
        ZipEntry::stored(MODULE_ABC, &abc_bytes(0x72)),
    ])
    .bytes;

    let app = build_zip(&[
        ZipEntry::stored("pack.info", PACK_INFO),
        ZipEntry::deflated("dup.hap", &hap_first),
        ZipEntry::deflated("dup.hap", &hap_second),
    ])
    .bytes;

    match Container::sniff(&app).expect("sniff") {
        Container::App { outer, modules } => {
            assert_eq!(outer.len(), 3);
            assert_eq!(modules, ["dup.hap", "dup.hap"]);
        }
        Container::Module(_) => panic!("expected Container::App"),
    }

    let extracted = abc_modules(&app).expect("extract both dup.hap CD entries");
    assert_eq!(extracted.len(), 2);
    assert_eq!(extracted[0].container_path, ["dup.hap".to_string()]);
    assert_eq!(extracted[1].container_path, ["dup.hap".to_string()]);
    assert_eq!(extracted[0].data.as_slice(), abc_bytes(0x71).as_slice());
    assert_eq!(extracted[1].data.as_slice(), abc_bytes(0x72).as_slice());
    assert_eq!(
        extracted[0].manifest_summary(),
        Some(ManifestSummary {
            module_name: Some("first_mod".to_string()),
            module_type: Some("entry".to_string()),
            is_stage_model: true,
        })
    );
    assert_eq!(
        extracted[1].manifest_summary(),
        Some(ManifestSummary {
            module_name: Some("second_mod".to_string()),
            module_type: Some("feature".to_string()),
            is_stage_model: true,
        })
    );
}
