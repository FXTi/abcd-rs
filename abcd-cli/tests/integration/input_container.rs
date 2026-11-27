//! Input-layer tests over synthesized containers (magic sniffing, module
//! selection, name resolution, hard-error listing).

use crate::common;
use abcd_cli::input::{self, ModuleSelection};

#[test]
fn hap_single_module_resolves_without_flags() {
    let hap = common::hap("entry", &common::tiny_abc());
    let modules = input::load_bytes(&hap, "entry.hap", ModuleSelection::Single).unwrap();
    assert_eq!(modules.len(), 1);
    assert_eq!(modules[0].name, "entry"); // from module.json
    assert_eq!(modules[0].abc.as_ref(), common::tiny_abc().as_slice());
    assert!(modules[0].provenance.contains("entry.hap"));
    assert!(modules[0].provenance.contains("ets/modules.abc"));
}

#[test]
fn hap_without_manifest_falls_back_to_file_stem() {
    let hap = common::hap_no_manifest(&common::tiny_abc());
    let modules = input::load_bytes(&hap, "feature.hap", ModuleSelection::Single).unwrap();
    assert_eq!(modules[0].name, "feature");
}

#[test]
fn app_single_selection_is_a_hard_error_listing_modules() {
    let app = common::app(&[
        ("entry.hap", common::hap("entry", &common::tiny_abc())),
        ("phone.hap", common::hap("phone", &common::tiny_abc())),
    ]);
    let err = input::load_bytes(&app, "bundle.app", ModuleSelection::Single).unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("2 modules"), "message: {msg}");
    assert!(msg.contains("entry"), "message: {msg}");
    assert!(msg.contains("phone"), "message: {msg}");
    assert!(msg.contains("--module"), "message: {msg}");
    assert_eq!(err.exit_code(), 1, "selection errors are user errors");
}

#[test]
fn app_module_flag_selects_by_name() {
    let app = common::app(&[
        ("entry.hap", common::hap("entry", &common::tiny_abc())),
        ("phone.hap", common::hap("phone", &common::tiny_abc())),
    ]);
    let modules = input::load_bytes(&app, "bundle.app", ModuleSelection::Named("phone")).unwrap();
    assert_eq!(modules.len(), 1);
    assert_eq!(modules[0].name, "phone");
    assert!(modules[0].provenance.contains("phone.hap"));
}

#[test]
fn app_module_flag_unknown_name_lists_available() {
    let app = common::app(&[
        ("entry.hap", common::hap("entry", &common::tiny_abc())),
        ("phone.hap", common::hap("phone", &common::tiny_abc())),
    ]);
    let err = input::load_bytes(&app, "bundle.app", ModuleSelection::Named("watch")).unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("watch"), "message: {msg}");
    assert!(msg.contains("entry"), "message: {msg}");
    assert!(msg.contains("phone"), "message: {msg}");
}

#[test]
fn app_all_returns_every_module() {
    let app = common::app(&[
        ("entry.hap", common::hap("entry", &common::tiny_abc())),
        ("phone.hap", common::hap("phone", &common::tiny_abc())),
    ]);
    let modules = input::load_bytes(&app, "bundle.app", ModuleSelection::All).unwrap();
    let names: Vec<&str> = modules.iter().map(|m| m.name.as_str()).collect();
    assert_eq!(names, ["entry", "phone"]);
}

#[test]
fn malformed_container_is_a_tool_error() {
    let bytes = b"PK\x03\x04garbage garbage garbage";
    let err = input::load_bytes(bytes, "broken.hap", ModuleSelection::Single).unwrap_err();
    assert_eq!(
        err.exit_code(),
        2,
        "container decode failures are tool errors"
    );
}

#[test]
fn bare_abc_never_touches_the_container_path() {
    // An .abc whose first bytes are not PK must be treated as raw bytecode
    // even when the name claims otherwise.
    let modules =
        input::load_bytes(&common::tiny_abc(), "weird.hap", ModuleSelection::Single).unwrap();
    assert_eq!(modules.len(), 1);
    assert_eq!(modules[0].name, "weird");
}

#[test]
fn hostile_module_json_name_is_deterministically_sanitized() {
    // Container-provided module names may come from quirky or hostile manifests;
    // read-only subcommands (`info`, `analyze`, `taint`) must still load them,
    // while writer commands receive a strictly safe single path segment.
    let hap = common::hap("../evil", &common::tiny_abc());
    let modules = input::load_bytes(&hap, "evil.hap", ModuleSelection::Single).unwrap();
    assert_eq!(modules.len(), 1);
    assert!(input::is_safe_path_segment(&modules[0].name));
    assert_eq!(modules[0].name, ".._evil");
}

#[test]
fn per_ability_hap_disambiguates_module_names() {
    // A per-ability hap (no ets/modules.abc; one abc per ability) yields
    // several modules that all share the module.json name — the input layer
    // must hand out unique, deterministic names.
    let hap = common::zip(&[
        ("module.json", &common::module_json("systemui")),
        ("ets/Application/AbilityStage.abc", &common::tiny_abc()),
        (
            "ets/ServiceExtension/ServiceExtension.abc",
            &common::tiny_abc(),
        ),
    ]);
    let modules = input::load_bytes(&hap, "SystemUI.hap", ModuleSelection::All).unwrap();
    let names: Vec<&str> = modules.iter().map(|m| m.name.as_str()).collect();
    assert_eq!(names, ["systemui", "systemui__ServiceExtension"]);
}

#[test]
fn triple_collision_walks_the_numeric_suffix_loop() {
    // Three abilities sharing the module.json name AND the entry stem:
    // the first keeps the base, the second gets `__<stem>`, and the third
    // walks the `__N` loop (N starts at 2).
    let hap = common::zip(&[
        ("module.json", &common::module_json("systemui")),
        ("ets/A/AbilityStage.abc", &common::tiny_abc()),
        ("ets/B/AbilityStage.abc", &common::tiny_abc()),
        ("ets/C/AbilityStage.abc", &common::tiny_abc()),
    ]);
    let modules = input::load_bytes(&hap, "SystemUI.hap", ModuleSelection::All).unwrap();
    let names: Vec<&str> = modules.iter().map(|m| m.name.as_str()).collect();
    assert_eq!(
        names,
        [
            "systemui",
            "systemui__AbilityStage",
            "systemui__AbilityStage2"
        ]
    );
}

#[test]
fn nested_module_without_manifest_uses_the_container_entry_stem() {
    // A nested hap with no module.json: the name falls back to the
    // innermost container entry stem (`nested.hap` → `nested`), not the
    // outer file's stem.
    let app = common::app(&[("nested.hap", common::hap_no_manifest(&common::tiny_abc()))]);
    let modules = input::load_bytes(&app, "bundle.app", ModuleSelection::Single).unwrap();
    assert_eq!(modules[0].name, "nested");
    assert!(
        modules[0].provenance.contains("bundle.app::nested.hap"),
        "provenance: {}",
        modules[0].provenance
    );
}

#[test]
fn load_from_disk_moves_bare_abc_and_enforces_selection() {
    let dir = common::tempdir("input-load-bare");
    let path = dir.join("modules.abc");
    let abc = common::tiny_abc();
    std::fs::write(&path, &abc).unwrap();

    let single = input::load(&path, ModuleSelection::Single).expect("load single");
    assert_eq!(single.len(), 1);
    assert_eq!(single[0].name, "modules");
    assert_eq!(single[0].abc.as_ref(), abc.as_slice());
    assert_eq!(single[0].provenance, path.display().to_string());

    let err = input::load(&path, ModuleSelection::Named("other")).unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(err.to_string().contains("has no module named"), "{err}");
}

#[test]
fn windows_reserved_device_names_and_trailing_dot_or_space_are_sanitized() {
    for bad_name in [
        "CON",
        "con.txt",
        "aux.config",
        "COM1",
        "lpt9.json",
        "CONIN$",
        "CONOUT$",
        "entry.",
        "entry ",
        "bad:name",
        "bad*name",
        ".",
        "..",
    ] {
        let hap = common::hap(bad_name, &common::tiny_abc());
        let modules = input::load_bytes(&hap, "evil.hap", ModuleSelection::Single)
            .unwrap_or_else(|e| panic!("bad_name={bad_name:?} blocked load: {e}"));
        assert_eq!(modules.len(), 1);
        assert!(
            input::is_safe_path_segment(&modules[0].name),
            "bad_name={bad_name:?} -> unsafe {:?}",
            modules[0].name
        );
    }
}

#[test]
fn fa_model_config_json_distro_module_name_resolves() {
    let config_json = br#"{"app":{"bundleName":"com.demo"},"module":{"distro":{"moduleName":"fa_entry","moduleType":"entry"}}}"#;
    let hap = common::zip(&[
        ("config.json", config_json),
        ("assets/js/default/pages/index.abc", &common::tiny_abc()),
    ]);
    let modules = input::load_bytes(&hap, "legacy_fa.hap", ModuleSelection::Single).unwrap();
    assert_eq!(modules.len(), 1);
    assert_eq!(modules[0].name, "fa_entry");
}

#[test]
fn case_insensitive_module_collisions_disambiguate_while_preserving_case() {
    let app = common::app(&[
        ("Entry.hap", common::hap("Entry", &common::tiny_abc())),
        ("entry.hap", common::hap("entry", &common::tiny_abc())),
        ("ENTRY.hap", common::hap("ENTRY", &common::tiny_abc())),
    ]);
    let modules = input::load_bytes(&app, "bundle.app", ModuleSelection::All).unwrap();
    let names: Vec<&str> = modules.iter().map(|m| m.name.as_str()).collect();
    assert_eq!(names, ["Entry", "entry__modules", "ENTRY__modules2"]);
}

/// Build a valid single-entry ZIP archive using `METHOD_DEFLATE` (`8`) over an
/// RFC 1951 final uncompressed block (`\x01 <len:u16> <~len:u16> <payload>`),
/// exercising `abcd_hap::EntryData::Owned(Arc<[u8]>)` -> `into_arc()` zero-copy
/// handoff across `extract`, `info`, `decompile`, `rewrite`, and `taint`.
fn deflated_hap(module_name: &str, abc: &[u8]) -> Vec<u8> {
    assert!(abc.len() <= u16::MAX as usize);
    let crc32 = |data: &[u8]| -> u32 {
        let mut crc = 0xFFFF_FFFFu32;
        for &b in data {
            crc ^= u32::from(b);
            for _ in 0..8 {
                crc = (crc >> 1) ^ (0xEDB8_8320 & (crc & 1).wrapping_neg());
            }
        }
        !crc
    };
    let deflate_type0 = |raw: &[u8]| -> Vec<u8> {
        let len = raw.len() as u16;
        let nlen = !len;
        let mut out = Vec::with_capacity(5 + raw.len());
        out.push(0x01); // BFINAL = 1, BTYPE = 00 (no compression)
        out.extend_from_slice(&len.to_le_bytes());
        out.extend_from_slice(&nlen.to_le_bytes());
        out.extend_from_slice(raw);
        out
    };

    let manifest = common::module_json(module_name);
    let raw_entries: [(&str, &[u8]); 2] = [("module.json", &manifest), ("ets/modules.abc", abc)];
    let compressed: Vec<Vec<u8>> = raw_entries
        .iter()
        .map(|(_, data)| deflate_type0(data))
        .collect();

    let mut zip = Vec::new();
    let mut local_offsets = Vec::new();
    for ((name, raw), comp) in raw_entries.iter().zip(&compressed) {
        local_offsets.push(zip.len() as u32);
        zip.extend_from_slice(&0x0403_4b50u32.to_le_bytes());
        zip.extend_from_slice(&20u16.to_le_bytes());
        zip.extend_from_slice(&0u16.to_le_bytes());
        zip.extend_from_slice(&8u16.to_le_bytes()); // METHOD_DEFLATE
        zip.extend_from_slice(&0u16.to_le_bytes());
        zip.extend_from_slice(&0u16.to_le_bytes());
        zip.extend_from_slice(&crc32(raw).to_le_bytes());
        zip.extend_from_slice(&(comp.len() as u32).to_le_bytes());
        zip.extend_from_slice(&(raw.len() as u32).to_le_bytes());
        zip.extend_from_slice(&(name.len() as u16).to_le_bytes());
        zip.extend_from_slice(&0u16.to_le_bytes());
        zip.extend_from_slice(name.as_bytes());
        zip.extend_from_slice(comp);
    }
    let cd_offset = zip.len() as u32;
    for (((name, raw), comp), &local) in raw_entries.iter().zip(&compressed).zip(&local_offsets) {
        zip.extend_from_slice(&0x0201_4b50u32.to_le_bytes());
        zip.extend_from_slice(&20u16.to_le_bytes());
        zip.extend_from_slice(&20u16.to_le_bytes());
        zip.extend_from_slice(&0u16.to_le_bytes());
        zip.extend_from_slice(&8u16.to_le_bytes()); // METHOD_DEFLATE
        zip.extend_from_slice(&0u16.to_le_bytes());
        zip.extend_from_slice(&0u16.to_le_bytes());
        zip.extend_from_slice(&crc32(raw).to_le_bytes());
        zip.extend_from_slice(&(comp.len() as u32).to_le_bytes());
        zip.extend_from_slice(&(raw.len() as u32).to_le_bytes());
        zip.extend_from_slice(&(name.len() as u16).to_le_bytes());
        zip.extend_from_slice(&0u16.to_le_bytes());
        zip.extend_from_slice(&0u16.to_le_bytes());
        zip.extend_from_slice(&0u16.to_le_bytes());
        zip.extend_from_slice(&0u16.to_le_bytes());
        zip.extend_from_slice(&0u32.to_le_bytes());
        zip.extend_from_slice(&local.to_le_bytes());
        zip.extend_from_slice(name.as_bytes());
    }
    let cd_size = zip.len() as u32 - cd_offset;
    zip.extend_from_slice(&0x0605_4b50u32.to_le_bytes());
    zip.extend_from_slice(&0u16.to_le_bytes());
    zip.extend_from_slice(&0u16.to_le_bytes());
    zip.extend_from_slice(&(raw_entries.len() as u16).to_le_bytes());
    zip.extend_from_slice(&(raw_entries.len() as u16).to_le_bytes());
    zip.extend_from_slice(&cd_size.to_le_bytes());
    zip.extend_from_slice(&cd_offset.to_le_bytes());
    zip.extend_from_slice(&0u16.to_le_bytes());
    zip
}

#[test]
fn deflated_and_nested_container_arc_input_runs_across_all_subcommands() {
    use std::sync::Arc;

    let abc = common::foldable_abc();
    let hap = deflated_hap("deflated_entry", &abc);
    let app = common::app(&[("deflated_entry.hap", hap.clone())]);

    for container_bytes in [&hap, &app] {
        let mods = input::load_bytes(container_bytes, "pkg.hap", ModuleSelection::Single)
            .expect("load deflated container");
        assert_eq!(mods.len(), 1);
        assert_eq!(mods[0].name, "deflated_entry");
        assert_eq!(mods[0].abc.as_ref(), abc.as_slice());
        assert_eq!(
            Arc::strong_count(&mods[0].abc),
            1,
            "inflated container entry must be held by a single Arc<[u8]> without extra copies"
        );

        let info_rep = abcd_cli::info::report(&mods[0], true).expect("info --verify");
        assert_eq!(info_rep.counts.methods, 1);

        let dec = abcd_cli::decompile::decompile(
            &mods[0],
            abcd_cli::decompile::DecompileOptions::default(),
        )
        .expect("decompile");
        assert!(dec.text.contains("function func_main_0("), "{}", dec.text);

        let rw = abcd_cli::rewrite::rewrite(
            &mods[0],
            abcd_cli::rewrite::RewriteOptions {
                optimize: true,
                check: true,
            },
        )
        .expect("rewrite --opt --check");
        assert!(rw.stats.optimized_changed);

        let cfg = abcd_cli::taint::resolve_config(None, Some("ohos")).expect("ohos preset");
        let taint_rep = abcd_cli::taint::report(&mods[0], &cfg).expect("taint");
        assert_eq!(taint_rep.module, "deflated_entry");
    }

    let out_dir = common::tempdir("extract-deflated-arc");
    let extracted =
        abcd_cli::extract::extract_bytes(&hap, "deflated.hap", &out_dir, false).expect("extract");
    assert_eq!(extracted.len(), 1);
    assert_eq!(
        std::fs::read(out_dir.join("deflated_entry.abc")).unwrap(),
        abc
    );
}
