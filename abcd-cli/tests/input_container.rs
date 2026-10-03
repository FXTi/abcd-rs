//! Input-layer tests over synthesized containers (magic sniffing, module
//! selection, name resolution, hard-error listing).

mod common;

use abcd_cli::input::{self, ModuleSelection};

#[test]
fn hap_single_module_resolves_without_flags() {
    let hap = common::hap("entry", &common::tiny_abc());
    let modules = input::load_bytes(&hap, "entry.hap", ModuleSelection::Single).unwrap();
    assert_eq!(modules.len(), 1);
    assert_eq!(modules[0].name, "entry"); // from module.json
    assert_eq!(modules[0].abc, common::tiny_abc());
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
fn hostile_module_json_name_is_a_hard_error() {
    // A container-provided module name lands in OUTPUT PATHS downstream
    // (`extract`, `decompile --all`); "../evil" must be rejected, never
    // sanitized into silent use.
    let hap = common::hap("../evil", &common::tiny_abc());
    let err = input::load_bytes(&hap, "evil.hap", ModuleSelection::Single).unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("../evil"), "message: {msg}");
    assert!(msg.contains("safe"), "message: {msg}");
    assert_eq!(err.exit_code(), 2, "hostile content is a tool error");
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
