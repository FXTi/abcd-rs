//! Tests for zero-`serde`, zero-recursion `ManifestSummary` parsing across
//! Stage `module.json` and FA `config.json` manifests.

use crate::common::*;
use abcd_hap::{MODULE_ABC, ManifestSummary, abc_modules, parse_manifest_summary};

#[test]
fn stage_manifest_extracts_module_name_and_type_ignoring_nested_abilities() {
    let json = br#"{
        "app": {
            "bundleName": "com.example.demo",
            "versionCode": 1000000,
            "minAPIVersion": 12
        },
        "module": {
            "abilities": [
                {
                    "name": "BeforeAbility",
                    "type": "page",
                    "exported": true
                }
            ],
            "name": "entry_stage",
            "type": "entry",
            "metadata": {
                "distro": {
                    "moduleName": "nested_not_fa",
                    "moduleType": "har"
                }
            },
            "extensionAbilities": [
                {
                    "name": "AfterExtension",
                    "type": "service"
                }
            ]
        }
    }"#;

    assert_eq!(
        parse_manifest_summary(json),
        Some(ManifestSummary {
            module_name: Some("entry_stage".to_string()),
            module_type: Some("entry".to_string()),
            is_stage_model: true,
        })
    );

    // When `module.name` is absent, nested ability `name` fields must never leak up.
    let no_top_name = br#"{
        "module": {
            "abilities": [{"name": "OnlyAbility", "type": "page"}],
            "type": "shared"
        }
    }"#;
    assert_eq!(
        parse_manifest_summary(no_top_name),
        Some(ManifestSummary {
            module_name: None,
            module_type: Some("shared".to_string()),
            is_stage_model: true,
        })
    );
}

#[test]
fn fa_manifest_distro_wins_over_ability_package_module_name_in_any_key_order() {
    // 1. `module.name` (AbilityPackage class) appears BEFORE `module.distro`.
    let fa_name_first = br#"{
        "app": {
            "bundleName": "com.example.fademo",
            "version": {"code": 1000000, "name": "1.0.0"}
        },
        "deviceConfig": {"default": {"debug": true}},
        "module": {
            "package": "com.example.fademo",
            "name": ".MyAbilityPackage",
            "abilities": [
                {"name": ".MainAbility", "type": "page", "visible": true}
            ],
            "distro": {
                "deliveryWithInstall": true,
                "moduleName": "fa_entry",
                "moduleType": "entry",
                "installationFree": false
            },
            "js": [
                {"name": ".MainAbility", "pages": ["pages/index"]}
            ]
        }
    }"#;
    assert_eq!(
        parse_manifest_summary(fa_name_first),
        Some(ManifestSummary {
            module_name: Some("fa_entry".to_string()),
            module_type: Some("entry".to_string()),
            is_stage_model: false,
        })
    );

    // 2. `module.distro` appears BEFORE `module.name`.
    let fa_distro_first = br#"{
        "module": {
            "distro": {
                "moduleType": "feature",
                "moduleName": "fa_feature"
            },
            "name": "com.example.fademo.MyApplication",
            "type": "ignored_stage_field"
        }
    }"#;
    assert_eq!(
        parse_manifest_summary(fa_distro_first),
        Some(ManifestSummary {
            module_name: Some("fa_feature".to_string()),
            module_type: Some("feature".to_string()),
            is_stage_model: false,
        })
    );

    // 3. `module.distro` present without `moduleName` must still report FA
    //    (`is_stage_model: false`) and NOT misreport `AbilityPackage` `module.name`.
    let fa_missing_distro_name = br#"{
        "module": {
            "name": ".MyAbilityPackage",
            "distro": {
                "moduleType": "entry"
            }
        }
    }"#;
    assert_eq!(
        parse_manifest_summary(fa_missing_distro_name),
        Some(ManifestSummary {
            module_name: None,
            module_type: Some("entry".to_string()),
            is_stage_model: false,
        })
    );
}

#[test]
fn utf8_bom_and_all_rfc8259_escapes_and_surrogate_pairs_decode_cleanly() {
    let mut with_bom = vec![0xEF, 0xBB, 0xBF];
    with_bom.extend_from_slice(
        br#"  {
            "extra_numbers": [0, -0, -42, 3.14159, 1.25e-04, 9E+12, true, false, null, {}],
            "\u006d\u006f\u0064\u0075\u006c\u0065": {
                "\u006e\u0061\u006d\u0065": "q\"bs\\sl\/b\bf\fn\nr\rt\t_\u4e2d\u6587_\uD83D\uDE80",
                "type": "entry\u002Drocket"
            }
        } "#,
    );

    let summary = parse_manifest_summary(&with_bom).expect("valid BOM + escaped JSON");
    assert!(summary.is_stage_model);
    assert_eq!(
        summary.module_name.as_deref(),
        Some("q\"bs\\sl/b\u{0008}f\u{000C}n\nr\rt\t_中文_🚀")
    );
    assert_eq!(summary.module_type.as_deref(), Some("entry-rocket"));
}

#[test]
fn malformed_json_and_non_manifest_documents_return_none() {
    let cases: &[&[u8]] = &[
        b"",
        b"   \t\r\n  ",
        b"\xEF\xBB\xBF",
        b"[]",
        b"\"string\"",
        b"123",
        b"true",
        b"null",
        b"{}",
        br#"{"app":{"bundleName":"no_module_section"}}"#,
        br#"{"module":"not_an_object"}"#,
        br#"{"module":[]}"#,
        br#"{"module":null}"#,
        br#"{"module":123}"#,
        br#"{"module":{"name":"ok"}} trailing"#,
        br#"{"module":{"name":"ok",}}"#,
        br#"{"module":{"name":"ok","arr":[1,]}}"#,
        br#"{"module":{"name":"ok","arr":[,1]}}"#,
        br#"{"module":{"name" "missing_colon"}}"#,
        br#"{"module":{"name":"unclosed}"#,
        br#"{"module":{"name":"ok""#,
        b"{\"module\":{\"name\":\"raw\nnewline\"}}",
        b"{\"module\":{\"name\":\"raw\x00nul\"}}",
        b"{\"module\":{\"name\":\"bad_utf8_\xFF\"}}",
        br#"{"module":{"name":"bad_esc_\x41"}}"#,
        br#"{"module":{"name":"short_u_\u12"}}"#,
        br#"{"module":{"name":"non_hex_\u123G"}}"#,
        br#"{"module":{"name":"lone_high_\uD800"}}"#,
        br#"{"module":{"name":"unpaired_high_\uD800\u0041"}}"#,
        br#"{"module":{"name":"lone_low_\uDC00"}}"#,
        br#"{"module":{"name":"ok","bad_num":01}}"#,
        br#"{"module":{"name":"ok","bad_num":-}}"#,
        br#"{"module":{"name":"ok","bad_num":1.}}"#,
        br#"{"module":{"name":"ok","bad_num":1e}}"#,
        br#"{"module":{"name":"ok","bad_num":1e+}}"#,
    ];

    for (idx, &input) in cases.iter().enumerate() {
        assert_eq!(
            parse_manifest_summary(input),
            None,
            "case #{idx} unexpectedly parsed: {:?}",
            String::from_utf8_lossy(input)
        );
    }
}

#[test]
fn abc_module_manifest_summary_handles_stage_fa_hqf_and_corrupt_json() {
    let fake_abc = b"PANDA\x00abc";

    // Stage .hap
    let stage_hap = build_zip(&[
        ZipEntry::stored(
            "module.json",
            br#"{"module":{"name":"stage_mod","type":"entry"}}"#,
        ),
        ZipEntry::stored(MODULE_ABC, fake_abc),
    ])
    .bytes;
    let stage_mods = abc_modules(&stage_hap).expect("stage hap");
    assert_eq!(
        stage_mods[0].manifest_summary(),
        Some(ManifestSummary {
            module_name: Some("stage_mod".to_string()),
            module_type: Some("entry".to_string()),
            is_stage_model: true,
        })
    );

    // FA .hap (`config.json`)
    let fa_hap = build_zip(&[
        ZipEntry::stored(
            "config.json",
            br#"{"module":{"name":".AppPkg","distro":{"moduleName":"fa_mod","moduleType":"feature"}}}"#,
        ),
        ZipEntry::stored("assets/js/default/app.abc", fake_abc),
    ])
    .bytes;
    let fa_mods = abc_modules(&fa_hap).expect("fa hap");
    assert_eq!(
        fa_mods[0].manifest_summary(),
        Some(ManifestSummary {
            module_name: Some("fa_mod".to_string()),
            module_type: Some("feature".to_string()),
            is_stage_model: false,
        })
    );

    // .hqf with `patch.json` only -> `manifest_summary()` is `None`.
    let hqf = build_zip(&[
        ZipEntry::stored("patch.json", br#"{"patch":{"name":"p"}}"#),
        ZipEntry::stored(MODULE_ABC, fake_abc),
    ])
    .bytes;
    let hqf_mods = abc_modules(&hqf).expect("hqf");
    assert_eq!(hqf_mods[0].manifest_summary(), None);

    // .hap with malformed `module.json` -> container still extracts `.abc`,
    // while `manifest_summary()` cleanly returns `None`.
    let bad_json_hap = build_zip(&[
        ZipEntry::stored("module.json", b"{not valid json"),
        ZipEntry::stored(MODULE_ABC, fake_abc),
    ])
    .bytes;
    let bad_mods = abc_modules(&bad_json_hap).expect("container remains valid");
    assert_eq!(bad_mods[0].manifest_summary(), None);
}
