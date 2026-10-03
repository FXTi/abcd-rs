//! `info` golden-output tests over a synthesized .abc.

mod common;

use abcd_cli::info;
use abcd_cli::input::{self, ModuleSelection};

fn report(verify: bool) -> info::InfoReport {
    let modules =
        input::load_bytes(&common::tiny_abc(), "modules.abc", ModuleSelection::Single).unwrap();
    info::report(&modules[0], verify).unwrap()
}

#[test]
fn text_report_is_the_golden_shape() {
    let text = info::render_text(&report(false));
    // tiny_abc: one class (the global class), one static method `f` with a
    // body, no fields.
    let expected_lines = [
        "module:          modules (modules.abc)",
        "classes:         1 (0 external)",
        "methods:         1 (1 with body)",
        "fields:          0",
        "debug infos:     0",
        "lossy strings:   0",
    ];
    for line in expected_lines {
        assert!(text.contains(line), "missing {line:?} in:\n{text}");
    }
    // Version/type values belong to the fixture; the fields must exist.
    assert!(text.contains("format version:  "), "{text}");
    assert!(text.contains("file type:       "), "{text}");
    assert!(text.contains("checksum:        0x"), "{text}");
    // No verify section without the flag.
    assert!(!text.contains("verify:"), "{text}");
}

#[test]
fn verify_appends_the_verdict() {
    let text = info::render_text(&report(true));
    assert!(
        text.contains("verify:          ok (1 methods, 1 instructions decoded)"),
        "{text}"
    );
}

#[test]
fn json_report_is_machine_readable() {
    let out = info::render(&[report(true)], true).unwrap();
    let value: serde_json::Value = serde_json::from_str(&out).unwrap();
    assert_eq!(value["module"], "modules");
    assert_eq!(value["counts"]["methods"], 1);
    assert_eq!(value["counts"]["methods_with_body"], 1);
    assert_eq!(value["counts"]["fields"], 0);
    assert_eq!(value["verify"]["verdict"], "ok");
    assert_eq!(value["verify"]["methods_checked"], 1);
    assert!(value["format_version"].as_str().unwrap().contains('.'));
}

#[test]
fn json_multi_module_renders_an_array() {
    let reports = [report(false), report(false)];
    let out = info::render(&reports, true).unwrap();
    let value: serde_json::Value = serde_json::from_str(&out).unwrap();
    assert_eq!(value.as_array().unwrap().len(), 2);
}

#[test]
fn info_works_through_a_hap_container() {
    let hap = common::hap("entry", &common::tiny_abc());
    let modules = input::load_bytes(&hap, "entry.hap", ModuleSelection::Single).unwrap();
    let report = info::report(&modules[0], false).unwrap();
    assert_eq!(report.module, "entry");
    assert!(report.provenance.contains("entry.hap::ets/modules.abc"));
    assert_eq!(report.counts.methods, 1);
}

#[test]
fn corrupt_abc_is_a_tool_error() {
    let mut bad = common::tiny_abc();
    bad.truncate(16); // header prefix only: structurally undecodable
    let modules = input::load_bytes(&bad, "bad.abc", ModuleSelection::Single).unwrap();
    let err = info::report(&modules[0], false).unwrap_err();
    assert_eq!(err.exit_code(), 2, "decode failure is a tool error");
}

#[test]
fn static_version_header_reports_static_type() {
    // The vendored GetFileType keys `static` off the header version field
    // (bytes 12..16) equal to 0.1.0.7; decode does not reject the type.
    let mut abc = common::tiny_abc();
    abc[12..16].copy_from_slice(&[0, 1, 0, 7]);
    let modules = input::load_bytes(&abc, "static.abc", ModuleSelection::Single).unwrap();
    let report = info::report(&modules[0], false).unwrap();
    assert_eq!(report.file_type, "static");
    let text = info::render_text(&report);
    assert!(text.contains("file type:       static"), "{text}");
}

#[test]
fn trailing_bytes_past_the_declared_size_report_invalid_type() {
    // GetFileType requires buffer size == header-declared file_size; the
    // decoder itself accepts a larger buffer, so one trailing byte keeps
    // the file decodable while the type reads `invalid`.
    let mut abc = common::tiny_abc();
    abc.push(0);
    let modules = input::load_bytes(&abc, "invalid.abc", ModuleSelection::Single).unwrap();
    let report = info::report(&modules[0], false).unwrap();
    assert_eq!(report.file_type, "invalid");
}

#[test]
fn render_in_text_mode_produces_the_text_report() {
    let out = info::render(&[report(false)], false).unwrap();
    assert!(
        out.contains("module:          modules (modules.abc)"),
        "{out}"
    );
    assert!(out.contains("file type:       dynamic"), "{out}");
}
