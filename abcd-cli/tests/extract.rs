//! `extract` tests, including the end-to-end pin: synthesized .hap →
//! extract → exact bytes on disk.

mod common;

use abcd_cli::extract;

#[test]
fn end_to_end_hap_extracts_exact_bytes() {
    let abc = common::tiny_abc();
    let hap = common::hap("entry", &abc);
    let dir = common::tempdir("extract-e2e");

    let written = extract::extract_bytes(&hap, "entry.hap", &dir, false).unwrap();
    assert_eq!(written.len(), 1);
    assert_eq!(written[0].name, "entry");
    assert_eq!(written[0].abc_size, abc.len());

    let abc_path = dir.join("entry.abc");
    let json_path = dir.join("entry.module.json");
    assert_eq!(written[0].abc_path, abc_path);
    assert_eq!(written[0].json_path.as_deref(), Some(json_path.as_path()));
    assert_eq!(
        std::fs::read(&abc_path).unwrap(),
        abc,
        ".abc bytes round-trip exactly"
    );
    assert_eq!(
        std::fs::read(&json_path).unwrap(),
        common::module_json("entry"),
        "module.json bytes round-trip exactly"
    );
}

#[test]
fn app_extracts_every_module() {
    let app = common::app(&[
        ("entry.hap", common::hap("entry", &common::tiny_abc())),
        ("phone.hap", common::hap("phone", &common::tiny_abc())),
    ]);
    let dir = common::tempdir("extract-app");
    let written = extract::extract_bytes(&app, "bundle.app", &dir, false).unwrap();
    let names: Vec<&str> = written.iter().map(|m| m.name.as_str()).collect();
    assert_eq!(names, ["entry", "phone"]);
    for name in names {
        assert_eq!(
            std::fs::read(dir.join(format!("{name}.abc"))).unwrap(),
            common::tiny_abc()
        );
        assert!(dir.join(format!("{name}.module.json")).exists());
    }
}

#[test]
fn existing_output_is_a_user_error_without_force() {
    let hap = common::hap("entry", &common::tiny_abc());
    let dir = common::tempdir("extract-collision");
    std::fs::write(dir.join("entry.abc"), b"sentinel").unwrap();

    let err = extract::extract_bytes(&hap, "entry.hap", &dir, false).unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(err.to_string().contains("--force"), "message: {err}");
    // Preflight: nothing was written over the sentinel.
    assert_eq!(std::fs::read(dir.join("entry.abc")).unwrap(), b"sentinel");

    // With --force the same call succeeds.
    extract::extract_bytes(&hap, "entry.hap", &dir, true).unwrap();
    assert_eq!(
        std::fs::read(dir.join("entry.abc")).unwrap(),
        common::tiny_abc()
    );
}

#[test]
fn bare_abc_is_rejected_with_a_user_error() {
    let dir = common::tempdir("extract-bare");
    let err = extract::extract_bytes(&common::tiny_abc(), "modules.abc", &dir, false).unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(
        err.to_string().contains("not a container"),
        "message: {err}"
    );
}

#[test]
fn no_manifest_still_extracts_abc_only() {
    let hap = common::hap_no_manifest(&common::tiny_abc());
    let dir = common::tempdir("extract-nomanifest");
    let written = extract::extract_bytes(&hap, "feature.hap", &dir, false).unwrap();
    assert_eq!(written.len(), 1);
    assert_eq!(written[0].name, "feature"); // falls back to file stem
    assert!(written[0].json_path.is_none());
    assert!(dir.join("feature.abc").exists());
    assert!(!dir.join("feature.module.json").exists());
}

#[test]
fn summary_mentions_counts_sizes_and_paths() {
    let abc = common::tiny_abc();
    let hap = common::hap("entry", &abc);
    let dir = common::tempdir("extract-summary");
    let written = extract::extract_bytes(&hap, "entry.hap", &dir, false).unwrap();
    let text = extract::render_summary("entry.hap", &dir, &written);
    assert!(
        text.contains("extracted 1 module(s) from entry.hap"),
        "summary: {text}"
    );
    assert!(
        text.contains(&format!("entry: {} bytes", abc.len())),
        "summary: {text}"
    );
    assert!(text.contains("entry.abc"), "summary: {text}");
    assert!(text.contains("entry.module.json"), "summary: {text}");
}

#[test]
fn out_dir_occupied_by_a_file_is_a_tool_error() {
    // create_dir_all on a path that exists as a regular file fails.
    let hap = common::hap("entry", &common::tiny_abc());
    let dir = common::tempdir("extract-io-err");
    let occupied = dir.join("occupied");
    std::fs::write(&occupied, b"x").unwrap();
    let err = extract::extract_bytes(&hap, "entry.hap", &occupied, false).unwrap_err();
    assert_eq!(err.exit_code(), 2);
    assert!(
        err.to_string().contains("cannot create output directory"),
        "{err}"
    );
}

#[test]
fn module_json_write_failure_is_a_tool_error() {
    // --force skips the collision preflight; a DIRECTORY squatting the
    // <name>.module.json path then fails the actual write (the .abc
    // payload write comes first and succeeds).
    let hap = common::hap("entry", &common::tiny_abc());
    let dir = common::tempdir("extract-json-err");
    std::fs::create_dir_all(dir.join("entry.module.json")).unwrap();
    let err = extract::extract_bytes(&hap, "entry.hap", &dir, true).unwrap_err();
    assert_eq!(err.exit_code(), 2);
    assert!(err.to_string().contains("cannot write"), "{err}");
    assert!(dir.join("entry.abc").exists(), "the .abc write came first");
}

#[test]
fn abc_write_failure_is_a_tool_error() {
    // Same shape, with the directory squatting the <name>.abc path: the
    // FIRST write fails and no module.json is produced.
    let hap = common::hap("entry", &common::tiny_abc());
    let dir = common::tempdir("extract-abc-err");
    std::fs::create_dir_all(dir.join("entry.abc")).unwrap();
    let err = extract::extract_bytes(&hap, "entry.hap", &dir, true).unwrap_err();
    assert_eq!(err.exit_code(), 2);
    assert!(err.to_string().contains("cannot write"), "{err}");
    assert!(
        !dir.join("entry.module.json").exists(),
        "nothing beyond the failed .abc write"
    );
}
