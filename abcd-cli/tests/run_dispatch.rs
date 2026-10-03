//! Dispatch-layer tests: full `argv` → [`Cli::try_parse_from`] →
//! [`abcd_cli::run`], the in-process twin of `main` (cli.rs's documented
//! no-spawn entry point).
//!
//! Every other test file drives leaf functions directly; this file pins
//! the dispatch layer itself (`run` + the per-command `run_*` bodies):
//! module selection, the `--all`-requires-`-o` user errors, and the
//! stdout/file routing of each subcommand. Stdout is captured by the test
//! harness and cannot be asserted; assertions land on the returned
//! `Result` and on file side effects.

mod common;

use std::path::{Path, PathBuf};

use abcd_cli::CliError;
use abcd_cli::cli::Cli;
use clap::Parser;

/// Parse `argv` and dispatch it, exactly as `main` does.
fn run_argv(argv: &[&str]) -> Result<(), CliError> {
    let cli = Cli::try_parse_from(argv).expect("argv must parse");
    abcd_cli::run(cli)
}

/// Write `bytes` to `dir.join(name)` and return the path as a String.
fn write_in(dir: &Path, name: &str, bytes: &[u8]) -> String {
    let path = dir.join(name);
    std::fs::write(&path, bytes).unwrap();
    path.to_str().unwrap().to_string()
}

/// A tempdir carrying one bare `tiny.abc`.
fn tiny_abc_file(tag: &str) -> (PathBuf, String) {
    let dir = common::tempdir(tag);
    let abc = write_in(&dir, "tiny.abc", &common::tiny_abc());
    (dir, abc)
}

/// A tempdir carrying a two-module `bundle.app` (entry + phone).
fn app_file(tag: &str) -> (PathBuf, String) {
    let dir = common::tempdir(tag);
    let app = common::app(&[
        ("entry.hap", common::hap("entry", &common::tiny_abc())),
        ("phone.hap", common::hap("phone", &common::tiny_abc())),
    ]);
    let path = write_in(&dir, "bundle.app", &app);
    (dir, path)
}

/// A tempdir carrying `tiny.pa`, the pandasm text of `tiny.abc` as
/// produced by our own disassembler.
fn pa_file(tag: &str) -> (PathBuf, String) {
    let dir = common::tempdir(tag);
    let abc = common::tiny_abc();
    let file = abcd_file::decode(&abc).expect("decode tiny");
    let pa = abcd_file::pandasm::emit_file(&file, "tiny.abc");
    let path = write_in(&dir, "tiny.pa", &pa);
    (dir, path)
}

/// A tempdir carrying a taint config (TAINT source, print sink).
fn taint_config_file(dir: &Path) -> String {
    write_in(
        dir,
        "taint.toml",
        br#"
[[sources]]
kind = "global_load"
name = "TAINT"

[[sinks]]
kind = "call"
name = "print"
"#,
    )
}

/// Decode the file at `path` (every writer command's output must decode).
fn decode_written(path: &Path) -> abcd_file::File {
    abcd_file::decode(&std::fs::read(path).unwrap()).expect("written file must decode")
}

// ---- extract ----

#[test]
fn extract_writes_module_bytes_to_disk() {
    let dir = common::tempdir("dispatch-extract");
    let hap = write_in(
        &dir,
        "entry.hap",
        &common::hap("entry", &common::tiny_abc()),
    );
    let out_dir = dir.join("out");
    run_argv(&["abcd", "extract", &hap, "-o", out_dir.to_str().unwrap()]).expect("extract");
    assert_eq!(
        std::fs::read(out_dir.join("entry.abc")).unwrap(),
        common::tiny_abc(),
        ".abc bytes round-trip exactly"
    );
    assert_eq!(
        std::fs::read(out_dir.join("entry.module.json")).unwrap(),
        common::module_json("entry"),
        "module.json bytes round-trip exactly"
    );
}

#[test]
fn extract_defaults_out_dir_to_the_cwd() {
    // `extract` without -o writes into the current directory (the
    // documented default). Every path in this test binary is absolute, so
    // the temporary chdir cannot leak into a sibling test.
    let dir = common::tempdir("dispatch-extract-cwd");
    let hap = write_in(
        &dir,
        "entry.hap",
        &common::hap("entry", &common::tiny_abc()),
    );
    let work = dir.join("cwd");
    std::fs::create_dir_all(&work).unwrap();
    std::env::set_current_dir(&work).unwrap();
    run_argv(&["abcd", "extract", &hap]).expect("extract into cwd");
    assert_eq!(
        std::fs::read(work.join("entry.abc")).unwrap(),
        common::tiny_abc()
    );
}

#[test]
fn extract_unreadable_input_is_a_user_error() {
    let dir = common::tempdir("dispatch-extract-err");
    let missing = dir.join("nope.hap");
    let err = run_argv(&["abcd", "extract", missing.to_str().unwrap()]).unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(err.to_string().contains("cannot read"), "{err}");
}

// ---- info ----

#[test]
fn info_prints_a_text_report() {
    // Text is the default output mode; stdout is harness-captured, so the
    // assertion is the successful dispatch itself.
    let (_dir, abc) = tiny_abc_file("dispatch-info");
    run_argv(&["abcd", "info", &abc]).expect("info");
}

#[test]
fn info_json_and_verify_flags() {
    let (_dir, abc) = tiny_abc_file("dispatch-info-json");
    run_argv(&["abcd", "info", "--json", "--verify", &abc]).expect("info --json --verify");
}

#[test]
fn info_unreadable_input_is_a_user_error() {
    let dir = common::tempdir("dispatch-info-missing");
    let missing = dir.join("nope.abc");
    let err = run_argv(&["abcd", "info", missing.to_str().unwrap()]).unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(err.to_string().contains("cannot read"), "{err}");
}

#[test]
fn info_corrupt_abc_is_a_tool_error() {
    let dir = common::tempdir("dispatch-info-corrupt");
    let mut bad = common::tiny_abc();
    bad.truncate(16);
    let bad = write_in(&dir, "bad.abc", &bad);
    let err = run_argv(&["abcd", "info", &bad]).unwrap_err();
    assert_eq!(err.exit_code(), 2, "decode failure is a tool error");
}

#[test]
fn info_container_without_selection_lists_modules() {
    let (_dir, app) = app_file("dispatch-info-sel");
    let err = run_argv(&["abcd", "info", &app]).unwrap_err();
    assert_eq!(err.exit_code(), 1);
    let msg = err.to_string();
    assert!(msg.contains("--module"), "{msg}");
    assert!(msg.contains("entry"), "{msg}");
    assert!(msg.contains("phone"), "{msg}");
}

#[test]
fn info_container_module_selection() {
    let (_dir, app) = app_file("dispatch-info-mod");
    run_argv(&["abcd", "info", &app, "--module", "entry"]).expect("info --module");
}

#[test]
fn info_all_json_multi_module() {
    let (_dir, app) = app_file("dispatch-info-all");
    run_argv(&["abcd", "info", &app, "--all", "--json"]).expect("info --all --json");
}

// ---- dis ----

#[test]
fn dis_writes_a_pa_file() {
    let (dir, abc) = tiny_abc_file("dispatch-dis");
    let out = dir.join("tiny.pa");
    run_argv(&["abcd", "dis", &abc, "-o", out.to_str().unwrap()]).expect("dis");
    let pa = std::fs::read_to_string(&out).unwrap();
    assert!(pa.contains("# source binary: tiny.abc"), "{pa}");
    assert!(pa.contains("func_main_0"), "{pa}");
}

#[test]
fn dis_to_stdout() {
    let (_dir, abc) = tiny_abc_file("dispatch-dis-stdout");
    run_argv(&["abcd", "dis", &abc]).expect("dis to stdout");
}

#[test]
fn dis_all_requires_an_output_dir() {
    let (_dir, app) = app_file("dispatch-dis-allerr");
    let err = run_argv(&["abcd", "dis", &app, "--all"]).unwrap_err();
    assert_eq!(
        err,
        CliError::User("--all requires -o <dir> (one <module>.pa per module)".to_string())
    );
    assert_eq!(err.exit_code(), 1);
}

#[test]
fn dis_all_writes_one_pa_per_module() {
    let (dir, app) = app_file("dispatch-dis-all");
    let out = dir.join("pa");
    run_argv(&["abcd", "dis", &app, "--all", "-o", out.to_str().unwrap()]).expect("dis --all");
    for name in ["entry", "phone"] {
        let pa = std::fs::read_to_string(out.join(format!("{name}.pa"))).unwrap();
        assert!(pa.contains("func_main_0"), "{name}.pa:\n{pa}");
    }
}

#[test]
fn dis_output_path_on_a_directory_is_a_tool_error() {
    // lib.rs's single-module write failure: -o names an existing
    // directory, so the .pa write fails (a tool error, not a panic).
    let (dir, abc) = tiny_abc_file("dispatch-dis-io");
    let occupied = dir.join("occupied");
    std::fs::create_dir_all(&occupied).unwrap();
    let err = run_argv(&["abcd", "dis", &abc, "-o", occupied.to_str().unwrap()]).unwrap_err();
    assert_eq!(err.exit_code(), 2);
    assert!(err.to_string().contains("cannot write"), "{err}");
}

// ---- asm ----

#[test]
fn asm_writes_an_abc_file() {
    let (dir, pa) = pa_file("dispatch-asm");
    let out = dir.join("out.abc");
    run_argv(&["abcd", "asm", &pa, "-o", out.to_str().unwrap()]).expect("asm");
    let file = decode_written(&out);
    assert_eq!(file.all_methods().count(), 1);
}

#[test]
fn asm_check_and_version_flags() {
    let (dir, pa) = pa_file("dispatch-asm-ver");
    let out = dir.join("out.abc");
    run_argv(&[
        "abcd",
        "asm",
        &pa,
        "--check",
        "--version",
        "12.0.6.0",
        "-o",
        out.to_str().unwrap(),
    ])
    .expect("asm --check --version");
    let file = decode_written(&out);
    assert_eq!(file.version, abcd_file::Version::new(12, 0, 6, 0));
}

#[test]
fn asm_to_stdout() {
    let (_dir, pa) = pa_file("dispatch-asm-stdout");
    run_argv(&["abcd", "asm", &pa]).expect("asm to stdout");
}

#[test]
fn asm_unreadable_input_is_a_user_error() {
    let dir = common::tempdir("dispatch-asm-err");
    let missing = dir.join("nope.pa");
    let err = run_argv(&["abcd", "asm", missing.to_str().unwrap()]).unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(err.to_string().contains("cannot read"), "{err}");
}

#[test]
fn asm_unparsable_input_is_a_user_error() {
    let dir = common::tempdir("dispatch-asm-parse");
    let junk = write_in(&dir, "junk.pa", b"this is not pandasm at all");
    let err = run_argv(&["abcd", "asm", &junk]).unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(err.to_string().contains("parse failed"), "{err}");
}

#[test]
fn asm_output_path_on_a_directory_is_a_tool_error() {
    let (dir, pa) = pa_file("dispatch-asm-io");
    let occupied = dir.join("occupied");
    std::fs::create_dir_all(&occupied).unwrap();
    let err = run_argv(&["abcd", "asm", &pa, "-o", occupied.to_str().unwrap()]).unwrap_err();
    assert_eq!(err.exit_code(), 2);
    assert!(err.to_string().contains("cannot write"), "{err}");
}

// ---- rewrite ----

#[test]
fn rewrite_writes_a_rewritten_abc() {
    let (dir, abc) = tiny_abc_file("dispatch-rewrite");
    let out = dir.join("out.abc");
    run_argv(&["abcd", "rewrite", &abc, "-o", out.to_str().unwrap()]).expect("rewrite");
    let file = decode_written(&out);
    assert_eq!(file.all_methods().count(), 1);
}

#[test]
fn rewrite_opt_with_a_real_change_takes_the_optimized_tag_arm() {
    // The foldable fixture gives abcd-opt something to change, so the
    // summary line's `optimized_changed` conditional fires its tag arm
    // (stdout; the side effect is the rewritten file).
    let dir = common::tempdir("dispatch-rewrite-opt");
    let abc = write_in(&dir, "fold.abc", &common::foldable_abc());
    let out = dir.join("out.abc");
    run_argv(&[
        "abcd",
        "rewrite",
        &abc,
        "--opt",
        "--check",
        "-o",
        out.to_str().unwrap(),
    ])
    .expect("rewrite --opt");
    let file = decode_written(&out);
    assert_eq!(file.all_methods().count(), 1);
}

#[test]
fn rewrite_to_stdout() {
    let (_dir, abc) = tiny_abc_file("dispatch-rewrite-stdout");
    run_argv(&["abcd", "rewrite", &abc]).expect("rewrite to stdout");
}

#[test]
fn rewrite_all_requires_an_output_dir() {
    let (_dir, app) = app_file("dispatch-rewrite-allerr");
    let err = run_argv(&["abcd", "rewrite", &app, "--all"]).unwrap_err();
    assert_eq!(
        err,
        CliError::User("--all requires -o <dir> (one <module>.abc per module)".to_string())
    );
    assert_eq!(err.exit_code(), 1);
}

#[test]
fn rewrite_all_writes_one_abc_per_module() {
    let (dir, app) = app_file("dispatch-rewrite-all");
    let out = dir.join("abc");
    run_argv(&[
        "abcd",
        "rewrite",
        &app,
        "--all",
        "--check",
        "-o",
        out.to_str().unwrap(),
    ])
    .expect("rewrite --all");
    for name in ["entry", "phone"] {
        let file = decode_written(&out.join(format!("{name}.abc")));
        assert_eq!(file.all_methods().count(), 1, "{name}.abc");
    }
}

#[test]
fn rewrite_output_path_on_a_directory_is_a_tool_error() {
    let (dir, abc) = tiny_abc_file("dispatch-rewrite-io");
    let occupied = dir.join("occupied");
    std::fs::create_dir_all(&occupied).unwrap();
    let err = run_argv(&["abcd", "rewrite", &abc, "-o", occupied.to_str().unwrap()]).unwrap_err();
    assert_eq!(err.exit_code(), 2);
    assert!(err.to_string().contains("cannot write"), "{err}");
}

// ---- decompile ----

#[test]
fn decompile_writes_a_js_file() {
    let (dir, abc) = tiny_abc_file("dispatch-decompile");
    let out = dir.join("out.js");
    run_argv(&["abcd", "decompile", &abc, "-o", out.to_str().unwrap()]).expect("decompile");
    let js = std::fs::read_to_string(&out).unwrap();
    assert!(js.contains("function func_main_0("), "{js}");
}

#[test]
fn decompile_to_stdout() {
    let (_dir, abc) = tiny_abc_file("dispatch-decompile-stdout");
    run_argv(&["abcd", "decompile", &abc, "--call-entry"]).expect("decompile to stdout");
}

#[test]
fn decompile_all_requires_an_output_dir() {
    let (_dir, app) = app_file("dispatch-decompile-allerr");
    let err = run_argv(&["abcd", "decompile", &app, "--all"]).unwrap_err();
    assert_eq!(
        err,
        CliError::User("--all requires -o <dir> (one <module>.js per module)".to_string())
    );
    assert_eq!(err.exit_code(), 1);
}

#[test]
fn decompile_all_writes_one_js_per_module() {
    let (dir, app) = app_file("dispatch-decompile-all");
    let out = dir.join("js");
    run_argv(&[
        "abcd",
        "decompile",
        &app,
        "--all",
        "-o",
        out.to_str().unwrap(),
    ])
    .expect("decompile --all");
    for name in ["entry", "phone"] {
        let js = std::fs::read_to_string(out.join(format!("{name}.js"))).unwrap();
        assert!(js.contains("function func_main_0("), "{name}.js:\n{js}");
    }
}

#[test]
fn decompile_output_path_on_a_directory_is_a_tool_error() {
    let (dir, abc) = tiny_abc_file("dispatch-decompile-io");
    let occupied = dir.join("occupied");
    std::fs::create_dir_all(&occupied).unwrap();
    let err = run_argv(&["abcd", "decompile", &abc, "-o", occupied.to_str().unwrap()]).unwrap_err();
    assert_eq!(err.exit_code(), 2);
    assert!(err.to_string().contains("cannot write"), "{err}");
}

// ---- analyze ----

#[test]
fn analyze_prints_a_text_report() {
    let (_dir, abc) = tiny_abc_file("dispatch-analyze");
    run_argv(&["abcd", "analyze", &abc]).expect("analyze");
}

#[test]
fn analyze_json_with_all_sections() {
    let (_dir, abc) = tiny_abc_file("dispatch-analyze-json");
    run_argv(&[
        "abcd",
        "analyze",
        &abc,
        "--callgraph",
        "--dominators",
        "--json",
    ])
    .expect("analyze --callgraph --dominators --json");
}

#[test]
fn analyze_all_json_multi_module() {
    let (_dir, app) = app_file("dispatch-analyze-all");
    run_argv(&["abcd", "analyze", &app, "--all", "--json"]).expect("analyze --all --json");
}

// ---- taint ----

#[test]
fn taint_prints_a_text_report() {
    let (dir, abc) = tiny_abc_file("dispatch-taint");
    let config = taint_config_file(&dir);
    run_argv(&["abcd", "taint", &abc, "--config", &config]).expect("taint");
}

#[test]
fn taint_missing_config_is_a_user_error() {
    let (dir, abc) = tiny_abc_file("dispatch-taint-err");
    let missing = dir.join("nope.toml");
    let err =
        run_argv(&["abcd", "taint", &abc, "--config", missing.to_str().unwrap()]).unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(err.to_string().contains("cannot read"), "{err}");
}

#[test]
fn taint_all_json_multi_module() {
    let (dir, app) = app_file("dispatch-taint-all");
    let config = taint_config_file(&dir);
    run_argv(&[
        "abcd", "taint", &app, "--config", &config, "--all", "--json",
    ])
    .expect("taint --all --json");
}
