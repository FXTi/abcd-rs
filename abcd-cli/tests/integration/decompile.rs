//! `decompile` tests over a synthesized .abc (through the full
//! decode → lift → emit pipeline).

use crate::common;
use abcd_cli::decompile::{self, DecompileOptions};
use abcd_cli::input::{self, ModuleSelection};

fn module(bytes: &[u8], name: &str) -> abcd_cli::input::InputModule {
    input::load_bytes(bytes, name, ModuleSelection::Single)
        .unwrap()
        .into_iter()
        .next()
        .unwrap()
}

#[test]
fn decompiles_a_bare_abc() {
    let m = module(&common::tiny_abc(), "modules.abc");
    let out = decompile::decompile(&m, DecompileOptions::default()).unwrap();
    assert!(
        out.text.contains("function func_main_0("),
        "expected the synthesized entry function in:\n{}",
        out.text
    );
    assert!(out.stats.functions >= 1);
}

#[test]
fn call_entry_flag_appends_the_entry_call() {
    let m = module(&common::tiny_abc(), "modules.abc");
    let plain = decompile::decompile(&m, DecompileOptions::default()).unwrap();
    let with_entry = decompile::decompile(
        &m,
        DecompileOptions {
            call_entry: true,
            ..Default::default()
        },
    )
    .unwrap();
    assert!(!plain.text.contains(".call(this)"));
    assert!(
        with_entry.text.contains(".call(this)"),
        "expected entry call in:\n{}",
        with_entry.text
    );
}

#[test]
fn decompiles_through_a_hap_container() {
    let hap = common::hap("entry", &common::tiny_abc());
    let m = module(&hap, "entry.hap");
    let out = decompile::decompile(&m, DecompileOptions::default()).unwrap();
    assert!(out.text.contains("function func_main_0("), "{}", out.text);
}

#[test]
fn write_all_lays_down_one_js_per_module() {
    let app = common::app(&[
        ("entry.hap", common::hap("entry", &common::tiny_abc())),
        ("phone.hap", common::hap("phone", &common::tiny_abc())),
    ]);
    let modules = input::load_bytes(&app, "bundle.app", ModuleSelection::All).unwrap();
    let dir = common::tempdir("decompile-all");
    let written = decompile::write_all(&modules, &dir, DecompileOptions::default()).unwrap();
    let names: Vec<&str> = written.iter().map(|(n, _, _)| n.as_str()).collect();
    assert_eq!(names, ["entry", "phone"]);
    for name in names {
        let path = dir.join(format!("{name}.js"));
        let text = std::fs::read_to_string(&path).unwrap();
        assert!(text.contains("function func_main_0("), "{name}.js:\n{text}");
    }
}

#[test]
fn corrupt_abc_is_a_tool_error() {
    let bad = vec![0u8; 32];
    let m = module(&bad, "bad.abc");
    let err = decompile::decompile(&m, DecompileOptions::default()).unwrap_err();
    assert_eq!(err.exit_code(), 2);
}

#[test]
fn lift_failure_is_a_tool_error() {
    let m = module(&common::lift_fail_abc(), "liftfail.abc");
    let err = decompile::decompile(&m, DecompileOptions::default()).unwrap_err();
    assert_eq!(err.exit_code(), 2, "lift failure is a tool error");
    let msg = err.to_string();
    assert!(msg.contains("failed to lift"), "{msg}");
    assert!(msg.contains("ldthisbyname"), "{msg}");
}

#[test]
fn write_all_out_dir_occupied_by_a_file_is_a_tool_error() {
    let dir = common::tempdir("decompile-io-err");
    let occupied = dir.join("occupied");
    std::fs::write(&occupied, b"x").unwrap();
    let m = module(&common::tiny_abc(), "modules.abc");
    let err = decompile::write_all(&[m], &occupied, DecompileOptions::default()).unwrap_err();
    assert_eq!(err.exit_code(), 2);
    assert!(
        err.to_string().contains("cannot create output directory"),
        "{err}"
    );
}

#[test]
fn write_all_write_failure_is_a_tool_error() {
    // A directory squatting the <name>.js output path fails the write.
    let dir = common::tempdir("decompile-write-err");
    std::fs::create_dir_all(dir.join("modules.js")).unwrap();
    let m = module(&common::tiny_abc(), "modules.abc");
    let err = decompile::write_all(&[m], &dir, DecompileOptions::default()).unwrap_err();
    assert_eq!(err.exit_code(), 2);
    assert!(err.to_string().contains("cannot write"), "{err}");
}

#[test]
fn write_all_aborts_the_batch_on_an_unliftable_module() {
    // [good, decode-ok/lift-fail]: the first module lands, the second
    // fails the decompile and the error aborts the batch.
    let good = module(&common::tiny_abc(), "good.abc");
    let bad = module(&common::lift_fail_abc(), "bad.abc");
    let dir = common::tempdir("decompile-batch-err");
    let err = decompile::write_all(&[good, bad], &dir, DecompileOptions::default()).unwrap_err();
    assert_eq!(err.exit_code(), 2);
    assert!(err.to_string().contains("failed to lift"), "{err}");
    assert!(dir.join("good.js").exists(), "the good module was written");
    assert!(!dir.join("bad.js").exists(), "the bad module was not");
}

#[test]
fn write_split_emits_js_and_ets_trees() {
    let m = module(&common::tiny_abc(), "modules.abc");
    let js_dir = common::tempdir("decompile-split-js");
    let (n_js, b_js) =
        decompile::write_split(&m, &js_dir, DecompileOptions::default()).expect("write_split js");
    assert_eq!(n_js, 1);
    assert!(b_js > 0);
    assert!(js_dir.join("index.js").exists());

    let ets_dir = common::tempdir("decompile-split-ets");
    let (n_ets, _) = decompile::write_split(
        &m,
        &ets_dir,
        DecompileOptions {
            arkui: true,
            ..Default::default()
        },
    )
    .expect("write_split ets");
    assert_eq!(n_ets, 1);
    assert!(ets_dir.join("index.ets").exists());
}

#[test]
fn streaming_decompile_matches_in_memory_and_preserves_target_on_error() {
    let m = module(&common::tiny_abc(), "modules.abc");
    let opts = DecompileOptions {
        call_entry: true,
        ..Default::default()
    };
    let expected = decompile::decompile(&m, opts).expect("decompile").text;

    let mut streamed = Vec::new();
    let n_writer = decompile::decompile_to_writer(&m, opts, &mut streamed).expect("to_writer");
    assert_eq!(n_writer, expected.len());
    assert_eq!(streamed, expected.as_bytes());

    let dir = common::tempdir("decompile-stream");
    let out_path = dir.join("modules.js");
    let n_path = decompile::decompile_to_path(&m, opts, &out_path).expect("to_path");
    assert_eq!(n_path, expected.len());
    assert_eq!(std::fs::read_to_string(&out_path).unwrap(), expected);

    let bad_decode = module(b"corrupt", "bad.abc");
    let missing = dir.join("never_created.js");
    assert!(decompile::decompile_to_path(&bad_decode, opts, &missing).is_err());
    assert!(
        !missing.exists(),
        "decode failure must not create an empty output file"
    );

    let bad_lift = module(&common::lift_fail_abc(), "liftfail.abc");
    assert!(decompile::decompile_to_path(&bad_lift, opts, &missing).is_err());
    assert!(
        !missing.exists(),
        "lift failure must not create an empty output file"
    );
    assert!(decompile::decompile_to_path(&bad_lift, opts, &out_path).is_err());
    assert_eq!(
        std::fs::read_to_string(&out_path).unwrap(),
        expected,
        "lift failure must not truncate an existing output file"
    );
}

#[test]
fn safe_join_enforces_portable_segment_rules_and_windows_device_names() {
    let root = common::tempdir("decompile-safe-join");
    for bad in [
        "",
        ".",
        "..",
        "a/../b.js",
        "/abs/path.js",
        "dir/",
        "a//b.js",
        "a\\b.js",
        "C:/foo.js",
        "pages/CON",
        "pages/con.js",
        "aux.config/index.js",
        "pages/LPT1.ets",
        "pages/COM9.ts",
        "pages/CONIN$.js",
        "pages/CONOUT$.js",
        "pages/trailing./index.js",
        "pages/trailing /index.js",
        "pages/bad*name.js",
        "pages/bad?name.js",
        "pages/ctrl\x7fname.js",
    ] {
        let err = decompile::safe_join(&root, bad).expect_err("unsafe path must be rejected");
        assert_eq!(err.exit_code(), 2, "bad={bad:?} -> {err}");
        assert!(
            err.to_string()
                .contains("refusing unsafe split output path"),
            "bad={bad:?} -> {err}"
        );
    }

    let ok = decompile::safe_join(&root, "com.example.app/pages/Index.ets")
        .expect("valid relative path must pass");
    assert_eq!(
        ok,
        root.join("com.example.app").join("pages").join("Index.ets")
    );
}

#[test]
fn decompile_to_writer_handles_broken_pipe_cleanly_and_reports_other_io_errors() {
    struct ErrWriter(std::io::ErrorKind);
    impl std::io::Write for ErrWriter {
        fn write(&mut self, _buf: &[u8]) -> std::io::Result<usize> {
            Err(std::io::Error::new(self.0, "simulated stdout failure"))
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Err(std::io::Error::new(self.0, "simulated stdout failure"))
        }
    }

    let m = module(&common::tiny_abc(), "modules.abc");
    let opts = DecompileOptions::default();

    assert_eq!(
        decompile::decompile_to_writer(&m, opts, ErrWriter(std::io::ErrorKind::BrokenPipe))
            .expect("BrokenPipe must return Ok"),
        0
    );

    let err =
        decompile::decompile_to_writer(&m, opts, ErrWriter(std::io::ErrorKind::PermissionDenied))
            .expect_err("non-BrokenPipe writer failure must return Err");
    assert_eq!(err.exit_code(), 2);
    assert!(
        err.to_string().contains("failed writing to stdout"),
        "{err}"
    );
}
