use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let manifest = env::var("CARGO_MANIFEST_DIR").unwrap();
    let out_dir = env::var("OUT_DIR").unwrap();

    // Phase 1: Ruby code generation (source_lang_enum.h, type.h, file_format_version.h)
    let gen_rb = format!("{manifest}/vendor/isa/gen.rb");
    let isa_yaml = format!("{manifest}/vendor/isa/isa.yaml");
    let tpl = format!("{manifest}/vendor/libpandafile/templates");

    // Each template gets only the requires it needs (matching upstream).
    // Ruby's `def` is last-writer-wins, so the final Gen.on_require must
    // match the module the template actually uses.
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &format!("{manifest}/vendor/libpandafile/plugin_options.rb"),
        &format!("{tpl}/source_lang_enum.h.erb"),
        &format!("{out_dir}/source_lang_enum.h"),
    );
    run_ruby(
        &gen_rb,
        &format!("{manifest}/vendor/libpandafile/types.yaml"),
        &format!("{manifest}/vendor/libpandafile/types.rb"),
        &format!("{tpl}/type.h.erb"),
        &format!("{out_dir}/type.h"),
    );
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &format!(
            "{manifest}/vendor/isa/isapi.rb,\
             {manifest}/vendor/libpandafile/pandafile_isapi.rb"
        ),
        &format!("{tpl}/file_format_version.h.erb"),
        &format!("{out_dir}/file_format_version.h"),
    );

    // Phase 2: Compile C++ library
    let vendor_pf = format!("{manifest}/vendor/libpandafile");
    let mut cpp_files: Vec<PathBuf> = Vec::new();

    // Collect vendor libpandafile .cpp files
    for entry in std::fs::read_dir(&vendor_pf).expect("read vendor/libpandafile") {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().is_some_and(|e| e == "cpp") {
            cpp_files.push(path);
        }
    }

    // Vendor libpandabase .cpp files
    cpp_files.push(format!("{manifest}/vendor/libpandabase/utils/utf.cpp").into());

    // Our bridge files
    cpp_files.push(format!("{manifest}/bridge/file_bridge.cpp").into());

    let mut build = cc::Build::new();
    build
        .cpp(true)
        .std("c++17")
        .warnings(false)
        .define("NDEBUG", None)
        .define("SUPPORT_KNOWN_EXCEPTION", None)
        // Include path priority: shim > shim/utils (for bare "logger.h") > OUT_DIR > bridge > vendor
        .include(&format!("{manifest}/bridge/shim"))
        .include(&format!("{manifest}/bridge/shim/utils"))
        .include(&out_dir)
        .include(&format!("{manifest}/bridge"))
        .include(&vendor_pf)
        .include(&format!("{manifest}/vendor/libpandabase"));

    // Force-include missing transitive headers that the upstream build provides
    let fixups = format!("{manifest}/bridge/shim/vendor_fixups.h");

    // Platform-specific flags
    let target = env::var("TARGET").unwrap_or_default();
    if target.contains("windows") {
        build
            .define("PANDA_TARGET_WINDOWS", None)
            .flag(&format!("/FI{manifest}/bridge/shim/platform_compat.h"))
            .flag(&format!("/FI{fixups}"))
            .flag("/EHsc");
    } else {
        build.flag("-include").flag(&fixups);
    }

    // Coverage: instrument C++ when running under cargo-llvm-cov
    if env::var("CARGO_LLVM_COV").is_ok() {
        build
            .flag("-fprofile-instr-generate")
            .flag("-fcoverage-mapping");
    }

    for f in &cpp_files {
        build.file(f);
    }

    build.compile("file_bridge");

    // No need to link system zlib — bridge/shim/zlib.h provides inline adler32

    // Phase 3: Generate Rust bindings via bindgen
    // file_bridge.h is a pure C header (only <stddef.h> + <stdint.h>, opaque types),
    // so no extra include paths are needed.
    let bindings = bindgen::Builder::default()
        .header(&format!("{manifest}/bridge/file_bridge.h"))
        .allowlist_function("abc_.*")
        .allowlist_type("Abc.*")
        .allowlist_var("ABC_.*")
        .generate()
        .expect("bindgen failed");

    bindings
        .write_to_file(format!("{out_dir}/bindings.rs"))
        .expect("failed to write bindings.rs");

    // Rerun triggers
    println!("cargo:rerun-if-changed=bridge/");
    println!("cargo:rerun-if-changed=vendor/");
}

fn run_ruby(gen_rb: &str, data: &str, requires: &str, template: &str, output: &str) {
    let status = Command::new("ruby")
        .args([
            "-rostruct",
            gen_rb,
            "-t",
            template,
            "-d",
            data,
            "-r",
            requires,
            "-o",
            output,
        ])
        .status()
        .unwrap_or_else(|e| panic!("Failed to run ruby: {e}. Is ruby installed?"));

    assert!(
        status.success(),
        "Ruby code generation failed for template: {template}"
    );
}
