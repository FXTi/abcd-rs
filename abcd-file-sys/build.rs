use std::path::PathBuf;
use std::process::Command;

fn main() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());

    // Phase 1: Ruby code generation (source_lang_enum.h, type.h, file_format_version.h)
    let vendor_isa = manifest_dir.join("vendor/isa");
    let vendor_pf = manifest_dir.join("vendor/libpandafile");
    let gen_rb = vendor_isa.join("gen.rb");
    let isa_yaml = vendor_isa.join("isa.yaml");
    let isapi = vendor_isa.join("isapi.rb");
    let pf_isapi = vendor_pf.join("pandafile_isapi.rb");
    let plugin_opts = vendor_pf.join("plugin_options.rb");
    let types_rb = vendor_pf.join("types.rb");
    let codegen_init = manifest_dir.join("bridge/codegen_init.rb");
    let requires = format!(
        "{},{},{},{},{}",
        isapi.display(),
        pf_isapi.display(),
        plugin_opts.display(),
        types_rb.display(),
        codegen_init.display()
    );
    let templates = vendor_pf.join("templates");
    let types_yaml = vendor_pf.join("types.yaml");

    run_ruby(
        &gen_rb,
        &isa_yaml,
        &requires,
        &templates.join("source_lang_enum.h.erb"),
        &out_dir.join("source_lang_enum.h"),
    );
    run_ruby(
        &gen_rb,
        &types_yaml,
        &requires,
        &templates.join("type.h.erb"),
        &out_dir.join("type.h"),
    );
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &requires,
        &templates.join("file_format_version.h.erb"),
        &out_dir.join("file_format_version.h"),
    );

    // Phase 2: Compile C++ library
    let vendor_dir = manifest_dir.join("vendor/libpandafile");
    let mut cpp_files: Vec<PathBuf> = Vec::new();

    // Collect vendor libpandafile .cpp files
    for entry in std::fs::read_dir(&vendor_dir).expect("read vendor/libpandafile") {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().is_some_and(|e| e == "cpp") {
            cpp_files.push(path);
        }
    }

    // Vendor libpandabase .cpp files
    cpp_files.push(manifest_dir.join("vendor/libpandabase/utils/utf.cpp"));

    // Our bridge files
    cpp_files.push(manifest_dir.join("bridge/file_bridge.cpp"));
    cpp_files.push(manifest_dir.join("bridge/file_impl.cpp"));

    let mut build = cc::Build::new();
    build
        .cpp(true)
        .std("c++17")
        .warnings(false)
        .define("NDEBUG", None)
        .define("SUPPORT_KNOWN_EXCEPTION", None)
        // Include path priority: shim > shim/utils (for bare "logger.h") > OUT_DIR > bridge > vendor
        .include(manifest_dir.join("bridge/shim"))
        .include(manifest_dir.join("bridge/shim/utils"))
        .include(&out_dir)
        .include(manifest_dir.join("bridge"))
        .include(&vendor_dir)
        .include(manifest_dir.join("vendor/libpandabase"));

    // Platform-specific flags
    let target = std::env::var("TARGET").unwrap_or_default();
    if target.contains("windows") {
        build
            .define("PANDA_TARGET_WINDOWS", None)
            .flag(&format!(
                "/FI{}",
                manifest_dir.join("bridge/shim/platform_compat.h").display()
            ))
            .flag("/EHsc");
    }

    // Coverage: instrument C++ when running under cargo-llvm-cov
    if std::env::var("CARGO_LLVM_COV").is_ok() {
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
    let bindings = bindgen::Builder::default()
        .header(manifest_dir.join("bridge/file_bridge.h").to_str().unwrap())
        .allowlist_function("abc_.*")
        .allowlist_type("Abc.*")
        .allowlist_var("ABC_.*")
        .clang_args([
            &format!("-I{}", manifest_dir.join("bridge/shim").display()),
            &format!("-I{}", out_dir.display()),
            &format!("-I{}", manifest_dir.join("bridge").display()),
            &format!("-I{}", vendor_dir.display()),
            &format!("-I{}", manifest_dir.join("vendor/libpandabase").display()),
        ])
        .generate()
        .expect("bindgen failed");

    let bindings_path = out_dir.join("bindings.rs");
    bindings
        .write_to_file(&bindings_path)
        .expect("failed to write bindings.rs");

    // Rerun triggers
    println!("cargo:rerun-if-changed=bridge/");
    println!("cargo:rerun-if-changed=vendor/");
}

fn run_ruby(
    gen_rb: &PathBuf,
    data: &PathBuf,
    requires: &str,
    template: &PathBuf,
    output: &PathBuf,
) {
    let status = Command::new("ruby")
        .args([
            "-rostruct",
            gen_rb.to_str().unwrap(),
            "-t",
            template.to_str().unwrap(),
            "-d",
            data.to_str().unwrap(),
            "-r",
            requires,
            "-o",
            output.to_str().unwrap(),
        ])
        .status()
        .unwrap_or_else(|e| panic!("Failed to run ruby: {e}. Is ruby installed?"));

    assert!(
        status.success(),
        "Ruby code generation failed for template: {}",
        template.display()
    );
}
