use std::path::PathBuf;

fn main() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let out_dir = std::env::var("OUT_DIR").unwrap();

    // Collect vendor .cpp files to compile
    let vendor_dir = manifest_dir.join("vendor/libpandafile");
    let mut cpp_files: Vec<PathBuf> = Vec::new();

    for entry in std::fs::read_dir(&vendor_dir).expect("read vendor/libpandafile") {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().is_some_and(|e| e == "cpp") {
            cpp_files.push(path);
        }
    }

    // Add our bridge
    cpp_files.push(manifest_dir.join("bridge/file_bridge.cpp"));

    // Build C++ library
    let mut build = cc::Build::new();
    build
        .cpp(true)
        .std("c++17")
        .warnings(false)
        .define("NDEBUG", None)
        .define("SUPPORT_KNOWN_EXCEPTION", None)
        // Include path priority: shim > vendor/libpandafile > vendor/libpandabase
        .include(manifest_dir.join("bridge/shim"))
        .include(manifest_dir.join("bridge"))
        .include(&vendor_dir)
        .include(manifest_dir.join("vendor/libpandabase"));

    // Platform-specific flags
    let target = std::env::var("TARGET").unwrap_or_default();
    if target.contains("windows") {
        build
            .define("PANDA_TARGET_WINDOWS", None)
            .flag("/FI")
            .flag("bridge/shim/platform_compat.h")
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

    // Link zlib (needed by file_writer.cpp for adler32 checksum)
    println!("cargo:rustc-link-lib=z");

    // Generate Rust bindings via bindgen
    let bindings = bindgen::Builder::default()
        .header(manifest_dir.join("bridge/file_bridge.h").to_str().unwrap())
        .allowlist_function("abc_.*")
        .allowlist_type("Abc.*")
        .allowlist_var("ABC_.*")
        .clang_args([
            &format!("-I{}", manifest_dir.join("bridge/shim").display()),
            &format!("-I{}", manifest_dir.join("bridge").display()),
            &format!("-I{}", vendor_dir.display()),
            &format!("-I{}", manifest_dir.join("vendor/libpandabase").display()),
        ])
        .generate()
        .expect("bindgen failed");

    let bindings_path = PathBuf::from(&out_dir).join("bindings.rs");
    bindings
        .write_to_file(&bindings_path)
        .expect("failed to write bindings.rs");

    // Rerun triggers
    println!("cargo:rerun-if-changed=bridge/");
    println!("cargo:rerun-if-changed=vendor/");
}
