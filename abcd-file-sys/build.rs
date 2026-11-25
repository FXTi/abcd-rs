// Build script for abcd-file-sys.
//
// Compiles the exception-guarded C++ `libpandafile` bridge (`bridge/file_bridge.cpp`)
// and upstream accessor/writer translation units from the workspace `vendor/`
// snapshot. All C++ generated headers and Rust FFI/enum bindings are
// pre-generated offline via `scripts/vendor-gen.py`, with every vendor enum and
// access-flag value checked at C++ compile time via `file_bridge_enum_checks.h`.

use std::env;
use std::path::{Path, PathBuf};

fn main() {
    let manifest = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR must be set");
    let local_vendor = format!("{manifest}/vendor");
    let vendor_root = if Path::new(&format!("{local_vendor}/arkcompiler_runtime_core")).is_dir() {
        local_vendor
    } else {
        format!("{manifest}/../vendor")
    };

    let ark = format!("{vendor_root}/arkcompiler_runtime_core");
    let vendor_pf = format!("{ark}/libpandafile");
    let vendor_gen = format!("{vendor_root}/generated");
    let vendor_shim = format!("{vendor_root}/shim");

    // Excluded upstream translation units in legacy `libpandafile/`:
    // - file_reader.cpp: legacy-tree drift (calls undeclared MethodParamItem::AddRuntimeAnnotation).
    // - file.cpp / pgo.cpp: pull in runtime ifstream/PGO machinery unused by the bridge.
    // - method_handle_data_accessor.cpp: unused by the bridge.
    const EXCLUDED: [&str; 4] = [
        "file_reader.cpp",
        "file.cpp",
        "pgo.cpp",
        "method_handle_data_accessor.cpp",
    ];

    let mut cpp_files: Vec<PathBuf> = Vec::new();
    for entry in std::fs::read_dir(&vendor_pf).expect("read vendor libpandafile") {
        let path = entry.expect("read vendor dir entry").path();
        let name = path
            .file_name()
            .expect("vendor entry must have file name")
            .to_string_lossy();
        if path.extension().is_some_and(|e| e == "cpp") && !EXCLUDED.contains(&name.as_ref()) {
            cpp_files.push(path);
        }
    }
    cpp_files.sort();
    cpp_files.push(format!("{ark}/libpandabase/utils/utf.cpp").into());
    cpp_files.push(format!("{manifest}/bridge/file_bridge.cpp").into());

    let mut build = cc::Build::new();
    build
        .cpp(true)
        .std("c++17")
        .warnings(false)
        .define("NDEBUG", None)
        .define("SUPPORT_KNOWN_EXCEPTION", None)
        // Include priority: crate shim > shared shim > shared shim/utils > generated > bridge > vendor
        .include(format!("{manifest}/bridge/shim"))
        .include(&vendor_shim)
        .include(format!("{vendor_shim}/utils"))
        .include(&vendor_gen)
        .include(format!("{manifest}/bridge"))
        .include(&vendor_pf)
        .include(format!("{ark}/libpandabase/include"))
        .include(format!("{ark}/libpandabase/include/libpandabase"))
        .include(format!("{ark}/assembler"))
        .include(&ark)
        .include(format!("{ark}/platforms"));

    let fixups = format!("{manifest}/bridge/shim/vendor_fixups.h");
    let target = env::var("TARGET").unwrap_or_default();
    if target.contains("windows") {
        build
            .define("PANDA_TARGET_WINDOWS", None)
            .flag(format!("/FI{vendor_shim}/platform_compat.h"))
            .flag(format!("/FI{fixups}"))
            .flag("/EHsc")
            .flag("/permissive-");
    } else {
        build.define("PANDA_TARGET_UNIX", None);
        if target.contains("apple") {
            build.define("PANDA_TARGET_MACOS", None);
        }
        build.flag("-include").flag(&fixups);
    }

    if env::var("CARGO_LLVM_COV").is_ok() {
        build
            .flag("-fprofile-instr-generate")
            .flag("-fcoverage-mapping");
    }

    for f in &cpp_files {
        build.file(f);
    }
    build.compile("file_bridge");

    println!("cargo:rerun-if-changed=bridge/");
    println!("cargo:rerun-if-changed=src/generated/");
    println!("cargo:rerun-if-changed={vendor_root}/");
    println!("cargo:rerun-if-changed={vendor_shim}/utils/logger.h");
}
