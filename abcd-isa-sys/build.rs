// Build script for abcd-isa-sys.
//
// Compiles the C++ ISA bridge (`bridge/isa_bridge.cpp`) and upstream emitter /
// format-version translation units from the workspace `vendor/` snapshot.
// All Ruby/ISA and FFI Rust bindings are pre-generated offline via
// `scripts/vendor-gen.py` and verified in CI (`vendor-verify`).

use std::env;
use std::path::Path;

fn main() {
    let manifest = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR must be set");
    let local_vendor = format!("{manifest}/vendor");
    let vendor_root = if Path::new(&format!("{local_vendor}/arkcompiler_runtime_core")).is_dir() {
        local_vendor
    } else {
        format!("{manifest}/../vendor")
    };

    let ark = format!("{vendor_root}/arkcompiler_runtime_core");
    let vendor_gen = format!("{vendor_root}/generated");
    let vendor_shim = format!("{vendor_root}/shim");

    let mut cc_build = cc::Build::new();
    cc_build
        .cpp(true)
        .std("c++17")
        .warnings(false)
        .define("NDEBUG", None)
        .define("SUPPORT_KNOWN_EXCEPTION", None)
        .include(format!("{manifest}/bridge/generated"))
        .include(&vendor_gen)
        .include(format!("{manifest}/bridge/shim"))
        .include(&vendor_shim)
        .include(format!("{manifest}/bridge"))
        .include(format!("{ark}/libpandafile"))
        .include(format!("{ark}/libpandabase/include"))
        // Upstream mixes both include forms: "macros.h" (bare, needs the inner
        // dir) and "libpandabase/utils/timers.h" (needs include/).
        .include(format!("{ark}/libpandabase/include/libpandabase"))
        .include(format!("{ark}/platforms"))
        .file(format!("{manifest}/bridge/isa_bridge.cpp"))
        .file(format!("{ark}/libpandafile/file_format_version.cpp"))
        .file(format!("{ark}/libpandafile/bytecode_emitter.cpp"));

    let target = env::var("TARGET").unwrap_or_default();
    // Force-include the crate-local shim `file.h` BEFORE everything so
    // upstream quote-includes of `"file.h"` resolve to our lightweight stub
    // (matching include guard `LIBPANDAFILE_FILE_H`) rather than pulling in OS
    // memory/filesystem headers unneeded by the ISA emitter.
    if target.contains("windows") {
        cc_build.define("PANDA_TARGET_WINDOWS", None);
        cc_build.flag(format!("/FI{vendor_shim}/platform_compat.h"));
        cc_build.flag(format!("/FI{manifest}/bridge/shim/file.h"));
        cc_build.flag("/EHsc");
        cc_build.flag("/permissive-");
    } else {
        cc_build.define("PANDA_TARGET_UNIX", None);
        if target.contains("apple") {
            cc_build.define("PANDA_TARGET_MACOS", None);
        }
        cc_build
            .flag("-include")
            .flag(format!("{manifest}/bridge/shim/file.h"));
    }

    if env::var("CARGO_LLVM_COV").is_ok() {
        cc_build
            .flag("-fprofile-instr-generate")
            .flag("-fcoverage-mapping");
    }

    cc_build.compile("isa_bridge");

    println!("cargo:rerun-if-changed=bridge/");
    println!("cargo:rerun-if-changed=src/generated/");
    println!("cargo:rerun-if-changed={vendor_root}/");
}
