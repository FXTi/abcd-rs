// Build script for abcd-isa-sys.
//
// Three phases:
//   1. Ruby code generation — runs gen.rb against isa.yaml to produce C++ headers
//      and the Rust `bytecode.rs` source.
//   2. C++ compilation — compiles the bridge (`isa_bridge.cpp`) and vendor sources
//      into a static library via the `cc` crate.
//   3. Rust FFI bindings — runs `bindgen` on the bridge header to produce
//      `bindings.rs`.

use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let manifest = env::var("CARGO_MANIFEST_DIR").unwrap();
    let out_dir = env::var("OUT_DIR").unwrap();

    // Phase 1: Ruby code generation
    let gen_rb = format!("{manifest}/vendor/isa/gen.rb");
    let isa_yaml = format!("{manifest}/vendor/isa/isa.yaml");
    let isapi = format!("{manifest}/vendor/isa/isapi.rb");
    let pf_isapi = format!("{manifest}/vendor/libpandafile/pandafile_isapi.rb");
    let requires = format!("{isapi},{pf_isapi}");

    // Generate bytecode_instruction_enum_gen.h
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &requires,
        &format!("{manifest}/vendor/libpandafile/templates/bytecode_instruction_enum_gen.h.erb"),
        &format!("{out_dir}/bytecode_instruction_enum_gen.h"),
    );

    // Generate bytecode_instruction-inl_gen.h
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &requires,
        &format!("{manifest}/vendor/libpandafile/templates/bytecode_instruction-inl_gen.h.erb"),
        &format!("{out_dir}/bytecode_instruction-inl_gen.h"),
    );

    // Generate bytecode_emitter_def_gen.h
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &requires,
        &format!("{manifest}/vendor/libpandafile/templates/bytecode_emitter_def_gen.h.erb"),
        &format!("{out_dir}/bytecode_emitter_def_gen.h"),
    );

    // Generate bytecode_emitter_gen.h
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &requires,
        &format!("{manifest}/vendor/libpandafile/templates/bytecode_emitter_gen.h.erb"),
        &format!("{out_dir}/bytecode_emitter_gen.h"),
    );

    // Generate file_format_version.h
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &requires,
        &format!("{manifest}/vendor/libpandafile/templates/file_format_version.h.erb"),
        &format!("{out_dir}/file_format_version.h"),
    );

    // Generate isa_bridge_emit_dispatch.h (C++ emitter dispatch switch)
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &requires,
        &format!("{manifest}/templates/isa_bridge_emit_dispatch.h.erb"),
        &format!("{out_dir}/isa_bridge_emit_dispatch.h"),
    );

    // Generate bytecode.rs (Rust Bytecode enum + Operands + insn constructors)
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &requires,
        &format!("{manifest}/templates/bytecode.rs.erb"),
        &format!("{out_dir}/bytecode.rs"),
    );

    // Phase 2: Compile C++ bridge
    let mut cc_build = cc::Build::new();
    cc_build
        .cpp(true)
        .std("c++17")
        .warnings(false)
        .define("NDEBUG", None)
        .include(&out_dir)
        .include(&format!("{manifest}/bridge/shim"))
        .include(&format!("{manifest}/bridge"))
        .include(&format!("{manifest}/vendor/libpandafile"))
        .include(&format!("{manifest}/vendor/libpandabase"))
        .file(&format!("{manifest}/bridge/isa_bridge.cpp"))
        .file(&format!(
            "{manifest}/vendor/libpandafile/file_format_version.cpp"
        ))
        .file(&format!(
            "{manifest}/vendor/libpandafile/bytecode_emitter.cpp"
        ));

    let target = env::var("TARGET").unwrap_or_default();
    if target.contains("windows") {
        cc_build.define("PANDA_TARGET_WINDOWS", None);
        // Force-include MSVC compat header before all source files
        cc_build.flag(&format!("/FI{manifest}/bridge/shim/platform_compat.h"));
        // Enable C++ exception handling (vendor code uses <iostream>)
        cc_build.flag("/EHsc");
    }

    // Coverage: instrument C++ when running under cargo-llvm-cov
    if env::var("CARGO_LLVM_COV").is_ok() {
        cc_build
            .flag("-fprofile-instr-generate")
            .flag("-fcoverage-mapping");
    }

    cc_build.compile("isa_bridge");

    // Phase 3: Generate Rust FFI bindings
    // Write a wrapper header that includes both the static header and generated declarations
    let wrapper_h = format!("{out_dir}/isa_bridge_bindgen.h");
    std::fs::write(
        &wrapper_h,
        format!("#include \"{manifest}/bridge/isa_bridge.h\"\n"),
    )
    .expect("failed to write bindgen wrapper header");

    let bindings = bindgen::Builder::default()
        .header(&wrapper_h)
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .allowlist_function("isa_.*")
        .allowlist_type("Isa.*")
        .allowlist_var("ISA_.*")
        .generate()
        .expect("bindgen failed");

    let out_path = PathBuf::from(&out_dir).join("bindings.rs");
    bindings
        .write_to_file(&out_path)
        .expect("failed to write bindings");

    // rerun-if-changed
    println!("cargo:rerun-if-changed=bridge/");
    println!("cargo:rerun-if-changed=templates/");
    println!("cargo:rerun-if-changed=vendor/");
}

/// Run a Ruby ERB code-generation step.
///
/// Invokes `gen.rb` with the given ISA data file, require paths, template, and
/// output path.  Panics if Ruby is not installed or the template fails.
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
