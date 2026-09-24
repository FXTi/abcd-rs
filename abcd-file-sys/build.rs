use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let manifest = env::var("CARGO_MANIFEST_DIR").unwrap();
    let out_dir = env::var("OUT_DIR").unwrap();

    // Phase 1: Ruby code generation (source_lang_enum.h, type.h, file_format_version.h)
    let gen_rb = format!("{manifest}/arkcompiler_runtime_core/isa/gen.rb");
    let isa_yaml = format!("{manifest}/arkcompiler_runtime_core/isa/isa.yaml");
    let tpl = format!("{manifest}/arkcompiler_runtime_core/libpandafile/templates");

    // Each template gets only the requires it needs (matching upstream).
    // Ruby's `def` is last-writer-wins, so the final Gen.on_require must
    // match the module the template actually uses.
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &format!("{manifest}/arkcompiler_runtime_core/templates/plugin_options.rb"),
        &format!("{tpl}/source_lang_enum.h.erb"),
        &format!("{out_dir}/source_lang_enum.h"),
    );
    run_ruby(
        &gen_rb,
        &format!("{manifest}/arkcompiler_runtime_core/libpandafile/types.yaml"),
        &format!("{manifest}/arkcompiler_runtime_core/libpandafile/types.rb"),
        &format!("{tpl}/type.h.erb"),
        &format!("{out_dir}/type.h"),
    );
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &format!(
            "{manifest}/arkcompiler_runtime_core/isa/isapi.rb,\
             {manifest}/arkcompiler_runtime_core/libpandafile/pandafile_isapi.rb"
        ),
        &format!("{tpl}/file_format_version.h.erb"),
        &format!("{out_dir}/file_format_version.h"),
    );

    // v7.0's bytecode_instruction.h includes bytecode_instruction_enum_gen.h
    // (generated upstream by the same gen.rb flow; the old flat vendored
    // snapshot predated that include).
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &format!(
            "{manifest}/arkcompiler_runtime_core/isa/isapi.rb,\
             {manifest}/arkcompiler_runtime_core/libpandafile/pandafile_isapi.rb"
        ),
        &format!("{tpl}/bytecode_instruction_enum_gen.h.erb"),
        &format!("{out_dir}/bytecode_instruction_enum_gen.h"),
    );
    for (tpl_name, out_name) in [
        (
            "bytecode_instruction-inl_gen.h.erb",
            "bytecode_instruction-inl_gen.h",
        ),
        (
            "bytecode_emitter_def_gen.h.erb",
            "bytecode_emitter_def_gen.h",
        ),
        ("bytecode_emitter_gen.h.erb", "bytecode_emitter_gen.h"),
    ] {
        run_ruby(
            &gen_rb,
            &isa_yaml,
            &format!(
                "{manifest}/arkcompiler_runtime_core/isa/isapi.rb,\
                 {manifest}/arkcompiler_runtime_core/libpandafile/pandafile_isapi.rb"
            ),
            &format!("{tpl}/{tpl_name}"),
            &format!("{out_dir}/{out_name}"),
        );
    }

    // Phase 1b: Generate file_bridge_enums.h from vendor headers
    // Parses modifiers.h to extract ACC_* names, then writes a C++ header
    // that references vendor constexpr/enum values directly.
    generate_enums_header(&manifest, &out_dir);

    // Phase 2: Compile C++ library
    let vendor_pf = format!("{manifest}/arkcompiler_runtime_core/libpandafile");
    let mut cpp_files: Vec<PathBuf> = Vec::new();

    // Collect vendor libpandafile .cpp files.
    //
    // The bridge needs only the accessor/writer/serializer translation units —
    // the same set as the old vendored subset.  Excluded upstream files:
    //   - file_reader.cpp: legacy-tree drift — calls
    //     MethodParamItem::AddRuntimeAnnotation, which legacy file_items.h
    //     does not declare (the consistent implementation lives in
    //     static_core/libarkfile).  Present at every upstream ref we tested,
    //     including our pinned master commit; unused by the bridge.
    //   - file.cpp / pgo.cpp: pull in runtime machinery (pgo, ifstream) that
    //     needs the full upstream build scaffolding; unused by the bridge.
    //   - method_handle_data_accessor.cpp: not part of the proven subset.
    const EXCLUDED: [&str; 4] = [
        "file_reader.cpp",
        "file.cpp",
        "pgo.cpp",
        "method_handle_data_accessor.cpp",
    ];
    for entry in std::fs::read_dir(&vendor_pf).expect("read vendor/libpandafile") {
        let entry = entry.unwrap();
        let path = entry.path();
        let name = path.file_name().unwrap().to_string_lossy();
        if path.extension().is_some_and(|e| e == "cpp") && !EXCLUDED.contains(&name.as_ref()) {
            cpp_files.push(path);
        }
    }

    // Vendor libpandabase .cpp files
    cpp_files
        .push(format!("{manifest}/arkcompiler_runtime_core/libpandabase/utils/utf.cpp").into());

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
        .include(&format!(
            "{manifest}/arkcompiler_runtime_core/libpandabase/include"
        ))
        // Upstream mixes both include forms: "macros.h" (bare, needs the
        // inner dir) and "libpandabase/utils/timers.h" (needs include/).
        .include(&format!(
            "{manifest}/arkcompiler_runtime_core/libpandabase/include/libpandabase"
        ))
        // assembler headers for annotation value type validation
        .include(&format!("{manifest}/arkcompiler_runtime_core/assembler"))
        // vendor root: upstream code uses repo-root-prefixed includes such as
        // "libpandabase/utils/timers.h", resolved by this path in our flat layout
        .include(&format!("{manifest}/arkcompiler_runtime_core"));

    // Force-include missing transitive headers that the upstream build provides
    let fixups = format!("{manifest}/bridge/shim/vendor_fixups.h");

    // Platform-specific flags
    let target = env::var("TARGET").unwrap_or_default();
    if target.contains("windows") {
        build
            .define("PANDA_TARGET_WINDOWS", None)
            .include(format!("{manifest}/arkcompiler_runtime_core/platforms"))
            .flag(&format!("/FI{manifest}/bridge/shim/platform_compat.h"))
            .flag(&format!("/FI{fixups}"))
            .flag("/EHsc");
    } else {
        // Full-subtree vendoring pulls os/file.h, which requires the
        // platform macro (the old flat subset never reached it).
        build.define("PANDA_TARGET_UNIX", None);
        // macOS has no stat64: upstream gates those paths on this macro.
        if target.contains("apple") {
            build.define("PANDA_TARGET_MACOS", None);
        }
        build.include(&format!("{manifest}/arkcompiler_runtime_core/platforms"));
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

    // Phase 3a: Generate Rust bindings for the C bridge API
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

    // Phase 3b: Generate Rust bindings for vendor enums/constants
    // Parses C++ vendor headers directly so constants come from vendor code,
    // not hand-maintained #define mirrors.
    let enum_bindings = bindgen::Builder::default()
        .header(&format!("{out_dir}/file_bridge_enums.h"))
        .clang_args(["-x", "c++", "-std=c++17"])
        .clang_arg(format!("-include{fixups}"))
        .clang_arg(format!("-I{manifest}/bridge/shim"))
        .clang_arg(format!("-I{manifest}/bridge/shim/utils"))
        .clang_arg(format!("-I{out_dir}"))
        .clang_arg(format!("-I{vendor_pf}"))
        .clang_arg(format!(
            "-I{manifest}/arkcompiler_runtime_core/libpandabase/include"
        ))
        .clang_arg(format!(
            "-I{manifest}/arkcompiler_runtime_core/libpandabase/include/libpandabase"
        ))
        .clang_arg(format!("-I{manifest}/arkcompiler_runtime_core"))
        .clang_arg("-DNDEBUG")
        .clang_arg("-DSUPPORT_KNOWN_EXCEPTION")
        // ACC_* re-exported via named enum
        .allowlist_var("ABC_ACC_.*")
        .allowlist_type("AbcAccessFlags")
        // Vendor enum classes
        .allowlist_type("panda::panda_file::LiteralTag")
        .allowlist_type("panda::panda_file::ModuleTag")
        .allowlist_type("panda::panda_file::FunctionKind")
        .allowlist_type("panda::panda_file::SourceLang")
        .allowlist_type("panda::panda_file::Type_TypeId")
        .allowlist_type("panda::panda_file::MethodHandleType")
        .constified_enum(".*")
        .disable_name_namespacing()
        .generate()
        .expect("bindgen enum pass failed");

    enum_bindings
        .write_to_file(format!("{out_dir}/enum_bindings.rs"))
        .expect("failed to write enum_bindings.rs");

    // Rerun triggers
    println!("cargo:rerun-if-changed=bridge/");
    // Only the subtrees the bridge actually consumes — the full submodule is
    // hundreds of MB and most of it (static_core, tests) never reaches us.
    println!("cargo:rerun-if-changed=arkcompiler_runtime_core/isa/");
    println!("cargo:rerun-if-changed=arkcompiler_runtime_core/libpandafile/");
    println!("cargo:rerun-if-changed=arkcompiler_runtime_core/libpandabase/");
    println!("cargo:rerun-if-changed=arkcompiler_runtime_core/assembler/");
    println!("cargo:rerun-if-changed=arkcompiler_runtime_core/platforms/unix/libpandabase/");
    println!("cargo:rerun-if-changed=arkcompiler_runtime_core/templates/plugin_options.rb");
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

/// Parse `modifiers.h` for `ACC_*` names and generate `file_bridge_enums.h` in OUT_DIR.
///
/// The generated header includes vendor C++ headers and re-exports:
/// - ACC_* constexpr values via an anonymous enum (names auto-extracted, values from vendor)
/// - enum class types (LiteralTag, ModuleTag, etc.) are included for bindgen to parse directly
///
/// Only writes the file when content actually changes to avoid unnecessary rebuilds.
fn generate_enums_header(manifest: &str, out_dir: &str) {
    let modifiers = std::fs::read_to_string(format!(
        "{manifest}/arkcompiler_runtime_core/libpandafile/modifiers.h"
    ))
    .expect("read modifiers.h");

    // Extract ACC_* names from any `constexpr` line containing an ACC_ identifier.
    let acc_names: Vec<&str> = modifiers
        .lines()
        .filter(|l| l.contains("constexpr"))
        .filter_map(|l| l.split_whitespace().find(|w| w.starts_with("ACC_")))
        .collect();

    let mut out = String::from(
        "/* Auto-generated by build.rs from vendor headers — do not edit. */\n\
         #pragma once\n\n\
         #include \"modifiers.h\"\n\
         #include \"literal_data_accessor.h\"\n\
         #include \"module_data_accessor.h\"\n\
         #include \"file_items.h\"\n\
         #include \"type.h\"\n\
         #include \"source_lang_enum.h\"\n\n\
         /* ACC_* are static constexpr in namespace panda — bindgen cannot extract\n\
          * them directly.  Re-export via anonymous enum whose values reference the\n\
          * vendor constexpr so only *names* are listed here; *values* always come\n\
          * from vendor code.  Names are auto-extracted from modifiers.h. */\n\
         enum AbcAccessFlags : uint32_t {\n",
    );
    for name in &acc_names {
        out.push_str(&format!("    ABC_{name} = panda::{name},\n"));
    }
    out.push_str(
        "};\n\n\
         /* The following enum classes are extracted automatically by bindgen:\n\
          *   panda::panda_file::LiteralTag       (literal_data_accessor.h)\n\
          *   panda::panda_file::ModuleTag        (module_data_accessor.h)\n\
          *   panda::panda_file::FunctionKind     (file_items.h)\n\
          *   panda::panda_file::SourceLang       (source_lang_enum.h)\n\
          *   panda::panda_file::Type::TypeId     (type.h)\n\
          */\n",
    );

    let path = format!("{out_dir}/file_bridge_enums.h");
    if std::fs::read_to_string(&path).ok().as_deref() != Some(out.as_str()) {
        std::fs::write(&path, &out).expect("write file_bridge_enums.h");
    }
}
