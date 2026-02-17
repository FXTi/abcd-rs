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

    // Generate isa_bridge_tables.h (our custom metadata tables)
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &requires,
        &format!("{manifest}/templates/isa_bridge_tables.h.erb"),
        &format!("{out_dir}/isa_bridge_tables.h"),
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

    // Generate isa_bridge_emitter.h (C bridge for emitter — implementations)
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &requires,
        &format!("{manifest}/templates/isa_bridge_emitter.h.erb"),
        &format!("{out_dir}/isa_bridge_emitter.h"),
    );

    // Generate isa_bridge_emitter_decl.h (declarations only, for bindgen)
    run_ruby(
        &gen_rb,
        &isa_yaml,
        &requires,
        &format!("{manifest}/templates/isa_bridge_emitter_decl.h.erb"),
        &format!("{out_dir}/isa_bridge_emitter_decl.h"),
    );

    // Phase 2: Compile C++ bridge
    cc::Build::new()
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
            "{manifest}/vendor/libpandafile/bytecode_emitter.cpp"
        ))
        .compile("isa_bridge");

    // Phase 3: Generate Rust FFI bindings
    // Write a wrapper header that includes both the static header and generated declarations
    let wrapper_h = format!("{out_dir}/isa_bridge_bindgen.h");
    std::fs::write(
        &wrapper_h,
        format!(
            "#include \"{manifest}/bridge/isa_bridge.h\"\n\
             #include \"{out_dir}/isa_bridge_emitter_decl.h\"\n\
             #include \"{out_dir}/isa_bridge_tables.h\"\n"
        ),
    )
    .expect("failed to write bindgen wrapper header");

    let bindings = bindgen::Builder::default()
        .header(&wrapper_h)
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("bindgen failed");

    let out_path = PathBuf::from(&out_dir).join("bindings.rs");
    bindings
        .write_to_file(&out_path)
        .expect("failed to write bindings");

    // Export bindings path for dependent crates via links metadata
    println!("cargo:bindings_rs={}", out_path.display());

    // rerun-if-changed
    for path in &[
        "bridge/isa_bridge.h",
        "bridge/isa_bridge.cpp",
        "bridge/shim/securec.h",
        "bridge/shim/file.h",
        "vendor/isa/isa.yaml",
        "vendor/libpandafile/bytecode_instruction.h",
        "vendor/libpandafile/bytecode_instruction-inl.h",
        "vendor/libpandafile/bytecode_emitter.h",
        "vendor/libpandafile/bytecode_emitter.cpp",
        "vendor/libpandabase/macros.h",
        "vendor/libpandabase/utils/span.h",
        "vendor/libpandabase/utils/bit_utils.h",
        "templates/isa_bridge_tables.h.erb",
        "templates/isa_bridge_emitter.h.erb",
        "templates/isa_bridge_emitter_decl.h.erb",
        "vendor/libpandafile/templates/bytecode_instruction_enum_gen.h.erb",
        "vendor/libpandafile/templates/bytecode_instruction-inl_gen.h.erb",
        "vendor/libpandafile/templates/bytecode_emitter_def_gen.h.erb",
        "vendor/libpandafile/templates/bytecode_emitter_gen.h.erb",
        "vendor/libpandafile/templates/file_format_version.h.erb",
    ] {
        println!("cargo:rerun-if-changed={manifest}/{path}");
    }
}

fn run_ruby(gen_rb: &str, data: &str, requires: &str, template: &str, output: &str) {
    let status = Command::new("ruby")
        .args([
            gen_rb, "-t", template, "-d", data, "-r", requires, "-o", output,
        ])
        .status()
        .unwrap_or_else(|e| panic!("Failed to run ruby: {e}. Is ruby installed?"));

    assert!(
        status.success(),
        "Ruby code generation failed for template: {template}"
    );
}
