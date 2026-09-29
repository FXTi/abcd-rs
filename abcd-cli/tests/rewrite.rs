//! `abcd rewrite` tests: the decode → lift → [opt] → lower → encode
//! pipeline over synthesized fixtures (zero binary fixtures rule).
//!
//! Byte-level parity of the lower against upstream is gated by the corpus
//! suites (tests/lift-lower/corpus_lower_oracle.rs); here we pin the CLI
//! plumbing: shape preservation on an identity rewrite, the `--check`
//! self-check, the `--opt` path, container input, and error mapping.

mod common;

use abcd_cli::CliError;
use abcd_cli::input::{self, ModuleSelection};
use abcd_cli::rewrite::{self, RewriteOptions};

/// A realistic minimal .abc: one static method `func_main_0() { return; }`
/// with the es2abc implicit frame slots — `num_args = 3`
/// ([func][newtarget][this], the `0xF` default callType shape that real
/// producer output always carries). `common::tiny_abc()` (zero args)
/// exercises the degenerate shape in
/// `degenerate_zero_arg_shape_rewrites_cleanly`; the success-path tests
/// use this three-arg fixture as the realistic shape.
fn rewritable_abc() -> Vec<u8> {
    use abcd_file::{AccessFlags, Builder, Type};
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _offsets) = abcd_isa::encode(&[abcd_isa::Bytecode::Return]).unwrap();
    b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 4, 3);
    b.deduplicate();
    b.finalize().expect("rewritable fixture must finalize")
}

/// Load one bare-abc module through the shared input layer.
fn module_of(abc: &[u8], source: &str) -> input::InputModule {
    let modules = input::load_bytes(abc, source, ModuleSelection::Single).expect("load");
    modules.into_iter().next().expect("one module")
}

/// (method count, total instruction count) of a decoded .abc.
fn shape(abc: &[u8]) -> (usize, usize) {
    let file = abcd_file::decode(abc).expect("decode for shape");
    let mut methods = 0;
    let mut instructions = 0;
    for (_class, method) in file.all_methods() {
        methods += 1;
        if let Some(body) = &method.body {
            instructions += body.bytecodes.len();
        }
    }
    (methods, instructions)
}

#[test]
fn identity_rewrite_preserves_method_and_instruction_counts() {
    // Identity is asserted on the pipeline's own normal form: the raw
    // fixture is NOT in es2abc-normal form (a bare `Return`, no seed loads
    // or copy-in prologue), so a v0.1-lift-faithful lower legitimately
    // materializes extra instructions on the first pass. The normalized
    // output is a fixpoint — the corpus byte-identity gates rely on the
    // same property over real producer output.
    let raw = rewritable_abc();
    let normalized = rewrite::rewrite(&module_of(&raw, "raw.abc"), RewriteOptions::default())
        .expect("normalizing rewrite")
        .abc;

    let module = module_of(&normalized, "normalized.abc");
    let out = rewrite::rewrite(&module, RewriteOptions::default()).expect("identity rewrite");
    assert_eq!(out.name, "normalized");
    assert_eq!(out.provenance, "normalized.abc");

    let (in_methods, in_insns) = shape(&module.abc);
    let (out_methods, out_insns) = shape(&out.abc);
    assert_eq!(in_methods, 1);
    assert_eq!(out_methods, in_methods, "method count must survive");
    assert_eq!(out_insns, in_insns, "instruction count must survive");
    assert_eq!(out.abc, module.abc, "the normal form is a fixpoint");

    // Stats are measured, not assumed: they must agree with the decode.
    assert_eq!(out.stats.methods, in_methods);
    assert_eq!(out.stats.lowered, in_methods, "the method has a body");
    assert_eq!(out.stats.input_instructions, in_insns);
    assert_eq!(out.stats.output_instructions, out_insns);
    assert!(!out.stats.optimized_changed, "no optimizer ran");
}

#[test]
fn rewrite_raw_fixture_stats_are_measured() {
    let module = module_of(&rewritable_abc(), "raw.abc");
    let out = rewrite::rewrite(&module, RewriteOptions::default()).expect("rewrite");
    let (out_methods, out_insns) = shape(&out.abc);
    assert_eq!(out_methods, 1);
    assert_eq!(
        out.stats.input_instructions, 1,
        "the raw fixture is bare Return"
    );
    assert_eq!(
        out.stats.output_instructions, out_insns,
        "stats must reflect the actual output"
    );
}

#[test]
fn rewrite_check_path_passes_on_valid_pipeline_output() {
    let module = module_of(&rewritable_abc(), "raw.abc");
    let opts = RewriteOptions {
        optimize: false,
        check: true,
    };
    let out = rewrite::rewrite(&module, opts).expect("rewrite --check");
    // --check already re-decoded internally; the bytes must still decode
    // for an independent reader.
    let (out_methods, _) = shape(&out.abc);
    assert_eq!(out_methods, 1);
}

#[test]
fn rewrite_optimize_path_completes_and_output_decodes() {
    let module = module_of(&rewritable_abc(), "raw.abc");
    let opts = RewriteOptions {
        optimize: true,
        check: true,
    };
    // No assertion on any specific optimization effect — only that the
    // full lift → opt → lower → encode → check pipeline completes and the
    // output is a decodable .abc with the same methods.
    let out = rewrite::rewrite(&module, opts).expect("rewrite --opt");
    let (out_methods, _) = shape(&out.abc);
    assert_eq!(out_methods, 1);
}

#[test]
fn rewrite_accepts_hap_container_input() {
    let hap = common::hap("entry", &rewritable_abc());
    let modules = input::load_bytes(&hap, "demo.hap", ModuleSelection::Single).expect("load");
    assert_eq!(modules[0].name, "entry");
    let out = rewrite::rewrite(&modules[0], RewriteOptions::default()).expect("rewrite hap module");
    assert_eq!(out.name, "entry");
    assert!(
        out.provenance.contains("demo.hap"),
        "provenance: {}",
        out.provenance
    );
    let (out_methods, _) = shape(&out.abc);
    assert_eq!(out_methods, 1);
}

#[test]
fn rewrite_corrupt_input_is_a_tool_error() {
    let modules =
        input::load_bytes(b"not an abc at all", "bad.abc", ModuleSelection::Single).expect("load");
    let err = rewrite::rewrite(&modules[0], RewriteOptions::default()).unwrap_err();
    assert_eq!(
        err,
        CliError::Tool(err.to_string()),
        "decode failure is a tool error"
    );
    assert_eq!(err.exit_code(), 2);
}

#[test]
fn degenerate_zero_arg_shape_rewrites_cleanly() {
    // `common::tiny_abc()` declares `num_args = 0` — a shape no real
    // producer emits (es2abc always carries the three implicit frame
    // slots). It used to trip the lower's frame-initial-constant
    // attribution (no anchor → UnallocatedOperand); fixed in abcd-lower
    // (use-based attribution, see abcd-lower/tests/lower_frame_init_orphan.rs).
    // The CLI must now rewrite this shape successfully.
    let module = module_of(&common::tiny_abc(), "tiny.abc");
    let out = rewrite::rewrite(
        &module,
        RewriteOptions {
            optimize: false,
            check: true,
        },
    )
    .expect("the degenerate shape rewrites cleanly after the lower fix");
    assert_eq!(out.stats.methods, 1);
    assert_eq!(out.stats.lowered, 1);
}

#[test]
fn write_all_writes_one_abc_per_module() {
    // A two-module .app container exercises the per-module writer path.
    let app = common::app(&[
        ("phone.hap", common::hap("phone", &rewritable_abc())),
        ("lite.hap", common::hap("lite", &rewritable_abc())),
    ]);
    let modules = input::load_bytes(&app, "demo.app", ModuleSelection::All).expect("load");
    assert_eq!(modules.len(), 2);

    let dir = common::tempdir("rewrite-write-all");
    let opts = RewriteOptions {
        optimize: false,
        check: true,
    };
    let written = rewrite::write_all(&modules, &dir, opts).expect("write_all");
    assert_eq!(written.len(), 2);
    let mut names: Vec<&str> = written.iter().map(|(n, _, _)| n.as_str()).collect();
    names.sort_unstable();
    assert_eq!(names, ["lite", "phone"]);
    for (name, path, size) in &written {
        assert_eq!(path.file_name().unwrap(), format!("{name}.abc").as_str());
        let bytes = std::fs::read(path).expect("read written abc");
        assert_eq!(bytes.len(), *size);
        shape(&bytes); // every written file decodes
    }
}
