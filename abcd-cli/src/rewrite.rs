//! `abcd rewrite` — rewrite `.abc` through the full IR pipeline:
//! `decode → lift → [opt] → lower → encode` (design/cli.md §2).
//!
//! A writer command: the emitted bytes are a new `.abc` file. `--check`
//! re-decodes the emitted bytes (a full structural decode — header, index
//! regions, and every method body's instruction stream), re-lifts them to IR,
//! and runs [`abcd_ir::verify_module`] before they leave the process, so a
//! pipeline bug surfaces as a tool error (exit 2) instead of a corrupt file on
//! disk.
//!
//! Whole-file lowering delegates to [`abcd_lower::rewrite_file_owned`]: the lifted
//! module is verified ([`abcd_ir::verify_module`]), optionally optimized, and
//! lowered back onto the decoded [`File`] by value with synced constant/literal
//! pools, IC slot sizing, and rebuilt per-method debug tables (`R3-H8`).

use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use abcd_file::File;
use abcd_ir::verify_module;
use abcd_lower::LowerOptions;

use crate::CliError;
use crate::input::InputModule;

/// Options for [`rewrite`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RewriteOptions {
    /// Run abcd-opt's optimization pipeline between lift and lower.
    pub optimize: bool,
    /// Re-decode, re-lift, and re-verify the emitted bytes before returning
    /// them; a failure is a tool error and the bytes are dropped, never
    /// written.
    pub check: bool,
}

/// Rewrite statistics. Every field is measured by the pipeline itself —
/// nothing here is estimated or assumed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RewriteStats {
    /// Methods in the input file (bodyless external declarations included).
    pub methods: usize,
    /// Functions that carried a body and were lowered back to bytecode.
    pub lowered: usize,
    /// Total decoded instructions across all input method bodies.
    pub input_instructions: usize,
    /// Total decoded instructions across all output method bodies (measured
    /// on the re-decoded output under `--check`, on the rebuilt in-memory
    /// file otherwise).
    pub output_instructions: usize,
    /// Whether abcd-opt reported a change (`false` when `optimize` is off).
    pub optimized_changed: bool,
}

/// One rewritten module: the new `.abc` bytes plus provenance and stats.
#[derive(Clone, Debug)]
pub struct RewrittenModule {
    /// Module name (from the input layer).
    pub name: String,
    /// The rewritten `.abc` bytes.
    pub abc: Vec<u8>,
    /// Human-readable provenance chain (from the input layer).
    pub provenance: String,
    /// Pipeline statistics.
    pub stats: RewriteStats,
}

/// (method count, total instruction count) across all method bodies.
fn shape(file: &File) -> (usize, usize) {
    let mut methods = 0;
    let mut instructions = 0;
    for (_class, method) in file.all_methods() {
        methods += 1;
        if let Some(body) = &method.body {
            instructions += body.insn_count();
        }
    }
    (methods, instructions)
}

/// Rewrite one module through `decode → lift → [opt] → lower → encode`.
///
/// All-or-nothing: any decode/lift/lower/encode failure is a tool error
/// and no bytes leave the function (design/cli.md §2–§3: writer commands get a
/// round-trip self-check and never emit partial output).
pub fn rewrite(module: &InputModule, opts: RewriteOptions) -> Result<RewrittenModule, CliError> {
    rewrite_core(
        module.name.clone(),
        module.provenance.clone(),
        Arc::clone(&module.abc),
        opts,
        false,
    )
}

pub(crate) fn rewrite_owned(
    module: InputModule,
    opts: RewriteOptions,
    timings: bool,
) -> Result<RewrittenModule, CliError> {
    let InputModule {
        name,
        abc,
        provenance,
        ..
    } = module;
    rewrite_core(name, provenance, abc, opts, timings)
}

fn rewrite_core(
    name: String,
    provenance: String,
    abc_in: Arc<[u8]>,
    opts: RewriteOptions,
    timings: bool,
) -> Result<RewrittenModule, CliError> {
    let ctx = || format!("rewrite {name} ({provenance})");

    // Stage 1: lazily decode the input bytes (`MethodCode::Span`).
    let t_dec = timings.then(Instant::now);
    let file = abcd_file::decode_lazy(abc_in)
        .map_err(|e| CliError::Tool(format!("{}: decode failed: {e}", ctx())))?;
    if let Some(start) = t_dec {
        crate::log_timing(true, &name, "decode", start.elapsed());
    }

    // Stage 2: lift the whole file to the IR, then verify it (same order
    // as the corpus pipeline's front_end: verify catches structural IR
    // bugs with precise errors before the lower trips over them).
    let t_lift = timings.then(Instant::now);
    let mut ir = abcd_lift::lift_file(&file)
        .map_err(|e| CliError::Tool(format!("{}: lift failed: {e}", ctx())))?;
    let report = verify_module(&ir);
    if !report.is_ok() {
        return Err(CliError::Tool(format!(
            "{}: IR verify failed: {:?}",
            ctx(),
            report.errors
        )));
    }
    if let Some(start) = t_lift {
        crate::log_timing(true, &name, "lift", start.elapsed());
    }

    // Stage 3 (optional): optimize.
    let t_rw = timings.then(Instant::now);
    let optimized_changed = opts.optimize && abcd_opt::optimize_module(&mut ir);

    // Stage 4: lower the IR back onto `file` by value via
    // `abcd_lower::rewrite_file_owned` (freeing replaced MethodSpan bodies
    // immediately without cloning `file`).
    let (methods, input_instructions) = shape(&file);
    let before_body_tags: Vec<&'static str> = if opts.check {
        file.all_methods()
            .map(|(_, m)| body_state(&m.body))
            .collect()
    } else {
        Vec::new()
    };
    let lowered = ir.functions.iter().filter(|f| !f.blocks.is_empty()).count();

    let rewritten_file = abcd_lower::rewrite_file_owned(&ir, file, LowerOptions::default())
        .map_err(|e| CliError::Tool(format!("{}: lower failed: {e}", ctx())))?;
    drop(ir);

    let unchecked_output_instructions = if opts.check {
        0
    } else {
        shape(&rewritten_file).1
    };

    // Stage 5: encode the rewritten file, then drop the in-memory File before
    // `--check` re-decodes `abc` so two `File` models never coexist in RAM.
    let abc = abcd_file::encode(&rewritten_file)
        .map_err(|e| CliError::Tool(format!("{}: encode failed: {e}", ctx())))?;
    drop(rewritten_file);

    // Stage 6 (optional): `--check` self-check (design/cli.md §2).
    // Re-decodes `abc` (header, index regions, and every method body's
    // instruction stream), verifies method-count and body-presence parity,
    // re-lifts the decoded file to SSA IR, and verifies the re-lifted IR.
    // Any failure is a tool error (exit 2) and the bad bytes are dropped.
    let output_instructions = if opts.check {
        check_emitted(&ctx, &abc, methods, &before_body_tags)?
    } else {
        unchecked_output_instructions
    };
    if let Some(start) = t_rw {
        crate::log_timing(true, &name, "rewrite", start.elapsed());
    }

    Ok(RewrittenModule {
        name,
        abc,
        provenance,
        stats: RewriteStats {
            methods,
            lowered,
            input_instructions,
            output_instructions,
            optimized_changed,
        },
    })
}

/// Run the `--check` readback pipeline (`decode_lazy → parity → lift_file → verify_module`)
/// over emitted `.abc` bytes, returning the decoded instruction count on success.
fn check_emitted(
    ctx: &dyn Fn() -> String,
    abc: &[u8],
    expected_methods: usize,
    before_body_tags: &[&'static str],
) -> Result<usize, CliError> {
    let redecoded = abcd_file::decode_lazy(Arc::from(abc)).map_err(|e| {
        CliError::Tool(format!(
            "{}: --check: emitted bytes do not re-decode: {e}",
            ctx()
        ))
    })?;
    let (out_methods, out_instructions) = shape(&redecoded);
    if out_methods != expected_methods {
        return Err(CliError::Tool(format!(
            "{}: --check: method count changed {expected_methods} -> {out_methods}",
            ctx()
        )));
    }
    for (&before_tag, (_, after)) in before_body_tags.iter().zip(redecoded.all_methods()) {
        let after_tag = body_state(&after.body);
        if before_tag != after_tag {
            return Err(CliError::Tool(format!(
                "{}: --check: method body presence changed ({before_tag} -> {after_tag})",
                ctx(),
            )));
        }
    }
    let relifted = abcd_lift::lift_file(&redecoded).map_err(|e| {
        CliError::Tool(format!(
            "{}: --check: emitted bytes failed to re-lift: {e}",
            ctx()
        ))
    })?;
    drop(redecoded);
    let verify_report = verify_module(&relifted);
    if !verify_report.is_ok() {
        return Err(CliError::Tool(format!(
            "{}: --check: re-lifted IR verify failed: {:?}",
            ctx(),
            verify_report.errors
        )));
    }
    Ok(out_instructions)
}

/// Short body-state tag for `--check` diagnostics.
fn body_state(body: &Option<abcd_file::MethodBody>) -> &'static str {
    match body {
        Some(b) if b.insn_count() == 0 => "empty body",
        Some(_) => "body",
        None => "no body",
    }
}

/// Rewrite every module and write one `<name>.abc` per module into
/// `out_dir` (mirrors `dis::write_all`).
pub fn write_all(
    modules: &[InputModule],
    out_dir: &Path,
    opts: RewriteOptions,
) -> Result<Vec<(String, PathBuf, usize)>, CliError> {
    std::fs::create_dir_all(out_dir).map_err(|e| {
        CliError::Tool(format!(
            "cannot create output directory {}: {e}",
            out_dir.display()
        ))
    })?;
    let mut written = Vec::with_capacity(modules.len());
    for m in modules {
        // `rewrite` is all-or-nothing and `--check` (when set) runs before
        // anything is written, so a bad module aborts the batch rather
        // than leaving a corrupt file behind.
        let out = rewrite(m, opts)?;
        let path = out_dir.join(format!("{}.abc", m.name));
        std::fs::write(&path, &out.abc)
            .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())))?;
        written.push((m.name.clone(), path, out.abc.len()));
    }
    Ok(written)
}

pub(crate) fn write_all_owned(
    modules: Vec<InputModule>,
    out_dir: &Path,
    opts: RewriteOptions,
    timings: bool,
) -> Result<Vec<(String, PathBuf, usize)>, CliError> {
    std::fs::create_dir_all(out_dir).map_err(|e| {
        CliError::Tool(format!(
            "cannot create output directory {}: {e}",
            out_dir.display()
        ))
    })?;
    let mut written = Vec::with_capacity(modules.len());
    for m in modules {
        let out = rewrite_owned(m, opts, timings)?;
        let path = out_dir.join(format!("{}.abc", out.name));
        std::fs::write(&path, &out.abc)
            .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())))?;
        let size = out.abc.len();
        written.push((out.name, path, size));
    }
    Ok(written)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn body_with(bytecodes: Vec<abcd_isa::Bytecode>) -> abcd_file::MethodBody {
        abcd_file::MethodBody {
            num_vregs: 0,
            num_args: 0,
            code: bytecodes.into(),
            entities: Default::default(),
            try_blocks: Vec::new(),
            ic_size: None,
        }
    }

    #[test]
    fn body_state_tags_each_shape() {
        // `body_state` feeds the `--check` body-presence-mismatch
        // diagnostic, which only fires on a pipeline bug (unreachable
        // end-to-end without fault injection); the tag mapping itself is
        // pinned here.
        assert_eq!(body_state(&None), "no body");
        assert_eq!(body_state(&Some(body_with(Vec::new()))), "empty body");
        assert_eq!(
            body_state(&Some(body_with(vec![abcd_isa::Bytecode::Returnundefined]))),
            "body"
        );
    }

    #[test]
    fn rewrite_opt_rebuilds_line_table_in_bounds_and_clears_stale_local_vars() {
        use abcd_file::{
            AccessFlags, Builder, LineEntry, LocalVarInfo, MethodDebugInfo, SourceLang, Type,
        };
        use abcd_isa::{Bytecode, Imm, Reg};

        // 5-instruction constant-foldable body (`1 + 2` -> `3`), so `--opt`
        // shrinks `body.bytecodes` and any un-rebuilt `line_table` index 4 or
        // `local_vars` range `[1, 4]` would point past the rewritten stream.
        let mut b = Builder::new();
        b.set_api(12, "");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let proto = b.create_proto(Type::Void, &[]);
        let (code, _offsets) = abcd_isa::encode(&[
            Bytecode::Ldai(Imm(1)),         // 0: acc = 1
            Bytecode::Sta(Reg(0)),          // 1: v0 = 1
            Bytecode::Ldai(Imm(2)),         // 2: acc = 2
            Bytecode::Add2(Imm(0), Reg(0)), // 3: acc = 2 + v0
            Bytecode::Return,               // 4: return acc
        ])
        .unwrap();
        b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 4, 3);
        b.deduplicate();
        let seed_abc = b.finalize().expect("seed foldable abc must finalize");

        let mut file = abcd_file::decode(&seed_abc).expect("decode seed abc");
        let src = file.strings.get_or_intern("main.js");
        let var_name = file.strings.get_or_intern("tmp");
        let ty = file.strings.get_or_intern("any");
        for class in file.classes.values_mut() {
            for method in &mut class.methods {
                method.debug = Some(MethodDebugInfo {
                    source_file: Some(src),
                    source_code: None,
                    line_table: vec![
                        LineEntry { index: 0, line: 10 },
                        LineEntry { index: 4, line: 14 },
                    ],
                    column_table: Vec::new(),
                    local_vars: vec![LocalVarInfo {
                        name: var_name,
                        type_name: ty,
                        type_signature: ty,
                        reg_number: 0,
                        start: 1,
                        end: 4,
                    }],
                    params: Vec::new(),
                });
            }
        }
        let input_abc = abcd_file::encode(&file).expect("encode input abc with debug");
        let check_in = abcd_file::decode(&input_abc).expect("re-decode input abc");
        let (_, in_method) = check_in.all_methods().next().expect("one input method");
        let in_dbg = in_method.debug.as_ref().expect("input carries debug info");
        assert!(!in_dbg.line_table.is_empty());
        assert_eq!(in_dbg.local_vars.len(), 1);

        let module = InputModule {
            name: "dbg".to_string(),
            abc: Arc::from(input_abc),
            module_json: None,
            provenance: "dbg.abc".to_string(),
        };
        let out = rewrite(
            &module,
            RewriteOptions {
                optimize: true,
                check: true,
            },
        )
        .expect("rewrite --opt --check must succeed");
        assert!(out.stats.optimized_changed);

        let out_file = abcd_file::decode(&out.abc).expect("re-decode rewritten abc");
        let (_, out_method) = out_file.all_methods().next().expect("one output method");
        let body = out_method.body.as_ref().expect("output method has body");
        assert!(body.insn_count() > 0);
        let dbg = out_method
            .debug
            .as_ref()
            .expect("output method retains rebuilt debug info");
        assert!(
            !dbg.line_table.is_empty(),
            "rebuilt line_table must preserve mapped source lines"
        );
        for entry in &dbg.line_table {
            assert!(
                (entry.index as usize) < body.insn_count(),
                "line_table index {} out of bounds for {} instructions",
                entry.index,
                body.insn_count()
            );
        }
        assert!(
            dbg.local_vars.is_empty(),
            "stale pre-rewrite local_vars must be cleared: {:?}",
            dbg.local_vars
        );
    }

    #[test]
    fn check_emitted_rejects_unliftable_or_corrupt_bytes_with_tool_error() {
        use abcd_file::{AccessFlags, Builder, Type};
        use abcd_isa::{Bytecode, Label};

        let ctx = || "rewrite probe (probe.abc)".to_string();

        // Corrupt bytes fail the re-decode step of `--check`.
        let err = check_emitted(&ctx, b"not an abc", 1, &["body"]).unwrap_err();
        assert_eq!(err.exit_code(), 2);
        assert!(err.to_string().contains("--check:"), "{err}");

        // Valid `.abc` carrying `jeqnull` decodes and passes method/body
        // parity, then fails `abcd_lift::lift_file` inside `--check` (`ADR-07`).
        let mut b = Builder::new();
        b.set_api(12, "");
        let cls = b.add_global_class();
        let proto = b.create_proto(Type::Void, &[]);
        let (code, _offsets) =
            abcd_isa::encode(&[Bytecode::Jeqnull(Label(0)), Bytecode::Returnundefined]).unwrap();
        b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 1, 0);
        b.deduplicate();
        let unliftable_abc = b.finalize().unwrap();

        let err = check_emitted(&ctx, &unliftable_abc, 1, &["body"]).unwrap_err();
        assert_eq!(err.exit_code(), 2);
        let msg = err.to_string();
        assert!(msg.contains("--check:"), "{msg}");
        assert!(msg.contains("re-lift"), "{msg}");
        assert!(msg.contains("jeqnull"), "{msg}");

        // Method-count and body-presence parity mismatches also report `--check:` tool errors.
        let err_count = check_emitted(&ctx, &unliftable_abc, 2, &["body", "body"]).unwrap_err();
        assert_eq!(err_count.exit_code(), 2);
        assert!(err_count.to_string().contains("--check:"), "{err_count}");

        let err_body = check_emitted(&ctx, &unliftable_abc, 1, &["no body"]).unwrap_err();
        assert_eq!(err_body.exit_code(), 2);
        assert!(err_body.to_string().contains("--check:"), "{err_body}");
    }

    #[test]
    fn check_emitted_enforces_exact_body_state_parity() {
        use abcd_file::{AccessFlags, Builder, Type};
        use abcd_isa::Bytecode;

        let mut b = Builder::new();
        b.set_api(12, "");
        let cls = b.add_global_class();
        let proto = b.create_proto(Type::Void, &[]);
        let (code, _) = abcd_isa::encode(&[Bytecode::Returnundefined]).unwrap();
        b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 1, 3);
        b.deduplicate();
        let body_abc = b.finalize().unwrap();

        let mut b2 = Builder::new();
        b2.set_api(12, "");
        let cls2 = b2.add_global_class();
        let proto2 = b2.create_proto(Type::Void, &[]);
        b2.class_add_method(cls2, "bodyless", proto2, AccessFlags::STATIC, &[], 0, 0);
        b2.deduplicate();
        let no_body_abc = b2.finalize().unwrap();

        let ctx = || "rewrite parity (parity.abc)".to_string();
        let insns =
            check_emitted(&ctx, &body_abc, 1, &["body"]).expect("matching body parity succeeds");
        assert_eq!(insns, 1);

        // Exact 3-way tag equality: `"empty body"` must never alias `"body"` or `"no body"`.
        let err_empty_to_body = check_emitted(&ctx, &body_abc, 1, &["empty body"]).unwrap_err();
        assert!(
            err_empty_to_body.to_string().contains("empty body -> body"),
            "{err_empty_to_body}"
        );
        let err_empty_to_none = check_emitted(&ctx, &no_body_abc, 1, &["empty body"]).unwrap_err();
        assert!(
            err_empty_to_none
                .to_string()
                .contains("empty body -> no body"),
            "{err_empty_to_none}"
        );
        // Matching `"no body"` passes parity and reaches `lift_file`.
        let err_relift = check_emitted(&ctx, &no_body_abc, 1, &["no body"]).unwrap_err();
        assert!(
            err_relift.to_string().contains("failed to re-lift"),
            "{err_relift}"
        );
    }
}
