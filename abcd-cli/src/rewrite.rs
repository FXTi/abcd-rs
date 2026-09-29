//! `abcd rewrite` — rewrite `.abc` through the full IR pipeline:
//! decode → lift → [opt] → lower → encode (design/cli-plan.md §2, §4 P2).
//!
//! A writer command: the emitted bytes are a new `.abc` file. `--check`
//! re-decodes the emitted bytes (a full structural decode — header, index
//! regions, and every method body's instruction stream) before they leave
//! the process, so a pipeline bug surfaces as a tool error (exit 2)
//! instead of a corrupt file on disk.
//!
//! The whole-file lowering pattern mirrors the corpus pipeline
//! (tests/lift-lower/rewrite_pipeline.rs): the lifted module is verified
//! (`abcd_ir::verify_module`), every function is lowered individually, and
//! the resulting bodies are spliced into a clone of the decoded file —
//! function `i` is the `i`-th method in `File::classes` iteration order
//! (the lift's pass-1 reservation order), so a per-method cursor joins the
//! two tables.

use std::path::{Path, PathBuf};

use abcd_file::File;
use abcd_ir::verify_module;
use abcd_lower::{LowerOptions, lower_function_with_options, to_method_body};

use crate::CliError;
use crate::input::InputModule;

/// Options for [`rewrite`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RewriteOptions {
    /// Run abcd-opt's optimization pipeline between lift and lower.
    pub optimize: bool,
    /// Re-decode the emitted bytes (full structural + per-method bytecode
    /// decode) before returning them; a failure is a tool error and the
    /// bytes are dropped, never written.
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
            instructions += body.bytecodes.len();
        }
    }
    (methods, instructions)
}

/// Rewrite one module through decode → lift → [opt] → lower → encode.
///
/// All-or-nothing: any decode/lift/lower/encode failure is a tool error
/// and no bytes leave the function (cli-plan.md §4: writer commands get a
/// round-trip self-check and never emit partial output).
pub fn rewrite(module: &InputModule, opts: RewriteOptions) -> Result<RewrittenModule, CliError> {
    let ctx = || format!("rewrite {} ({})", module.name, module.provenance);

    // Stage 1: decode the input bytes.
    let file = abcd_file::decode(&module.abc)
        .map_err(|e| CliError::Tool(format!("{}: decode failed: {e}", ctx())))?;

    // Stage 2: lift the whole file to the IR, then verify it (same order
    // as the corpus pipeline's front_end: verify catches structural IR
    // bugs with precise errors before the lower trips over them).
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

    // Stage 3 (optional): optimize.
    let optimized_changed = opts.optimize && abcd_opt::optimize_module(&mut ir);

    // Stage 4: lower every function back to a MethodBody and splice the
    // bodies into a clone of the decoded file.
    //
    // `FuncId`s are collected from `ClassData::methods` (never constructed
    // by path) and validated to cover the function table contiguously —
    // the lift's pass-1 reservation (classes in `File::classes` order,
    // methods in declaration order) makes them exactly
    // `0..functions.len()`, which is the order the splice cursor below
    // relies on.
    let mut func_ids: Vec<_> = ir
        .classes
        .iter()
        .flat_map(|class| class.methods.iter().copied())
        .collect();
    func_ids.sort_unstable_by_key(|id| id.index());
    if func_ids.len() != ir.functions.len()
        || func_ids.iter().enumerate().any(|(i, id)| id.index() != i)
    {
        return Err(CliError::Tool(format!(
            "{}: lift produced {} functions but class tables reference {}; \
             cannot map lowered bodies back to file methods",
            ctx(),
            ir.functions.len(),
            func_ids.len()
        )));
    }

    // LowerOptions field doc: `prune_unused_frame_init_consts` must be set
    // when lowering abcd-opt's output (the optimizer can delete the last
    // use of a frame-initial constant, and the v0.2 seed is
    // instruction-less, so the lower must skip the materialization); it
    // must stay clear for lift output, which v0.1-lift emits verbatim.
    let lower_options = LowerOptions {
        prune_unused_frame_init_consts: opts.optimize,
    };

    let mut bodies = Vec::with_capacity(func_ids.len());
    let mut lowered = 0;
    for &func_id in &func_ids {
        let func = ir.func(func_id).expect("coverage validated above");
        // Bodyless functions (external/native declarations) keep their
        // `None` body; everything else lowers to a fresh MethodBody.
        if func.blocks.is_empty() {
            bodies.push(None);
            continue;
        }
        let name = ir.sym.resolve(func.name).unwrap_or("?");
        let layout = lower_function_with_options(&ir, func_id, lower_options)
            .map_err(|e| CliError::Tool(format!("{}: lower of {name} failed: {e}", ctx())))?;
        let body = to_method_body(&ir, func_id, &layout, &file)
            .map_err(|e| CliError::Tool(format!("{}: relocation of {name} failed: {e}", ctx())))?;
        bodies.push(Some(body));
        lowered += 1;
    }

    let mut rebuilt = file.clone();
    let mut cursor = bodies.into_iter();
    for class in rebuilt.classes.values_mut() {
        for method in &mut class.methods {
            let body = cursor.next().expect("one slot per method");
            if method.body.is_some() {
                method.body = Some(body.expect("a lowered body for every method that had one"));
            }
        }
    }
    debug_assert!(cursor.next().is_none());

    // Stage 5: encode the rebuilt file.
    let abc = abcd_file::encode(&rebuilt)
        .map_err(|e| CliError::Tool(format!("{}: encode failed: {e}", ctx())))?;

    let (methods, input_instructions) = shape(&file);

    // Stage 6 (optional): `--check` self-check. `abcd_file::decode` is a
    // full structural decode — header, index regions, and every method
    // body's instruction stream (each body comes back as decoded
    // `Vec<Bytecode>`; a corrupt instruction fails the decode). The body
    // pattern is then compared against the input: every method that had a
    // body must still have one with a non-empty instruction stream. Any
    // mismatch is a tool error and the bad bytes are dropped — the caller
    // never sees them.
    let output_instructions = if opts.check {
        let checked = abcd_file::decode(&abc).map_err(|e| {
            CliError::Tool(format!(
                "{}: --check failed: emitted bytes do not re-decode: {e}",
                ctx()
            ))
        })?;
        let (out_methods, _) = shape(&checked);
        if out_methods != methods {
            return Err(CliError::Tool(format!(
                "{}: --check failed: method count changed {methods} -> {out_methods}",
                ctx()
            )));
        }
        for ((_, before), (_, after)) in file.all_methods().zip(checked.all_methods()) {
            match (&before.body, &after.body) {
                (Some(_), Some(after_body)) if !after_body.bytecodes.is_empty() => {}
                (None, None) => {}
                (before_body, after_body) => {
                    return Err(CliError::Tool(format!(
                        "{}: --check failed: method body presence changed \
                         ({} -> {})",
                        ctx(),
                        body_state(before_body),
                        body_state(after_body),
                    )));
                }
            }
        }
        shape(&checked).1
    } else {
        shape(&rebuilt).1
    };

    Ok(RewrittenModule {
        name: module.name.clone(),
        abc,
        provenance: module.provenance.clone(),
        stats: RewriteStats {
            methods,
            lowered,
            input_instructions,
            output_instructions,
            optimized_changed,
        },
    })
}

/// Short body-state tag for `--check` diagnostics.
fn body_state(body: &Option<abcd_file::MethodBody>) -> &'static str {
    match body {
        Some(b) if b.bytecodes.is_empty() => "empty body",
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
