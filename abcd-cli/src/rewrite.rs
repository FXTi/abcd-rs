//! `abcd rewrite` — rewrite `.abc` through the full IR pipeline:
//! `decode → lift → [opt] → lower → encode` (design/cli.md §2).
//!
//! A writer command: the emitted bytes are a new `.abc` file. `--check`
//! re-decodes the emitted bytes (a full structural decode — header, index
//! regions, and every method body's instruction stream) before they leave
//! the process, so a pipeline bug surfaces as a tool error (exit 2)
//! instead of a corrupt file on disk.
//!
//! Whole-file lowering delegates to [`abcd_lower::rewrite_file`]: the lifted
//! module is verified ([`abcd_ir::verify_module`]), optionally optimized, and
//! lowered back onto the decoded [`File`] with synced constant/literal pools,
//! IC slot sizing, and rebuilt per-method debug tables (`R3-H8`).

use std::path::{Path, PathBuf};

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

/// Rewrite one module through `decode → lift → [opt] → lower → encode`.
///
/// All-or-nothing: any decode/lift/lower/encode failure is a tool error
/// and no bytes leave the function (design/cli.md §2–§3: writer commands get a
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

    // Stage 4: lower the IR back onto `file` via `abcd_lower::rewrite_file`
    // (syncing constant/literal pools, IC slot counts, and method debug info).
    let (methods, input_instructions) = shape(&file);
    let before_body_tags: Vec<&'static str> = if opts.check {
        file.all_methods()
            .map(|(_, m)| body_state(&m.body))
            .collect()
    } else {
        Vec::new()
    };
    let lowered = ir.functions.iter().filter(|f| !f.blocks.is_empty()).count();

    let rewritten_file = abcd_lower::rewrite_file(&ir, &file, LowerOptions::default())
        .map_err(|e| CliError::Tool(format!("{}: lower failed: {e}", ctx())))?;
    drop(ir);
    drop(file);

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
        let (out_methods, out_instructions) = shape(&checked);
        if out_methods != methods {
            return Err(CliError::Tool(format!(
                "{}: --check failed: method count changed {methods} -> {out_methods}",
                ctx()
            )));
        }
        for (before_tag, (_, after)) in before_body_tags.into_iter().zip(checked.all_methods()) {
            let after_tag = body_state(&after.body);
            let ok = match before_tag {
                "no body" => after_tag == "no body",
                _ => after_tag == "body",
            };
            if !ok {
                return Err(CliError::Tool(format!(
                    "{}: --check failed: method body presence changed \
                     ({before_tag} -> {after_tag})",
                    ctx(),
                )));
            }
        }
        out_instructions
    } else {
        unchecked_output_instructions
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

#[cfg(test)]
mod tests {
    use super::*;

    fn body_with(bytecodes: Vec<abcd_isa::Bytecode>) -> abcd_file::MethodBody {
        abcd_file::MethodBody {
            num_vregs: 0,
            num_args: 0,
            bytecodes,
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
            abc: input_abc,
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
        assert!(!body.bytecodes.is_empty());
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
                (entry.index as usize) < body.bytecodes.len(),
                "line_table index {} out of bounds for {} instructions",
                entry.index,
                body.bytecodes.len()
            );
        }
        assert!(
            dbg.local_vars.is_empty(),
            "stale pre-rewrite local_vars must be cleared: {:?}",
            dbg.local_vars
        );
    }
}
