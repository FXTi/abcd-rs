//! `abcd decompile` — bytecode → JavaScript via decode → lift → emit.
//!
//! Pipeline rules (design/decompile.md §3.2): the decompiler consumes the
//! lifted PRE-opt IR — no abcd-opt pass runs here, and the `inline` pass in
//! particular must never run before decompile.

use std::path::Path;

use abcd_decompile::{DecompiledModule, EmitOptions, decompile_module};

use crate::CliError;
use crate::input::InputModule;

/// CLI-facing emission options; mapped 1:1 onto [`EmitOptions`].
#[derive(Clone, Copy, Debug, Default)]
pub struct DecompileOptions {
    /// `--ts`: TypeScript annotations from IR signature metadata.
    pub ts: bool,
    /// `--line-anchors`: `// line N` anchors before located statements.
    pub line_anchors: bool,
    /// `--call-entry`: append the `func_main_0.call(this);` entry call.
    pub call_entry: bool,
}

impl From<DecompileOptions> for EmitOptions {
    fn from(o: DecompileOptions) -> Self {
        EmitOptions {
            line_anchors: o.line_anchors,
            ts: o.ts,
            call_entry: o.call_entry,
        }
    }
}

/// Decompile one module to JS text.
pub fn decompile(
    module: &InputModule,
    opts: DecompileOptions,
) -> Result<DecompiledModule, CliError> {
    let file = abcd_file::decode(&module.abc).map_err(|e| {
        CliError::Tool(format!(
            "failed to decode {} ({}): {e}",
            module.name, module.provenance
        ))
    })?;
    let ir = abcd_lift::lift_file(&file).map_err(|e| {
        CliError::Tool(format!(
            "failed to lift {} ({}): {e}",
            module.name, module.provenance
        ))
    })?;
    Ok(decompile_module(&ir, &opts.into()))
}

/// Write one decompiled module per input module into `out_dir` as
/// `<module-name>.js`, returning the written paths.
pub fn write_all(
    modules: &[InputModule],
    out_dir: &Path,
    opts: DecompileOptions,
) -> Result<Vec<(String, std::path::PathBuf, usize)>, CliError> {
    std::fs::create_dir_all(out_dir).map_err(|e| {
        CliError::Tool(format!(
            "cannot create output directory {}: {e}",
            out_dir.display()
        ))
    })?;
    let mut written = Vec::with_capacity(modules.len());
    for m in modules {
        let js = decompile(m, opts)?.text;
        let path = out_dir.join(format!("{}.js", m.name));
        std::fs::write(&path, &js)
            .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())))?;
        written.push((m.name.clone(), path, js.len()));
    }
    Ok(written)
}
