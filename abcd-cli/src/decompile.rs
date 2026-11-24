//! `abcd decompile` — bytecode → JavaScript via decode → lift → emit.
//!
//! Pipeline rules (design/decompile.md §1): the decompiler consumes the
//! lifted PRE-opt IR — no abcd-opt pass runs here, and the `inline` pass in
//! particular must never run before decompile.

use std::path::{Component, Path, PathBuf};

use abcd_decompile::{
    DecompiledModule, EmitOptions, SplitDecompiledModule, decompile_module, decompile_module_split,
};

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
    /// `--arkui`: reconstruct OpenHarmony ArkUI `@Component struct` & `build()`.
    pub arkui: bool,
}

impl From<DecompileOptions> for EmitOptions {
    fn from(o: DecompileOptions) -> Self {
        EmitOptions {
            line_anchors: o.line_anchors,
            ts: o.ts,
            call_entry: o.call_entry,
            arkui: o.arkui,
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

/// Decompile one module into a multi-file directory tree (`--split-modules`).
pub fn decompile_split(
    module: &InputModule,
    opts: DecompileOptions,
) -> Result<SplitDecompiledModule, CliError> {
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
    Ok(decompile_module_split(&ir, &opts.into()))
}

/// Write a split module tree under `out_dir`, enforcing relative-path containment.
pub fn write_split(
    module: &InputModule,
    out_dir: &Path,
    opts: DecompileOptions,
) -> Result<(usize, usize), CliError> {
    let split = decompile_split(module, opts)?;
    std::fs::create_dir_all(out_dir).map_err(|e| {
        CliError::Tool(format!(
            "cannot create output directory {}: {e}",
            out_dir.display()
        ))
    })?;
    let mut total_bytes = 0usize;
    for sf in &split.files {
        let dst = safe_join(out_dir, &sf.rel_path)?;
        if let Some(parent) = dst.parent() {
            std::fs::create_dir_all(parent).map_err(|e| {
                CliError::Tool(format!("cannot create directory {}: {e}", parent.display()))
            })?;
        }
        std::fs::write(&dst, &sf.text)
            .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", dst.display())))?;
        total_bytes += sf.text.len();
    }
    Ok((split.files.len(), total_bytes))
}

fn safe_join(root: &Path, rel: &str) -> Result<PathBuf, CliError> {
    let p = Path::new(rel);
    let mut out = root.to_path_buf();
    for c in p.components() {
        match c {
            Component::Normal(seg) => out.push(seg),
            _ => {
                return Err(CliError::Tool(format!(
                    "refusing unsafe split output path {rel:?}"
                )));
            }
        }
    }
    Ok(out)
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
