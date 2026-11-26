//! `abcd decompile` — bytecode → JavaScript via decode → lift → emit.
//!
//! Pipeline rules (design/decompile.md §1): the decompiler consumes the
//! lifted PRE-opt IR — no abcd-opt pass runs here, and the `inline` pass in
//! particular must never run before decompile.

use std::io::{BufWriter, Write as _};
use std::path::{Path, PathBuf};

use abcd_decompile::{
    DecompiledModule, EmitOptions, SplitDecompiledModule, decompile_module, decompile_module_split,
    decompile_module_split_each, decompile_module_to_writer,
};

use crate::CliError;
use crate::input::InputModule;

const IO_BUF_CAPACITY: usize = 256 * 1024;

struct CountingWriter<W> {
    inner: W,
    bytes: usize,
}

impl<W: std::io::Write> std::io::Write for CountingWriter<W> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let n = self.inner.write(buf)?;
        self.bytes += n;
        Ok(n)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.inner.flush()
    }
}

fn emit_counted<W: std::io::Write>(
    ir: &abcd_ir::Module,
    opts: &EmitOptions,
    out: W,
) -> std::io::Result<usize> {
    let mut writer = BufWriter::with_capacity(
        IO_BUF_CAPACITY,
        CountingWriter {
            inner: out,
            bytes: 0,
        },
    );
    decompile_module_to_writer(ir, opts, &mut writer)?;
    writer.flush()?;
    Ok(writer.get_ref().bytes)
}

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
    let ir = {
        let file = abcd_file::decode(&module.abc).map_err(|e| {
            CliError::Tool(format!(
                "failed to decode {} ({}): {e}",
                module.name, module.provenance
            ))
        })?;
        abcd_lift::lift_file(&file).map_err(|e| {
            CliError::Tool(format!(
                "failed to lift {} ({}): {e}",
                module.name, module.provenance
            ))
        })?
    };
    Ok(decompile_module(&ir, &opts.into()))
}

/// Stream one decompiled module directly to `out`, returning the number of
/// emitted bytes (`0` if `out` closes early with `BrokenPipe`).
pub fn decompile_to_writer<W: std::io::Write>(
    module: &InputModule,
    opts: DecompileOptions,
    out: W,
) -> Result<usize, CliError> {
    let ir = {
        let file = abcd_file::decode(&module.abc).map_err(|e| {
            CliError::Tool(format!(
                "failed to decode {} ({}): {e}",
                module.name, module.provenance
            ))
        })?;
        abcd_lift::lift_file(&file).map_err(|e| {
            CliError::Tool(format!(
                "failed to lift {} ({}): {e}",
                module.name, module.provenance
            ))
        })?
    };
    match emit_counted(&ir, &opts.into(), out) {
        Ok(n) => Ok(n),
        Err(e) if e.kind() == std::io::ErrorKind::BrokenPipe => Ok(0),
        Err(e) => Err(CliError::Tool(format!("failed writing to stdout: {e}"))),
    }
}

/// Stream one decompiled module to `path`, returning the number of emitted
/// bytes. Decodes and lifts `module` before creating or truncating `path` so
/// corrupt or unliftable inputs never leave an empty file on disk.
pub fn decompile_to_path(
    module: &InputModule,
    opts: DecompileOptions,
    path: &Path,
) -> Result<usize, CliError> {
    let ir = {
        let file = abcd_file::decode(&module.abc).map_err(|e| {
            CliError::Tool(format!(
                "failed to decode {} ({}): {e}",
                module.name, module.provenance
            ))
        })?;
        abcd_lift::lift_file(&file).map_err(|e| {
            CliError::Tool(format!(
                "failed to lift {} ({}): {e}",
                module.name, module.provenance
            ))
        })?
    };
    let out_file = std::fs::File::create(path)
        .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())))?;
    emit_counted(&ir, &opts.into(), out_file)
        .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())))
}

/// Decompile one module into a multi-file directory tree (`--split-modules`).
pub fn decompile_split(
    module: &InputModule,
    opts: DecompileOptions,
) -> Result<SplitDecompiledModule, CliError> {
    let ir = {
        let file = abcd_file::decode(&module.abc).map_err(|e| {
            CliError::Tool(format!(
                "failed to decode {} ({}): {e}",
                module.name, module.provenance
            ))
        })?;
        abcd_lift::lift_file(&file).map_err(|e| {
            CliError::Tool(format!(
                "failed to lift {} ({}): {e}",
                module.name, module.provenance
            ))
        })?
    };
    Ok(decompile_module_split(&ir, &opts.into()))
}

/// Write a split module tree under `out_dir`, enforcing relative-path containment.
pub fn write_split(
    module: &InputModule,
    out_dir: &Path,
    opts: DecompileOptions,
) -> Result<(usize, usize), CliError> {
    let ir = {
        let file = abcd_file::decode(&module.abc).map_err(|e| {
            CliError::Tool(format!(
                "failed to decode {} ({}): {e}",
                module.name, module.provenance
            ))
        })?;
        abcd_lift::lift_file(&file).map_err(|e| {
            CliError::Tool(format!(
                "failed to lift {} ({}): {e}",
                module.name, module.provenance
            ))
        })?
    };
    std::fs::create_dir_all(out_dir).map_err(|e| {
        CliError::Tool(format!(
            "cannot create output directory {}: {e}",
            out_dir.display()
        ))
    })?;
    let mut total_files = 0usize;
    let mut total_bytes = 0usize;
    decompile_module_split_each(&ir, &opts.into(), |sf| -> Result<(), CliError> {
        let dst = safe_join(out_dir, &sf.rel_path)?;
        if let Some(parent) = dst.parent() {
            std::fs::create_dir_all(parent).map_err(|e| {
                CliError::Tool(format!("cannot create directory {}: {e}", parent.display()))
            })?;
        }
        std::fs::write(&dst, &sf.text)
            .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", dst.display())))?;
        total_files += 1;
        total_bytes += sf.text.len();
        Ok(())
    })?;
    Ok((total_files, total_bytes))
}

/// Join a POSIX-style relative split-module path (`a/b/c.js`) onto `root`,
/// validating every segment with [`crate::input::is_safe_path_segment`] so
/// traversal segments, backslashes, trailing dots/spaces, and Windows reserved
/// device names are rejected identically on every host OS.
pub fn safe_join(root: &Path, rel: &str) -> Result<PathBuf, CliError> {
    if rel.is_empty() {
        return Err(CliError::Tool(format!(
            "refusing unsafe split output path {rel:?}"
        )));
    }
    let mut out = root.to_path_buf();
    for seg in rel.split('/') {
        if !crate::input::is_safe_path_segment(seg) {
            return Err(CliError::Tool(format!(
                "refusing unsafe split output path {rel:?}"
            )));
        }
        out.push(seg);
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
        let path = out_dir.join(format!("{}.js", m.name));
        let size = decompile_to_path(m, opts, &path)?;
        written.push((m.name.clone(), path, size));
    }
    Ok(written)
}
