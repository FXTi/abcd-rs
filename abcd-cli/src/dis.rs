//! `abcd dis` — disassemble to pandasm `.pa` text.
//!
//! The emitter (`abcd_file::pandasm::emit_file`) is byte-identical to
//! upstream `ark_disasm`, enforced per-push by the corpus byte-diff gate
//! (`tests/file-isa/pandasm_dis.rs`, design/cli.md §2, design/decisions.md ADR-11). Output is raw
//! BYTES, not String: upstream prints string contents unescaped, so valid
//! output is not necessarily UTF-8.

use std::io::{BufWriter, Write as _};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use crate::input::InputModule;
use crate::{CliError, ExecContext};

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
    file: &abcd_file::File,
    source_name: &str,
    out: W,
) -> std::io::Result<usize> {
    let mut writer = BufWriter::with_capacity(
        IO_BUF_CAPACITY,
        CountingWriter {
            inner: out,
            bytes: 0,
        },
    );
    abcd_file::pandasm::emit_file_to_writer(file, source_name, &mut writer)?;
    writer.flush()?;
    Ok(writer.get_ref().bytes)
}

/// Disassemble one module to pandasm text bytes.
pub fn disassemble(module: &InputModule) -> Result<Vec<u8>, CliError> {
    let file = crate::decode_abc_arc(
        Arc::clone(&module.abc),
        &module.name,
        &module.provenance,
        ExecContext::default(),
    )?;
    Ok(abcd_file::pandasm::emit_file(
        &file,
        &source_name_of(&module.provenance),
    ))
}

/// Stream disassembled pandasm text of `module` directly to `out`, returning
/// the number of emitted bytes (`0` if `out` closes early with `BrokenPipe`).
pub fn disassemble_to_writer<W: std::io::Write>(
    module: &InputModule,
    out: W,
) -> Result<usize, CliError> {
    disassemble_arc_to_writer(
        Arc::clone(&module.abc),
        &module.name,
        &module.provenance,
        out,
        ExecContext::default(),
    )
}

pub(crate) fn disassemble_owned_to_writer<W: std::io::Write>(
    module: InputModule,
    out: W,
    ctx: ExecContext,
) -> Result<usize, CliError> {
    let InputModule {
        name,
        abc,
        provenance,
        ..
    } = module;
    disassemble_arc_to_writer(abc, &name, &provenance, out, ctx)
}

fn disassemble_arc_to_writer<W: std::io::Write>(
    abc: Arc<[u8]>,
    name: &str,
    provenance: &str,
    out: W,
    ctx: ExecContext,
) -> Result<usize, CliError> {
    let file = crate::decode_abc_arc(abc, name, provenance, ctx)?;
    let t_dis = ctx.timings.then(Instant::now);
    let res = match emit_counted(&file, &source_name_of(provenance), out) {
        Ok(n) => Ok(n),
        Err(e) if e.kind() == std::io::ErrorKind::BrokenPipe => Ok(0),
        Err(e) => Err(CliError::Tool(format!("failed writing to stdout: {e}"))),
    };
    if let Some(start) = t_dis {
        crate::log_timing(true, name, "dis", start.elapsed());
    }
    res
}

/// Stream disassembled pandasm text of `module` to `path`, returning the
/// number of emitted bytes. Decodes `module` before creating or truncating
/// `path` so corrupt inputs never leave an empty file on disk.
pub fn disassemble_to_path(module: &InputModule, path: &Path) -> Result<usize, CliError> {
    disassemble_arc_to_path(
        Arc::clone(&module.abc),
        &module.name,
        &module.provenance,
        path,
        ExecContext::default(),
    )
}

pub(crate) fn disassemble_owned_to_path(
    module: InputModule,
    path: &Path,
    ctx: ExecContext,
) -> Result<usize, CliError> {
    let InputModule {
        name,
        abc,
        provenance,
        ..
    } = module;
    disassemble_arc_to_path(abc, &name, &provenance, path, ctx)
}

fn disassemble_arc_to_path(
    abc: Arc<[u8]>,
    name: &str,
    provenance: &str,
    path: &Path,
    ctx: ExecContext,
) -> Result<usize, CliError> {
    let file = crate::decode_abc_arc(abc, name, provenance, ctx)?;
    let out_file = std::fs::File::create(path)
        .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())))?;
    let t_dis = ctx.timings.then(Instant::now);
    let size = emit_counted(&file, &source_name_of(provenance), out_file)
        .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())))?;
    if let Some(start) = t_dis {
        crate::log_timing(true, name, "dis", start.elapsed());
    }
    Ok(size)
}

/// The name printed in the `# source binary:` header, matching upstream
/// ark_disasm's basename convention: the input file's basename for a bare
/// `.abc`, the innermost entry's basename for container-extracted modules
/// (`app.app::entry.hap::ets/modules.abc` → `modules.abc`).
fn source_name_of(provenance: &str) -> String {
    let last = provenance.rsplit("::").next().unwrap_or(provenance);
    last.rsplit(['/', '\\']).next().unwrap_or(last).to_string()
}

/// Write one `<module>.pa` per module into `out_dir`.
pub fn write_all(
    modules: &[InputModule],
    out_dir: &Path,
) -> Result<Vec<(String, PathBuf, usize)>, CliError> {
    std::fs::create_dir_all(out_dir).map_err(|e| {
        CliError::Tool(format!(
            "cannot create output directory {}: {e}",
            out_dir.display()
        ))
    })?;
    let mut written = Vec::with_capacity(modules.len());
    for m in modules {
        let path = out_dir.join(format!("{}.pa", m.name));
        let size = disassemble_to_path(m, &path)?;
        written.push((m.name.clone(), path, size));
    }
    Ok(written)
}

pub(crate) fn write_all_owned(
    modules: Vec<InputModule>,
    out_dir: &Path,
    ctx: ExecContext,
) -> Result<Vec<(String, PathBuf, usize)>, CliError> {
    std::fs::create_dir_all(out_dir).map_err(|e| {
        CliError::Tool(format!(
            "cannot create output directory {}: {e}",
            out_dir.display()
        ))
    })?;
    let mut written = Vec::with_capacity(modules.len());
    for m in modules {
        let mod_name = m.name.clone();
        let path = out_dir.join(format!("{mod_name}.pa"));
        let size = disassemble_owned_to_path(m, &path, ctx)?;
        written.push((mod_name, path, size));
    }
    Ok(written)
}

/// Print raw bytes to stdout (the text may not be UTF-8).
pub fn print_raw(bytes: &[u8]) -> Result<(), CliError> {
    crate::write_stdout_bytes(bytes)
}
