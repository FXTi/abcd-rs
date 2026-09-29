//! `abcd dis` — disassemble to pandasm `.pa` text.
//!
//! The emitter (`abcd_file::pandasm::emit_file`) is byte-identical to
//! upstream `ark_disasm`, enforced per-push by the corpus byte-diff gate
//! (`tests/file-isa/pandasm_dis.rs`, cli-plan.md §4.1). Output is raw
//! BYTES, not String: upstream prints string contents unescaped, so valid
//! output is not necessarily UTF-8.

use std::io::Write as _;
use std::path::{Path, PathBuf};

use crate::CliError;
use crate::input::InputModule;

/// Disassemble one module to pandasm text bytes.
pub fn disassemble(module: &InputModule) -> Result<Vec<u8>, CliError> {
    let file = abcd_file::decode(&module.abc).map_err(|e| {
        CliError::Tool(format!(
            "failed to decode {} ({}): {e}",
            module.name, module.provenance
        ))
    })?;
    Ok(abcd_file::pandasm::emit_file(&file, &source_name(module)))
}

/// The name printed in the `# source binary:` header, matching upstream
/// ark_disasm's basename convention: the input file's basename for a bare
/// `.abc`, the innermost entry's basename for container-extracted modules
/// (`app.app::entry.hap::ets/modules.abc` → `modules.abc`).
fn source_name(module: &InputModule) -> String {
    let last = module
        .provenance
        .rsplit("::")
        .next()
        .unwrap_or(&module.provenance);
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
        let pa = disassemble(m)?;
        let path = out_dir.join(format!("{}.pa", m.name));
        std::fs::write(&path, &pa)
            .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())))?;
        written.push((m.name.clone(), path, pa.len()));
    }
    Ok(written)
}

/// Print raw bytes to stdout (the text may not be UTF-8).
pub fn print_raw(bytes: &[u8]) -> Result<(), CliError> {
    let mut out = std::io::stdout().lock();
    out.write_all(bytes)
        .and_then(|()| out.flush())
        .map_err(|e| CliError::Tool(format!("cannot write to stdout: {e}")))
}
