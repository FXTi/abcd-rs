//! `abcd extract` — write each module's `.abc` (and `module.json`) to disk.

use std::path::{Path, PathBuf};

use crate::CliError;
use crate::input::{InputModule, load_container_modules};

/// One written module of an extract run.
#[derive(Clone, Debug)]
pub struct ExtractedModule {
    /// Module name (see [`crate::input::InputModule::name`]).
    pub name: String,
    /// Byte size of the `.abc` payload.
    pub abc_size: usize,
    /// Path the `.abc` was written to.
    pub abc_path: PathBuf,
    /// Path the module manifest was written to, if one existed.
    pub json_path: Option<PathBuf>,
    /// Provenance chain from the outermost container.
    pub provenance: String,
}

/// Extract every module of the container at `path` into `out_dir`.
///
/// Existing output files are never overwritten unless `force` — the
/// preflight check runs before any byte is written, so a collision leaves
/// the output directory untouched.
pub fn extract_path(
    path: &Path,
    out_dir: &Path,
    force: bool,
) -> Result<Vec<ExtractedModule>, CliError> {
    let bytes = std::fs::read(path)
        .map_err(|e| CliError::User(format!("cannot read {}: {e}", path.display())))?;
    extract_bytes(&bytes, &path.display().to_string(), out_dir, force)
}

/// In-memory twin of [`extract_path`] (tests drive this directly).
pub fn extract_bytes(
    bytes: &[u8],
    source_name: &str,
    out_dir: &Path,
    force: bool,
) -> Result<Vec<ExtractedModule>, CliError> {
    let modules = load_container_modules(bytes, source_name)?;
    plan_and_write(&modules, out_dir, force)
}

/// Compute output paths, preflight collisions, then write.
fn plan_and_write(
    modules: &[InputModule],
    out_dir: &Path,
    force: bool,
) -> Result<Vec<ExtractedModule>, CliError> {
    let mut planned: Vec<ExtractedModule> = Vec::with_capacity(modules.len());
    // No duplicate-name guard here: `input::container_modules` already
    // enforces globally unique module names (input.rs dedup loop), so two
    // modules can never share a name at this point.
    for m in modules {
        let abc_path = out_dir.join(format!("{}.abc", m.name));
        let json_path = m
            .module_json
            .as_ref()
            .map(|_| out_dir.join(format!("{}.module.json", m.name)));
        planned.push(ExtractedModule {
            name: m.name.clone(),
            abc_size: m.abc.len(),
            abc_path,
            json_path,
            provenance: m.provenance.clone(),
        });
    }

    // Preflight: no output path (regular file, directory, or symlink —
    // including dangling symlinks) may exist unless --force.
    if !force {
        for p in &planned {
            for path in std::iter::once(&p.abc_path).chain(p.json_path.iter()) {
                if std::fs::symlink_metadata(path).is_ok() {
                    return Err(CliError::User(format!(
                        "{} already exists (pass --force to overwrite)",
                        path.display()
                    )));
                }
            }
        }
    }

    std::fs::create_dir_all(out_dir).map_err(|e| {
        CliError::Tool(format!(
            "cannot create output directory {}: {e}",
            out_dir.display()
        ))
    })?;
    for (m, p) in modules.iter().zip(&planned) {
        write_extracted_file(&p.abc_path, &m.abc, force)?;
        if let (Some(json), Some(json_path)) = (&m.module_json, &p.json_path) {
            write_extracted_file(json_path, json, force)?;
        }
    }
    Ok(planned)
}

/// Write `bytes` to `path`, using atomic `create_new(true)` (`O_EXCL`) when
/// `!force` so neither TOCTOU races nor dangling symlinks can overwrite
/// existing files.
fn write_extracted_file(path: &Path, bytes: &[u8], force: bool) -> Result<(), CliError> {
    use std::io::Write;

    if force {
        return std::fs::write(path, bytes)
            .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())));
    }
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|e| {
            if e.kind() == std::io::ErrorKind::AlreadyExists {
                CliError::User(format!(
                    "{} already exists (pass --force to overwrite)",
                    path.display()
                ))
            } else {
                CliError::Tool(format!("cannot write {}: {e}", path.display()))
            }
        })?;
    file.write_all(bytes)
        .and_then(|()| file.flush())
        .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())))
}

/// Human-readable summary of an extract run (goes to stdout).
pub fn render_summary(source_name: &str, out_dir: &Path, modules: &[ExtractedModule]) -> String {
    let mut out = format!(
        "extracted {} module(s) from {source_name} -> {}\n",
        modules.len(),
        out_dir.display()
    );
    for m in modules {
        out.push_str(&format!(
            "  {}: {} bytes -> {}",
            m.name,
            m.abc_size,
            m.abc_path.display()
        ));
        if let Some(json) = &m.json_path {
            out.push_str(&format!(" (+ {})", json.display()));
        }
        out.push('\n');
    }
    out
}
