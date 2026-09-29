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
    let mut seen_names: Vec<&str> = Vec::with_capacity(modules.len());
    for m in modules {
        if seen_names.contains(&m.name.as_str()) {
            return Err(CliError::Tool(format!(
                "container yields two modules named {:?}; refusing to pick output names",
                m.name
            )));
        }
        seen_names.push(&m.name);
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

    // Preflight: no output path may exist unless --force.
    if !force {
        for p in &planned {
            for path in std::iter::once(&p.abc_path).chain(p.json_path.iter()) {
                if path.exists() {
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
        std::fs::write(&p.abc_path, &m.abc)
            .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", p.abc_path.display())))?;
        if let (Some(json), Some(json_path)) = (&m.module_json, &p.json_path) {
            std::fs::write(json_path, json).map_err(|e| {
                CliError::Tool(format!("cannot write {}: {e}", json_path.display()))
            })?;
        }
    }
    Ok(planned)
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
