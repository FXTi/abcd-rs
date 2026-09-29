//! `abcd asm` — assemble pandasm `.pa` text into an `.abc` file
//! (the round-trip direction of `abcd dis`; design/cli-plan.md §2, §4 P2).
//!
//! Input is a pandasm TEXT file (the container/abc input layer does not
//! apply). The parser (`abcd_file::pandasm::parse_file*`) is the one the
//! corpus round-trip gates exercise; a `.pa` carries no format version, so
//! `--version` overrides the default (`parse_file`'s
//! [`abcd_file::pandasm::DEFAULT_VERSION`], matching upstream ark_asm
//! always writing the current version).
//!
//! A writer command: `--check` re-decodes the emitted bytes (full
//! structural + per-method instruction decode) before they leave the
//! process, so a parser/encoder bug surfaces as a tool error (exit 2)
//! instead of a corrupt file on disk.

use std::io::Write as _;
use std::path::{Path, PathBuf};

use crate::CliError;

/// Assemble one pandasm text into `.abc` bytes.
pub fn assemble(
    pa: &[u8],
    source_name: &str,
    version: Option<abcd_file::Version>,
    check: bool,
) -> Result<Vec<u8>, CliError> {
    let file = match version {
        Some(v) => abcd_file::pandasm::parse_file_with_version(pa, v),
        None => abcd_file::pandasm::parse_file(pa),
    }
    .map_err(|e| CliError::User(format!("{source_name}: parse failed: {e}")))?;
    let abc = abcd_file::encode(&file)
        .map_err(|e| CliError::Tool(format!("{source_name}: encode failed: {e}")))?;
    if check {
        abcd_file::decode(&abc).map_err(|e| {
            CliError::Tool(format!(
                "{source_name}: --check failed: emitted bytes do not re-decode: {e}"
            ))
        })?;
    }
    Ok(abc)
}

/// Run the command: read `input`, write the assembled bytes.
pub fn run_asm(
    input: &Path,
    output: Option<&PathBuf>,
    version: Option<abcd_file::Version>,
    check: bool,
) -> Result<(), CliError> {
    let pa = std::fs::read(input)
        .map_err(|e| CliError::User(format!("cannot read {}: {e}", input.display())))?;
    let abc = assemble(&pa, &input.display().to_string(), version, check)?;
    match output {
        Some(path) => {
            std::fs::write(path, &abc)
                .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())))?;
            println!("{} bytes -> {}", abc.len(), path.display());
        }
        None => {
            let mut out = std::io::stdout().lock();
            out.write_all(&abc)
                .and_then(|()| out.flush())
                .map_err(|e| CliError::Tool(format!("cannot write to stdout: {e}")))?;
        }
    }
    Ok(())
}
