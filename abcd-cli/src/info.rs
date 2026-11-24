//! `abcd info` — readelf-style summary of an .abc file.
//!
//! The report shows header metadata and entity counts matching the decoded
//! [`abcd_file::File`] model via [`abcd_file::inspect_summary`] — nothing is
//! invented. `--verify` streams debug-info extraction and every method body's
//! bytecode instruction and try-block verification, making the verdict
//! explicit and binding it to the process exit code (0 pass, 2 fail).

use abcd_file::{FileSummary, FileType, VerifySummary};
use serde::Serialize;

use crate::CliError;
use crate::input::InputModule;

/// Machine-readable per-module report (serialized by `--json`).
#[derive(Clone, Debug, Serialize)]
pub struct InfoReport {
    /// Module name (container provenance or file stem).
    pub module: String,
    /// Where the bytes came from.
    pub provenance: String,
    /// Input `.abc` size in bytes.
    pub input_bytes: usize,
    /// File-format version, `major.minor.patch.build`.
    pub format_version: String,
    /// `static` / `dynamic` / `invalid` (from the file header).
    pub file_type: String,
    /// Header checksum field.
    pub checksum: u32,
    /// Header-declared file size.
    pub header_size: u32,
    /// Counts over the decoded model.
    pub counts: Counts,
    /// Present only under `--verify`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verify: Option<VerifyReport>,
}

/// Entity counts of the decoded file.
#[derive(Clone, Debug, Serialize)]
pub struct Counts {
    /// Interned strings.
    pub strings: usize,
    /// Class records (including external references).
    pub classes: usize,
    /// Classes external to this file (descriptors only).
    pub external_classes: usize,
    /// Methods across all classes.
    pub methods: usize,
    /// Methods carrying a bytecode body.
    pub methods_with_body: usize,
    /// Fields across all classes.
    pub fields: usize,
    /// Literal arrays (including nested ones recovered at decode).
    pub literal_arrays: usize,
    /// Entity-index entries (offset → name/descriptor map).
    pub entity_index_entries: usize,
    /// Methods with debug info.
    pub debug_infos: usize,
    /// Strings with lossy MUTF-8 forms preserved verbatim (lone surrogates).
    pub lossy_strings: usize,
}

/// Explicit verification verdict (`--verify`).
#[derive(Clone, Debug, Serialize)]
pub struct VerifyReport {
    /// Methods whose bytecode stream was fully decoded.
    pub methods_checked: usize,
    /// Total instructions decoded across all method bodies.
    pub instructions_decoded: usize,
    /// Always `"ok"` — a failed verification never produces a report,
    /// it is the command's error exit (code 2).
    pub verdict: &'static str,
}

/// Inspect one module and build its report. With `verify`, full streaming
/// bytecode and debug-info verification runs and any failure is reported as a
/// tool error (exit code 2 either way).
pub fn report(module: &InputModule, verify: bool) -> Result<InfoReport, CliError> {
    let summary: FileSummary = abcd_file::inspect_summary(&module.abc, verify).map_err(|e| {
        CliError::Tool(format!(
            "failed to decode {} ({}): {e}",
            module.name, module.provenance
        ))
    })?;
    Ok(build_report(
        &module.name,
        &module.provenance,
        module.abc.len(),
        summary,
    ))
}

/// Zero-copy twin of [`report`] over an `.abc` buffer whose trailing 16 bytes
/// are `[0u8; 16]` (`logical_len = padded_abc.len() - 16`), delegating to
/// [`abcd_file::inspect_summary_zeropadded`].
pub fn report_zeropadded(
    name: &str,
    provenance: &str,
    padded_abc: &[u8],
    verify: bool,
) -> Result<InfoReport, CliError> {
    let summary: FileSummary = abcd_file::inspect_summary_zeropadded(padded_abc, verify)
        .map_err(|e| CliError::Tool(format!("failed to decode {name} ({provenance}): {e}")))?;
    Ok(build_report(
        name,
        provenance,
        padded_abc.len().saturating_sub(16),
        summary,
    ))
}

fn build_report(
    name: &str,
    provenance: &str,
    input_bytes: usize,
    summary: FileSummary,
) -> InfoReport {
    let verify_report = summary.verify.map(
        |VerifySummary {
             methods_checked,
             instructions_decoded,
         }| VerifyReport {
            methods_checked,
            instructions_decoded,
            verdict: "ok",
        },
    );

    let file_type = match summary.file_type {
        FileType::Static => "static",
        FileType::Dynamic => "dynamic",
        FileType::Invalid => "invalid",
    };

    InfoReport {
        module: name.to_string(),
        provenance: provenance.to_string(),
        input_bytes,
        format_version: summary.version.to_string(),
        file_type: file_type.to_string(),
        checksum: summary.checksum,
        header_size: summary.size,
        counts: Counts {
            strings: summary.strings,
            classes: summary.classes,
            external_classes: summary.external_classes,
            methods: summary.methods,
            methods_with_body: summary.methods_with_body,
            fields: summary.fields,
            literal_arrays: summary.literal_arrays,
            entity_index_entries: summary.entity_index_entries,
            debug_infos: summary.debug_infos,
            lossy_strings: summary.lossy_strings,
        },
        verify: verify_report,
    }
}

/// Human-readable rendering of one report (goes to stdout).
pub fn render_text(report: &InfoReport) -> String {
    let c = &report.counts;
    let mut out = format!(
        "module:          {} ({})\n\
         input bytes:     {}\n\
         format version:  {}\n\
         file type:       {}\n\
         checksum:        {:#010x}\n\
         header size:     {}\n\
         strings:         {}\n\
         classes:         {} ({} external)\n\
         methods:         {} ({} with body)\n\
         fields:          {}\n\
         literal arrays:  {}\n\
         entity index:    {} entries\n\
         debug infos:     {}\n\
         lossy strings:   {}\n",
        report.module,
        report.provenance,
        report.input_bytes,
        report.format_version,
        report.file_type,
        report.checksum,
        report.header_size,
        c.strings,
        c.classes,
        c.external_classes,
        c.methods,
        c.methods_with_body,
        c.fields,
        c.literal_arrays,
        c.entity_index_entries,
        c.debug_infos,
        c.lossy_strings,
    );
    if let Some(v) = &report.verify {
        out.push_str(&format!(
            "verify:          {} ({} methods, {} instructions decoded)\n",
            v.verdict, v.methods_checked, v.instructions_decoded
        ));
    }
    out
}

/// Render reports per `--json`: a single module yields one object,
/// several modules yield an array.
pub fn render(reports: &[InfoReport], json: bool) -> Result<String, CliError> {
    if json {
        let value = if reports.len() == 1 {
            serde_json::to_value(&reports[0])
        } else {
            serde_json::to_value(reports)
        }
        .map_err(|e| CliError::Tool(format!("failed to serialize report: {e}")))?;
        serde_json::to_string_pretty(&value)
            .map_err(|e| CliError::Tool(format!("failed to serialize report: {e}")))
    } else {
        Ok(reports
            .iter()
            .map(render_text)
            .collect::<Vec<_>>()
            .join("\n"))
    }
}
