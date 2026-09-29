//! `abcd info` — readelf-style summary of an .abc file.
//!
//! The report shows exactly what the decoded [`abcd_file::File`] model
//! carries — nothing is invented. `--verify` is a full eager decode: abcd-
//! file's decoder already walks every method body and decodes each bytecode
//! instruction (a bad instruction is a hard decode error), so a successful
//! decode IS the verification; the flag makes the verdict explicit and
//! binds it to the process exit code (0 pass, 2 fail).

use abcd_file::FileType;
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

/// Decode one module and build its report. With `verify`, the decode
/// failure that would already be a tool error is additionally reported as
/// the verification verdict by the caller (exit code 2 either way).
pub fn report(module: &InputModule, verify: bool) -> Result<InfoReport, CliError> {
    let file = abcd_file::decode(&module.abc).map_err(|e| {
        CliError::Tool(format!(
            "failed to decode {} ({}): {e}",
            module.name, module.provenance
        ))
    })?;

    let methods: Vec<_> = file.all_methods().collect();
    let methods_with_body = methods.iter().filter(|(_, m)| m.body.is_some()).count();
    let debug_infos = methods.iter().filter(|(_, m)| m.debug.is_some()).count();

    let verify_report = verify.then(|| {
        let instructions_decoded = methods
            .iter()
            .filter_map(|(_, m)| m.body.as_ref())
            .map(|b| b.bytecodes.len())
            .sum();
        VerifyReport {
            methods_checked: methods_with_body,
            instructions_decoded,
            verdict: "ok",
        }
    });

    let file_type = match file.file_type {
        FileType::Static => "static",
        FileType::Dynamic => "dynamic",
        FileType::Invalid => "invalid",
    };

    Ok(InfoReport {
        module: module.name.clone(),
        provenance: module.provenance.clone(),
        input_bytes: module.abc.len(),
        format_version: file.version.to_string(),
        file_type: file_type.to_string(),
        checksum: file.checksum,
        header_size: file.size,
        counts: Counts {
            strings: file.strings.len(),
            classes: file.classes.len(),
            external_classes: file.classes.values().filter(|c| c.is_external).count(),
            methods: methods.len(),
            methods_with_body,
            fields: file.classes.values().map(|c| c.fields.len()).sum(),
            literal_arrays: file.literal_arrays.len(),
            entity_index_entries: file.entity_map.len(),
            debug_infos,
            lossy_strings: file.string_raw_bytes.len(),
        },
        verify: verify_report,
    })
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
