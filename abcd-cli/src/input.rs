//! Shared input layer (design/cli.md §1).
//!
//! Every bytecode-consuming command accepts both a bare `.abc` file and a
//! container (`.hap` / `.hsp` / `.app` / `.hqf`). The kind is sniffed by
//! magic bytes: a leading `PK\x03\x04` (local header) or `PK\x05\x06` (empty
//! ZIP end-of-central-directory) means ZIP container (handled by abcd-hap),
//! anything else is read as raw Ark bytecode.
//!
//! Multi-module containers (`.app`) never resolve silently: without
//! `--module <name>` or `--all` the caller gets a hard error listing the
//! available module names.

use std::collections::BTreeSet;
use std::path::Path;

use crate::CliError;

/// Local file header signature of a non-empty ZIP container.
const ZIP_LOCAL_MAGIC: &[u8; 4] = b"PK\x03\x04";
/// End-of-central-directory signature at offset 0 of an empty ZIP container.
const ZIP_EMPTY_MAGIC: &[u8; 4] = b"PK\x05\x06";

/// How many modules of a multi-module container a command wants.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ModuleSelection<'a> {
    /// Resolve only when the input yields exactly one module.
    #[default]
    Single,
    /// `--module <name>`: pick one module by name.
    Named(&'a str),
    /// `--all`: take every module.
    All,
}

/// One module's bytecode with provenance, owned and ready for decoding.
#[derive(Clone, Debug)]
pub struct InputModule {
    /// Module name: the `name` field of `module.json` when present,
    /// otherwise derived from the container entry name, otherwise the
    /// source file stem.
    pub name: String,
    /// Raw `.abc` bytes.
    pub abc: Vec<u8>,
    /// Raw `module.json` / `config.json` bytes, if the container carried one.
    pub module_json: Option<Vec<u8>>,
    /// Human-readable provenance chain (e.g.
    /// `app.app::entry.hap::ets/modules.abc`).
    pub provenance: String,
}

/// True when `bytes` looks like a ZIP container (magic-byte sniff:
/// `PK\x03\x04` local header or `PK\x05\x06` empty ZIP archive).
pub fn is_container(bytes: &[u8]) -> bool {
    bytes.starts_with(ZIP_LOCAL_MAGIC) || bytes.starts_with(ZIP_EMPTY_MAGIC)
}

/// Read `path` into a single allocation carrying a trailing 16-byte `[0u8; 16]`
/// sentinel (`logical_len = buf.len() - 16`), suitable for zero-copy inspection
/// via [`abcd_file::inspect_summary_zeropadded`].
pub fn read_padded_file(path: &Path) -> Result<Vec<u8>, CliError> {
    use std::io::Read;

    let io_err = |e: std::io::Error| CliError::User(format!("cannot read {}: {e}", path.display()));
    let mut file = std::fs::File::open(path).map_err(io_err)?;
    let len = usize::try_from(file.metadata().map_err(io_err)?.len())
        .map_err(|_| CliError::User(format!("cannot read {}: file too large", path.display())))?;
    let cap = len
        .checked_add(16)
        .ok_or_else(|| CliError::User(format!("cannot read {}: file too large", path.display())))?;
    let mut buf = Vec::with_capacity(cap);
    file.read_to_end(&mut buf).map_err(io_err)?;
    buf.extend_from_slice(&[0u8; 16]);
    Ok(buf)
}

/// Read `path` and resolve it to module(s) per `selection`.
pub fn load(path: &Path, selection: ModuleSelection<'_>) -> Result<Vec<InputModule>, CliError> {
    let bytes = std::fs::read(path)
        .map_err(|e| CliError::User(format!("cannot read {}: {e}", path.display())))?;
    let source_name = path.display().to_string();
    let modules = if is_container(&bytes) {
        let mods = container_modules(&bytes, &source_name)?;
        drop(bytes);
        mods
    } else {
        vec![InputModule {
            name: file_stem(&source_name),
            abc: bytes,
            module_json: None,
            provenance: source_name.clone(),
        }]
    };
    select(modules, &source_name, selection)
}

/// In-memory twin of [`load`] (tests drive this directly). `source_name` is
/// used for provenance and the bare-abc module-name fallback.
pub fn load_bytes(
    bytes: &[u8],
    source_name: &str,
    selection: ModuleSelection<'_>,
) -> Result<Vec<InputModule>, CliError> {
    let modules = if is_container(bytes) {
        container_modules(bytes, source_name)?
    } else {
        vec![InputModule {
            name: file_stem(source_name),
            abc: bytes.to_vec(),
            module_json: None,
            provenance: source_name.to_string(),
        }]
    };
    select(modules, source_name, selection)
}

/// Extract every module of a container, ignoring selection (used by
/// `extract`, which always writes all modules).
pub fn load_container_modules(
    bytes: &[u8],
    source_name: &str,
) -> Result<Vec<InputModule>, CliError> {
    if !is_container(bytes) {
        return Err(CliError::User(format!(
            "{source_name} is not a container (expected .hap/.hsp/.app/.hqf; \
             use `abcd info`/`abcd decompile` for bare .abc files)"
        )));
    }
    container_modules(bytes, source_name)
}

/// Map abcd-hap modules onto owned [`InputModule`]s with resolved names.
fn container_modules(bytes: &[u8], source_name: &str) -> Result<Vec<InputModule>, CliError> {
    let modules = abcd_hap::abc_modules(bytes)
        .map_err(|e| CliError::Tool(format!("failed to read container {source_name}: {e}")))?;
    let mut out = Vec::with_capacity(modules.len());
    let mut used_keys: BTreeSet<String> = BTreeSet::new();
    for m in modules {
        let summary = m.manifest_summary();
        let abc = m.data.as_slice().to_vec();
        let module_json = m.module_json.as_ref().map(|d| d.as_slice().to_vec());
        let raw_base = resolve_module_name(
            summary.as_ref().and_then(|s| s.module_name.as_deref()),
            module_json.as_deref(),
            &m.container_path,
            source_name,
        );
        // Sanitize container-supplied names deterministically rather than
        // aborting read-only subcommands (`info`, `analyze`, `taint`, `dis`,
        // `decompile`) when a container carries quirky `module.json` strings,
        // while guaranteeing `is_safe_path_segment` for writer commands.
        let base = sanitize_module_name(&raw_base);
        // A per-ability hap (ets/<Ability>/<Name>.abc …) or a container with
        // case-only name variants (`Entry` + `entry`) yields modules whose
        // output filenames collide on case-insensitive filesystems (APFS/NTFS).
        // Deduplicate collision keys case-insensitively while preserving the
        // original case in `m.name`: first occurrence keeps `base`, collisions
        // get `<base>__<entry-stem>`, then `__N` on repeat.
        let name = if used_keys.contains(&base.to_ascii_lowercase()) {
            let stem = sanitize_module_name(&file_stem(&m.entry_name));
            let mut candidate = sanitize_module_name(&format!("{base}__{stem}"));
            let mut n = 2;
            while used_keys.contains(&candidate.to_ascii_lowercase()) {
                candidate = sanitize_module_name(&format!("{base}__{stem}{n}"));
                n += 1;
            }
            candidate
        } else {
            base
        };
        debug_assert!(is_safe_path_segment(&name));
        used_keys.insert(name.to_ascii_lowercase());
        let mut provenance = source_name.to_string();
        for hop in &m.container_path {
            provenance.push_str("::");
            provenance.push_str(hop);
        }
        provenance.push_str("::");
        provenance.push_str(&m.entry_name);
        out.push(InputModule {
            name,
            abc,
            module_json,
            provenance,
        });
    }
    Ok(out)
}

/// Module name resolution order: Stage `module.name` or FA
/// `module.distro.moduleName` via [`abcd_hap::ManifestSummary`], then the
/// innermost container entry stem (`entry.hap` → `entry`), then the source
/// file stem.
fn resolve_module_name(
    summary_name: Option<&str>,
    module_json: Option<&[u8]>,
    container_path: &[String],
    source_name: &str,
) -> String {
    if let Some(name) = summary_name
        && !name.is_empty()
    {
        return name.to_string();
    }
    if let Some(json) = module_json
        && let Some(name) = module_json_name(json)
    {
        return name;
    }
    if let Some(entry) = container_path.last() {
        return file_stem(entry);
    }
    file_stem(source_name)
}

/// Pull the module name out of a Stage-model `module.json` (`module.name`) or
/// an FA-model `config.json` (`module.distro.moduleName`) via `abcd-hap`'s
/// zero-recursion manifest parser. Anything unparseable falls back to the
/// caller's derivation.
fn module_json_name(json: &[u8]) -> Option<String> {
    abcd_hap::parse_manifest_summary(json)?
        .module_name
        .filter(|s| !s.is_empty())
}

/// Stem of the final path component (`dir/entry.hap` → `entry`).
pub(crate) fn file_stem(path: &str) -> String {
    let base = path.rsplit(['/', '\\']).next().unwrap_or(path);
    match base.rsplit_once('.') {
        Some((stem, _ext)) if !stem.is_empty() => stem.to_string(),
        _ => base.to_string(),
    }
}

/// True when `stem` (the portion of a path segment before the first `.`) is a
/// Windows reserved device name (`CON`, `PRN`, `AUX`, `NUL`, `COM0`..`COM9`,
/// `LPT0`..`LPT9`, `CONIN$`, `CONOUT$`), matched case-insensitively.
fn is_windows_reserved_device(stem: &str) -> bool {
    let b = stem.as_bytes();
    match b.len() {
        3 => {
            b.eq_ignore_ascii_case(b"CON")
                || b.eq_ignore_ascii_case(b"PRN")
                || b.eq_ignore_ascii_case(b"AUX")
                || b.eq_ignore_ascii_case(b"NUL")
        }
        4 => {
            (b[..3].eq_ignore_ascii_case(b"COM") || b[..3].eq_ignore_ascii_case(b"LPT"))
                && b[3].is_ascii_digit()
        }
        6 => b.eq_ignore_ascii_case(b"CONIN$"),
        7 => b.eq_ignore_ascii_case(b"CONOUT$"),
        _ => false,
    }
}

/// Portable single path-segment validator shared across container module names
/// (`extract`, `dis`/`rewrite`/`decompile --all`) and `--split-modules` output
/// paths (`decompile::safe_join`).
///
/// Rejects empty segments, `.` and `..`, `/` and `\`, control characters
/// (`<= 0x1F`, `0x7F`, or Unicode C1 controls), Windows-forbidden characters
/// (`<`, `>`, `:`, `"`, `|`, `?`, `*`), trailing `.` or `' '`, and Windows
/// reserved device names checked case-insensitively on the stem before the
/// first `.`.
pub fn is_safe_path_segment(seg: &str) -> bool {
    if seg.is_empty() || seg == "." || seg == ".." || seg.ends_with('.') || seg.ends_with(' ') {
        return false;
    }
    if seg.chars().any(|c| {
        c <= '\x1f'
            || c == '\x7f'
            || c.is_control()
            || matches!(c, '/' | '\\' | '<' | '>' | ':' | '"' | '|' | '?' | '*')
    }) {
        return false;
    }
    let stem = seg.split('.').next().unwrap_or(seg);
    !is_windows_reserved_device(stem)
}

/// A module name is safe iff it is a single, inert portable path component.
#[cfg(test)]
fn safe_module_name(name: &str) -> Option<String> {
    is_safe_path_segment(name).then(|| name.to_string())
}

/// Deterministically sanitize an arbitrary container-supplied module name into
/// a valid single path segment satisfying [`is_safe_path_segment`].
pub fn sanitize_module_name(raw: &str) -> String {
    if is_safe_path_segment(raw) {
        return raw.to_string();
    }
    let mut cleaned = String::with_capacity(raw.len().max(7));
    for c in raw.chars() {
        if c <= '\x1f'
            || c == '\x7f'
            || c.is_control()
            || matches!(c, '/' | '\\' | '<' | '>' | ':' | '"' | '|' | '?' | '*')
        {
            cleaned.push('_');
        } else {
            cleaned.push(c);
        }
    }
    let trimmed = cleaned.trim_end_matches(['.', ' ']);
    if trimmed.is_empty() || trimmed == "." || trimmed == ".." {
        return "_module".to_string();
    }
    let stem = trimmed.split('.').next().unwrap_or(trimmed);
    if is_windows_reserved_device(stem) {
        format!("_{trimmed}")
    } else {
        trimmed.to_string()
    }
}

/// Apply the module-selection rule (never silently pick from several).
fn select(
    mut modules: Vec<InputModule>,
    source_name: &str,
    selection: ModuleSelection<'_>,
) -> Result<Vec<InputModule>, CliError> {
    let listing = |mods: &[InputModule]| {
        let names: Vec<&str> = mods.iter().map(|m| m.name.as_str()).collect();
        format!("; available modules: {}", names.join(", "))
    };
    match selection {
        ModuleSelection::All => Ok(modules),
        ModuleSelection::Named(want) => match modules.iter().position(|m| m.name == want) {
            Some(i) => Ok(vec![modules.swap_remove(i)]),
            None => Err(CliError::User(format!(
                "{source_name} has no module named {want:?}{}",
                listing(&modules)
            ))),
        },
        ModuleSelection::Single => {
            if modules.len() == 1 {
                return Ok(modules);
            }
            Err(CliError::User(format!(
                "{source_name} contains {} modules; pass --module <name> or --all{}",
                modules.len(),
                listing(&modules),
            )))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn container_sniff_magic() {
        assert!(is_container(b"PK\x03\x04rest"));
        assert!(is_container(b"PK\x05\x06\x00\x00")); // empty ZIP EOCD
        assert!(!is_container(b"PK\x03")); // truncated
        assert!(!is_container(b"PK\x05")); // truncated
        assert!(!is_container(b"PLEX")); // abc magic family is not PK
        assert!(!is_container(b""));
    }

    #[test]
    fn bare_abc_is_single_module() {
        let mods = load_bytes(b"\x00\x01", "foo/modules.abc", ModuleSelection::Single).unwrap();
        assert_eq!(mods.len(), 1);
        assert_eq!(mods[0].name, "modules");
        assert_eq!(mods[0].abc, b"\x00\x01");
        assert_eq!(mods[0].provenance, "foo/modules.abc");
    }

    #[test]
    fn file_stem_derivation() {
        assert_eq!(file_stem("entry.hap"), "entry");
        assert_eq!(file_stem("a/b/phone.hsp"), "phone");
        assert_eq!(file_stem("noext"), "noext");
        assert_eq!(file_stem(".abc"), ".abc"); // empty stem keeps the base
    }

    #[test]
    fn module_json_name_parsing() {
        let stage = br#"{"app":{},"module":{"name":"entry"}}"#;
        assert_eq!(module_json_name(stage).as_deref(), Some("entry"));
        assert_eq!(module_json_name(b"{}"), None);
        assert_eq!(module_json_name(b"not json"), None);
        assert_eq!(module_json_name(br#"{"module":{"name":""}}"#), None);
        assert_eq!(module_json_name(br#"{"module":{"name":3}}"#), None);
    }

    #[test]
    fn safe_module_name_rejects_path_injection() {
        // The traversal cases a hostile container would try.
        assert_eq!(safe_module_name("../evil"), None);
        assert_eq!(safe_module_name("../../tmp/x"), None);
        assert_eq!(safe_module_name("/abs/path"), None);
        assert_eq!(safe_module_name("a\\b"), None);
        assert_eq!(safe_module_name("C:\\x"), None);
        assert_eq!(safe_module_name("."), None);
        assert_eq!(safe_module_name(".."), None);
        assert_eq!(safe_module_name(""), None);
        assert_eq!(safe_module_name("with\nnewline"), None);
        assert_eq!(safe_module_name("del\x7fchar"), None);
        assert_eq!(safe_module_name("nul\x00byte"), None);
        // Windows-forbidden characters, trailing dot/space, and reserved device names.
        for bad in [
            "a<b",
            "a>b",
            "a:b",
            "a\"b",
            "a|b",
            "a?b",
            "a*b",
            "trailing.",
            "trailing ",
            "CON",
            "con",
            "con.txt",
            "PRN",
            "prn.abc",
            "AUX",
            "aux.json",
            "aux.config.js",
            "NUL",
            "nul.pa",
            "COM0",
            "com1.txt",
            "COM9.json",
            "LPT0",
            "lpt1.js",
            "LPT9",
            "CONIN$",
            "conin$.txt",
            "CONOUT$",
            "conout$.log",
        ] {
            assert_eq!(safe_module_name(bad), None, "must reject {bad:?}");
        }
        // Legit names survive, including unicode, 4-byte UTF-8 stems, and dotted names.
        assert_eq!(safe_module_name("entry").as_deref(), Some("entry"));
        assert_eq!(
            safe_module_name("com.example.app").as_deref(),
            Some("com.example.app")
        );
        assert_eq!(safe_module_name("com10").as_deref(), Some("com10"));
        assert_eq!(
            safe_module_name("console.js").as_deref(),
            Some("console.js")
        );
        assert_eq!(safe_module_name("abä").as_deref(), Some("abä"));
        assert_eq!(safe_module_name("模块").as_deref(), Some("模块"));
        assert_eq!(
            safe_module_name("my-module_2").as_deref(),
            Some("my-module_2")
        );
    }
}
