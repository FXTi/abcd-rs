//! Shared input layer (design/cli-plan.md §3.2).
//!
//! Every bytecode-consuming command accepts both a bare `.abc` file and a
//! container (`.hap` / `.hsp` / `.app` / `.hqf`). The kind is sniffed by
//! magic bytes: a leading `PK\x03\x04` means ZIP container (handled by
//! abcd-hap), anything else is read as raw Ark bytecode.
//!
//! Multi-module containers (`.app`) never resolve silently: without
//! `--module <name>` or `--all` the caller gets a hard error listing the
//! available module names.

use std::path::Path;

use crate::CliError;

/// Local file header signature of every ZIP dialect container in scope.
const ZIP_MAGIC: &[u8; 4] = b"PK\x03\x04";

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

/// True when `bytes` looks like a ZIP container (magic-byte sniff).
pub fn is_container(bytes: &[u8]) -> bool {
    bytes.len() >= ZIP_MAGIC.len() && &bytes[..ZIP_MAGIC.len()] == ZIP_MAGIC
}

/// Read `path` and resolve it to module(s) per `selection`.
pub fn load(path: &Path, selection: ModuleSelection<'_>) -> Result<Vec<InputModule>, CliError> {
    let bytes = std::fs::read(path)
        .map_err(|e| CliError::User(format!("cannot read {}: {e}", path.display())))?;
    load_bytes(&bytes, &path.display().to_string(), selection)
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
    for m in modules {
        let abc = m.data.as_slice().to_vec();
        let module_json = m.module_json.as_ref().map(|d| d.as_slice().to_vec());
        let name = resolve_module_name(module_json.as_deref(), &m.container_path, source_name);
        // Module names end up in OUTPUT PATHS (`extract`, `decompile --all`),
        // and they come from container content — an attacker-controlled
        // module.json `name` like "../../tmp/x" must not escape the output
        // directory (the in-memory reader needs no Zip Slip guard; the CLI
        // writer does).
        let name = safe_module_name(&name).ok_or_else(|| {
            CliError::Tool(format!(
                "{source_name}: module name {name:?} is not a safe output path component"
            ))
        })?;
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

/// Module name resolution order: `module.json`'s `name` field, then the
/// innermost container entry stem (`entry.hap` → `entry`), then the source
/// file stem.
fn resolve_module_name(
    module_json: Option<&[u8]>,
    container_path: &[String],
    source_name: &str,
) -> String {
    if let Some(json) = module_json {
        if let Some(name) = module_json_name(json) {
            return name;
        }
    }
    if let Some(entry) = container_path.last() {
        return file_stem(entry);
    }
    file_stem(source_name)
}

/// Pull the module name out of a Stage-model `module.json`
/// (`module.name`) or an FA-model `config.json` (same layout). Anything
/// unparseable falls back to the caller's derivation.
fn module_json_name(json: &[u8]) -> Option<String> {
    let value: serde_json::Value = serde_json::from_slice(json).ok()?;
    let name = value.get("module")?.get("name")?.as_str()?;
    if name.is_empty() {
        return None;
    }
    Some(name.to_string())
}

/// Stem of the final path component (`dir/entry.hap` → `entry`).
fn file_stem(path: &str) -> String {
    let base = path.rsplit(['/', '\\']).next().unwrap_or(path);
    match base.rsplit_once('.') {
        Some((stem, _ext)) if !stem.is_empty() => stem.to_string(),
        _ => base.to_string(),
    }
}

/// A module name is safe iff it is a single, inert path component: no
/// separators (including Windows-style), no drive/absolute prefix, no dot
/// specials, no control characters.
fn safe_module_name(name: &str) -> Option<String> {
    let safe = !name.is_empty()
        && name != "."
        && name != ".."
        && !name.contains(['/', '\\', ':'])
        && !name.chars().any(char::is_control);
    safe.then(|| name.to_string())
}

/// Apply the module-selection rule (never silently pick from several).
fn select(
    modules: Vec<InputModule>,
    source_name: &str,
    selection: ModuleSelection<'_>,
) -> Result<Vec<InputModule>, CliError> {
    let listing = || {
        let names: Vec<&str> = modules.iter().map(|m| m.name.as_str()).collect();
        format!("; available modules: {}", names.join(", "))
    };
    match selection {
        ModuleSelection::All => Ok(modules),
        ModuleSelection::Named(want) => match modules.iter().position(|m| m.name == want) {
            Some(i) => Ok(vec![
                modules.into_iter().nth(i).expect("position checked above"),
            ]),
            None => Err(CliError::User(format!(
                "{source_name} has no module named {want:?}{}",
                listing()
            ))),
        },
        ModuleSelection::Single => {
            if modules.len() == 1 {
                return Ok(modules);
            }
            Err(CliError::User(format!(
                "{source_name} contains {} modules; pass --module <name> or --all{}",
                modules.len(),
                listing(),
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
        assert!(!is_container(b"PK\x03")); // truncated
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
        // Legit names survive, including unicode and dotted names.
        assert_eq!(safe_module_name("entry").as_deref(), Some("entry"));
        assert_eq!(
            safe_module_name("com.example.app").as_deref(),
            Some("com.example.app")
        );
        assert_eq!(safe_module_name("模块").as_deref(), Some("模块"));
        assert_eq!(
            safe_module_name("my-module_2").as_deref(),
            Some("my-module_2")
        );
    }
}
