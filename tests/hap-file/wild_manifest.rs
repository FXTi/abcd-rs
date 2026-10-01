//! Wild-corpus manifest parsing (the gate's oracle).
//!
//! The export-wild image step writes `manifest.json` as a single JSON
//! object: `{"packages": [{"path", "sha256", "size", "abc_layout",
//! "module_name", "expectation"}]}`. Only `path` and `expectation` drive
//! the gate; the rest is provenance kept for diagnostics.

use std::path::Path;

/// Per-package decode expectation, as labeled by the corpus builder.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Deserialize)]
pub enum Expectation {
    /// Every extracted .abc module must decode cleanly.
    #[serde(rename = "decode-ok")]
    DecodeOk,
    /// The container must parse, and at least one module must fail decode
    /// with an "invalid opcode" error (pre-fix ISA bytecode in the wild).
    #[serde(rename = "negative-invalid-opcode")]
    NegativeInvalidOpcode,
}

/// One wild-corpus package row.
#[derive(Debug, serde::Deserialize)]
pub struct Package {
    /// Path relative to the corpus root (`OpenHarmony-x/y.hap`).
    pub path: String,
    /// SHA-256 of the package bytes (provenance; the gate reads the files
    /// fresh, so this is informational).
    #[allow(dead_code)]
    pub sha256: String,
    /// Package size in bytes (informational).
    #[allow(dead_code)]
    pub size: u64,
    /// .abc layout class: merged | per-ability | fa-assets (informational).
    #[allow(dead_code)]
    pub abc_layout: String,
    /// Declaring module name (informational).
    #[allow(dead_code)]
    pub module_name: String,
    pub expectation: Expectation,
}

/// The manifest root object.
#[derive(Debug, serde::Deserialize)]
pub struct Manifest {
    pub packages: Vec<Package>,
}

impl Manifest {
    /// Load and parse a manifest file.
    pub fn load(path: &Path) -> Result<Self, String> {
        let text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
        Self::parse(&text)
    }

    /// Parse manifest JSON text. Unknown expectations are a hard parse
    /// error — the gate must never silently reclassify a row.
    pub fn parse(text: &str) -> Result<Self, String> {
        serde_json::from_str(text).map_err(|e| e.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pkg(path: &str, expectation: &str) -> String {
        format!(
            r#"{{"path":"{path}","sha256":"00","size":1,"abc_layout":"merged","module_name":".entry","expectation":"{expectation}"}}"#
        )
    }

    #[test]
    fn parses_both_expectations() {
        let text = format!(
            r#"{{"packages":[{},{}]}}"#,
            pkg("a/x.hap", "decode-ok"),
            pkg("b/y.hap", "negative-invalid-opcode")
        );
        let m = Manifest::parse(&text).unwrap();
        assert_eq!(m.packages.len(), 2);
        assert_eq!(m.packages[0].expectation, Expectation::DecodeOk);
        assert_eq!(m.packages[0].path, "a/x.hap");
        assert_eq!(
            m.packages[1].expectation,
            Expectation::NegativeInvalidOpcode
        );
    }

    #[test]
    fn rejects_unknown_expectation() {
        let text = format!(r#"{{"packages":[{}]}}"#, pkg("a/x.hap", "maybe-ok"));
        assert!(Manifest::parse(&text).is_err());
    }

    #[test]
    fn rejects_missing_field() {
        // No "expectation" key: the row is not a valid oracle entry.
        let text = r#"{"packages":[{"path":"a/x.hap","sha256":"00","size":1,"abc_layout":"merged","module_name":".entry"}]}"#;
        assert!(Manifest::parse(text).is_err());
    }

    #[test]
    fn rejects_malformed_json() {
        assert!(Manifest::parse("not json").is_err());
    }

    #[test]
    fn accepts_empty_package_list() {
        let m = Manifest::parse(r#"{"packages":[]}"#).unwrap();
        assert!(m.packages.is_empty());
    }
}
