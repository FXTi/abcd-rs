//! TOML configuration for `abcd taint` (design/cli-plan.md §6 — ruled
//! TOML, phase 3).
//!
//! The schema maps [`abcd_taint::TaintConfig`] field-by-field. Example:
//!
//! ```toml
//! # All four analysis toggles default to true (the driver defaults).
//! builtin_summaries = true
//! seed_all_functions = true
//! follow_returns_past_seeds = true
//! native_identity = true
//! max_field_chain = 5   # access-path k-limit (DEFAULT_MAX_FIELD_CHAIN)
//! alias_rung = 2        # 0 | 1 | 2 (see analysis-strategy.md §4.4)
//!
//! # Sources: name-keyed (SourceSpec).
//! [[sources]]
//! kind = "function_params"   # parameters of every function with this name
//! name = "func_main_0"       # "*" = every function
//! # params = [3, 4]          # optional: only these indices; absent = all
//!
//! [[sources]]
//! kind = "global_load"       # every TryGetGlobal(name) result is tainted
//! name = "TAINT"
//!
//! # Sinks: name-keyed (SinkSpec).
//! [[sinks]]
//! kind = "call"              # calls whose callee name candidates match
//! name = "print"             # bare global or qualified ("console.log")
//!
//! # Extra summaries (TaintConfig::extra_summaries): a compact subset of
//! # the full Summary model. Endpoints are strings: "param:N" (0-based
//! # call argument), "base" (receiver), "return" (call result).
//! # Field-chain endpoints are NOT expressible here — FieldKey::Named
//! # needs module-interned symbols, which a module-independent config
//! # file cannot supply (the builtin registry avoids named keys the
//! # same way).
//! [[extra_summaries]]
//! name = "sanitize"
//! arity = 1                  # optional; absent = variadic
//! doc = "returns its argument unchanged"
//! exclusive = false          # optional; true = model is complete
//! callback_param = 2         # optional: mini-gap tag (arg N is a callback)
//! flows = [ { from = "param:0", to = "return" } ]
//! alias_flows = [ { from = "param:0", to = "base" } ]
//! clears = [ "param:1" ]
//! ```
//!
//! An empty (or absent-section) file is legal: it is `TaintConfig`'s
//! defaults with no sources and no sinks — the analysis runs and reports
//! zero hits. Parse and validation failures are USER errors (exit 1)
//! carrying the TOML position.

use abcd_taint::{Endpoint, SinkSpec, SourceSpec, Summary, TaintConfig};
use serde::Deserialize;

use crate::CliError;

/// The default access-path k-limit (abcd-analysis `DEFAULT_MAX_FIELD_CHAIN`).
fn default_max_field_chain() -> usize {
    abcd_analysis::dataflow::heap::DEFAULT_MAX_FIELD_CHAIN
}

/// The driver default for every boolean toggle.
fn driver_default_true() -> bool {
    true
}

/// The driver default alias rung (the whole-module PTA).
fn default_alias_rung() -> u8 {
    2
}

/// The top-level TOML document. Unknown keys are rejected — a typo'd
/// knob must never silently no-op (hard-errors-over-warnings rule).
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct TaintToml {
    /// Taint sources.
    #[serde(default)]
    sources: Vec<SourceToml>,
    /// Taint sinks.
    #[serde(default)]
    sinks: Vec<SinkToml>,
    /// Register the top-20 corpus builtins (default true).
    #[serde(default = "driver_default_true")]
    builtin_summaries: bool,
    /// Seed every function with the zero fact (default true).
    #[serde(default = "driver_default_true")]
    seed_all_functions: bool,
    /// heros `followReturnsPastSeeds` (default true).
    #[serde(default = "driver_default_true")]
    follow_returns_past_seeds: bool,
    /// Unknown-call identity heuristic (default true).
    #[serde(default = "driver_default_true")]
    native_identity: bool,
    /// Access-path k-limit (default `DEFAULT_MAX_FIELD_CHAIN` = 5).
    #[serde(default = "default_max_field_chain")]
    max_field_chain: usize,
    /// Alias-oracle rung: 0, 1, or 2 (default 2).
    #[serde(default = "default_alias_rung")]
    alias_rung: u8,
    /// Extra `(name, arity, summary)` registrations.
    #[serde(default)]
    extra_summaries: Vec<SummaryToml>,
}

/// `[[sources]]` entry — tagged on `kind`, mirroring [`SourceSpec`].
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum SourceToml {
    /// Parameters of every function named `name` are tainted.
    FunctionParams {
        /// The function name (`func_main_0` for module entry points;
        /// `"*"` = every function).
        name: String,
        /// Specific parameter indices; absent = all parameters.
        params: Option<Vec<u16>>,
    },
    /// Every `TryGetGlobal(name)` result is tainted.
    GlobalLoad {
        /// The global's name.
        name: String,
    },
}

/// `[[sinks]]` entry — tagged on `kind`, mirroring [`SinkSpec`].
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum SinkToml {
    /// A call whose callee-name candidates include `name`.
    Call {
        /// The callee name (bare global like `print`, or qualified like
        /// `console.log`).
        name: String,
    },
}

/// `[[extra_summaries]]` entry — the compact TOML subset of [`Summary`]
/// (see the module docs for the field-chain limitation).
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct SummaryToml {
    /// The callee name this summary registers under.
    name: String,
    /// Exact argument count; absent = variadic.
    arity: Option<usize>,
    /// Human-readable semantics note (rendered in reports).
    #[serde(default)]
    doc: String,
    /// Complete model: kills the call edge into the callee body.
    #[serde(default)]
    exclusive: bool,
    /// Propagation flows (non-aliasing).
    #[serde(default)]
    flows: Vec<FlowToml>,
    /// Aliasing flows (the reference itself is stored — mutators).
    #[serde(default)]
    alias_flows: Vec<FlowToml>,
    /// Endpoints whose taint is killed.
    #[serde(default)]
    clears: Vec<String>,
    /// Mini-gap tag: the builtin invokes argument N with elements of
    /// the base.
    callback_param: Option<u16>,
}

/// One `{ from, to }` propagation rule.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct FlowToml {
    /// Source endpoint string (`param:N` / `base`).
    from: String,
    /// Sink endpoint string (`param:N` / `base` / `return`).
    to: String,
}

/// Parse one endpoint string. Field-chain endpoints are rejected here
/// (see the module docs): the strings a config file can carry cannot
/// name module-interned `FieldKey::Named` symbols.
fn endpoint(text: &str) -> Result<Endpoint, CliError> {
    match text {
        "base" => return Ok(Endpoint::Base),
        "return" => return Ok(Endpoint::Return),
        _ => {}
    }
    if let Some(rest) = text.strip_prefix("param:") {
        if let Ok(i) = rest.parse::<u16>() {
            return Ok(Endpoint::Param(i));
        }
    }
    Err(CliError::User(format!(
        "invalid summary endpoint {text:?} (expected \"param:N\", \"base\", or \"return\")"
    )))
}

impl FlowToml {
    /// Convert to `(from, to)` endpoints, rejecting the shapes the
    /// summary model itself declares meaningless (`Endpoint::Return` is
    /// never a flow source).
    fn endpoints(&self) -> Result<(Endpoint, Endpoint), CliError> {
        let from = endpoint(&self.from)?;
        let to = endpoint(&self.to)?;
        if from == Endpoint::Return {
            return Err(CliError::User(format!(
                "invalid flow {:?} -> {:?}: \"return\" is never a flow source",
                self.from, self.to
            )));
        }
        Ok((from, to))
    }
}

impl SummaryToml {
    /// Build the [`Summary`] and its registration key.
    fn build(&self) -> Result<(String, Option<usize>, Summary), CliError> {
        let mut summary = Summary::new(&self.doc);
        for f in &self.flows {
            let (from, to) = f.endpoints()?;
            summary = summary.flow(from, to);
        }
        for f in &self.alias_flows {
            let (from, to) = f.endpoints()?;
            summary = summary.alias_flow(from, to);
        }
        for c in &self.clears {
            summary = summary.clear(endpoint(c)?);
        }
        if self.exclusive {
            summary = summary.exclusive();
        }
        if let Some(param) = self.callback_param {
            summary = summary.callback(param);
        }
        Ok((self.name.clone(), self.arity, summary))
    }
}

/// Parse a TOML taint configuration into [`TaintConfig`].
///
/// Errors are [`CliError::User`] (exit 1): TOML parse failures carry the
/// `toml` crate's `line N, column M` position verbatim; semantic
/// failures (bad endpoint strings, `alias_rung` outside 0..=2) name the
/// offending value.
pub fn parse(text: &str) -> Result<TaintConfig, CliError> {
    let raw: TaintToml =
        toml::from_str(text).map_err(|e| CliError::User(format!("invalid taint config: {e}")))?;
    raw.into_config()
}

impl TaintToml {
    /// Validate and lower to the driver's [`TaintConfig`].
    fn into_config(self) -> Result<TaintConfig, CliError> {
        if self.alias_rung > 2 {
            return Err(CliError::User(format!(
                "invalid alias_rung {} (expected 0, 1, or 2)",
                self.alias_rung
            )));
        }
        let sources = self
            .sources
            .into_iter()
            .map(|s| match s {
                SourceToml::FunctionParams { name, params } => {
                    SourceSpec::FunctionParams { name, params }
                }
                SourceToml::GlobalLoad { name } => SourceSpec::GlobalLoad { name },
            })
            .collect();
        let sinks = self
            .sinks
            .into_iter()
            .map(|s| match s {
                SinkToml::Call { name } => SinkSpec::Call { name },
            })
            .collect();
        let mut extra_summaries = Vec::with_capacity(self.extra_summaries.len());
        for s in &self.extra_summaries {
            extra_summaries.push(s.build()?);
        }
        Ok(TaintConfig {
            sources,
            sinks,
            builtin_summaries: self.builtin_summaries,
            extra_summaries,
            seed_all_functions: self.seed_all_functions,
            follow_returns_past_seeds: self.follow_returns_past_seeds,
            native_identity: self.native_identity,
            max_field_chain: self.max_field_chain,
            alias_rung: self.alias_rung,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_config_is_the_driver_defaults() {
        let cfg = parse("").unwrap();
        assert!(cfg.sources.is_empty() && cfg.sinks.is_empty());
        assert!(cfg.builtin_summaries);
        assert!(cfg.seed_all_functions);
        assert!(cfg.follow_returns_past_seeds);
        assert!(cfg.native_identity);
        assert_eq!(
            cfg.max_field_chain,
            abcd_analysis::dataflow::heap::DEFAULT_MAX_FIELD_CHAIN
        );
        assert_eq!(cfg.alias_rung, 2);
    }

    #[test]
    fn full_config_round_trips() {
        let cfg = parse(
            r##"
            builtin_summaries = false
            alias_rung = 1
            max_field_chain = 3

            [[sources]]
            kind = "function_params"
            name = "func_main_0"
            params = [3, 4]

            [[sources]]
            kind = "global_load"
            name = "TAINT"

            [[sinks]]
            kind = "call"
            name = "print"

            [[extra_summaries]]
            name = "sanitize"
            arity = 1
            doc = "identity"
            flows = [ { from = "param:0", to = "return" } ]
            clears = [ "base" ]
            exclusive = true
            callback_param = 2
            "##,
        )
        .unwrap();
        assert_eq!(cfg.sources.len(), 2);
        assert_eq!(
            cfg.sources[0],
            SourceSpec::FunctionParams {
                name: "func_main_0".to_string(),
                params: Some(vec![3, 4]),
            }
        );
        assert_eq!(
            cfg.sources[1],
            SourceSpec::GlobalLoad {
                name: "TAINT".to_string()
            }
        );
        assert_eq!(
            cfg.sinks,
            vec![SinkSpec::Call {
                name: "print".to_string()
            }]
        );
        assert!(!cfg.builtin_summaries);
        assert_eq!(cfg.alias_rung, 1);
        assert_eq!(cfg.max_field_chain, 3);
        let (name, arity, summary) = &cfg.extra_summaries[0];
        assert_eq!(name, "sanitize");
        assert_eq!(*arity, Some(1));
        assert_eq!(summary.doc, "identity");
        assert!(summary.exclusive);
        assert_eq!(summary.flows.len(), 1);
        assert_eq!(summary.clears, vec![Endpoint::Base]);
        assert!(summary.callback.is_some());
    }

    #[test]
    fn bad_toml_is_a_user_error_with_position() {
        let err = parse("kind = [").unwrap_err();
        assert_eq!(err.exit_code(), 1);
        let msg = err.to_string();
        assert!(msg.contains("line"), "{msg}");
        assert!(msg.contains("column"), "{msg}");
    }

    #[test]
    fn wrong_field_type_is_a_user_error_with_position() {
        let err = parse("max_field_chain = \"five\"").unwrap_err();
        assert_eq!(err.exit_code(), 1);
        let msg = err.to_string();
        assert!(msg.contains("line"), "{msg}");
    }

    #[test]
    fn unknown_keys_are_rejected() {
        let err = parse("surces = []").unwrap_err();
        assert_eq!(err.exit_code(), 1);
        assert!(err.to_string().contains("surces"), "{err}");
    }

    #[test]
    fn unknown_source_kind_is_rejected() {
        let err = parse("[[sources]]\nkind = \"env\"\nname = \"x\"").unwrap_err();
        assert_eq!(err.exit_code(), 1);
    }

    #[test]
    fn alias_rung_out_of_range_is_a_user_error() {
        let err = parse("alias_rung = 3").unwrap_err();
        assert_eq!(err.exit_code(), 1);
        assert!(err.to_string().contains("alias_rung"), "{err}");
    }

    #[test]
    fn return_as_flow_source_is_rejected() {
        let err = parse(
            r#"[[extra_summaries]]
            name = "x"
            flows = [ { from = "return", to = "base" } ]
            "#,
        )
        .unwrap_err();
        assert_eq!(err.exit_code(), 1);
        assert!(err.to_string().contains("never a flow source"), "{err}");
    }

    #[test]
    fn bad_endpoint_string_is_a_user_error() {
        let err = parse(
            r#"[[extra_summaries]]
            name = "x"
            flows = [ { from = "param:0", to = "result" } ]
            "#,
        )
        .unwrap_err();
        assert_eq!(err.exit_code(), 1);
        assert!(
            err.to_string().contains("invalid summary endpoint"),
            "{err}"
        );
    }
}
