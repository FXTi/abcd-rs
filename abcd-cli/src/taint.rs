//! `abcd taint` — source→sink taint analysis over one module
//! (design/cli.md §2, design/analysis.md §3).
//!
//! Pipeline: `.abc` → [`abcd_file::decode`] → [`abcd_lift::lift_file`] →
//! [`abcd_taint::run_taint`] with a [`TaintConfig`] parsed from the
//! `--config` TOML file ([`crate::taint_config`]). The report carries
//! every [`abcd_taint::SinkHit`] — sink name, call site, source location, tainted
//! operand position, the fact, the seed it derived from, and the
//! propagation path ([`abcd_taint::PathStep`] sequence) — plus the driver's
//! counters. Text is the human default; `--json` is the same data,
//! machine-readable.

use std::collections::BTreeMap;
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

use abcd_analysis::dataflow::heap::FieldKey;
use abcd_ir::{Loc, Module, Sym};
use abcd_taint::{Fact, TaintBase, TaintConfig, TaintFact, TaintReport};
use serde::Serialize;

use crate::input::InputModule;
use crate::{CliError, ExecContext};

/// Machine-readable taint report of one module (serialized by `--json`).
#[derive(Clone, Debug, Serialize)]
pub struct TaintCliReport {
    /// Module name (container provenance or file stem).
    pub module: String,
    /// Where the bytes came from.
    pub provenance: String,
    /// The effective configuration, for self-describing output.
    pub config: ConfigReport,
    /// Source→sink hits, in the driver's deterministic order.
    pub hits: Vec<HitReport>,
    /// Summary-registry counters.
    pub stats: StatsReport,
    /// Summary hits by builtin/extra name.
    pub summary_hits: BTreeMap<String, usize>,
    /// Named misses — the "report missing" backlog.
    pub summary_misses: BTreeMap<String, usize>,
    /// `(call site, summary name)` applications, in order.
    pub summaries_applied: Vec<SummaryApplication>,
    /// Total propagated path edges (solver work).
    pub path_edges: usize,
    /// Callback-summary sites whose callback resolved to user bodies.
    pub gap_sites_resolved: usize,
    /// Callback-summary sites with an unresolved callback value.
    pub gap_sites_unresolved: usize,
    /// The alias rung the analysis actually ran at (rung 2 can degrade
    /// to rung 1 on the PTA step budget — loud, never silent).
    pub alias_rung_used: u8,
    /// Whether Rung-2 pointer analysis ran in demand-driven root-sliced mode.
    pub pta_root_sliced: bool,
}

/// The effective [`TaintConfig`], echoed for reproducibility.
#[derive(Clone, Debug, Serialize)]
pub struct ConfigReport {
    /// Configured source specs, as rendered strings.
    pub sources: Vec<String>,
    /// Configured sink specs, as rendered strings.
    pub sinks: Vec<String>,
    /// Whether the builtin summary set was registered.
    pub builtin_summaries: bool,
    /// Number of extra (user) summaries.
    pub extra_summaries: usize,
    /// Dummy-main coverage toggle.
    pub seed_all_functions: bool,
    /// heros `followReturnsPastSeeds` toggle.
    pub follow_returns_past_seeds: bool,
    /// Unknown-call identity heuristic toggle.
    pub native_identity: bool,
    /// OpenHarmony Ability/Extension/ArkUI lifecycle harness toggle.
    pub ohos_lifecycle: bool,
    /// Access-path k-limit.
    pub max_field_chain: usize,
    /// Requested alias rung.
    pub alias_rung: u8,
    /// Optional Rung-2 pointer-analysis step budget override.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub pta_step_budget: Option<usize>,
}

/// One source→sink hit.
#[derive(Clone, Debug, Serialize)]
pub struct HitReport {
    /// The sink name that matched.
    pub sink: String,
    /// The sink call instruction's `InstId` arena index.
    pub call: u32,
    /// Source location, when the file carried line info.
    pub location: Option<LocReport>,
    /// Which call operand carried the taint (`arg N`, `this`, `base`,
    /// `callee`).
    pub position: String,
    /// The taint fact at the sink, rendered (e.g. `local v12`,
    /// `global TAINT.x[*]`).
    pub fact: String,
    /// The seed the flow derived from.
    pub seed: SeedReport,
    /// The propagation path, seed-first (best-effort across call/return
    /// anchor switches — the driver's documented approximation).
    pub path: Vec<PathStepReport>,
}

/// A source location (T8: 1-based line, optional 1-based column).
#[derive(Clone, Copy, Debug, Serialize)]
pub struct LocReport {
    /// 1-based source line.
    pub line: u32,
    /// 1-based source column, when present.
    pub column: Option<u32>,
}

/// The seed a hit derived from: an anchor function plus a fact.
#[derive(Clone, Debug, Serialize)]
pub struct SeedReport {
    /// The anchor function's `FuncId` arena index.
    pub function: u32,
    /// The anchor function's resolved name.
    pub function_name: String,
    /// The seed fact, rendered (`zero` for the Λ fact).
    pub fact: String,
}

/// One step of a reported taint path.
#[derive(Clone, Debug, Serialize)]
pub struct PathStepReport {
    /// The instruction's `InstId` arena index.
    pub inst: u32,
    /// Source location, when present.
    pub location: Option<LocReport>,
    /// The `Op` variant tag.
    pub op: String,
}

/// One applied summary.
#[derive(Clone, Debug, Serialize)]
pub struct SummaryApplication {
    /// The call site's `InstId` arena index.
    pub inst: u32,
    /// The summary name.
    pub summary: String,
}

/// The summary-registry counters (abcd-taint `RegistryStats`).
#[derive(Clone, Debug, Serialize)]
pub struct StatsReport {
    /// Summary lookups performed.
    pub lookups: usize,
    /// Negative-cache hits.
    pub negative_cache_hits: usize,
    /// Call sites stepped into (no summary, callee has a body).
    pub sites_body_step: usize,
    /// Call sites conservatively kept (native/builtin fallback).
    pub sites_native_keep: usize,
    /// Call sites with no resolvable name at all.
    pub sites_unknown: usize,
}

/// Read and parse a `--config` TOML file. Read and parse failures are
/// user errors (exit 1); parse errors carry the TOML position.
pub fn load_config(path: &Path) -> Result<TaintConfig, CliError> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| CliError::User(format!("cannot read {}: {e}", path.display())))?;
    crate::taint_config::parse(&text)
        .map_err(|e| CliError::User(format!("{}: {e}", path.display())))
}

/// Build an effective [`TaintConfig`] from optional `--config` TOML and/or
/// `--preset` flags.
pub fn resolve_config(
    config_path: Option<&Path>,
    preset: Option<&str>,
) -> Result<TaintConfig, CliError> {
    let mut cfg = match config_path {
        Some(p) => load_config(p)?,
        None => TaintConfig::default(),
    };
    if let Some(name) = preset {
        crate::taint_config::apply_preset_by_name(&mut cfg, name)?;
    }
    Ok(cfg)
}

/// Decode, lift, and run the taint analysis over one module.
pub fn report(module: &InputModule, config: &TaintConfig) -> Result<TaintCliReport, CliError> {
    report_arc(
        module.name.clone(),
        module.provenance.clone(),
        Arc::clone(&module.abc),
        module.module_json.as_deref(),
        config,
        ExecContext::default(),
    )
}

pub(crate) fn report_owned(
    module: InputModule,
    config: &TaintConfig,
    ctx: ExecContext,
) -> Result<TaintCliReport, CliError> {
    let InputModule {
        name,
        abc,
        module_json,
        provenance,
    } = module;
    let mut run_cfg = config.clone();
    if run_cfg.manifest_json.is_none()
        && let Some(mj) = module_json.as_deref()
        && let Ok(txt) = std::str::from_utf8(mj)
    {
        run_cfg.manifest_json = Some(txt.to_owned());
    }
    drop(module_json);
    run_single_with_cfg(name, provenance, abc, run_cfg, ctx)
}

fn report_arc(
    name: String,
    provenance: String,
    abc: Arc<[u8]>,
    module_json: Option<&[u8]>,
    config: &TaintConfig,
    ctx: ExecContext,
) -> Result<TaintCliReport, CliError> {
    let mut run_cfg = config.clone();
    if run_cfg.manifest_json.is_none()
        && let Some(mj) = module_json
        && let Ok(txt) = std::str::from_utf8(mj)
    {
        run_cfg.manifest_json = Some(txt.to_owned());
    }
    run_single_with_cfg(name, provenance, abc, run_cfg, ctx)
}

fn run_single_with_cfg(
    name: String,
    provenance: String,
    abc: Arc<[u8]>,
    run_cfg: TaintConfig,
    ctx: ExecContext,
) -> Result<TaintCliReport, CliError> {
    let lift_opts = abcd_lift::LiftOptions {
        retain_tail_capacity: run_cfg.ohos_lifecycle,
        parallel: true,
    };
    let ir = crate::lift_abc_arc(abc, &name, &provenance, &lift_opts, ctx)?;
    let t_taint = ctx.timings.then(Instant::now);
    let prepared = abcd_taint::PreparedModule::owned(ir, &run_cfg);
    let report = abcd_taint::run_taint_prepared(&prepared, &run_cfg);
    let out = build_report(&name, &provenance, &run_cfg, prepared.module(), &report);
    if let Some(start) = t_taint {
        crate::log_timing(true, &name, "taint", start.elapsed());
    }
    Ok(out)
}

/// Decode, lift, link all `modules` into one unified [`Module`] via
/// [`abcd_analysis::module_link::merge_ir_modules_owned`], and run
/// whole-application cross-module taint analysis.
pub fn report_linked(
    modules: &[InputModule],
    config: &TaintConfig,
) -> Result<TaintCliReport, CliError> {
    if modules.len() == 1 {
        return report(&modules[0], config);
    }
    let lift_opts = abcd_lift::LiftOptions {
        retain_tail_capacity: config.ohos_lifecycle,
        parallel: true,
    };
    let mut manifests = Vec::new();
    let mut names = Vec::with_capacity(modules.len());
    let mut provs = Vec::with_capacity(modules.len());
    let mut first_err: Option<CliError> = None;
    let stream = modules.iter().map_while(|m| {
        if let Some(mj) = m.module_json.as_deref()
            && let Ok(txt) = std::str::from_utf8(mj)
        {
            manifests.push(txt.to_owned());
        }
        match crate::lift_abc_arc(
            Arc::clone(&m.abc),
            &m.name,
            &m.provenance,
            &lift_opts,
            ExecContext::default(),
        ) {
            Ok(ir) => {
                names.push(m.name.clone());
                provs.push(m.provenance.clone());
                Some((m.name.clone(), ir))
            }
            Err(e) => {
                first_err = Some(e);
                None
            }
        }
    });
    let merged_ir = abcd_analysis::module_link::merge_ir_modules_owned(stream);
    if let Some(err) = first_err {
        return Err(err);
    }
    let mut run_cfg = config.clone();
    if run_cfg.manifest_json.is_none() && !manifests.is_empty() {
        run_cfg.manifest_json = Some(manifests.join("\n"));
    }
    let linked_name = names.join("+");
    let linked_prov = provs.join(" + ");
    let prepared = abcd_taint::PreparedModule::owned(merged_ir, &run_cfg);
    let rep = abcd_taint::run_taint_prepared(&prepared, &run_cfg);
    Ok(build_report(
        &linked_name,
        &linked_prov,
        &run_cfg,
        prepared.module(),
        &rep,
    ))
}

pub(crate) fn report_linked_owned(
    mut modules: Vec<InputModule>,
    config: &TaintConfig,
    ctx: ExecContext,
) -> Result<TaintCliReport, CliError> {
    if modules.len() == 1 {
        return report_owned(modules.swap_remove(0), config, ctx);
    }
    let lift_opts = abcd_lift::LiftOptions {
        retain_tail_capacity: config.ohos_lifecycle,
        parallel: true,
    };
    let mut manifests = Vec::new();
    let mut names = Vec::with_capacity(modules.len());
    let mut provs = Vec::with_capacity(modules.len());
    let mut first_err: Option<CliError> = None;
    let stream = modules.into_iter().map_while(|m| {
        let InputModule {
            name,
            abc,
            module_json,
            provenance,
        } = m;
        if let Some(mj) = module_json.as_deref()
            && let Ok(txt) = std::str::from_utf8(mj)
        {
            manifests.push(txt.to_owned());
        }
        drop(module_json);
        match crate::lift_abc_arc(abc, &name, &provenance, &lift_opts, ctx) {
            Ok(ir) => {
                names.push(name.clone());
                provs.push(provenance);
                Some((name, ir))
            }
            Err(e) => {
                first_err = Some(e);
                None
            }
        }
    });
    let merged_ir = abcd_analysis::module_link::merge_ir_modules_owned(stream);
    if let Some(err) = first_err {
        return Err(err);
    }
    let linked_name = names.join("+");
    let linked_prov = provs.join(" + ");
    let mut run_cfg = config.clone();
    if run_cfg.manifest_json.is_none() && !manifests.is_empty() {
        run_cfg.manifest_json = Some(manifests.join("\n"));
    }
    let t_taint = ctx.timings.then(Instant::now);
    let prepared = abcd_taint::PreparedModule::owned(merged_ir, &run_cfg);
    let rep = abcd_taint::run_taint_prepared(&prepared, &run_cfg);
    let out = build_report(
        &linked_name,
        &linked_prov,
        &run_cfg,
        prepared.module(),
        &rep,
    );
    if let Some(start) = t_taint {
        crate::log_timing(true, &linked_name, "taint", start.elapsed());
    }
    Ok(out)
}

/// Project the driver's [`TaintReport`] onto the serializable CLI
/// report (name/fact resolution happens here, against the prepared module's
/// symbol table so harness-interned symbols such as `"context"` resolve).
fn build_report(
    module_name: &str,
    provenance: &str,
    config: &TaintConfig,
    ir: &Module,
    report: &TaintReport,
) -> TaintCliReport {
    let hits = report
        .hits
        .iter()
        .map(|h| HitReport {
            sink: h.sink.clone(),
            call: h.call.index() as u32,
            location: h.loc.map(loc_report),
            position: h.position.clone(),
            fact: render_fact(ir, &h.fact),
            seed: SeedReport {
                function: h.seed.0.index() as u32,
                function_name: ir
                    .func(h.seed.0)
                    .and_then(|f| ir.sym.resolve(f.name))
                    .unwrap_or("<unnamed>")
                    .to_string(),
                fact: render_seed_fact(ir, &h.seed.1),
            },
            path: h
                .path
                .iter()
                .map(|s| PathStepReport {
                    inst: s.inst.index() as u32,
                    location: s.loc.map(loc_report),
                    op: s.op.clone(),
                })
                .collect(),
        })
        .collect();
    TaintCliReport {
        module: module_name.to_string(),
        provenance: provenance.to_string(),
        config: ConfigReport {
            sources: config.sources.iter().map(|s| format!("{s:?}")).collect(),
            sinks: config.sinks.iter().map(|s| format!("{s:?}")).collect(),
            builtin_summaries: config.builtin_summaries,
            extra_summaries: config.extra_summaries.len(),
            seed_all_functions: config.seed_all_functions,
            follow_returns_past_seeds: config.follow_returns_past_seeds,
            native_identity: config.native_identity,
            ohos_lifecycle: config.ohos_lifecycle,
            max_field_chain: config.max_field_chain,
            alias_rung: config.alias_rung,
            pta_step_budget: config.pta_step_budget,
        },
        hits,
        stats: StatsReport {
            lookups: report.stats.lookups,
            negative_cache_hits: report.stats.negative_cache_hits,
            sites_body_step: report.stats.sites_body_step,
            sites_native_keep: report.stats.sites_native_keep,
            sites_unknown: report.stats.sites_unknown,
        },
        summary_hits: report.summary_hits.clone(),
        summary_misses: report.summary_misses.clone(),
        summaries_applied: report
            .summaries_applied
            .iter()
            .map(|(iid, name)| SummaryApplication {
                inst: iid.index() as u32,
                summary: name.clone(),
            })
            .collect(),
        path_edges: report.path_edges,
        gap_sites_resolved: report.gap_sites_resolved,
        gap_sites_unresolved: report.gap_sites_unresolved,
        alias_rung_used: report.alias_rung_used,
        pta_root_sliced: report.pta_root_sliced,
    }
}

fn loc_report(loc: Loc) -> LocReport {
    LocReport {
        line: loc.line,
        column: loc.column,
    }
}

/// Render a fact access path with the module's names resolved.
fn render_fact(ir: &Module, fact: &TaintFact) -> String {
    let mut out = match &fact.base {
        TaintBase::Local(v) => format!("local v{}", v.index()),
        TaintBase::Heap(sites) => {
            let inner = sites
                .iter()
                .map(|i| format!("i{}", i.index()))
                .collect::<Vec<_>>()
                .join(", ");
            format!("heap {{{inner}}}")
        }
        TaintBase::Global(sym) => format!("global {}", resolve_sym(ir, *sym)),
        TaintBase::ModuleVar(cid, slot) => {
            if cid.index() == 0 && ir.classes.len() <= 1 {
                format!("modulevar {slot}")
            } else {
                format!("modulevar c{}:{slot}", cid.index())
            }
        }
        TaintBase::LexVar(level, slot) => format!("lexvar {level}:{slot}"),
    };
    for key in fact.fields.elements() {
        match key {
            FieldKey::Named(sym) => {
                out.push('.');
                out.push_str(&resolve_sym(ir, *sym));
            }
            FieldKey::AnyIndex => out.push_str("[*]"),
            FieldKey::AnyDynamic => out.push_str("[dyn]"),
        }
    }
    out
}

/// Render a seed fact (the Λ fact reads `zero`).
fn render_seed_fact(ir: &Module, fact: &Fact) -> String {
    match fact {
        Fact::Zero => "zero".to_string(),
        Fact::Taint(t) => render_fact(ir, t),
    }
}

fn resolve_sym(ir: &Module, sym: Sym) -> String {
    ir.sym
        .resolve(sym)
        .map(str::to_string)
        .unwrap_or_else(|| format!("<sym {}>", sym.index()))
}

/// Human-readable rendering of one report (goes to stdout).
pub fn render_text(report: &TaintCliReport) -> String {
    let c = &report.config;
    let mut out = format!(
        "module:          {} ({})\n\
         sources:         {}\n\
         sinks:           {}\n\
         summaries:       {} builtin, {} extra\n\
         alias rung:      {} (used {})\n",
        report.module,
        report.provenance,
        c.sources.len(),
        c.sinks.len(),
        if c.builtin_summaries { "on" } else { "off" },
        c.extra_summaries,
        c.alias_rung,
        report.alias_rung_used,
    );
    if let Some(budget) = c.pta_step_budget {
        out.push_str(&format!("pta budget:      {budget}\n"));
    }
    out.push_str(&format!("pta root sliced: {}\n", report.pta_root_sliced));
    out.push_str(&format!("path edges:      {}\n", report.path_edges));

    out.push_str(&format!("\nhits: {}\n", report.hits.len()));
    for (i, h) in report.hits.iter().enumerate() {
        out.push_str(&format!(
            "[{}] sink {} (call i{}, {}) fact: {}\n",
            i + 1,
            h.sink,
            h.call,
            h.position,
            h.fact,
        ));
        if let Some(loc) = h.location {
            out.push_str(&format!("    at {}\n", render_loc(loc)));
        }
        out.push_str(&format!(
            "    seed: fn {} {}, fact {}\n",
            h.seed.function, h.seed.function_name, h.seed.fact
        ));
        if !h.path.is_empty() {
            out.push_str("    path:\n");
            for step in &h.path {
                let loc = step
                    .location
                    .map(|l| format!(" ({})", render_loc(l)))
                    .unwrap_or_default();
                out.push_str(&format!("      i{}  {}{}\n", step.inst, step.op, loc));
            }
        }
    }

    let st = &report.stats;
    out.push_str(&format!(
        "\nstats: lookups={} neg-cache={} body-step={} native-keep={} unknown={}\n",
        st.lookups,
        st.negative_cache_hits,
        st.sites_body_step,
        st.sites_native_keep,
        st.sites_unknown
    ));
    let hits_line = render_name_counts(&report.summary_hits);
    out.push_str(&format!("summary hits: {hits_line}\n"));
    let misses_line = render_name_counts(&report.summary_misses);
    out.push_str(&format!("summary misses: {misses_line}\n"));
    out
}

fn render_loc(loc: LocReport) -> String {
    match loc.column {
        Some(col) => format!("line {}, col {}", loc.line, col),
        None => format!("line {}", loc.line),
    }
}

fn render_name_counts(counts: &BTreeMap<String, usize>) -> String {
    if counts.is_empty() {
        return "(none)".to_string();
    }
    counts
        .iter()
        .map(|(name, n)| format!("{name}={n}"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// Render reports per `--json`: a single module yields one object,
/// several modules yield an array.
pub fn render(reports: &[TaintCliReport], json: bool) -> Result<String, CliError> {
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
