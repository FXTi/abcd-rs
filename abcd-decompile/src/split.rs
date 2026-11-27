//! Multi-module `--merge-abc` directory-tree splitter (`--split-modules`, #26).
//!
//! Partitions a lifted [`abcd_ir::Module`] by its owning record classes
//! ([`abcd_ir::ClassData`]) into safe relative file paths (`.js` / `.ts` /
//! `.ets` and `.json`), resolving per-record ES module slots (`RegularImport`,
//! `NamespaceImport`, and `LocalExport`) without cross-record slot collisions
//! and rewriting internal OHMUrl (`@bundle:`, `@package:`, `@normalized:`)
//! specifiers into navigable POSIX relative imports.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::convert::Infallible;

use abcd_analysis::OhmUrl;
use abcd_ir::consts::Const;
use abcd_ir::id::{ClassId, FuncId};
use abcd_ir::module::{ClassData, EsModule, ExportDecl, FunctionKind, Module};
use abcd_ir::op::{ModuleVarKind, Op};
use rayon::prelude::*;

use crate::consts::{render_pool_string, render_sym_string, sym_str};
use crate::emit::{
    BatchLimits, DecompileStats, EmitOptions, Emitter, ORPHAN_SCAN_BATCH, PreparedFunc,
    accumulate_decompile_stats, collect_orphans_for_funcs, consumed_functions, emit_esm_imports,
    func_may_have_orphan_lexenv, index_has_fallback_module_slot, module_facing_name,
    next_bounded_top_batch, orphan_lexenv_names_in_func, precompute_func_inst_weights,
    prepare_func, prepare_func_only, try_extend_batch_funcs,
};
use crate::legalize::{Legalizer, sanitize};
use crate::names::{DecompileIndex, module_slot_fallback};
use crate::recover::recover_func_with_index;

/// Kind of a split output file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SplitFileKind {
    /// An ECMAScript module record (`import` / `export` metadata present).
    Module,
    /// A script/CommonJS record without ES module metadata.
    Script,
    /// A `--merge-abc` JSON asset record (`jsonFileContent` field).
    Json,
}

/// One file produced by [`decompile_module_split`] or [`decompile_module_split_each`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplitFile {
    /// Safe POSIX-separated relative output path (e.g. `"pages/Index.js"` or
    /// `"cfg.json"`), guaranteed free of `..`, leading `/`, drive prefixes,
    /// and Windows reserved device names.
    pub rel_path: String,
    /// Canonical record name inside the `.abc` container (descriptor stripped
    /// of surrounding `L...;`, with `/` separators normalized as in `.abc`
    /// record names).
    pub record_name: String,
    /// Kind of this record (`Module`, `Script`, or `Json`).
    pub kind: SplitFileKind,
    /// Emitted source or JSON payload.
    pub text: String,
    /// Per-file decompile statistics (zeroed for `Json` records).
    pub stats: DecompileStats,
}

/// Multi-file decompile output for a `--merge-abc` (or single-record) [`Module`].
#[derive(Clone, Debug)]
pub struct SplitDecompiledModule {
    /// Emitted files in deterministic class-table order.
    pub files: Vec<SplitFile>,
    /// Aggregate decompile statistics summed across all emitted files.
    pub stats: DecompileStats,
}

/// Synthetic/compiler metadata record descriptors that never correspond to
/// user source files in `--merge-abc` bundles.
const SYNTHETIC_DESCRIPTORS: &[&str] = &[
    "L_ESModuleRecord;",
    "L_ESScopeNamesRecord;",
    "L_ModuleRequestPhaseRecord;",
    "L_ESSlotNumberAnnotation;",
    "L_ESConcurrentModuleRequestsAnnotation;",
];

/// Windows reserved device basenames (case-insensitive) that must not be
/// emitted raw onto portable filesystems.
const WINDOWS_RESERVED: &[&str] = &[
    "CON", "PRN", "AUX", "NUL", "CONIN$", "CONOUT$", "COM0", "COM1", "COM2", "COM3", "COM4",
    "COM5", "COM6", "COM7", "COM8", "COM9", "LPT0", "LPT1", "LPT2", "LPT3", "LPT4", "LPT5", "LPT6",
    "LPT7", "LPT8", "LPT9",
];

/// Normalize an `.abc` class descriptor or OHMUrl record identifier into a
/// safe relative file path with extension `ext` (e.g. `"js"`, `"ts"`, `"ets"`,
/// or `"json"` when `is_json` is `true`).
///
/// Returns `None` for compiler-internal metadata records (`L_ESModuleRecord;`,
/// `L_ESSlotNumberAnnotation;`, etc.) and external `@ohos.*` / `@system.*`
/// SDK stub records.
pub fn normalize_record_path(descriptor: &str, is_json: bool, ext: &str) -> Option<String> {
    if SYNTHETIC_DESCRIPTORS.contains(&descriptor) {
        return None;
    }
    let raw = OhmUrl::strip_descriptor(descriptor);
    if raw.is_empty() {
        return None;
    }
    // External system/SDK/native stub descriptors (`@ohos.*`, `@hms:*`, `@kit.*`,
    // `@arkts.*`, `@system.*`, `@native:*`, `@normalized:Y&...`) are foreign
    // references, not bundled user files.
    if OhmUrl::is_sdk_specifier(raw) {
        return None;
    }

    let logical = OhmUrl::peel_import_path(raw);
    let mut segments = Vec::new();
    for part in logical.split(['/', '\\']) {
        let trimmed = part.trim();
        if trimmed.is_empty() || trimmed == "." || trimmed == ".." {
            continue;
        }
        let clean = sanitize_path_segment(trimmed);
        if !clean.is_empty() && clean != "." && clean != ".." {
            segments.push(clean);
        }
    }
    if segments.is_empty() {
        segments.push("index".to_string());
    }

    let target_ext = if is_json { "json" } else { ext };
    if let Some(last) = segments.last_mut() {
        // Strip existing matching source extension before appending `target_ext`.
        for known in [
            ".d.ets", ".d.ts", ".ets", ".ts", ".mjs", ".cjs", ".js", ".json",
        ] {
            if last.len() > known.len() && last.ends_with(known) {
                last.truncate(last.len() - known.len());
                break;
            }
        }
        let trimmed = last.trim_end_matches(['.', ' ']).to_string();
        *last = if trimmed.is_empty() {
            "_".to_string()
        } else {
            escape_windows_reserved_segment(&trimmed)
        };
        last.push('.');
        last.push_str(target_ext);
    }
    for seg in segments.iter_mut().rev().skip(1) {
        *seg = escape_windows_reserved_segment(seg);
    }
    Some(segments.join("/"))
}

fn sanitize_path_segment(seg: &str) -> String {
    let mut out = String::with_capacity(seg.len());
    for ch in seg.chars() {
        if ch.is_control() || matches!(ch, '<' | '>' | ':' | '"' | '|' | '?' | '*' | '\0') {
            out.push('_');
        } else {
            out.push(ch);
        }
    }
    let trimmed = out.trim_end_matches(['.', ' ']);
    trimmed.to_string()
}

/// Escape Windows reserved device names on the stem BEFORE the first `.`
/// (`aux.config` -> `aux_.config`, `CONIN$` -> `CONIN$_`), and strip any
/// trailing dots/spaces before `.` so segments are portable across NTFS/APFS/ext4.
fn escape_windows_reserved_segment(seg: &str) -> String {
    let (raw_stem, rest) = match seg.find('.') {
        Some(dot) => (&seg[..dot], &seg[dot..]),
        None => (seg, ""),
    };
    if raw_stem.is_empty() {
        return seg.to_string();
    }
    let stem = raw_stem.trim_end_matches(['.', ' ']);
    if stem.is_empty() {
        return format!("_{rest}");
    }
    if WINDOWS_RESERVED
        .iter()
        .any(|&r| stem.eq_ignore_ascii_case(r))
    {
        format!("{stem}_{rest}")
    } else if stem.len() != raw_stem.len() {
        format!("{stem}{rest}")
    } else {
        seg.to_string()
    }
}

/// Whether `cls` carries a `--merge-abc` `jsonFileContent` string field.
fn has_json_content(module: &Module, cls: &ClassData) -> bool {
    cls.fields.iter().any(|f| {
        sym_str(module, f.name) == "jsonFileContent"
            && f.initial_value
                .and_then(|cid| module.consts.get(cid))
                .is_some_and(|c| matches!(c, Const::String(_)))
    })
}

/// Extract the JSON payload from a `--merge-abc` JSON record class
/// (`jsonFileContent` field carrying a `Const::String`).
fn json_content_of(module: &Module, cls: &ClassData) -> Option<String> {
    for f in &cls.fields {
        if sym_str(module, f.name) == "jsonFileContent"
            && let Some(cid) = f.initial_value
            && let Some(Const::String(sym)) = module.consts.get(cid)
        {
            let mut s = sym_str(module, *sym);
            if !s.is_empty() && !s.ends_with('\n') {
                s.push('\n');
            }
            return Some(s);
        }
    }
    None
}

/// Partition and decompile `module` into a multi-file directory tree.
///
/// - On `--merge-abc` bundles, emits one `.js`/`.ts`/`.ets` or `.json` file per
///   bundled record class, isolating per-record `EsModule` slot bindings and
///   rewriting internal OHMUrl module specifiers into relative POSIX imports.
/// - On standalone single-module `.abc` files (`L_GLOBAL;`), emits a single
///   file named after `L_GLOBAL;`'s `source_file` (or `index.<ext>`).
pub fn decompile_module_split(module: &Module, opts: &EmitOptions) -> SplitDecompiledModule {
    let mut files = Vec::new();
    let stats = match decompile_module_split_each(module, opts, |sf| -> Result<(), Infallible> {
        files.push(sf);
        Ok(())
    }) {
        Ok(stats) => stats,
        Err(never) => match never {},
    };
    SplitDecompiledModule { files, stats }
}

/// Test-only helper exposing [`decompile_module_split`] with custom [`BatchLimits`].
#[cfg(test)]
pub(crate) fn split_with_limits(
    module: &Module,
    opts: &EmitOptions,
    limits: BatchLimits,
) -> SplitDecompiledModule {
    let mut files = Vec::new();
    let stats = match decompile_module_split_each_with_limits(
        module,
        opts,
        limits,
        |sf| -> Result<(), Infallible> {
            files.push(sf);
            Ok(())
        },
    ) {
        Ok(stats) => stats,
        Err(never) => match never {},
    };
    SplitDecompiledModule { files, stats }
}

/// Partition and stream each emitted [`SplitFile`] of `module` in deterministic
/// class-table order to `on_file` without buffering all function ASTs or all
/// [`SplitFile`] payloads in memory.
///
/// Records are prepared in adaptive parallel batches capped at `65,536`
/// deduplicated transitive instructions (`MAX_BATCH_PREPARED_INSTS`) and `512`
/// transitive functions (`MAX_BATCH_PREPARED_FUNCS`), delivered one-by-one to
/// `on_file` in exact `planned` order, and their ASTs are dropped before
/// starting the next batch. Behavior, file contents, and [`DecompileStats`] are
/// 100% shared and byte-identical with [`decompile_module_split`].
pub fn decompile_module_split_each<F, E>(
    module: &Module,
    opts: &EmitOptions,
    on_file: F,
) -> Result<DecompileStats, E>
where
    F: FnMut(SplitFile) -> Result<(), E>,
{
    decompile_module_split_each_with_limits(module, opts, BatchLimits::default(), on_file)
}

pub(crate) fn decompile_module_split_each_with_limits<F, E>(
    module: &Module,
    opts: &EmitOptions,
    limits: BatchLimits,
    mut on_file: F,
) -> Result<DecompileStats, E>
where
    F: FnMut(SplitFile) -> Result<(), E>,
{
    let ext = if opts.arkui {
        "ets"
    } else if opts.ts {
        "ts"
    } else {
        "js"
    };

    let consumed = consumed_functions(module);
    let inst_weights = precompute_func_inst_weights(module);
    let index = DecompileIndex::build_split(module);
    let has_fallback_slot = index_has_fallback_module_slot(&index);

    // Group all functions and top-level unconsumed functions by `ClassId`.
    let mut class_all_funcs: HashMap<ClassId, Vec<FuncId>> = HashMap::new();
    let mut class_funcs: HashMap<ClassId, Vec<FuncId>> = HashMap::new();
    for (fi, fdata) in module.functions.iter().enumerate() {
        let fid = FuncId::new(fi as u32);
        class_all_funcs.entry(fdata.class_id).or_default().push(fid);
        if !consumed.contains(&fid) {
            class_funcs.entry(fdata.class_id).or_default().push(fid);
        }
    }

    // Plan output paths for all non-synthetic records first so cross-record
    // OHMUrl imports can resolve to exact relative paths.
    let is_standalone = is_standalone_single_module(module);
    let mut planned: Vec<PlannedRecord> = Vec::new();
    let mut used_paths: BTreeSet<String> = BTreeSet::new();

    for (ci, cls) in module.classes.iter().enumerate() {
        let cid = ClassId::new(ci as u32);
        let desc = sym_str(module, cls.descriptor);
        if SYNTHETIC_DESCRIPTORS.contains(&desc.as_str()) {
            continue;
        }
        let is_json = has_json_content(module, cls);
        let has_funcs = class_funcs.get(&cid).is_some_and(|v| !v.is_empty());
        let has_esm = cls.es_module.is_some()
            || (is_standalone
                && desc == "L_GLOBAL;"
                && (!module.imports.is_empty()
                    || !module.exports.is_empty()
                    || !module.module_requests.is_empty()));
        if !is_json && !has_funcs && !has_esm {
            continue;
        }

        let base_path = if is_standalone && desc == "L_GLOBAL;" {
            cls.source_file
                .map(|sf| sym_str(module, sf))
                .and_then(|sf| normalize_record_path(&sf, false, ext))
                .unwrap_or_else(|| format!("index.{ext}"))
        } else {
            match normalize_record_path(&desc, is_json, ext) {
                Some(p) => p,
                None => continue,
            }
        };

        let rel_path = disambiguate_path(base_path, &mut used_paths);
        let record_name = OhmUrl::strip_descriptor(&desc).to_string();
        let kind = if is_json {
            SplitFileKind::Json
        } else if has_esm {
            SplitFileKind::Module
        } else {
            SplitFileKind::Script
        };
        planned.push(PlannedRecord {
            cid,
            rel_path,
            record_name,
            kind,
        });
    }

    // Build specifier → planned-index lookup table for internal OHMUrl & JSON resolution.
    let mut spec_to_idx: HashMap<String, usize> = HashMap::new();
    for (idx, p) in planned.iter().enumerate() {
        for key in candidate_record_keys(&p.record_name, &p.rel_path) {
            spec_to_idx.entry(key).or_insert(idx);
        }
    }

    let max_records_per_batch = limits.max_funcs.max(1);
    let mut total_stats = DecompileStats::default();
    let mut batch_start = 0usize;

    while batch_start < planned.len() {
        let mut visited_fids: BTreeSet<FuncId> = BTreeSet::new();
        let mut batch_inst_weight = 0usize;
        let mut single_oversized = false;
        let mut batch_end = batch_start;

        while batch_end < planned.len() && batch_end - batch_start < max_records_per_batch {
            let plan = &planned[batch_end];
            if plan.kind == SplitFileKind::Json {
                batch_end += 1;
                continue;
            }
            let tfs = class_funcs.get(&plan.cid).map(Vec::as_slice).unwrap_or(&[]);
            if batch_end == batch_start {
                if tfs.len() <= 1 {
                    let _ = try_extend_batch_funcs(
                        module,
                        &inst_weights,
                        tfs,
                        &mut visited_fids,
                        &mut batch_inst_weight,
                        None,
                    );
                } else if !try_extend_batch_funcs(
                    module,
                    &inst_weights,
                    tfs,
                    &mut visited_fids,
                    &mut batch_inst_weight,
                    Some(limits),
                ) {
                    single_oversized = true;
                    batch_end = batch_start + 1;
                    break;
                }
                batch_end = batch_start + 1;
                if visited_fids.len() >= limits.max_funcs || batch_inst_weight >= limits.max_insts {
                    break;
                }
            } else {
                if !try_extend_batch_funcs(
                    module,
                    &inst_weights,
                    tfs,
                    &mut visited_fids,
                    &mut batch_inst_weight,
                    Some(limits),
                ) {
                    break;
                }
                batch_end += 1;
                if visited_fids.len() >= limits.max_funcs || batch_inst_weight >= limits.max_insts {
                    break;
                }
            }
        }

        let batch_plans = &planned[batch_start..batch_end];
        let mut batch_prepared: BTreeMap<FuncId, PreparedFunc> = BTreeMap::new();
        let mut batch_orphans: HashMap<ClassId, BTreeSet<String>> = HashMap::new();

        if single_oversized {
            let cid = batch_plans[0].cid;
            if let Some(all_fids) = class_all_funcs.get(&cid) {
                let orphans =
                    collect_orphans_for_funcs(module, &index, all_fids, has_fallback_slot);
                if !orphans.is_empty() {
                    batch_orphans.insert(cid, orphans);
                }
            }
        } else {
            let batch_cids: HashSet<ClassId> = batch_plans
                .iter()
                .filter(|p| p.kind != SplitFileKind::Json)
                .map(|p| p.cid)
                .collect();
            let emit_fids: Vec<FuncId> = visited_fids.iter().copied().collect();

            let mut extra_orphan_fids: Vec<FuncId> = Vec::new();
            for plan in batch_plans {
                if plan.kind == SplitFileKind::Json {
                    continue;
                }
                if let Some(all_fids) = class_all_funcs.get(&plan.cid) {
                    for &fid in all_fids {
                        if !visited_fids.contains(&fid)
                            && func_may_have_orphan_lexenv(module, fid, &index, has_fallback_slot)
                        {
                            extra_orphan_fids.push(fid);
                        }
                    }
                }
            }

            type BatchPrepItem = (FuncId, PreparedFunc, Option<(ClassId, BTreeSet<String>)>);
            let prepared_and_orphans: Vec<BatchPrepItem> = emit_fids
                .into_par_iter()
                .map(|fid| {
                    let top_level = !consumed.contains(&fid);
                    let owner_cid = module.func(fid).map(|fd| fd.class_id);
                    let need_orphans = owner_cid.is_some_and(|c| batch_cids.contains(&c))
                        && func_may_have_orphan_lexenv(module, fid, &index, has_fallback_slot);
                    if let Some(cid) = owner_cid
                        && need_orphans
                    {
                        let (pre, orphans) = prepare_func(module, Some(&index), fid, top_level);
                        (fid, pre, Some((cid, orphans)))
                    } else {
                        let pre = prepare_func_only(module, Some(&index), fid, top_level);
                        (fid, pre, None)
                    }
                })
                .collect();

            for (fid, pre, maybe_orphans) in prepared_and_orphans {
                batch_prepared.insert(fid, pre);
                if let Some((cid, orphans)) = maybe_orphans
                    && !orphans.is_empty()
                {
                    batch_orphans.entry(cid).or_default().extend(orphans);
                }
            }

            for chunk in extra_orphan_fids.chunks(ORPHAN_SCAN_BATCH) {
                let extra: Vec<(ClassId, BTreeSet<String>)> = chunk
                    .par_iter()
                    .filter_map(|&fid| {
                        let cid = module.func(fid)?.class_id;
                        let rf = recover_func_with_index(module, fid, &index);
                        let orphans = orphan_lexenv_names_in_func(&rf);
                        (!orphans.is_empty()).then_some((cid, orphans))
                    })
                    .collect();
                for (cid, orphans) in extra {
                    batch_orphans.entry(cid).or_default().extend(orphans);
                }
            }
        }

        for (offset, plan) in batch_plans.iter().enumerate() {
            let my_idx = batch_start + offset;
            if plan.kind == SplitFileKind::Json {
                let json_text =
                    json_content_of(module, &module.classes[plan.cid.index()]).unwrap_or_default();
                on_file(SplitFile {
                    rel_path: plan.rel_path.clone(),
                    record_name: plan.record_name.clone(),
                    kind: SplitFileKind::Json,
                    text: json_text,
                    stats: DecompileStats::default(),
                })?;
                continue;
            }

            let cls = &module.classes[plan.cid.index()];
            let fallback_esm;
            let esm: Option<&EsModule> = if let Some(e) = &cls.es_module {
                Some(e)
            } else if is_standalone
                && (!module.imports.is_empty()
                    || !module.exports.is_empty()
                    || !module.module_requests.is_empty())
            {
                fallback_esm = EsModule {
                    imports: module.imports.clone(),
                    exports: module.exports.clone(),
                    module_requests: module.module_requests.clone(),
                };
                Some(&fallback_esm)
            } else {
                None
            };

            let record_funcs: &[FuncId] = &cls.methods;
            let top_funcs = class_funcs.get(&plan.cid).map(Vec::as_slice).unwrap_or(&[]);
            let orphans = batch_orphans.remove(&plan.cid).unwrap_or_default();

            let mut em = Emitter {
                module,
                index: Some(&index),
                opts,
                stats: DecompileStats::default(),
                fn_names: Legalizer::new(),
                current_fn_has_fallback: false,
                current_kind: FunctionKind::Function,
                class_depth: 0,
                hoisted: BTreeSet::new(),
                prepared: std::mem::take(&mut batch_prepared),
                emitting_funcs: HashSet::new(),
                arkui_components: HashMap::new(),
            };

            let text = emit_single_record(
                &mut em,
                plan.cid,
                &plan.rel_path,
                esm,
                record_funcs,
                top_funcs,
                orphans,
                &consumed,
                &inst_weights,
                limits,
                single_oversized,
                &planned,
                &spec_to_idx,
                my_idx,
            );
            batch_prepared = std::mem::take(&mut em.prepared);
            let file_stats = em.stats;
            accumulate_decompile_stats(&mut total_stats, &file_stats);
            on_file(SplitFile {
                rel_path: plan.rel_path.clone(),
                record_name: plan.record_name.clone(),
                kind: plan.kind,
                text,
                stats: file_stats,
            })?;
        }

        // `batch_prepared` and `batch_orphans` drop here before the next batch.
        batch_start = batch_end;
    }

    Ok(total_stats)
}

fn is_standalone_single_module(module: &Module) -> bool {
    let mut non_synth = 0usize;
    let mut has_global = false;
    for cls in &module.classes {
        let desc = sym_str(module, cls.descriptor);
        if SYNTHETIC_DESCRIPTORS.contains(&desc.as_str()) {
            continue;
        }
        if cls.methods.is_empty() && cls.es_module.is_none() && !has_json_content(module, cls) {
            continue;
        }
        non_synth += 1;
        if desc == "L_GLOBAL;" {
            has_global = true;
        }
    }
    non_synth == 1 && has_global
}

fn disambiguate_path(base: String, used: &mut BTreeSet<String>) -> String {
    if used.insert(base.to_ascii_lowercase()) {
        return base;
    }
    let (stem, ext) = match base.rfind('.') {
        Some(dot) => (&base[..dot], &base[dot..]),
        None => (base.as_str(), ""),
    };
    let mut n = 1usize;
    loop {
        let cand = format!("{stem}${n}{ext}");
        if used.insert(cand.to_ascii_lowercase()) {
            return cand;
        }
        n += 1;
    }
}

fn candidate_record_keys(record_name: &str, rel_path: &str) -> Vec<String> {
    let mut keys = vec![record_name.to_string()];
    let no_ext = strip_known_ext(rel_path);
    keys.push(no_ext.to_string());
    // OHMUrl `@bundle:bundleName/moduleName/ets/...`: note `hvigor` often emits
    // record descriptors like `bundleName/moduleName/ets/...` (with `.` or `/`)
    // while `MODULE_REQUEST_ARRAY` writes `@bundle:bundleName/moduleName@har/ets/...`.
    if let Some((left, right)) = record_name.split_once("@") {
        keys.push(format!("{left}/{right}"));
    }
    // Dotted hvigor package descriptor (`com.example.app.entry.ets.pages.Index`
    // or `pkg_modules..ohpm...`): normalize `.` runs into `/` paths when
    // unambiguous for `@package:` / `@bundle:` matching.
    keys.push(OhmUrl::peel_import_path(record_name).to_string());
    if let Some(u) = OhmUrl::parse(record_name)
        && !u.bundle_name.is_empty()
    {
        keys.push(format!("{}/{}", u.bundle_name, u.import_path));
    }
    keys
}

fn strip_known_ext(path: &str) -> &str {
    for ext in [".ets", ".ts", ".js", ".json"] {
        if let Some(s) = path.strip_suffix(ext) {
            return s;
        }
    }
    path
}

struct PlannedRecord {
    cid: ClassId,
    rel_path: String,
    record_name: String,
    kind: SplitFileKind,
}

#[allow(
    clippy::too_many_arguments,
    reason = "per-record split emitter threads record metadata, ESM tables, function slices, batch limits, and specifier maps"
)]
fn emit_single_record(
    em: &mut Emitter<'_>,
    cid: ClassId,
    my_rel_path: &str,
    esm: Option<&EsModule>,
    record_funcs: &[FuncId],
    top_funcs: &[FuncId],
    orphan_names: BTreeSet<String>,
    consumed: &BTreeSet<FuncId>,
    inst_weights: &[u32],
    limits: BatchLimits,
    chunk_top_funcs: bool,
    planned: &[PlannedRecord],
    spec_to_idx: &HashMap<String, usize>,
    my_idx: usize,
) -> String {
    let module = em.module;
    let opts = em.opts;
    let mut out = String::new();
    if !opts.arkui {
        out.push_str("// Decompiled by abcd-decompile (abcd-rs) — Stage B + emission v1.\n");
        out.push_str("// Fallback honesty: `/* fallback Op … */` marks unrecoverable ops; `/* elided … */` marks deliberately dropped compiler guards.\n");
        if opts.ts {
            out.push_str("// TypeScript mode: annotations come from IR signatures (≤11-format files only, format fact #A7); functions without signatures keep bare parameter lists.\n");
        }
    }

    let resolve_spec = |spec_sym: abcd_ir::Sym| -> String {
        let raw = sym_str(module, spec_sym);
        if let Some(rewritten) = rewrite_specifier(&raw, my_rel_path, planned, spec_to_idx, my_idx)
        {
            render_pool_string(module, &rewritten)
        } else {
            render_sym_string(module, spec_sym)
        }
    };

    let record_env = em
        .index
        .and_then(|idx| idx.per_class_env.as_ref())
        .and_then(|m| m.get(&cid));

    // 1. Imports (plus side-effect-only module requests in exact `module_requests` order).
    if let Some(esm) = esm {
        emit_esm_imports(
            module,
            &esm.imports,
            &esm.exports,
            &esm.module_requests,
            record_env.map(|env| env.import_locals.as_slice()),
            &mut em.fn_names,
            &resolve_spec,
            &mut out,
        );
    }

    // 2. Global store hoists scoped strictly to this record's functions.
    let mut globals = BTreeSet::new();
    let mut record_globals = BTreeSet::new();
    let mut local_slots = BTreeSet::new();
    for &fid in record_funcs {
        let Some(fd) = module.func(fid) else {
            continue;
        };
        for &bid in &fd.blocks {
            let Some(block) = module.block(bid) else {
                continue;
            };
            for &iid in &block.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::StoreGlobal { name, .. } | Op::TryStoreGlobal { name, .. } => {
                        let n = sanitize(&sym_str(module, *name));
                        if globals.insert(n.clone()) {
                            em.fn_names.reserve(&n);
                        }
                    }
                    Op::StoreGlobalRecord { name, .. } => {
                        let n = sanitize(&sym_str(module, *name));
                        if record_globals.insert(n.clone()) {
                            em.fn_names.reserve(&n);
                        }
                    }
                    Op::LoadModuleVar {
                        index,
                        kind:
                            ModuleVarKind::Local
                            | ModuleVarKind::SendableLocal
                            | ModuleVarKind::SendableClass,
                    }
                    | Op::StoreModuleVar { index, .. } => {
                        local_slots.insert(*index);
                    }
                    _ => {}
                }
            }
        }
    }
    for g in &globals {
        out.push_str(&format!("var {g};\n"));
    }
    for g in record_globals.difference(&globals) {
        out.push_str(&format!("let {g};\n"));
    }

    // 3. Per-record local module-slot predeclarations (never duplicating `import` locals
    //    or top-level `--arkui` `struct` declarations!).
    let mut arkui_structs = BTreeSet::new();
    if opts.arkui && !opts.call_entry {
        for &f in top_funcs {
            if module
                .func(f)
                .is_some_and(|fd| sym_str(module, fd.name) == "func_main_0")
            {
                let pre = em.peek_prepared(f, true);
                arkui_structs.extend(crate::arkui::arkui_main_struct_names(&pre));
            }
        }
        if chunk_top_funcs {
            em.prepared.clear();
        }
    }
    for sname in &arkui_structs {
        em.fn_names.reserve(sname);
    }

    let mut declared_locals = arkui_structs;
    for s in &local_slots {
        let name = record_env
            .and_then(|env| env.local_slots.get(s))
            .cloned()
            .unwrap_or_else(|| module_slot_fallback(*s));
        em.fn_names.reserve(&name);
        if declared_locals.insert(name.clone()) {
            out.push_str(&format!("let {name};\n"));
        }
    }

    // Also ensure any `ExportDecl::Local` binding not touched by bytecode instructions
    // has a declaration if no top-level function will declare it.
    if let Some(esm) = esm {
        for exp in &esm.exports {
            if let ExportDecl::Local { local_name, .. } = exp {
                let local = crate::emit::resolve_export_local_ident(
                    module,
                    &esm.exports,
                    record_env,
                    &sym_str(module, *local_name),
                );
                if !declared_locals.contains(&local)
                    && !globals.contains(&local)
                    && !record_globals.contains(&local)
                {
                    let has_matching_top_fn = top_funcs.iter().any(|&f| {
                        module
                            .func(f)
                            .is_some_and(|fd| sanitize(&sym_str(module, fd.name)) == local)
                    });
                    if !has_matching_top_fn && declared_locals.insert(local.clone()) {
                        em.fn_names.reserve(&local);
                        out.push_str(&format!("let {local};\n"));
                    }
                }
            }
        }
    }

    // 4. Orphan lexical-slot predeclarations scoped to this record.
    for name in orphan_names {
        em.fn_names.reserve(&name);
        out.push_str(&format!("let {name}; /* orphan lexenv slot (G1) */\n"));
    }

    // 5. Top-level functions of this record.
    let mut entry_call: Option<String> = None;
    if chunk_top_funcs {
        let mut cursor = 0usize;
        while cursor < top_funcs.len() {
            let (take, batch_fids) =
                next_bounded_top_batch(module, inst_weights, &top_funcs[cursor..], limits);
            let chunk = &top_funcs[cursor..cursor + take];
            cursor += take;
            let prepared_batch: Vec<(FuncId, PreparedFunc)> = batch_fids
                .into_par_iter()
                .map(|fid| {
                    let top_level = !consumed.contains(&fid);
                    (fid, prepare_func_only(module, em.index, fid, top_level))
                })
                .collect();
            em.prepared = prepared_batch.into_iter().collect();

            for &f in chunk {
                if opts.arkui {
                    crate::arkui::precompute_arkui_components(em, f);
                }
                if opts.arkui
                    && !opts.call_entry
                    && module
                        .func(f)
                        .is_some_and(|fd| sym_str(module, fd.name) == "func_main_0")
                    && crate::arkui::try_emit_arkui_main(em, f, &mut out)
                {
                    em.arkui_components.clear();
                    continue;
                }
                let emitted = em.emit_top_level_function(f, &mut out);
                if opts.call_entry && emitted.1 == "func_main_0" {
                    entry_call = Some(emitted.0);
                }
                if opts.arkui {
                    em.arkui_components.clear();
                }
            }
            em.prepared.clear();
            em.arkui_components.clear();
        }
    } else {
        for &f in top_funcs {
            if opts.arkui {
                crate::arkui::precompute_arkui_components(em, f);
            }
            if opts.arkui
                && !opts.call_entry
                && module
                    .func(f)
                    .is_some_and(|fd| sym_str(module, fd.name) == "func_main_0")
                && crate::arkui::try_emit_arkui_main(em, f, &mut out)
            {
                em.arkui_components.clear();
                continue;
            }
            let emitted = em.emit_top_level_function(f, &mut out);
            if opts.call_entry && emitted.1 == "func_main_0" {
                entry_call = Some(emitted.0);
            }
            if opts.arkui {
                em.arkui_components.clear();
            }
        }
    }
    if let Some(name) = entry_call {
        out.push_str(&format!("{name}.call(this);\n"));
    }

    // 6. Exports.
    if let Some(esm) = esm {
        for exp in &esm.exports {
            match exp {
                ExportDecl::Local {
                    local_name,
                    export_name,
                } => {
                    let local = crate::emit::resolve_export_local_ident(
                        module,
                        &esm.exports,
                        record_env,
                        &sym_str(module, *local_name),
                    );
                    let export = module_facing_name(module, &sym_str(module, *export_name));
                    if local == export {
                        out.push_str(&format!("export {{ {local} }};\n"));
                    } else {
                        out.push_str(&format!("export {{ {local} as {export} }};\n"));
                    }
                }
                ExportDecl::Indirect {
                    export_name,
                    import_name,
                    module_request,
                } => {
                    let import = module_facing_name(module, &sym_str(module, *import_name));
                    let export = module_facing_name(module, &sym_str(module, *export_name));
                    let spec = resolve_spec(*module_request);
                    out.push_str(&format!("export {{ {import} as {export} }} from {spec};\n"));
                }
                ExportDecl::Star { module_request } => {
                    let spec = resolve_spec(*module_request);
                    out.push_str(&format!("export * from {spec};\n"));
                }
            }
        }
    }

    out
}

/// Rewrite internal OHMUrl specifiers (`@bundle:...`, `@package:...`, `@normalized:...`)
/// or extensionless JSON relative imports (`./cfg` → `./cfg.json`) when the
/// target record exists in `planned`.
fn rewrite_specifier(
    raw: &str,
    from_rel_path: &str,
    planned: &[PlannedRecord],
    spec_to_idx: &HashMap<String, usize>,
    my_idx: usize,
) -> Option<String> {
    if raw.starts_with("./") || raw.starts_with("../") {
        // Resolve relative to `from_rel_path`: if it resolves to a JSON record
        // without `.json`, append `.json`; otherwise keep the author's relative specifier.
        let resolved = resolve_posix_relative(from_rel_path, raw)?;
        let stripped = strip_known_ext(&resolved);
        if let Some(&target_idx) = spec_to_idx.get(stripped)
            && planned[target_idx].kind == SplitFileKind::Json
            && !raw.ends_with(".json")
        {
            return Some(format!("{raw}.json"));
        }
        return None;
    }

    let parsed_ohm = OhmUrl::parse(raw)?;
    if !parsed_ohm.is_internal_bundle_url() {
        return None;
    }

    let peeled = parsed_ohm.import_path;
    let mut lookup_candidates = vec![
        peeled.to_string(),
        peeled.replace('@', "/"),
        strip_known_ext(peeled).to_string(),
    ];
    if !parsed_ohm.bundle_name.is_empty() {
        let with_bundle = format!("{}/{}", parsed_ohm.bundle_name, peeled);
        lookup_candidates.push(strip_known_ext(&with_bundle).to_string());
        lookup_candidates.push(with_bundle);
    }
    if !parsed_ohm.module_name.is_empty() && !peeled.starts_with(parsed_ohm.module_name) {
        let with_mod = format!("{}/{}", parsed_ohm.module_name, peeled);
        lookup_candidates.push(strip_known_ext(&with_mod).to_string());
        lookup_candidates.push(with_mod);
    }
    let target_idx = lookup_candidates
        .iter()
        .find_map(|k| spec_to_idx.get(k).copied())?;
    if target_idx == my_idx {
        return None;
    }
    let target = &planned[target_idx];
    let target_rel = if target.kind == SplitFileKind::Json {
        target.rel_path.clone()
    } else {
        strip_known_ext(&target.rel_path).to_string()
    };
    Some(relative_posix_path(from_rel_path, &target_rel))
}

fn resolve_posix_relative(from_file: &str, rel_spec: &str) -> Option<String> {
    let mut parts: Vec<&str> = from_file.split('/').collect();
    parts.pop(); // directory of `from_file`
    for seg in rel_spec.split('/') {
        match seg {
            "" | "." => {}
            ".." => {
                parts.pop()?;
            }
            other => parts.push(other),
        }
    }
    Some(parts.join("/"))
}

fn relative_posix_path(from_file: &str, to_target: &str) -> String {
    let from_dir: Vec<&str> = {
        let mut v: Vec<&str> = from_file.split('/').collect();
        v.pop();
        v
    };
    let to_parts: Vec<&str> = to_target.split('/').collect();
    let common = from_dir
        .iter()
        .zip(to_parts.iter())
        .take_while(|(a, b)| a == b)
        .count();
    let ups = from_dir.len() - common;
    let mut out = Vec::new();
    if ups == 0 {
        out.push(".".to_string());
    } else {
        for _ in 0..ups {
            out.push("..".to_string());
        }
    }
    for &seg in &to_parts[common..] {
        out.push(seg.to_string());
    }
    out.join("/")
}

#[cfg(test)]
mod tests {
    use super::*;
    use abcd_ir::ValueDef;
    use abcd_ir::function::{Block, FunctionData, Inst, Value};
    use abcd_ir::id::{BlockId, ValueId};
    use abcd_ir::module::{Dialect, FieldData, ImportDecl, Modifiers, ModuleRequest, SourceLang};
    use abcd_ir::op::{BinOp, LexEnvKind};
    use abcd_ir::ty::Ty;

    fn add_cls(m: &mut Module, desc: &str) -> ClassId {
        let cid = ClassId::new(m.classes.len() as u32);
        let sym = m.sym.intern(desc);
        m.classes.push(ClassData::new(sym, sym));
        cid
    }

    fn add_fn_to_cls(m: &mut Module, cid: ClassId, name: &str, kind: FunctionKind) -> FuncId {
        let sym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(cid, sym, kind);
        fd.modifiers |= Modifiers::STATIC;
        m.functions.push(fd);
        m.classes[cid.index()].methods.push(fid);
        let bid = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(fid).unwrap().blocks.push(bid);
        for _ in 0..3 {
            add_param(m, fid);
        }
        fid
    }

    fn add_param(m: &mut Module, fid: FuncId) -> ValueId {
        let idx = m.func(fid).unwrap().params.len() as u16;
        let vid = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Param(idx),
            ty: Ty::Any,
        });
        m.func_mut(fid).unwrap().params.push(vid);
        vid
    }

    fn entry_of(m: &Module, fid: FuncId) -> BlockId {
        m.func(fid).unwrap().blocks[0]
    }

    fn emit_val(m: &mut Module, b: BlockId, op: Op) -> ValueId {
        let iid = abcd_ir::InstId::new(m.insts.len() as u32);
        let vid = ValueId::new(m.values.len() as u32);
        m.insts.push(Inst {
            op,
            result: Some(vid),
            block: b,
            loc: None,
        });
        m.values.push(Value {
            def: ValueDef::Inst(iid),
            ty: Ty::Any,
        });
        m.block_mut(b).unwrap().insts.push(iid);
        vid
    }

    fn emit_void(m: &mut Module, b: BlockId, op: Op) {
        let iid = abcd_ir::InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op,
            result: None,
            block: b,
            loc: None,
        });
        m.block_mut(b).unwrap().insts.push(iid);
    }

    #[test]
    fn split_with_limits_matches_byte_for_byte_across_budgets_and_oversized_records() {
        let mut m = Module::with_dialect(Dialect::DynamicEcma);
        let _synth = add_cls(&mut m, "L_ESModuleRecord;");

        // Shared inline closure referenced across multiple records and functions.
        let cid_shared_owner = add_cls(&mut m, "Lcom.demo/app/ets/util/Shared;");
        let s_shared = m.sym.intern("sharedAdd");
        m.classes[cid_shared_owner.index()].es_module = Some(EsModule {
            module_requests: vec![],
            imports: vec![],
            exports: vec![ExportDecl::Local {
                local_name: s_shared,
                export_name: s_shared,
            }],
        });
        let f_shared_cb = add_fn_to_cls(
            &mut m,
            cid_shared_owner,
            "sharedAdd",
            FunctionKind::Function,
        );
        {
            let x = add_param(&mut m, f_shared_cb);
            let b = entry_of(&m, f_shared_cb);
            let lex = emit_val(
                &mut m,
                b,
                Op::GetLexVar {
                    level: 2,
                    slot: 1,
                    kind: LexEnvKind::Plain,
                },
            );
            let sum = emit_val(
                &mut m,
                b,
                Op::BinaryOp {
                    op: BinOp::Add,
                    left: x,
                    right: lex,
                },
            );
            emit_void(&mut m, b, Op::Return { value: Some(sum) });
        }
        let f_shared_main = add_fn_to_cls(
            &mut m,
            cid_shared_owner,
            "func_main_0",
            FunctionKind::Function,
        );
        {
            let b = entry_of(&m, f_shared_main);
            let df = emit_val(
                &mut m,
                b,
                Op::DefineFunc {
                    body: f_shared_cb,
                    captures: vec![],
                    length: 1,
                },
            );
            let cl = emit_val(&mut m, b, Op::AllocClosure { func: df });
            emit_void(
                &mut m,
                b,
                Op::StoreModuleVar {
                    index: 0,
                    value: cl,
                },
            );
            emit_void(&mut m, b, Op::Return { value: None });
        }

        // JSON asset record.
        let cid_json = add_cls(&mut m, "Lcom.demo/app/ets/config;");
        {
            let jf_name = m.sym.intern("jsonFileContent");
            let jf_val = m.sym.intern("{\"env\":\"prod\"}");
            let jf_cid = m.consts.push(Const::String(jf_val));
            m.classes[cid_json.index()].fields.push(FieldData {
                name: jf_name,
                ty: Ty::Any,
                modifiers: Modifiers::NONE,
                initial_value: Some(jf_cid),
                annotations: Vec::new(),
            });
        }

        // Record with multiple top-level functions whose combined instruction weight (> 100)
        // exceeds `max_insts = 32` (exercises `single_oversized = true` + `chunk_top_funcs`).
        let cid_heavy_record = add_cls(&mut m, "Lcom.demo/app/ets/service/HeavyRecord;");
        m.classes[cid_heavy_record.index()].source_lang = SourceLang::ArkTS;
        for m_idx in 0..8 {
            let fn_name = if m_idx == 7 {
                "func_main_0".to_string()
            } else {
                format!("service_op_{m_idx}")
            };
            let fid = add_fn_to_cls(&mut m, cid_heavy_record, &fn_name, FunctionKind::Function);
            let mut acc = add_param(&mut m, fid);
            let b = entry_of(&m, fid);
            for step in 0..8 {
                let c = m.consts.push(Const::number((m_idx * 10 + step) as f64));
                let v = emit_val(&mut m, b, Op::LoadConst(c));
                acc = emit_val(
                    &mut m,
                    b,
                    Op::BinaryOp {
                        op: BinOp::Add,
                        left: acc,
                        right: v,
                    },
                );
            }
            if m_idx % 3 == 0 {
                let df = emit_val(
                    &mut m,
                    b,
                    Op::DefineFunc {
                        body: f_shared_cb,
                        captures: vec![],
                        length: 1,
                    },
                );
                let cl = emit_val(&mut m, b, Op::AllocClosure { func: df });
                acc = emit_val(
                    &mut m,
                    b,
                    Op::BinaryOp {
                        op: BinOp::Add,
                        left: acc,
                        right: cl,
                    },
                );
            }
            emit_void(&mut m, b, Op::Return { value: Some(acc) });
        }

        // Record with an oversized SINGLE top-level function (> 80 instructions) + cross-record
        // OHMUrl & JSON imports.
        let cid_giant_fn = add_cls(&mut m, "Lcom.demo/app/ets/Entry;");
        let req_shared = m.sym.intern("@bundle:com.demo/app/ets/util/Shared");
        let req_cfg = m.sym.intern("./config");
        let s_cfg = m.sym.intern("cfg");
        let s_def = m.sym.intern("default");
        let s_out = m.sym.intern("boot");
        m.classes[cid_giant_fn.index()].es_module = Some(EsModule {
            module_requests: vec![
                ModuleRequest {
                    specifier: req_shared,
                    lazy: false,
                },
                ModuleRequest {
                    specifier: req_cfg,
                    lazy: false,
                },
            ],
            imports: vec![
                ImportDecl::Regular {
                    local_name: s_shared,
                    import_name: s_shared,
                    module_request: req_shared,
                },
                ImportDecl::Regular {
                    local_name: s_cfg,
                    import_name: s_def,
                    module_request: req_cfg,
                },
            ],
            exports: vec![ExportDecl::Local {
                local_name: s_out,
                export_name: s_out,
            }],
        });
        let f_entry = add_fn_to_cls(&mut m, cid_giant_fn, "func_main_0", FunctionKind::Function);
        {
            let b = entry_of(&m, f_entry);
            let mut acc = emit_val(
                &mut m,
                b,
                Op::LoadModuleVar {
                    index: 0,
                    kind: ModuleVarKind::External,
                },
            );
            let cfg_v = emit_val(
                &mut m,
                b,
                Op::LoadModuleVar {
                    index: 1,
                    kind: ModuleVarKind::External,
                },
            );
            acc = emit_val(
                &mut m,
                b,
                Op::BinaryOp {
                    op: BinOp::Add,
                    left: acc,
                    right: cfg_v,
                },
            );
            for k in 0..40 {
                let c = m.consts.push(Const::number(k as f64));
                let v = emit_val(&mut m, b, Op::LoadConst(c));
                acc = emit_val(
                    &mut m,
                    b,
                    Op::BinaryOp {
                        op: BinOp::Add,
                        left: acc,
                        right: v,
                    },
                );
            }
            emit_void(
                &mut m,
                b,
                Op::StoreModuleVar {
                    index: 0,
                    value: acc,
                },
            );
            emit_void(&mut m, b, Op::Return { value: None });
        }

        let budgets = [
            BatchLimits {
                max_insts: 1,
                max_funcs: 1,
            },
            BatchLimits {
                max_insts: 32,
                max_funcs: 2,
            },
            BatchLimits {
                max_insts: 48,
                max_funcs: 3,
            },
            BatchLimits::default(),
        ];

        for opts in [
            EmitOptions::default(),
            EmitOptions {
                ts: true,
                call_entry: true,
                ..EmitOptions::default()
            },
            EmitOptions {
                arkui: true,
                ..EmitOptions::default()
            },
        ] {
            let baseline = decompile_module_split(&m, &opts);
            assert_eq!(baseline.files.len(), 4);
            for lim in budgets {
                let got = split_with_limits(&m, &opts, lim);
                assert_eq!(got.files, baseline.files, "files mismatch at {lim:?}");
                assert_eq!(got.stats, baseline.stats, "stats mismatch at {lim:?}");
            }
        }
    }
}
