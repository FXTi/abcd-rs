//! Multi-module `--merge-abc` directory-tree splitter (`--split-modules`, #26).
//!
//! Partitions a lifted [`abcd_ir::Module`] by its owning record classes
//! ([`abcd_ir::ClassData`]) into safe relative file paths (`.js` / `.ts` /
//! `.ets` and `.json`), resolving per-record ES module slots (`RegularImport`,
//! `NamespaceImport`, and `LocalExport`) without cross-record slot collisions
//! and rewriting internal OHMUrl (`@bundle:`, `@package:`, `@normalized:`)
//! specifiers into navigable POSIX relative imports.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use abcd_ir::consts::Const;
use abcd_ir::id::{ClassId, FuncId};
use abcd_ir::module::{ClassData, EsModule, ExportDecl, FunctionKind, ImportDecl, Module};
use abcd_ir::op::{ModuleVarKind, Op};
use rayon::prelude::*;

use crate::consts::{render_pool_string, render_sym_string, sym_str};
use crate::emit::{
    DecompileStats, EmitOptions, Emitter, PreparedFunc, consumed_functions, merge_fold_stats,
    merge_struct_stats, module_facing_name, prepare_func,
};
use crate::legalize::{Legalizer, is_legal_ident, sanitize};
use crate::names::{DecompileIndex, module_slot_fallback};

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

/// One file produced by [`decompile_module_split`].
#[derive(Clone, Debug)]
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
    "CON", "PRN", "AUX", "NUL", "COM1", "COM2", "COM3", "COM4", "COM5", "COM6", "COM7", "COM8",
    "COM9", "LPT1", "LPT2", "LPT3", "LPT4", "LPT5", "LPT6", "LPT7", "LPT8", "LPT9",
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
    let raw = strip_descriptor(descriptor);
    if raw.is_empty() {
        return None;
    }
    // External system/SDK stub descriptors (`@ohos.app`, `@system.router`, `@kit.*`)
    // are foreign references, not bundled user files.
    if raw.starts_with("@ohos.")
        || raw.starts_with("@ohos:")
        || raw.starts_with("@system.")
        || raw.starts_with("@system:")
        || raw.starts_with("@kit.")
        || raw.starts_with("@arkts.")
    {
        return None;
    }

    let logical = peel_ohmurl(raw);
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
        if is_windows_reserved(last) {
            last.push('_');
        }
        last.push('.');
        last.push_str(target_ext);
    }
    for seg in segments.iter_mut().rev().skip(1) {
        if is_windows_reserved(seg) {
            seg.push('_');
        }
    }
    Some(segments.join("/"))
}

fn strip_descriptor(desc: &str) -> &str {
    desc.strip_prefix('L')
        .and_then(|s| s.strip_suffix(';'))
        .unwrap_or(desc)
}

/// Unwrap OHMUrl record prefixes (`@bundle:...`, `@package:...`, `@normalized:...`)
/// into their underlying logical module path.
fn peel_ohmurl(raw: &str) -> &str {
    if let Some(rest) = raw.strip_prefix("@bundle:") {
        return rest;
    }
    if let Some(rest) = raw.strip_prefix("@package:") {
        return rest;
    }
    if let Some(rest) = raw.strip_prefix("@normalized:") {
        // `@normalized:<isNative>&<moduleName>&<bundleName>/<importPath>&<version>`
        let parts: Vec<&str> = rest.split('&').collect();
        if parts.len() >= 4 && !parts[3].is_empty() {
            return parts[3];
        }
        if parts.len() >= 3 && !parts[2].is_empty() {
            return parts[2];
        }
        return rest;
    }
    raw
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

fn is_windows_reserved(stem: &str) -> bool {
    let base = stem.split('.').next().unwrap_or(stem);
    WINDOWS_RESERVED
        .iter()
        .any(|&r| base.eq_ignore_ascii_case(r))
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
    let ext = if opts.arkui {
        "ets"
    } else if opts.ts {
        "ts"
    } else {
        "js"
    };

    let consumed = consumed_functions(module);
    let index = DecompileIndex::build_split(module);

    let (prepared_vec, orphan_sets): (Vec<PreparedFunc>, Vec<BTreeSet<String>>) =
        (0..module.functions.len())
            .into_par_iter()
            .map(|i| {
                let func = FuncId::new(i as u32);
                let top_level = !consumed.contains(&func);
                prepare_func(module, Some(&index), func, top_level)
            })
            .unzip();

    // Group top-level unconsumed functions and orphan lexenv names by `ClassId`.
    let mut class_funcs: HashMap<ClassId, Vec<FuncId>> = HashMap::new();
    let mut class_orphans: HashMap<ClassId, BTreeSet<String>> = HashMap::new();
    for (fi, fdata) in module.functions.iter().enumerate() {
        let fid = FuncId::new(fi as u32);
        if let Some(orphans) = orphan_sets.get(fi) {
            class_orphans
                .entry(fdata.class_id)
                .or_default()
                .extend(orphans.iter().cloned());
        }
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
        let json_text = json_content_of(module, cls);
        let has_funcs = class_funcs.get(&cid).is_some_and(|v| !v.is_empty());
        let has_esm = cls.es_module.is_some()
            || (is_standalone
                && desc == "L_GLOBAL;"
                && (!module.imports.is_empty()
                    || !module.exports.is_empty()
                    || !module.module_requests.is_empty()));
        if json_text.is_none() && !has_funcs && !has_esm {
            continue;
        }

        let is_json = json_text.is_some();
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
        let record_name = strip_descriptor(&desc).to_string();
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
            json_text,
        });
    }

    // Build specifier → planned-index lookup table for internal OHMUrl & JSON resolution.
    let mut spec_to_idx: HashMap<String, usize> = HashMap::new();
    for (idx, p) in planned.iter().enumerate() {
        for key in candidate_record_keys(&p.record_name, &p.rel_path) {
            spec_to_idx.entry(key).or_insert(idx);
        }
    }

    let mut prepared_slots: Vec<Option<PreparedFunc>> =
        prepared_vec.into_iter().map(Some).collect();
    let mut files = Vec::with_capacity(planned.len());
    let mut total_stats = DecompileStats::default();

    for (my_idx, plan) in planned.iter().enumerate() {
        if let Some(json_text) = &plan.json_text {
            files.push(SplitFile {
                rel_path: plan.rel_path.clone(),
                record_name: plan.record_name.clone(),
                kind: SplitFileKind::Json,
                text: json_text.clone(),
                stats: DecompileStats::default(),
            });
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

        // Collect all functions transitively reachable inside this record
        // (methods of `plan.cid` so globals/slots stay strictly per-record).
        let record_funcs: &[FuncId] = &cls.methods;
        let top_funcs = class_funcs.get(&plan.cid).map(Vec::as_slice).unwrap_or(&[]);
        let orphans = class_orphans.remove(&plan.cid).unwrap_or_default();

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
            prepared: std::mem::take(&mut prepared_slots),
            reused: BTreeMap::new(),
        };

        let text = emit_single_record(
            &mut em,
            plan.cid,
            &plan.rel_path,
            esm,
            record_funcs,
            top_funcs,
            orphans,
            &planned,
            &spec_to_idx,
            my_idx,
        );
        prepared_slots = std::mem::take(&mut em.prepared);
        let file_stats = em.stats;
        accumulate_stats(&mut total_stats, &file_stats);
        files.push(SplitFile {
            rel_path: plan.rel_path.clone(),
            record_name: plan.record_name.clone(),
            kind: plan.kind,
            text,
            stats: file_stats,
        });
    }

    SplitDecompiledModule {
        files,
        stats: total_stats,
    }
}

fn is_standalone_single_module(module: &Module) -> bool {
    let mut non_synth = 0usize;
    let mut has_global = false;
    for cls in &module.classes {
        let desc = sym_str(module, cls.descriptor);
        if SYNTHETIC_DESCRIPTORS.contains(&desc.as_str()) {
            continue;
        }
        if cls.methods.is_empty()
            && cls.es_module.is_none()
            && json_content_of(module, cls).is_none()
        {
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
    if used.insert(base.clone()) {
        return base;
    }
    let (stem, ext) = match base.rfind('.') {
        Some(dot) => (&base[..dot], &base[dot..]),
        None => (base.as_str(), ""),
    };
    let mut n = 1usize;
    loop {
        let cand = format!("{stem}${n}{ext}");
        if used.insert(cand.clone()) {
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
    keys.push(peel_ohmurl(record_name).to_string());
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
    json_text: Option<String>,
}

#[allow(clippy::too_many_arguments)]
fn emit_single_record(
    em: &mut Emitter<'_>,
    cid: ClassId,
    my_rel_path: &str,
    esm: Option<&EsModule>,
    record_funcs: &[FuncId],
    top_funcs: &[FuncId],
    orphan_names: BTreeSet<String>,
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

    // 1. Imports (plus side-effect-only module requests).
    let mut referenced_requests = BTreeSet::new();
    if let Some(esm) = esm {
        for imp in &esm.imports {
            match imp {
                ImportDecl::Regular {
                    local_name,
                    import_name,
                    module_request,
                } => {
                    referenced_requests.insert(*module_request);
                    let local = sanitize(&sym_str(module, *local_name));
                    let import = module_facing_name(&sym_str(module, *import_name));
                    let spec = resolve_spec(*module_request);
                    em.fn_names.reserve(&local);
                    if import == "default" && is_legal_ident(&local) {
                        out.push_str(&format!("import {local} from {spec};\n"));
                    } else if local == import {
                        out.push_str(&format!("import {{ {local} }} from {spec};\n"));
                    } else {
                        out.push_str(&format!("import {{ {import} as {local} }} from {spec};\n"));
                    }
                }
                ImportDecl::Namespace {
                    local_name,
                    module_request,
                } => {
                    referenced_requests.insert(*module_request);
                    let local = sanitize(&sym_str(module, *local_name));
                    let spec = resolve_spec(*module_request);
                    em.fn_names.reserve(&local);
                    out.push_str(&format!("import * as {local} from {spec};\n"));
                }
            }
        }
        for exp in &esm.exports {
            match exp {
                ExportDecl::Indirect { module_request, .. }
                | ExportDecl::Star { module_request } => {
                    referenced_requests.insert(*module_request);
                }
                ExportDecl::Local { .. } => {}
            }
        }
        for req in &esm.module_requests {
            if !referenced_requests.contains(&req.specifier) {
                let spec = resolve_spec(req.specifier);
                out.push_str(&format!("import {spec};\n"));
            }
        }
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
    let arkui_structs: BTreeSet<String> = if opts.arkui && !opts.call_entry {
        top_funcs
            .iter()
            .filter(|&&f| {
                module
                    .func(f)
                    .is_some_and(|fd| sym_str(module, fd.name) == "func_main_0")
            })
            .filter_map(|&f| em.prepared.get(f.index()).and_then(|s| s.as_ref()))
            .flat_map(crate::arkui::arkui_main_struct_names)
            .collect()
    } else {
        BTreeSet::new()
    };
    for sname in &arkui_structs {
        em.fn_names.reserve(sname);
    }

    let record_env = em
        .index
        .and_then(|idx| idx.per_class_env.as_ref())
        .and_then(|m| m.get(&cid));
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
                let local = sanitize(&sym_str(module, *local_name));
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
    for &f in top_funcs {
        if opts.arkui
            && !opts.call_entry
            && module
                .func(f)
                .is_some_and(|fd| sym_str(module, fd.name) == "func_main_0")
            && crate::arkui::try_emit_arkui_main(em, f, &mut out)
        {
            continue;
        }
        let emitted = em.emit_top_level_function(f, &mut out);
        if opts.call_entry && emitted.1 == "func_main_0" {
            entry_call = Some(emitted.0);
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
                    let local = sanitize(&sym_str(module, *local_name));
                    let export = module_facing_name(&sym_str(module, *export_name));
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
                    let import = module_facing_name(&sym_str(module, *import_name));
                    let export = module_facing_name(&sym_str(module, *export_name));
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

    if !(raw.starts_with("@bundle:")
        || raw.starts_with("@package:")
        || raw.starts_with("@normalized:"))
    {
        return None;
    }

    let peeled = peel_ohmurl(raw);
    let lookup_candidates = [
        peeled.to_string(),
        peeled.replace('@', "/"),
        strip_known_ext(peeled).to_string(),
    ];
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

fn accumulate_stats(dst: &mut DecompileStats, src: &DecompileStats) {
    dst.functions += src.functions;
    dst.functions_with_fallbacks += src.functions_with_fallbacks;
    for (&k, &v) in &src.fallback_comments {
        *dst.fallback_comments.entry(k).or_insert(0) += v;
    }
    for (&k, &v) in &src.elided_comments {
        *dst.elided_comments.entry(k).or_insert(0) += v;
    }
    dst.classes += src.classes;
    dst.class_methods += src.class_methods;
    dst.closures += src.closures;
    dst.structure = merge_struct_stats(std::mem::take(&mut dst.structure), &src.structure);
    dst.folds = merge_fold_stats(std::mem::take(&mut dst.folds), &src.folds);
    dst.function_bodies += src.function_bodies;
}
