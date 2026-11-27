//! Cross-module ES `import` / `export` resolution and multi-`.abc` IR linking (#27 Phase 1).
//!
//! Connects per-record [`abcd_ir::module::EsModule`] tables (`imports`,
//! `exports`, `module_requests`) and JSON asset records (`jsonFileContent`)
//! across [`abcd_ir::ClassData`] records inside `--merge-abc` bundles (as well
//! as across multi-`.abc` containers merged via [`merge_ir_modules`]).
//!
//! ## Upstream ArkCompiler module-slot invariants
//!
//! Within each record class `C`:
//! 1. [`Op::LoadModuleVar`] with `External` / `SendableExternal` / `Lazy` /
//!    `LazySendable` indexes 0-based into `C`'s [`ImportDecl::Regular`] entries.
//! 2. [`Op::LoadModuleVar`] with `Local` / `SendableLocal` / `SendableClass`
//!    and [`Op::StoreModuleVar`] index 0-based into `C`'s distinct
//!    [`ExportDecl::Local::local_name`] entries in declaration order.
//! 3. [`Op::GetModuleNamespace`] indexes 0-based into `C`'s
//!    [`EsModule::module_requests`].

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use abcd_ir::consts::{Const, ConstPool};
use abcd_ir::id::{BlockId, ClassId, ConstId, FuncId, InstId, Sym, ValueId};
use abcd_ir::module::{ClassData, EsModule, ExportDecl, ImportDecl, Module};
use abcd_ir::op::Op;
use abcd_ir::remap::{IdRemapper, remap_module_body};
use abcd_ir::symbol::SymbolTable;

use crate::ohmurl::{OhmUrl, OhmUrlKind};

/// Compiler-synthetic metadata record descriptors in `--merge-abc` files.
const SYNTHETIC_DESCRIPTORS: &[&str] = &[
    "L_ESModuleRecord;",
    "L_ESScopeNamesRecord;",
    "L_ModuleRequestPhaseRecord;",
    "L_ESSlotNumberAnnotation;",
    "L_ESConcurrentModuleRequestsAnnotation;",
];

/// A resolved local module-variable slot `(record class, 0-based local slot)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModuleSlotRef {
    /// Owning record class in [`Module::classes`].
    pub class_id: ClassId,
    /// 0-based local export slot index in `class_id`.
    pub slot: u32,
}

/// Resolution of one external `LoadModuleVar` index in an importing record.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExternalSlotTarget {
    /// Internal `(exporting ClassId, local_slot)` pairs reached through
    /// direct, indirect (`export { x as y } from ...`), or `export *` chains.
    pub slots: Vec<ModuleSlotRef>,
    /// Internal target record `ClassId`s reached via `export * as ns from ...`
    /// namespace re-exports (`#82`).
    pub namespace_classes: Vec<ClassId>,
    /// JSON payload constants reached when importing `default` of a bundled
    /// JSON record (`jsonFileContent`).
    pub json_consts: Vec<ConstId>,
    /// External `(module_request, import_name)` pairs that did not resolve to
    /// an internal record (e.g. `@ohos.net.http`, `@kit.NetworkKit`).
    pub external_imports: Vec<(Sym, Sym)>,
    /// `true` when at least one resolution path left the bundle (an external
    /// SDK module or missing export).
    pub unresolved_external: bool,
}

/// Whole-module ES `import` / `export` linkage index over [`Module`].
#[derive(Clone, Debug)]
pub struct ModuleLinkTable {
    /// Function → owning `ClassId`.
    func_class: Vec<ClassId>,
    /// Block → owning `FuncId`.
    block_func: Vec<Option<FuncId>>,
    /// Per-record `(ClassId, external_slot)` → resolved targets.
    external_loads: BTreeMap<(ClassId, u32), ExternalSlotTarget>,
    /// Per-record `(ClassId, request_idx)` → resolved internal target `ClassId`.
    namespace_targets: BTreeMap<(ClassId, u32), ClassId>,
    /// Per-record `(ClassId, request_idx)` → raw specifier `Sym` when external.
    namespace_external: BTreeMap<(ClassId, u32), Sym>,
    /// Per-record `ClassId` → exported property `Sym` → resolved `ModuleSlotRef`s.
    namespace_exports: BTreeMap<ClassId, BTreeMap<Sym, Vec<ModuleSlotRef>>>,
    /// Per-record `ClassId` → exported sub-namespace `Sym` → target record `ClassId`s
    /// (`export * as sub from "./sub"`).
    namespace_submodules: BTreeMap<ClassId, BTreeMap<Sym, Vec<ClassId>>>,
    /// `(ClassId, local_slot)` → `(FuncId, ValueId)` definitions written via
    /// `Op::StoreModuleVar`.
    slot_stores: BTreeMap<ModuleSlotRef, Vec<(FuncId, ValueId)>>,
    /// Topological post-order of record `func_main_0` entry functions
    /// (dependencies initialized before importers).
    init_order: Vec<FuncId>,
    /// ESM record `ClassId`s whose transitive `export * from` graph reaches an
    /// unresolved external module request.
    unresolved_star_classes: BTreeSet<ClassId>,
    /// Whether this module carries multi-record `--merge-abc` ES module tables.
    has_multi_record_esm: bool,
}

impl ModuleLinkTable {
    /// Construct the cross-module resolution index for `module`.
    pub fn build(module: &Module) -> Self {
        Self::build_with_harness(module, None)
    }

    /// Construct the cross-module resolution index for `module` with an explicit
    /// optional lifecycle `harness_func` (`#75`, `#76`).
    pub fn build_with_harness(module: &Module, harness_func: Option<FuncId>) -> Self {
        let func_class: Vec<ClassId> = module.functions.iter().map(|f| f.class_id).collect();
        let mut block_func = vec![None; module.blocks.len()];
        for (fi, f) in module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            for &b in &f.blocks {
                if let Some(slot) = block_func.get_mut(b.index()) {
                    *slot = Some(fid);
                }
            }
        }

        // Collect per-class EsModule views and normalized record lookup keys.
        let standalone = is_standalone_single_module(module, harness_func);
        let mut esm_by_class: BTreeMap<ClassId, EsModule> = BTreeMap::new();
        let mut json_by_class: BTreeMap<ClassId, ConstId> = BTreeMap::new();
        let mut class_rel_path: BTreeMap<ClassId, String> = BTreeMap::new();
        let mut key_to_class: HashMap<String, ClassId> = HashMap::new();
        let mut esm_record_count = 0usize;

        for (ci, cls) in module.classes.iter().enumerate() {
            let cid = ClassId::new(ci as u32);
            let desc = sym_str(module, cls.descriptor);
            if SYNTHETIC_DESCRIPTORS.contains(&desc) {
                continue;
            }
            if let Some(jc) = json_const_of(module, cls) {
                json_by_class.insert(cid, jc);
            }
            if let Some(esm) = &cls.es_module {
                esm_by_class.insert(cid, esm.clone());
                esm_record_count += 1;
            } else if standalone
                && desc == "L_GLOBAL;"
                && (!module.imports.is_empty()
                    || !module.exports.is_empty()
                    || !module.module_requests.is_empty())
            {
                esm_by_class.insert(
                    cid,
                    EsModule {
                        imports: module.imports.clone(),
                        exports: module.exports.clone(),
                        module_requests: module.module_requests.clone(),
                    },
                );
            }

            let raw_name = strip_descriptor(desc);
            if !raw_name.is_empty() && !is_sdk_specifier(raw_name) {
                let norm = normalize_logical_path(raw_name);
                class_rel_path.insert(cid, norm.clone());
                for k in candidate_keys(raw_name, &norm) {
                    key_to_class.entry(k).or_insert(cid);
                }
            }
        }

        // Build per-class distinct LocalExport `local_name -> slot` tables.
        let mut local_name_to_slot: BTreeMap<ClassId, HashMap<String, u32>> = BTreeMap::new();
        for (&cid, esm) in &esm_by_class {
            let mut map = HashMap::new();
            let mut next_slot = 0u32;
            for exp in &esm.exports {
                if let ExportDecl::Local { local_name, .. } = exp {
                    let lname = sym_str(module, *local_name).to_owned();
                    if !lname.is_empty() && !map.contains_key(&lname) {
                        map.insert(lname, next_slot);
                        next_slot += 1;
                    }
                }
            }
            local_name_to_slot.insert(cid, map);
        }

        // Collect all `Op::StoreModuleVar` stores per `(ClassId, slot)`.
        let mut slot_stores: BTreeMap<ModuleSlotRef, Vec<(FuncId, ValueId)>> = BTreeMap::new();
        for (fi, f) in module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            let cid = f.class_id;
            for &b in &f.blocks {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    if let Op::StoreModuleVar { index, value } = &inst.op {
                        slot_stores
                            .entry(ModuleSlotRef {
                                class_id: cid,
                                slot: *index,
                            })
                            .or_default()
                            .push((fid, *value));
                    }
                }
            }
        }

        let lookup_candidates = |candidates: &[String]| -> Option<ClassId> {
            if let Some(cid) = candidates.iter().find_map(|c| key_to_class.get(c).copied()) {
                return Some(cid);
            }
            for c in candidates {
                if let Some(&cid) = key_to_class
                    .get(&format!("{c}/index"))
                    .or_else(|| key_to_class.get(&format!("{c}.index")))
                {
                    return Some(cid);
                }
                if let Some(stem) = c
                    .strip_suffix("/index")
                    .or_else(|| c.strip_suffix(".index"))
                    && let Some(&cid) = key_to_class.get(stem)
                {
                    return Some(cid);
                }
            }
            None
        };

        let resolve_spec = |from_cid: ClassId, spec_sym: Sym| -> Option<ClassId> {
            let raw = sym_str(module, spec_sym);
            if raw.is_empty() || is_sdk_specifier(raw) {
                return None;
            }
            if raw.starts_with("./") || raw.starts_with("../") {
                let base = class_rel_path.get(&from_cid)?;
                let resolved = if base.contains('/') {
                    resolve_posix_relative(base, raw)?
                } else {
                    resolve_dot_relative(base, raw)?
                };
                let stripped = strip_known_ext(&resolved);
                let mut rel_candidates = Vec::with_capacity(3);
                push_unique(&mut rel_candidates, resolved.clone());
                push_unique(&mut rel_candidates, stripped.to_owned());
                if base.contains('/') {
                    push_unique(&mut rel_candidates, stripped.replace('/', "."));
                }
                return lookup_candidates(&rel_candidates);
            }
            let candidates = collect_candidates(raw, None);
            lookup_candidates(&candidates)
        };

        let ctx = ExportResolveCtx {
            module,
            esm_by_class: &esm_by_class,
            json_by_class: &json_by_class,
            local_name_to_slot: &local_name_to_slot,
            resolve_spec: &resolve_spec,
            star_names_memo: std::cell::RefCell::new(HashMap::new()),
            export_memo: std::cell::RefCell::new(HashMap::new()),
        };

        // Precompute external-import slot targets and namespace targets.
        let mut external_loads: BTreeMap<(ClassId, u32), ExternalSlotTarget> = BTreeMap::new();
        let mut namespace_targets: BTreeMap<(ClassId, u32), ClassId> = BTreeMap::new();
        let mut namespace_external: BTreeMap<(ClassId, u32), Sym> = BTreeMap::new();
        let mut dep_edges: BTreeMap<ClassId, Vec<ClassId>> = BTreeMap::new();

        for (&cid, esm) in &esm_by_class {
            let mut ext_idx = 0u32;
            for imp in &esm.imports {
                if let ImportDecl::Regular {
                    import_name,
                    module_request,
                    ..
                } = imp
                {
                    let imp_str = sym_str(module, *import_name);
                    let target = if let Some(target_cid) = resolve_spec(cid, *module_request) {
                        dep_edges.entry(cid).or_default().push(target_cid);
                        ctx.resolve_export_cached(target_cid, imp_str)
                    } else {
                        ExternalSlotTarget {
                            unresolved_external: true,
                            external_imports: vec![(*module_request, *import_name)],
                            ..ExternalSlotTarget::default()
                        }
                    };
                    external_loads.insert((cid, ext_idx), target);
                    ext_idx += 1;
                }
            }

            for (req_idx, req) in esm.module_requests.iter().enumerate() {
                if let Some(target_cid) = resolve_spec(cid, req.specifier) {
                    namespace_targets.insert((cid, req_idx as u32), target_cid);
                    dep_edges.entry(cid).or_default().push(target_cid);
                } else {
                    namespace_external.insert((cid, req_idx as u32), req.specifier);
                }
            }
        }

        // Precompute namespace export maps for every ESM record (memoized across
        // star re-export chains).
        let mut namespace_exports: BTreeMap<ClassId, BTreeMap<Sym, Vec<ModuleSlotRef>>> =
            BTreeMap::new();
        let mut namespace_submodules: BTreeMap<ClassId, BTreeMap<Sym, Vec<ClassId>>> =
            BTreeMap::new();
        let mut unresolved_star_classes: BTreeSet<ClassId> = BTreeSet::new();
        let mut lossy_export_syms: BTreeMap<&str, Vec<Sym>> = BTreeMap::new();
        for s in module.sym.lossy_syms() {
            if let Some(text) = module.sym.resolve(s) {
                lossy_export_syms.entry(text).or_default().push(s);
            }
        }
        for &cid in esm_by_class.keys() {
            let (names, has_ext_star) = ctx.collect_exported_names_cached(cid);
            if has_ext_star {
                unresolved_star_classes.insert(cid);
            }
            let mut sym_map: BTreeMap<Sym, Vec<ModuleSlotRef>> = BTreeMap::new();
            let mut sub_map: BTreeMap<Sym, Vec<ClassId>> = BTreeMap::new();
            for ename in names {
                let target = ctx.resolve_export_cached(cid, &ename);
                if target.slots.is_empty() && target.namespace_classes.is_empty() {
                    continue;
                }
                let lossless_sym = module.sym.get(&ename);
                let lossy_syms = lossy_export_syms
                    .get(ename.as_str())
                    .map_or(&[][..], Vec::as_slice);
                if !target.slots.is_empty() {
                    if let Some(sym) = lossless_sym {
                        sym_map.insert(sym, target.slots.clone());
                    }
                    for &sym in lossy_syms {
                        sym_map.insert(sym, target.slots.clone());
                    }
                }
                if !target.namespace_classes.is_empty() {
                    if let Some(sym) = lossless_sym {
                        sub_map.insert(sym, target.namespace_classes.clone());
                    }
                    for &sym in lossy_syms {
                        sub_map.insert(sym, target.namespace_classes.clone());
                    }
                }
            }
            if !sym_map.is_empty() {
                namespace_exports.insert(cid, sym_map);
            }
            if !sub_map.is_empty() {
                namespace_submodules.insert(cid, sub_map);
            }
        }

        // Compute deterministic post-order `func_main_0` initialization sequence.
        let mut main_of_class: BTreeMap<ClassId, FuncId> = BTreeMap::new();
        for (fi, f) in module.functions.iter().enumerate() {
            if !f.is_external && !f.blocks.is_empty() && sym_str(module, f.name) == "func_main_0" {
                main_of_class
                    .entry(f.class_id)
                    .or_insert(FuncId::new(fi as u32));
            }
        }
        let mut init_order = Vec::new();
        let mut visited_cls = BTreeSet::new();
        let mut dfs_stack: Vec<(ClassId, usize)> = Vec::new();
        for &root_cid in main_of_class.keys() {
            if !visited_cls.insert(root_cid) {
                continue;
            }
            dfs_stack.push((root_cid, 0));
            while let Some((cid, next_idx)) = dfs_stack.last_mut() {
                let cur_cid = *cid;
                let deps = dep_edges.get(&cur_cid).map(Vec::as_slice).unwrap_or(&[]);
                let mut pushed = false;
                while *next_idx < deps.len() {
                    let d = deps[*next_idx];
                    *next_idx += 1;
                    if visited_cls.insert(d) {
                        dfs_stack.push((d, 0));
                        pushed = true;
                        break;
                    }
                }
                if !pushed {
                    if let Some(&fid) = main_of_class.get(&cur_cid) {
                        init_order.push(fid);
                    }
                    dfs_stack.pop();
                }
            }
        }

        ModuleLinkTable {
            func_class,
            block_func,
            external_loads,
            namespace_targets,
            namespace_external,
            namespace_exports,
            namespace_submodules,
            slot_stores,
            init_order,
            unresolved_star_classes,
            has_multi_record_esm: esm_record_count > 0,
        }
    }

    /// Extend `func_class` and `block_func` in `O(Δ)` for functions and basic
    /// blocks appended to `module` after this table was built (for example, via
    /// [`crate::ohos_lifecycle::EntryPlan::append`]; `#71`).
    pub fn extend_appended(&mut self, module: &Module) {
        let old_funcs = self.func_class.len();
        if module.blocks.len() > self.block_func.len() {
            self.block_func.resize(module.blocks.len(), None);
        }
        if module.functions.len() > old_funcs {
            self.func_class.reserve(module.functions.len() - old_funcs);
            for (offset, f) in module.functions[old_funcs..].iter().enumerate() {
                let fid = FuncId::new((old_funcs + offset) as u32);
                self.func_class.push(f.class_id);
                for &b in &f.blocks {
                    if let Some(slot) = self.block_func.get_mut(b.index()) {
                        *slot = Some(fid);
                    }
                }
            }
        }
    }

    /// Borrow the dense `BlockId::index() -> Option<FuncId>` ownership slice (`#78`).
    #[must_use]
    #[inline]
    pub fn block_func_slice(&self) -> &[Option<FuncId>] {
        &self.block_func
    }

    /// Owning `FuncId` of basic block `block` (`#78`).
    #[must_use]
    #[inline]
    pub fn func_of_block(&self, block: BlockId) -> Option<FuncId> {
        self.block_func.get(block.index()).copied().flatten()
    }

    /// Whether `module` carries per-record `--merge-abc` `EsModule` metadata.
    pub fn has_multi_record_esm(&self) -> bool {
        self.has_multi_record_esm
    }

    /// Owning `ClassId` of `func`.
    pub fn func_class(&self, func: FuncId) -> Option<ClassId> {
        self.func_class.get(func.index()).copied()
    }

    /// Owning `FuncId` of instruction `inst`.
    pub fn inst_func(&self, module: &Module, inst: InstId) -> Option<FuncId> {
        let block = module.inst(inst)?.block;
        self.func_of_block(block)
    }

    /// Owning `ClassId` of instruction `inst`.
    pub fn inst_class(&self, module: &Module, inst: InstId) -> Option<ClassId> {
        let func = self.inst_func(module, inst)?;
        self.func_class(func)
    }

    /// Resolve an external/lazy `LoadModuleVar` in `importing_class` at `ext_index`.
    pub fn external_load(
        &self,
        importing_class: ClassId,
        ext_index: u32,
    ) -> Option<&ExternalSlotTarget> {
        self.external_loads.get(&(importing_class, ext_index))
    }

    /// Resolve a `GetModuleNamespace` in `importing_class` at `req_index` to an
    /// internal record `ClassId`.
    pub fn namespace_target(&self, importing_class: ClassId, req_index: u32) -> Option<ClassId> {
        self.namespace_targets
            .get(&(importing_class, req_index))
            .copied()
    }

    /// Resolve a `GetModuleNamespace` in `importing_class` at `req_index` to its
    /// external specifier `Sym` when the target record is outside the bundle.
    pub fn namespace_external(&self, importing_class: ClassId, req_index: u32) -> Option<Sym> {
        self.namespace_external
            .get(&(importing_class, req_index))
            .copied()
    }

    /// All exported property bindings `export_sym -> Vec<ModuleSlotRef>` of `target_class`.
    pub fn namespace_exports(
        &self,
        target_class: ClassId,
    ) -> Option<&BTreeMap<Sym, Vec<ModuleSlotRef>>> {
        self.namespace_exports.get(&target_class)
    }

    /// All exported sub-namespace bindings `export_sym -> Vec<ClassId>` of
    /// `target_class` (`export * as ns from "./sub"`).
    pub fn namespace_submodules(
        &self,
        target_class: ClassId,
    ) -> Option<&BTreeMap<Sym, Vec<ClassId>>> {
        self.namespace_submodules.get(&target_class)
    }

    /// Resolve `ns.<prop>` on a `GetModuleNamespace` of `importing_class` at `req_index`.
    pub fn resolve_namespace_member(
        &self,
        importing_class: ClassId,
        req_index: u32,
        prop: Sym,
    ) -> Option<&[ModuleSlotRef]> {
        let target_cid = self.namespace_target(importing_class, req_index)?;
        self.namespace_exports
            .get(&target_cid)
            .and_then(|m| m.get(&prop))
            .map(Vec::as_slice)
    }

    /// Values `(FuncId, ValueId)` stored via `Op::StoreModuleVar` into `slot_ref`.
    pub fn stored_values(&self, slot_ref: ModuleSlotRef) -> &[(FuncId, ValueId)] {
        self.slot_stores
            .get(&slot_ref)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Topological dependency-first order of `func_main_0` initializers across records.
    pub fn init_order(&self) -> &[FuncId] {
        &self.init_order
    }

    /// Whether `class_id`'s transitive `export * from` graph reaches an
    /// unresolved external module request (meaning `import * as ns` on
    /// `class_id` may expose unmodeled properties).
    pub fn has_unresolved_star(&self, class_id: ClassId) -> bool {
        self.unresolved_star_classes.contains(&class_id)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExportEdgeKind {
    Indirect,
    Star,
}

#[derive(Clone, Default)]
struct MemoExportEntry {
    slots: Vec<ModuleSlotRef>,
    namespace_classes: Vec<ClassId>,
    json_consts: Vec<ConstId>,
    external_imports: Vec<(Sym, Sym)>,
    direct_unresolved: bool,
    has_external_star: bool,
}

impl MemoExportEntry {
    fn found_any(&self) -> bool {
        !self.slots.is_empty() || !self.namespace_classes.is_empty() || !self.json_consts.is_empty()
    }

    fn to_target(&self) -> ExternalSlotTarget {
        ExternalSlotTarget {
            slots: self.slots.clone(),
            namespace_classes: self.namespace_classes.clone(),
            json_consts: self.json_consts.clone(),
            external_imports: self.external_imports.clone(),
            unresolved_external: self.direct_unresolved
                || self.has_external_star
                || !self.found_any(),
        }
    }
}

struct ExpandedExportNode {
    base: MemoExportEntry,
    edges: Vec<((ClassId, String), ExportEdgeKind)>,
}

struct ExportResolveCtx<'a, F> {
    module: &'a Module,
    esm_by_class: &'a BTreeMap<ClassId, EsModule>,
    json_by_class: &'a BTreeMap<ClassId, ConstId>,
    local_name_to_slot: &'a BTreeMap<ClassId, HashMap<String, u32>>,
    resolve_spec: &'a F,
    star_names_memo: std::cell::RefCell<HashMap<ClassId, (BTreeSet<String>, bool)>>,
    export_memo: std::cell::RefCell<HashMap<(ClassId, String), MemoExportEntry>>,
}

impl<'a, F> ExportResolveCtx<'a, F>
where
    F: Fn(ClassId, Sym) -> Option<ClassId>,
{
    fn resolve_export_cached(
        &self,
        root_cid: ClassId,
        root_export_name: &str,
    ) -> ExternalSlotTarget {
        let key = (root_cid, root_export_name.to_owned());
        if let Some(hit) = self.export_memo.borrow().get(&key) {
            return hit.to_target();
        }
        self.ensure_memoized(&key);
        self.export_memo.borrow().get(&key).map_or_else(
            || ExternalSlotTarget {
                unresolved_external: true,
                ..ExternalSlotTarget::default()
            },
            MemoExportEntry::to_target,
        )
    }

    fn collect_exported_names_cached(&self, root_cid: ClassId) -> (BTreeSet<String>, bool) {
        let (mut out, has_ext_star) = self.star_exported_names_cached(root_cid);
        if self.json_by_class.contains_key(&root_cid) {
            out.insert("default".to_owned());
        }
        if let Some(esm) = self.esm_by_class.get(&root_cid) {
            for exp in &esm.exports {
                if let ExportDecl::Local { export_name, .. }
                | ExportDecl::Indirect { export_name, .. } = exp
                    && sym_str(self.module, *export_name) == "default"
                {
                    out.insert("default".to_owned());
                }
            }
        }
        (out, has_ext_star)
    }

    fn star_exported_names_cached(&self, root_cid: ClassId) -> (BTreeSet<String>, bool) {
        if let Some(hit) = self.star_names_memo.borrow().get(&root_cid) {
            return hit.clone();
        }
        // Iterative Tarjan SCC over `ExportDecl::Star` module graph so cyclic
        // `export * from` chains populate both exported names and monotone
        // `has_ext_star` across every SCC member in `O(M + E_star)`.
        struct StarFrame {
            cid: ClassId,
            children: Vec<ClassId>,
            idx: usize,
            local_names: BTreeSet<String>,
            local_ext_star: bool,
        }

        let mut index_counter = 0u32;
        let mut indices: HashMap<ClassId, u32> = HashMap::new();
        let mut lowlink: HashMap<ClassId, u32> = HashMap::new();
        let mut on_stack: HashSet<ClassId> = HashSet::new();
        let mut scc_stack: Vec<(ClassId, Vec<ClassId>, BTreeSet<String>, bool)> = Vec::new();
        let mut dfs: Vec<StarFrame> = Vec::new();

        let make_frame = |cid: ClassId| -> StarFrame {
            let mut local_names = BTreeSet::new();
            let mut children = Vec::new();
            let mut local_ext_star = false;
            if let Some(esm) = self.esm_by_class.get(&cid) {
                for exp in &esm.exports {
                    match exp {
                        ExportDecl::Local { export_name, .. }
                        | ExportDecl::Indirect { export_name, .. } => {
                            let s = sym_str(self.module, *export_name);
                            if !s.is_empty() && s != "default" {
                                local_names.insert(s.to_owned());
                            }
                        }
                        ExportDecl::Star { module_request } => {
                            if let Some(next_cid) = (self.resolve_spec)(cid, *module_request) {
                                children.push(next_cid);
                            } else {
                                local_ext_star = true;
                            }
                        }
                    }
                }
            }
            StarFrame {
                cid,
                children,
                idx: 0,
                local_names,
                local_ext_star,
            }
        };

        index_counter += 1;
        indices.insert(root_cid, index_counter);
        lowlink.insert(root_cid, index_counter);
        on_stack.insert(root_cid);
        let first = make_frame(root_cid);
        scc_stack.push((
            root_cid,
            first.children.clone(),
            first.local_names.clone(),
            first.local_ext_star,
        ));
        dfs.push(first);

        while let Some(top) = dfs.last_mut() {
            let u = top.cid;
            if top.idx < top.children.len() {
                let w = top.children[top.idx];
                top.idx += 1;
                if self.star_names_memo.borrow().contains_key(&w) {
                    continue;
                }
                if let std::collections::hash_map::Entry::Vacant(e) = indices.entry(w) {
                    index_counter += 1;
                    e.insert(index_counter);
                    lowlink.insert(w, index_counter);
                    on_stack.insert(w);
                    let next_f = make_frame(w);
                    scc_stack.push((
                        w,
                        next_f.children.clone(),
                        next_f.local_names.clone(),
                        next_f.local_ext_star,
                    ));
                    dfs.push(next_f);
                } else if on_stack.contains(&w) {
                    let w_idx = indices[&w];
                    if let Some(u_low) = lowlink.get_mut(&u) {
                        *u_low = (*u_low).min(w_idx);
                    }
                }
            } else {
                let finished = dfs.pop();
                if let (Some(fin), Some(parent)) = (finished, dfs.last())
                    && let Some(&fin_low) = lowlink.get(&fin.cid)
                    && let Some(p_low) = lowlink.get_mut(&parent.cid)
                {
                    *p_low = (*p_low).min(fin_low);
                }
                if indices.get(&u) == lowlink.get(&u) {
                    let mut members = Vec::new();
                    let mut union_names = BTreeSet::new();
                    let mut union_ext = false;
                    while let Some((m_cid, m_children, m_names, m_ext)) = scc_stack.pop() {
                        on_stack.remove(&m_cid);
                        union_names.extend(m_names);
                        union_ext |= m_ext;
                        members.push((m_cid, m_children));
                        if m_cid == u {
                            break;
                        }
                    }
                    let memo_ref = self.star_names_memo.borrow();
                    for (_, m_children) in &members {
                        for ch in m_children {
                            if let Some((ch_names, ch_ext)) = memo_ref.get(ch) {
                                union_names.extend(ch_names.iter().cloned());
                                union_ext |= *ch_ext;
                            }
                        }
                    }
                    drop(memo_ref);
                    let mut memo_mut = self.star_names_memo.borrow_mut();
                    for (m_cid, _) in members {
                        memo_mut.insert(m_cid, (union_names.clone(), union_ext));
                    }
                }
            }
        }

        self.star_names_memo
            .borrow()
            .get(&root_cid)
            .cloned()
            .unwrap_or_default()
    }

    fn expand_node(&self, cid: ClassId, export_name: &str) -> ExpandedExportNode {
        let mut base = MemoExportEntry::default();
        let mut edges = Vec::new();

        if export_name == "default"
            && let Some(&jc) = self.json_by_class.get(&cid)
        {
            base.json_consts.push(jc);
            return ExpandedExportNode { base, edges };
        }
        let Some(esm) = self.esm_by_class.get(&cid) else {
            base.direct_unresolved = true;
            return ExpandedExportNode { base, edges };
        };

        let mut matched_direct = false;
        for exp in &esm.exports {
            match exp {
                ExportDecl::Local {
                    local_name,
                    export_name: ename,
                } if sym_str(self.module, *ename) == export_name => {
                    matched_direct = true;
                    let lname = sym_str(self.module, *local_name);
                    if let Some(&slot) =
                        self.local_name_to_slot.get(&cid).and_then(|m| m.get(lname))
                    {
                        let sr = ModuleSlotRef {
                            class_id: cid,
                            slot,
                        };
                        if !base.slots.contains(&sr) {
                            base.slots.push(sr);
                        }
                    } else {
                        base.direct_unresolved = true;
                    }
                }
                ExportDecl::Indirect {
                    export_name: ename,
                    import_name,
                    module_request,
                } if sym_str(self.module, *ename) == export_name => {
                    matched_direct = true;
                    let iname = sym_str(self.module, *import_name);
                    if let Some(next_cid) = (self.resolve_spec)(cid, *module_request) {
                        if iname == "*" {
                            // `export * as ns from "./sub"` re-exports `next_cid`'s
                            // module namespace object — preserve namespace identity
                            // instead of flattening exports into bare slots (`#82`).
                            if !base.namespace_classes.contains(&next_cid) {
                                base.namespace_classes.push(next_cid);
                            }
                        } else {
                            edges.push(((next_cid, iname.to_owned()), ExportEdgeKind::Indirect));
                        }
                    } else {
                        base.direct_unresolved = true;
                        let pair = (*module_request, *import_name);
                        if !base.external_imports.contains(&pair) {
                            base.external_imports.push(pair);
                        }
                    }
                }
                _ => {}
            }
        }

        if matched_direct {
            return ExpandedExportNode { base, edges };
        }
        if export_name == "default" {
            base.direct_unresolved = true;
            return ExpandedExportNode { base, edges };
        }

        // ECMA-262 §16.2.1.6.2: `export * from` forwards non-`default` bindings;
        // external star targets (`has_external_star`) propagate monotonically (`|=`).
        for exp in &esm.exports {
            if let ExportDecl::Star { module_request } = exp {
                if let Some(next_cid) = (self.resolve_spec)(cid, *module_request) {
                    edges.push(((next_cid, export_name.to_owned()), ExportEdgeKind::Star));
                } else {
                    base.has_external_star = true;
                }
            }
        }

        ExpandedExportNode { base, edges }
    }

    fn ensure_memoized(&self, root_key: &(ClassId, String)) {
        // Iterative Tarjan SCC over `(ClassId, export_name)` states: each
        // `(module, export_name)` pair is expanded at most once (`O(M * E)`),
        // and `direct_unresolved` / `has_external_star` propagate monotonically
        // (`|=`) across cyclic `export * from` components without overwriting.
        struct DfsFrame {
            key: (ClassId, String),
            edges: Vec<((ClassId, String), ExportEdgeKind)>,
            idx: usize,
        }

        let mut index_counter = 0u32;
        let mut indices: HashMap<(ClassId, String), u32> = HashMap::new();
        let mut lowlink: HashMap<(ClassId, String), u32> = HashMap::new();
        let mut on_stack: HashSet<(ClassId, String)> = HashSet::new();
        let mut scc_stack: Vec<((ClassId, String), ExpandedExportNode)> = Vec::new();
        let mut dfs: Vec<DfsFrame> = Vec::new();

        let root_exp = self.expand_node(root_key.0, &root_key.1);
        index_counter += 1;
        indices.insert(root_key.clone(), index_counter);
        lowlink.insert(root_key.clone(), index_counter);
        on_stack.insert(root_key.clone());
        dfs.push(DfsFrame {
            key: root_key.clone(),
            edges: root_exp.edges.clone(),
            idx: 0,
        });
        scc_stack.push((root_key.clone(), root_exp));

        while let Some(top) = dfs.last_mut() {
            let u_key = top.key.clone();
            if top.idx < top.edges.len() {
                let (w_key, _) = top.edges[top.idx].clone();
                top.idx += 1;
                if self.export_memo.borrow().contains_key(&w_key) {
                    continue;
                }
                if !indices.contains_key(&w_key) {
                    let w_exp = self.expand_node(w_key.0, &w_key.1);
                    index_counter += 1;
                    indices.insert(w_key.clone(), index_counter);
                    lowlink.insert(w_key.clone(), index_counter);
                    on_stack.insert(w_key.clone());
                    dfs.push(DfsFrame {
                        key: w_key.clone(),
                        edges: w_exp.edges.clone(),
                        idx: 0,
                    });
                    scc_stack.push((w_key, w_exp));
                } else if on_stack.contains(&w_key) {
                    let w_idx = indices[&w_key];
                    if let Some(u_low) = lowlink.get_mut(&u_key) {
                        *u_low = (*u_low).min(w_idx);
                    }
                }
            } else {
                let finished = dfs.pop();
                if let (Some(fin), Some(parent)) = (finished, dfs.last())
                    && let Some(&fin_low) = lowlink.get(&fin.key)
                    && let Some(p_low) = lowlink.get_mut(&parent.key)
                {
                    *p_low = (*p_low).min(fin_low);
                }
                if indices.get(&u_key) == lowlink.get(&u_key) {
                    let mut members: Vec<((ClassId, String), ExpandedExportNode)> = Vec::new();
                    let mut scc_set: HashSet<(ClassId, String)> = HashSet::new();
                    while let Some((m_key, m_exp)) = scc_stack.pop() {
                        on_stack.remove(&m_key);
                        scc_set.insert(m_key.clone());
                        let done = m_key == u_key;
                        members.push((m_key, m_exp));
                        if done {
                            break;
                        }
                    }

                    let mut slot_set = BTreeSet::new();
                    let mut ns_set = BTreeSet::new();
                    let mut json_consts = Vec::new();
                    let mut external_imports = Vec::new();
                    let mut direct_unresolved = false;
                    let mut has_external_star = false;

                    // Process in discovery order (`members` was popped in reverse).
                    let memo_ref = self.export_memo.borrow();
                    for (_, m_exp) in members.iter().rev() {
                        slot_set.extend(m_exp.base.slots.iter().copied());
                        ns_set.extend(m_exp.base.namespace_classes.iter().copied());
                        for &jc in &m_exp.base.json_consts {
                            if !json_consts.contains(&jc) {
                                json_consts.push(jc);
                            }
                        }
                        for &ext_imp in &m_exp.base.external_imports {
                            if !external_imports.contains(&ext_imp) {
                                external_imports.push(ext_imp);
                            }
                        }
                        direct_unresolved |= m_exp.base.direct_unresolved;
                        has_external_star |= m_exp.base.has_external_star;

                        for (target_key, edge_kind) in &m_exp.edges {
                            if scc_set.contains(target_key) {
                                continue;
                            }
                            if let Some(child) = memo_ref.get(target_key) {
                                slot_set.extend(child.slots.iter().copied());
                                ns_set.extend(child.namespace_classes.iter().copied());
                                for &jc in &child.json_consts {
                                    if !json_consts.contains(&jc) {
                                        json_consts.push(jc);
                                    }
                                }
                                for &ext_imp in &child.external_imports {
                                    if !external_imports.contains(&ext_imp) {
                                        external_imports.push(ext_imp);
                                    }
                                }
                                direct_unresolved |= child.direct_unresolved;
                                has_external_star |= child.has_external_star;
                                if *edge_kind == ExportEdgeKind::Indirect && !child.found_any() {
                                    direct_unresolved = true;
                                }
                            } else {
                                direct_unresolved = true;
                            }
                        }
                    }
                    drop(memo_ref);

                    // If an `Indirect` edge stayed wholly inside the SCC and the SCC
                    // found no binding, `!found_any()` in `to_target()` already marks
                    // `unresolved_external = true`; if an `Indirect` edge inside the
                    // SCC coexisted with another member's binding, check in-SCC indirects.
                    let scc_entry = MemoExportEntry {
                        slots: slot_set.into_iter().collect(),
                        namespace_classes: ns_set.into_iter().collect(),
                        json_consts,
                        external_imports,
                        direct_unresolved,
                        has_external_star,
                    };
                    let mut memo_mut = self.export_memo.borrow_mut();
                    for (m_key, _) in members {
                        memo_mut.insert(m_key, scc_entry.clone());
                    }
                }
            }
        }
    }
}

fn sym_str(module: &Module, sym: Sym) -> &str {
    module.sym.resolve(sym).unwrap_or("")
}

fn strip_descriptor(desc: &str) -> &str {
    OhmUrl::strip_descriptor(desc)
}

fn is_sdk_specifier(s: &str) -> bool {
    OhmUrl::is_sdk_specifier(s)
}

/// Parse `@normalized:<rest>` or bare `&<rest>` OHMUrl forms into
/// `(mod_name, bundle_name, import_path)` via [`OhmUrl`].
fn parse_normalized_ohmurl(raw: &str) -> Option<(&str, &str, &str)> {
    let parsed = OhmUrl::parse(raw)?;
    if matches!(parsed.kind, OhmUrlKind::Normalized { .. }) && !parsed.import_path.is_empty() {
        Some((parsed.module_name, parsed.bundle_name, parsed.import_path))
    } else {
        None
    }
}

fn peel_ohmurl(raw: &str) -> &str {
    OhmUrl::peel_import_path(raw)
}

fn strip_known_ext(path: &str) -> &str {
    for ext in [
        ".d.ets", ".d.ts", ".ets", ".ts", ".mjs", ".cjs", ".js", ".json",
    ] {
        if let Some(s) = path.strip_suffix(ext) {
            return s;
        }
    }
    path
}

fn normalize_logical_path(raw: &str) -> String {
    let peeled = peel_ohmurl(raw);
    let segs: Vec<&str> = peeled
        .split(['/', '\\'])
        .filter(|s| !s.is_empty() && *s != "." && *s != "..")
        .collect();
    strip_known_ext(&segs.join("/")).to_owned()
}

fn push_unique(out: &mut Vec<String>, candidate: String) {
    if !candidate.is_empty() && !out.contains(&candidate) {
        out.push(candidate);
    }
}

fn collect_candidates(raw: &str, extra_norm: Option<&str>) -> Vec<String> {
    let mut out = Vec::with_capacity(10);
    push_unique(&mut out, raw.to_owned());
    push_unique(&mut out, strip_known_ext(raw).to_owned());

    if let Some((mod_name, bundle_name, import_path)) = parse_normalized_ohmurl(raw) {
        let imp = strip_known_ext(import_path);
        let dots = imp.replace('/', ".");
        if !bundle_name.is_empty() {
            push_unique(&mut out, format!("{bundle_name}/{imp}"));
            push_unique(&mut out, format!("{bundle_name}.{dots}"));
        }
        push_unique(&mut out, import_path.to_owned());
        push_unique(&mut out, imp.to_owned());
        push_unique(&mut out, import_path.replace('/', "."));
        push_unique(&mut out, dots.clone());
        if !bundle_name.is_empty()
            && let Some(sub) = imp.strip_prefix(&format!("{bundle_name}/"))
        {
            push_unique(&mut out, sub.to_owned());
            push_unique(&mut out, sub.replace('/', "."));
        }
        if !mod_name.is_empty() {
            if !imp.starts_with(&format!("{mod_name}/")) {
                push_unique(&mut out, format!("{mod_name}/{imp}"));
                push_unique(&mut out, format!("{mod_name}.{dots}"));
            }
            let mod_marker = format!("/{mod_name}/");
            if let Some(pos) = imp.find(&mod_marker) {
                let tail = &imp[pos + 1..];
                push_unique(&mut out, tail.to_owned());
                push_unique(&mut out, tail.replace('/', "."));
            } else if let Some((_, after_bundle)) = imp.split_once('/')
                && after_bundle == mod_name
            {
                push_unique(&mut out, after_bundle.to_owned());
            }
        }
    }

    let p = peel_ohmurl(raw);
    let p_no_ext = strip_known_ext(p);
    push_unique(&mut out, p.to_owned());
    push_unique(&mut out, p_no_ext.to_owned());
    push_unique(&mut out, p.replace('/', "."));
    push_unique(&mut out, p_no_ext.replace('/', "."));

    if p.contains('@') {
        push_unique(&mut out, p.replace('@', "/"));
        push_unique(&mut out, p_no_ext.replace('@', "/"));
    }

    if let Some(norm) = extra_norm {
        push_unique(&mut out, norm.to_owned());
        push_unique(&mut out, norm.replace('/', "."));
        if norm.contains('@') {
            push_unique(&mut out, norm.replace('@', "/"));
        }
    }

    out
}

fn candidate_keys(raw_name: &str, norm_no_ext: &str) -> Vec<String> {
    collect_candidates(raw_name, Some(norm_no_ext))
}

fn resolve_posix_relative(from_path_no_ext: &str, rel_spec: &str) -> Option<String> {
    let mut parts: Vec<&str> = from_path_no_ext.split('/').collect();
    parts.pop();
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

fn resolve_dot_relative(from_dot_no_ext: &str, rel_spec: &str) -> Option<String> {
    let mut parts: Vec<&str> = from_dot_no_ext.split('.').collect();
    parts.pop();
    for seg in rel_spec.split('/') {
        match seg {
            "" | "." => {}
            ".." => {
                parts.pop()?;
            }
            other => parts.push(other),
        }
    }
    Some(parts.join("."))
}

fn json_const_of(module: &Module, cls: &ClassData) -> Option<ConstId> {
    for f in &cls.fields {
        if sym_str(module, f.name) == "jsonFileContent"
            && let Some(cid) = f.initial_value
            && matches!(module.consts.get(cid), Some(Const::String(_)))
        {
            return Some(cid);
        }
    }
    None
}

pub(crate) fn is_standalone_single_module(module: &Module, harness_func: Option<FuncId>) -> bool {
    let mut non_synth = 0usize;
    let mut has_global = false;
    for cls in &module.classes {
        let desc = sym_str(module, cls.descriptor);
        if SYNTHETIC_DESCRIPTORS.contains(&desc) {
            continue;
        }
        let has_real_methods = cls.methods.iter().any(|&fid| Some(fid) != harness_func);
        if !has_real_methods && cls.es_module.is_none() && json_const_of(module, cls).is_none() {
            continue;
        }
        non_synth += 1;
        if desc == "L_GLOBAL;" {
            has_global = true;
        }
    }
    non_synth == 1 && has_global
}

// ── Multi-`.abc` IR combiner (`merge_ir_modules` / `merge_ir_modules_owned`) ──

/// Combine multiple lifted [`Module`]s (for example, `entry.hap` + shared
/// `.hsp` libraries from an `.app` container) into one unified [`Module`] so
/// cross-container `@bundle:` / ES module imports resolve in a single whole-app
/// call-graph, PTA, and IFDS pass.
///
/// Each input pair `(module_name, module)` has standalone `L_GLOBAL;` records
/// renamed to `L<module_name>;` with top-level `imports`/`exports`/`module_requests`
/// promoted onto that class's [`ClassData::es_module`].
///
/// Prefer [`merge_ir_modules_owned`] when the caller can yield owned [`Module`]s
/// by value to avoid cloning module `0` and stream modules `1..N` one at a time.
pub fn merge_ir_modules(inputs: &[(&str, &Module)]) -> Module {
    merge_ir_modules_owned(inputs.iter().map(|&(name, m)| (name, m.clone())))
}

/// Streaming by-value multi-`.abc` [`Module`] combiner (`#71`).
///
/// - **Single-element fast path**: returns `m` directly without cloning when
///   `m` already carries per-record [`ClassData::es_module`] metadata, or
///   normalizes standalone `L_GLOBAL;` in-place when `m` is a standalone module.
/// - **Multi-module streaming path**: normalizes module `0` in-place as the
///   accumulator, then streams modules `1..N` one at a time by value, remapping
///   and moving each module's arenas into the accumulator and dropping each
///   input [`Module`] before advancing `inputs`.
pub fn merge_ir_modules_owned<I, S>(inputs: I) -> Module
where
    I: IntoIterator<Item = (S, Module)>,
    S: AsRef<str>,
{
    let mut iter = inputs.into_iter();
    let Some((first_name, mut out)) = iter.next() else {
        return Module::new();
    };
    let Some((second_name, second_mod)) = iter.next() else {
        if out.classes.iter().any(|c| c.es_module.is_some()) {
            return out;
        }
        normalize_module_in_place(&mut out, first_name.as_ref());
        return out;
    };

    normalize_module_in_place(&mut out, first_name.as_ref());
    drop(first_name);

    append_module_owned(&mut out, second_name.as_ref(), second_mod);
    drop(second_name);

    for (mod_name, src) in iter {
        append_module_owned(&mut out, mod_name.as_ref(), src);
    }
    out
}

fn normalize_module_in_place(m: &mut Module, mod_name: &str) {
    let standalone = is_standalone_single_module(m, None);
    let top_imports = std::mem::take(&mut m.imports);
    let top_exports = std::mem::take(&mut m.exports);
    let top_reqs = std::mem::take(&mut m.module_requests);
    if !standalone {
        return;
    }

    let has_top_esm = !top_imports.is_empty() || !top_exports.is_empty() || !top_reqs.is_empty();
    let renamed_syms = (!mod_name.is_empty()).then(|| {
        let d = m.sym.intern(&format!("L{mod_name};"));
        let n = m.sym.intern(mod_name);
        (d, n)
    });
    for cls in &mut m.classes {
        if m.sym.resolve(cls.descriptor) == Some("L_GLOBAL;") {
            if let Some((new_desc, new_name)) = renamed_syms {
                cls.descriptor = new_desc;
                cls.name = new_name;
            }
            if cls.es_module.is_none() && has_top_esm {
                cls.es_module = Some(EsModule {
                    imports: top_imports.clone(),
                    exports: top_exports.clone(),
                    module_requests: top_reqs.clone(),
                });
            }
        }
    }
}

struct AppendRemapper<'a> {
    sym_map: &'a [Sym],
    dst_sym: &'a mut SymbolTable,
    oob_empty_sym: Option<Sym>,
    const_map: &'a [ConstId],
    class_offset: u32,
    func_offset: u32,
    block_offset: u32,
    inst_offset: u32,
    value_offset: u32,
}

impl IdRemapper for AppendRemapper<'_> {
    #[inline]
    fn remap_sym(&mut self, id: Sym) -> Sym {
        self.sym_map.get(id.index()).copied().unwrap_or_else(|| {
            *self
                .oob_empty_sym
                .get_or_insert_with(|| self.dst_sym.intern(""))
        })
    }

    #[inline]
    fn remap_const(&mut self, id: ConstId) -> ConstId {
        self.const_map.get(id.index()).copied().unwrap_or(id)
    }

    #[inline]
    fn remap_class(&mut self, id: ClassId) -> ClassId {
        ClassId::new(self.class_offset.wrapping_add(id.raw()))
    }

    #[inline]
    fn remap_func(&mut self, id: FuncId) -> FuncId {
        FuncId::new(self.func_offset.wrapping_add(id.raw()))
    }

    #[inline]
    fn remap_block(&mut self, id: BlockId) -> BlockId {
        BlockId::new(self.block_offset.wrapping_add(id.raw()))
    }

    #[inline]
    fn remap_inst(&mut self, id: InstId) -> InstId {
        InstId::new(self.inst_offset.wrapping_add(id.raw()))
    }

    #[inline]
    fn remap_value(&mut self, id: ValueId) -> ValueId {
        ValueId::new(self.value_offset.wrapping_add(id.raw()))
    }
}

fn append_module_owned(dst: &mut Module, mod_name: &str, mut src: Module) {
    normalize_module_in_place(&mut src, mod_name);

    let class_offset = dst.classes.len() as u32;
    let func_offset = dst.functions.len() as u32;
    let block_offset = dst.blocks.len() as u32;
    let inst_offset = dst.insts.len() as u32;
    let value_offset = dst.values.len() as u32;

    let mut sym_map = Vec::with_capacity(src.sym.len());
    for i in 0..src.sym.len() {
        let s = Sym::new(i as u32);
        let mapped = match src.sym.raw_mutf8(s) {
            Some(raw) => dst.sym.intern_raw_mutf8(raw),
            None => dst.sym.intern(src.sym.resolve(s).unwrap_or("")),
        };
        sym_map.push(mapped);
    }
    src.sym = SymbolTable::new();
    src.sym.drop_index();

    let mut oob_empty_sym = None;
    let const_map = remap_consts_into(
        &src.consts,
        &mut dst.consts,
        &sym_map,
        &mut dst.sym,
        &mut oob_empty_sym,
        func_offset,
    );
    src.consts = ConstPool::new();
    src.consts.drop_index();

    let mut remapper = AppendRemapper {
        sym_map: &sym_map,
        dst_sym: &mut dst.sym,
        oob_empty_sym,
        const_map: &const_map,
        class_offset,
        func_offset,
        block_offset,
        inst_offset,
        value_offset,
    };
    remap_module_body(&mut src, &mut remapper);

    dst.classes.append(&mut src.classes);
    dst.functions.append(&mut src.functions);
    dst.blocks.append(&mut src.blocks);
    dst.insts.append(&mut src.insts);
    dst.values.append(&mut src.values);
}

fn remap_consts_into(
    src_consts: &ConstPool,
    dst_consts: &mut ConstPool,
    sym_map: &[Sym],
    dst_sym: &mut SymbolTable,
    oob_empty_sym: &mut Option<Sym>,
    func_offset: u32,
) -> Vec<ConstId> {
    enum ConstVisit {
        Enter(ConstId),
        FinishArray(ConstId, Vec<ConstId>),
        FinishTypedArray(ConstId, abcd_ir::TypedArrayTag, Vec<ConstId>),
        FinishObject(ConstId, Vec<ConstId>, Vec<ConstId>),
        FinishBufferRef(ConstId, ConstId),
    }

    let mut map_sym = |s: Sym| -> Sym {
        sym_map
            .get(s.index())
            .copied()
            .unwrap_or_else(|| *oob_empty_sym.get_or_insert_with(|| dst_sym.intern("")))
    };

    let len = src_consts.len();
    let mut mapped: Vec<Option<ConstId>> = vec![None; len];
    let mut in_progress: HashSet<ConstId> = HashSet::new();
    let mut undef_fallback: Option<ConstId> = None;
    let mut stack: Vec<ConstVisit> = Vec::new();

    for root_idx in 0..len {
        let root_cid = ConstId::new(root_idx as u32);
        if mapped[root_idx].is_some() {
            continue;
        }
        stack.push(ConstVisit::Enter(root_cid));
        while let Some(step) = stack.pop() {
            match step {
                ConstVisit::Enter(cid) => {
                    let Some(slot) = mapped.get(cid.index()) else {
                        continue;
                    };
                    if slot.is_some() || !in_progress.insert(cid) {
                        continue;
                    }
                    let leaf = match src_consts.get(cid) {
                        None | Some(Const::Undefined) => Some(Const::Undefined),
                        Some(Const::Hole) => Some(Const::Hole),
                        Some(Const::Null) => Some(Const::Null),
                        Some(Const::Bool(b)) => Some(Const::Bool(*b)),
                        Some(Const::Int8(v)) => Some(Const::Int8(*v)),
                        Some(Const::Int32(v)) => Some(Const::Int32(*v)),
                        Some(Const::Float32(bits)) => Some(Const::Float32(*bits)),
                        Some(Const::Number(bits)) => Some(Const::Number(*bits)),
                        Some(Const::Int64(v)) => Some(Const::Int64(*v)),
                        Some(Const::UInt64(v)) => Some(Const::UInt64(*v)),
                        Some(Const::Accessor(v)) => Some(Const::Accessor(*v)),
                        Some(Const::MethodAffiliate(v)) => Some(Const::MethodAffiliate(*v)),
                        Some(Const::BuiltinTypeIndex(v)) => Some(Const::BuiltinTypeIndex(*v)),
                        Some(Const::EtsImplements(s)) => Some(Const::EtsImplements(map_sym(*s))),
                        Some(Const::LitNull(v)) => Some(Const::LitNull(*v)),
                        Some(Const::String(s)) => Some(Const::String(map_sym(*s))),
                        Some(Const::BigInt(s)) => Some(Const::BigInt(map_sym(*s))),
                        Some(Const::MethodRef { func, kind }) => Some(Const::MethodRef {
                            func: FuncId::new(func_offset.wrapping_add(func.raw())),
                            kind: *kind,
                        }),
                        Some(Const::ArrayLiteral(items)) => {
                            let items_cloned = items.clone();
                            stack.push(ConstVisit::FinishArray(cid, items.clone()));
                            for &ch in items_cloned.iter().rev() {
                                if mapped.get(ch.index()).is_some_and(Option::is_none) {
                                    stack.push(ConstVisit::Enter(ch));
                                }
                            }
                            None
                        }
                        Some(Const::TypedArrayLiteral { tag, items }) => {
                            let items_cloned = items.clone();
                            stack.push(ConstVisit::FinishTypedArray(cid, *tag, items.clone()));
                            for &ch in items_cloned.iter().rev() {
                                if mapped.get(ch.index()).is_some_and(Option::is_none) {
                                    stack.push(ConstVisit::Enter(ch));
                                }
                            }
                            None
                        }
                        Some(Const::ObjectLiteral { keys, values }) => {
                            let keys_cloned = keys.clone();
                            let values_cloned = values.clone();
                            stack.push(ConstVisit::FinishObject(cid, keys.clone(), values.clone()));
                            for &ch in values_cloned.iter().rev() {
                                if mapped.get(ch.index()).is_some_and(Option::is_none) {
                                    stack.push(ConstVisit::Enter(ch));
                                }
                            }
                            for &ch in keys_cloned.iter().rev() {
                                if mapped.get(ch.index()).is_some_and(Option::is_none) {
                                    stack.push(ConstVisit::Enter(ch));
                                }
                            }
                            None
                        }
                        Some(Const::LiteralBufferRef(inner)) => {
                            let inner_id = *inner;
                            stack.push(ConstVisit::FinishBufferRef(cid, inner_id));
                            if mapped.get(inner_id.index()).is_some_and(Option::is_none) {
                                stack.push(ConstVisit::Enter(inner_id));
                            }
                            None
                        }
                    };
                    if let Some(c) = leaf {
                        in_progress.remove(&cid);
                        mapped[cid.index()] = Some(dst_consts.push(c));
                    }
                }
                ConstVisit::FinishArray(cid, items) => {
                    in_progress.remove(&cid);
                    let mut out_items = Vec::with_capacity(items.len());
                    for ch in items {
                        let m = match mapped.get(ch.index()).copied().flatten() {
                            Some(id) => id,
                            None => *undef_fallback
                                .get_or_insert_with(|| dst_consts.push(Const::Undefined)),
                        };
                        out_items.push(m);
                    }
                    mapped[cid.index()] = Some(dst_consts.push(Const::ArrayLiteral(out_items)));
                }
                ConstVisit::FinishTypedArray(cid, tag, items) => {
                    in_progress.remove(&cid);
                    let mut out_items = Vec::with_capacity(items.len());
                    for ch in items {
                        let m = match mapped.get(ch.index()).copied().flatten() {
                            Some(id) => id,
                            None => *undef_fallback
                                .get_or_insert_with(|| dst_consts.push(Const::Undefined)),
                        };
                        out_items.push(m);
                    }
                    mapped[cid.index()] = Some(dst_consts.push(Const::TypedArrayLiteral {
                        tag,
                        items: out_items,
                    }));
                }
                ConstVisit::FinishObject(cid, keys, values) => {
                    in_progress.remove(&cid);
                    let mut out_keys = Vec::with_capacity(keys.len());
                    for ch in keys {
                        let m = match mapped.get(ch.index()).copied().flatten() {
                            Some(id) => id,
                            None => *undef_fallback
                                .get_or_insert_with(|| dst_consts.push(Const::Undefined)),
                        };
                        out_keys.push(m);
                    }
                    let mut out_values = Vec::with_capacity(values.len());
                    for ch in values {
                        let m = match mapped.get(ch.index()).copied().flatten() {
                            Some(id) => id,
                            None => *undef_fallback
                                .get_or_insert_with(|| dst_consts.push(Const::Undefined)),
                        };
                        out_values.push(m);
                    }
                    mapped[cid.index()] = Some(dst_consts.push(Const::ObjectLiteral {
                        keys: out_keys,
                        values: out_values,
                    }));
                }
                ConstVisit::FinishBufferRef(cid, inner) => {
                    in_progress.remove(&cid);
                    let m = match mapped.get(inner.index()).copied().flatten() {
                        Some(id) => id,
                        None => {
                            *undef_fallback.get_or_insert_with(|| dst_consts.push(Const::Undefined))
                        }
                    };
                    mapped[cid.index()] = Some(dst_consts.push(Const::LiteralBufferRef(m)));
                }
            }
        }
    }

    mapped
        .into_iter()
        .map(|opt| opt.unwrap_or_else(|| dst_consts.push(Const::Undefined)))
        .collect()
}

#[cfg(test)]
mod tests;
