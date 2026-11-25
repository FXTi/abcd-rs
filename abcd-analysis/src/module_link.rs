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

use abcd_ir::ValueDef;
use abcd_ir::consts::Const;
use abcd_ir::function::{
    Block, Catch, ColumnEntry, DebugData, Edge, FunctionData, Inst, LineEntry, LocalName,
    LocalScope, TryRegion, Value,
};
use abcd_ir::id::{BlockId, ClassId, ConstId, FuncId, InstId, Sym, ValueId};
use abcd_ir::module::{
    AnnValue, Annotation, ClassData, EsModule, ExportDecl, FieldData, ImportDecl, Module,
    ModuleRequest, Signature,
};
use abcd_ir::op::{Op, PropKey, SuperKey};
use abcd_ir::ty::{StaticTy, Ty};

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
    /// `(ClassId, local_slot)` → `(FuncId, ValueId)` definitions written via
    /// `Op::StoreModuleVar`.
    slot_stores: BTreeMap<ModuleSlotRef, Vec<(FuncId, ValueId)>>,
    /// Topological post-order of record `func_main_0` entry functions
    /// (dependencies initialized before importers).
    init_order: Vec<FuncId>,
    /// Whether this module carries multi-record `--merge-abc` ES module tables.
    has_multi_record_esm: bool,
}

impl ModuleLinkTable {
    /// Construct the cross-module resolution index for `module`.
    pub fn build(module: &Module) -> Self {
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
        let standalone = is_standalone_single_module(module);
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
                    let mut target = ExternalSlotTarget::default();
                    let imp_str = sym_str(module, *import_name);
                    if let Some(target_cid) = resolve_spec(cid, *module_request) {
                        dep_edges.entry(cid).or_default().push(target_cid);
                        let mut visited = HashSet::new();
                        ctx.resolve_export(target_cid, imp_str, &mut visited, &mut target);
                    } else {
                        target.unresolved_external = true;
                        target
                            .external_imports
                            .push((*module_request, *import_name));
                    }
                    target.slots.sort();
                    target.slots.dedup();
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

        // Precompute namespace export maps for every target record referenced by a namespace import
        // (and all ESM records generally).
        let mut namespace_exports: BTreeMap<ClassId, BTreeMap<Sym, Vec<ModuleSlotRef>>> =
            BTreeMap::new();
        let mut all_export_syms: BTreeMap<String, Vec<Sym>> = BTreeMap::new();
        for i in 0..module.sym.len() {
            let s = Sym::new(i as u32);
            if let Some(text) = module.sym.resolve(s) {
                all_export_syms.entry(text.to_owned()).or_default().push(s);
            }
        }
        for &cid in esm_by_class.keys() {
            let mut names = BTreeSet::new();
            ctx.collect_exported_names(cid, &mut HashSet::new(), &mut names);
            let mut sym_map: BTreeMap<Sym, Vec<ModuleSlotRef>> = BTreeMap::new();
            for ename in names {
                let mut target = ExternalSlotTarget::default();
                ctx.resolve_export(cid, &ename, &mut HashSet::new(), &mut target);
                target.slots.sort();
                target.slots.dedup();
                if !target.slots.is_empty()
                    && let Some(syms) = all_export_syms.get(&ename)
                {
                    for &sym in syms {
                        sym_map.insert(sym, target.slots.clone());
                    }
                }
            }
            if !sym_map.is_empty() {
                namespace_exports.insert(cid, sym_map);
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
            slot_stores,
            init_order,
            has_multi_record_esm: esm_record_count > 0,
        }
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
        self.block_func.get(block.index()).copied().flatten()
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
}

struct ExportResolveCtx<'a, F> {
    module: &'a Module,
    esm_by_class: &'a BTreeMap<ClassId, EsModule>,
    json_by_class: &'a BTreeMap<ClassId, ConstId>,
    local_name_to_slot: &'a BTreeMap<ClassId, HashMap<String, u32>>,
    resolve_spec: &'a F,
}

impl<'a, F> ExportResolveCtx<'a, F>
where
    F: Fn(ClassId, Sym) -> Option<ClassId>,
{
    fn resolve_export(
        &self,
        root_cid: ClassId,
        root_export_name: &str,
        visited: &mut HashSet<(ClassId, String)>,
        out: &mut ExternalSlotTarget,
    ) {
        enum ResolveStep {
            Call {
                cid: ClassId,
                export_name: String,
            },
            PushLocal(ModuleSlotRef),
            PushExternalImport {
                req: Sym,
                name: Sym,
            },
            MarkUnresolved,
            StarStep {
                next_cid: ClassId,
                export_name: String,
            },
            StarAfterChild {
                before_count: usize,
                saved_unres: bool,
            },
            StarFinish,
        }

        let mut stack: Vec<ResolveStep> = vec![ResolveStep::Call {
            cid: root_cid,
            export_name: root_export_name.to_owned(),
        }];
        let mut star_found: Vec<bool> = Vec::new();

        while let Some(step) = stack.pop() {
            match step {
                ResolveStep::PushLocal(slot_ref) => out.slots.push(slot_ref),
                ResolveStep::PushExternalImport { req, name } => {
                    out.unresolved_external = true;
                    out.external_imports.push((req, name));
                }
                ResolveStep::MarkUnresolved => {
                    out.unresolved_external = true;
                }
                ResolveStep::StarStep {
                    next_cid,
                    export_name,
                } => {
                    let before_count = out.slots.len() + out.json_consts.len();
                    let saved_unres = out.unresolved_external;
                    out.unresolved_external = false;
                    stack.push(ResolveStep::StarAfterChild {
                        before_count,
                        saved_unres,
                    });
                    stack.push(ResolveStep::Call {
                        cid: next_cid,
                        export_name,
                    });
                }
                ResolveStep::StarAfterChild {
                    before_count,
                    saved_unres,
                } => {
                    if out.slots.len() + out.json_consts.len() > before_count
                        && let Some(top) = star_found.last_mut()
                    {
                        *top = true;
                    }
                    out.unresolved_external = saved_unres;
                }
                ResolveStep::StarFinish => {
                    let found = star_found.pop().unwrap_or(false);
                    if !found {
                        out.unresolved_external = true;
                    }
                }
                ResolveStep::Call { cid, export_name } => {
                    if !visited.insert((cid, export_name.clone())) {
                        continue;
                    }
                    if export_name == "default"
                        && let Some(&jc) = self.json_by_class.get(&cid)
                    {
                        out.json_consts.push(jc);
                        continue;
                    }
                    let Some(esm) = self.esm_by_class.get(&cid) else {
                        out.unresolved_external = true;
                        continue;
                    };

                    let mut matched_direct = false;
                    let mut direct_actions: Vec<ResolveStep> = Vec::new();
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
                                    direct_actions.push(ResolveStep::PushLocal(ModuleSlotRef {
                                        class_id: cid,
                                        slot,
                                    }));
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
                                        // `export * as ns from "./sub"` re-exports namespace:
                                        // conservatively union all local slots of `next_cid`.
                                        let mut names = BTreeSet::new();
                                        self.collect_exported_names(
                                            next_cid,
                                            &mut HashSet::new(),
                                            &mut names,
                                        );
                                        for n in names {
                                            direct_actions.push(ResolveStep::Call {
                                                cid: next_cid,
                                                export_name: n,
                                            });
                                        }
                                    } else {
                                        direct_actions.push(ResolveStep::Call {
                                            cid: next_cid,
                                            export_name: iname.to_owned(),
                                        });
                                    }
                                } else {
                                    direct_actions.push(ResolveStep::PushExternalImport {
                                        req: *module_request,
                                        name: *import_name,
                                    });
                                }
                            }
                            _ => {}
                        }
                    }
                    if matched_direct || export_name == "default" {
                        if !matched_direct {
                            out.unresolved_external = true;
                        } else {
                            for act in direct_actions.into_iter().rev() {
                                stack.push(act);
                            }
                        }
                        continue;
                    }

                    // ECMA-262 §16.2.1.6.2: `export * from` forwards non-`default` bindings.
                    star_found.push(false);
                    stack.push(ResolveStep::StarFinish);
                    for exp in esm.exports.iter().rev() {
                        if let ExportDecl::Star { module_request } = exp {
                            if let Some(next_cid) = (self.resolve_spec)(cid, *module_request) {
                                stack.push(ResolveStep::StarStep {
                                    next_cid,
                                    export_name: export_name.clone(),
                                });
                            } else {
                                stack.push(ResolveStep::MarkUnresolved);
                            }
                        }
                    }
                }
            }
        }
    }

    fn collect_exported_names(
        &self,
        root_cid: ClassId,
        visited: &mut HashSet<ClassId>,
        out: &mut BTreeSet<String>,
    ) {
        let mut stack: Vec<(ClassId, bool)> = vec![(root_cid, true)];
        while let Some((cid, is_root)) = stack.pop() {
            if !visited.insert(cid) {
                continue;
            }
            if is_root && self.json_by_class.contains_key(&cid) {
                out.insert("default".to_owned());
            }
            let Some(esm) = self.esm_by_class.get(&cid) else {
                continue;
            };
            let mut star_children: Vec<ClassId> = Vec::new();
            for exp in &esm.exports {
                match exp {
                    ExportDecl::Local { export_name, .. }
                    | ExportDecl::Indirect { export_name, .. } => {
                        let s = sym_str(self.module, *export_name);
                        if !s.is_empty() && (is_root || s != "default") {
                            out.insert(s.to_owned());
                        }
                    }
                    ExportDecl::Star { module_request } => {
                        if let Some(next_cid) = (self.resolve_spec)(cid, *module_request) {
                            star_children.push(next_cid);
                        }
                    }
                }
            }
            for next_cid in star_children.into_iter().rev() {
                stack.push((next_cid, false));
            }
        }
    }
}

fn sym_str(module: &Module, sym: Sym) -> &str {
    module.sym.resolve(sym).unwrap_or("")
}

fn strip_descriptor(desc: &str) -> &str {
    desc.strip_prefix('L')
        .and_then(|s| s.strip_suffix(';'))
        .unwrap_or(desc)
}

fn is_sdk_specifier(s: &str) -> bool {
    s.starts_with("@ohos.")
        || s.starts_with("@ohos:")
        || s.starts_with("@kit.")
        || s.starts_with("@system.")
        || s.starts_with("@system:")
        || s.starts_with("@arkts.")
        || s.starts_with("@native:")
        || s.starts_with("@hms.")
        || s.starts_with("@hms:")
        || s.starts_with("@normalized:Y&")
}

/// Parse `@normalized:<rest>` or bare `&<rest>` OHMUrl forms into
/// `(mod_name, bundle_name, import_path)`.
fn parse_normalized_ohmurl(raw: &str) -> Option<(&str, &str, &str)> {
    let parsed = if let Some(rest) = raw.strip_prefix("@normalized:") {
        let parts: Vec<&str> = rest.split('&').collect();
        match parts.as_slice() {
            [_is_native, mod_name, bundle_name, import_path, _ver, ..] => {
                Some((*mod_name, *bundle_name, *import_path))
            }
            [_is_native, mod_name, p2, p3] => {
                if p3.contains('/') || (!p3.is_empty() && p2.is_empty()) {
                    Some((*mod_name, "", *p3))
                } else {
                    Some((*mod_name, "", *p2))
                }
            }
            [_is_native, mod_name, import_path] => Some((*mod_name, "", *import_path)),
            _ => None,
        }
    } else if let Some(rest) = raw.strip_prefix('&') {
        let parts: Vec<&str> = rest.split('&').collect();
        match parts.as_slice() {
            [mod_name, bundle_name, import_path, _ver, ..] => {
                Some((*mod_name, *bundle_name, *import_path))
            }
            [p0, p1, _ver] => {
                if p1.contains('/') {
                    Some((*p0, "", *p1))
                } else {
                    Some(("", "", *p0))
                }
            }
            [p0, ..] => Some(("", "", *p0)),
            [] => None,
        }
    } else {
        None
    };
    parsed.filter(|(_, _, imp)| !imp.is_empty())
}

fn peel_ohmurl(raw: &str) -> &str {
    if let Some(rest) = raw.strip_prefix("@bundle:") {
        return rest;
    }
    if let Some(rest) = raw.strip_prefix("@package:") {
        return rest;
    }
    if let Some((_, _, import_path)) = parse_normalized_ohmurl(raw) {
        return import_path;
    }
    if let Some(rest) = raw.strip_prefix("@normalized:") {
        return rest;
    }
    raw
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

fn is_standalone_single_module(module: &Module) -> bool {
    let mut non_synth = 0usize;
    let mut has_global = false;
    for cls in &module.classes {
        let desc = sym_str(module, cls.descriptor);
        if SYNTHETIC_DESCRIPTORS.contains(&desc) {
            continue;
        }
        if cls.methods.is_empty() && cls.es_module.is_none() && json_const_of(module, cls).is_none()
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

// ── Multi-`.abc` IR combiner (`merge_ir_modules`) ──────────────────────────

/// Combine multiple lifted [`Module`]s (for example, `entry.hap` + shared
/// `.hsp` libraries from an `.app` container) into one unified [`Module`] so
/// cross-container `@bundle:` / ES module imports resolve in a single whole-app
/// call-graph, PTA, and IFDS pass.
///
/// Each input pair `(module_name, module)` has standalone `L_GLOBAL;` records
/// renamed to `L<module_name>;` with top-level `imports`/`exports`/`module_requests`
/// promoted onto that class's [`ClassData::es_module`].
pub fn merge_ir_modules(inputs: &[(&str, &Module)]) -> Module {
    if inputs.len() == 1 && inputs[0].1.classes.iter().any(|c| c.es_module.is_some()) {
        return inputs[0].1.clone();
    }
    let mut out = Module::new();
    for &(mod_name, src) in inputs {
        append_module(&mut out, mod_name, src);
    }
    out
}

fn append_module(dst: &mut Module, mod_name: &str, src: &Module) {
    let class_base = dst.classes.len() as u32;
    let func_base = dst.functions.len() as u32;
    let block_base = dst.blocks.len() as u32;
    let inst_base = dst.insts.len() as u32;
    let val_base = dst.values.len() as u32;

    let map_cid = |c: ClassId| ClassId::new(class_base + c.index() as u32);
    let map_fid = |f: FuncId| FuncId::new(func_base + f.index() as u32);
    let map_bid = |b: BlockId| BlockId::new(block_base + b.index() as u32);
    let map_iid = |i: InstId| InstId::new(inst_base + i.index() as u32);
    let map_vid = |v: ValueId| ValueId::new(val_base + v.index() as u32);

    // Map constants into `dst.consts` iteratively with cycle guards.
    let const_map = remap_consts_into(src, dst, &map_fid);
    let map_const = |c: ConstId| const_map.get(c.index()).copied().unwrap_or(c);

    let map_ann = |dst: &mut Module, a: &Annotation| -> Annotation {
        Annotation {
            class: map_cid(a.class),
            elements: a
                .elements
                .iter()
                .map(|(k, v)| {
                    let nk = map_sym_from(src, dst, *k);
                    let nv = remap_ann_val(v, src, dst, &map_const, &map_cid);
                    (nk, nv)
                })
                .collect(),
        }
    };

    let standalone = is_standalone_single_module(src);

    // Classes
    for cls in &src.classes {
        let raw_desc = sym_str(src, cls.descriptor);
        let (new_desc, new_name) = if standalone && raw_desc == "L_GLOBAL;" && !mod_name.is_empty()
        {
            let d = dst.sym.intern(&format!("L{mod_name};"));
            let n = dst.sym.intern(mod_name);
            (d, n)
        } else {
            (
                map_sym_from(src, dst, cls.descriptor),
                map_sym_from(src, dst, cls.name),
            )
        };
        let es_module = if let Some(esm) = &cls.es_module {
            Some(remap_esm(esm, src, dst))
        } else if standalone
            && raw_desc == "L_GLOBAL;"
            && (!src.imports.is_empty()
                || !src.exports.is_empty()
                || !src.module_requests.is_empty())
        {
            Some(remap_esm(
                &EsModule {
                    imports: src.imports.clone(),
                    exports: src.exports.clone(),
                    module_requests: src.module_requests.clone(),
                },
                src,
                dst,
            ))
        } else {
            None
        };

        let fields: Vec<FieldData> = cls
            .fields
            .iter()
            .map(|f| {
                let fname = map_sym_from(src, dst, f.name);
                let fanns = f.annotations.iter().map(|a| map_ann(dst, a)).collect();
                FieldData {
                    name: fname,
                    ty: remap_ty(&f.ty, &map_cid),
                    modifiers: f.modifiers,
                    initial_value: f.initial_value.map(map_const),
                    annotations: fanns,
                }
            })
            .collect();
        let cls_anns: Vec<Annotation> = cls.annotations.iter().map(|a| map_ann(dst, a)).collect();
        let source_file = cls.source_file.map(|s| map_sym_from(src, dst, s));

        dst.classes.push(ClassData {
            descriptor: new_desc,
            name: new_name,
            modifiers: cls.modifiers,
            source_lang: cls.source_lang,
            super_class: cls.super_class.map(map_cid),
            interfaces: cls.interfaces.iter().copied().map(map_cid).collect(),
            fields,
            methods: cls.methods.iter().copied().map(map_fid).collect(),
            annotations: cls_anns,
            source_file,
            es_module,
            scope_names: cls.scope_names.map(map_const),
        });
    }

    // Functions
    for f in &src.functions {
        let mut nf = FunctionData::new(map_cid(f.class_id), map_sym_from(src, dst, f.name), f.kind);
        nf.modifiers = f.modifiers;
        nf.is_external = f.is_external;
        nf.sig = f.sig.as_ref().map(|s| Signature {
            return_ty: s.return_ty.as_ref().map(|t| remap_ty(t, &map_cid)),
            param_tys: s.param_tys.iter().map(|t| remap_ty(t, &map_cid)).collect(),
        });
        nf.params = f.params.iter().copied().map(&map_vid).collect();
        nf.frame_init_consts = f.frame_init_consts.iter().copied().map(&map_vid).collect();
        nf.blocks = f.blocks.iter().copied().map(&map_bid).collect();
        nf.try_regions = f
            .try_regions
            .iter()
            .map(|r| TryRegion {
                protected: r.protected.iter().copied().map(&map_bid).collect(),
                catches: r
                    .catches
                    .iter()
                    .map(|c| Catch {
                        handler: map_bid(c.handler),
                        exception: map_vid(c.exception),
                        type_class: c.type_class.map(map_cid),
                    })
                    .collect(),
            })
            .collect();
        nf.annotations = f.annotations.iter().map(|a| map_ann(dst, a)).collect();
        nf.debug = f.debug.as_ref().map(|d| DebugData {
            source_file: d.source_file.map(|s| map_sym_from(src, dst, s)),
            source_code: d.source_code.clone(),
            line_table: d
                .line_table
                .iter()
                .map(|le| LineEntry {
                    inst: map_iid(le.inst),
                    line: le.line,
                })
                .collect(),
            column_table: d
                .column_table
                .iter()
                .map(|ce| ColumnEntry {
                    inst: map_iid(ce.inst),
                    column: ce.column,
                })
                .collect(),
            local_names: d
                .local_names
                .iter()
                .map(|ln| LocalName {
                    name: map_sym_from(src, dst, ln.name),
                    ty: ln.ty.as_ref().map(|t| remap_ty(t, &map_cid)),
                    scope: ln.scope.map(|sc| LocalScope {
                        start: map_iid(sc.start),
                        end: map_iid(sc.end),
                    }),
                })
                .collect(),
            param_names: d
                .param_names
                .iter()
                .map(|&s| map_sym_from(src, dst, s))
                .collect(),
            scope_names: d.scope_names.map(map_const),
        });
        dst.functions.push(nf);
    }

    // Blocks
    for b in &src.blocks {
        dst.blocks.push(Block {
            insts: b.insts.iter().copied().map(map_iid).collect(),
            preds: b
                .preds
                .iter()
                .map(|e| Edge {
                    from: map_bid(e.from),
                    kind: e.kind,
                })
                .collect(),
        });
    }

    // Instructions
    for inst in &src.insts {
        let mut op = remap_op(&inst.op, src, dst, &map_const, &map_fid, &map_bid);
        for v in op.operands_mut() {
            *v = map_vid(*v);
        }
        dst.insts.push(Inst {
            op,
            result: inst.result.map(map_vid),
            block: map_bid(inst.block),
            loc: inst.loc,
        });
    }

    // Values
    for v in &src.values {
        let def = match v.def {
            ValueDef::Param(i) => ValueDef::Param(i),
            ValueDef::Inst(iid) => ValueDef::Inst(map_iid(iid)),
            ValueDef::Const(cid) => ValueDef::Const(map_const(cid)),
            ValueDef::ExceptionParam(bid) => ValueDef::ExceptionParam(map_bid(bid)),
        };
        dst.values.push(Value {
            def,
            ty: remap_ty(&v.ty, &map_cid),
        });
    }
}

fn map_sym_from(src: &Module, dst: &mut Module, s: Sym) -> Sym {
    match src.sym.raw_mutf8(s) {
        Some(raw) => dst.sym.intern_raw_mutf8(raw),
        None => dst.sym.intern(src.sym.resolve(s).unwrap_or("")),
    }
}

fn remap_ty(ty: &Ty, map_cid: &impl Fn(ClassId) -> ClassId) -> Ty {
    match ty {
        Ty::Static(StaticTy::Reference(c)) => return Ty::Static(StaticTy::Reference(map_cid(*c))),
        Ty::Union(_) => {}
        other => return other.clone(),
    }
    enum TyStep<'a> {
        Enter(&'a Ty),
        MakeUnion(usize),
    }
    let mut stack = vec![TyStep::Enter(ty)];
    let mut results: Vec<Ty> = Vec::new();
    while let Some(step) = stack.pop() {
        match step {
            TyStep::Enter(Ty::Static(StaticTy::Reference(c))) => {
                results.push(Ty::Static(StaticTy::Reference(map_cid(*c))));
            }
            TyStep::Enter(Ty::Union(tys)) => {
                stack.push(TyStep::MakeUnion(tys.len()));
                for t in tys.iter().rev() {
                    stack.push(TyStep::Enter(t));
                }
            }
            TyStep::Enter(other) => results.push(other.clone()),
            TyStep::MakeUnion(n) => {
                let members = results.split_off(results.len() - n);
                results.push(Ty::union(members));
            }
        }
    }
    results.pop().unwrap_or(Ty::Any)
}

fn remap_consts_into(
    src: &Module,
    dst: &mut Module,
    map_fid: &impl Fn(FuncId) -> FuncId,
) -> Vec<ConstId> {
    enum ConstVisit {
        Enter(ConstId),
        FinishArray(ConstId, Vec<ConstId>),
        FinishTypedArray(ConstId, abcd_ir::TypedArrayTag, Vec<ConstId>),
        FinishObject(ConstId, Vec<ConstId>, Vec<ConstId>),
        FinishBufferRef(ConstId, ConstId),
    }

    let len = src.consts.len();
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
                    let leaf = match src.consts.get(cid) {
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
                        Some(Const::EtsImplements(s)) => {
                            Some(Const::EtsImplements(map_sym_from(src, dst, *s)))
                        }
                        Some(Const::LitNull(v)) => Some(Const::LitNull(*v)),
                        Some(Const::String(s)) => Some(Const::String(map_sym_from(src, dst, *s))),
                        Some(Const::BigInt(s)) => Some(Const::BigInt(map_sym_from(src, dst, *s))),
                        Some(Const::MethodRef { func, kind }) => Some(Const::MethodRef {
                            func: map_fid(*func),
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
                        mapped[cid.index()] = Some(dst.consts.push(c));
                    }
                }
                ConstVisit::FinishArray(cid, items) => {
                    in_progress.remove(&cid);
                    let mut out_items = Vec::with_capacity(items.len());
                    for ch in items {
                        let m = match mapped.get(ch.index()).copied().flatten() {
                            Some(id) => id,
                            None => *undef_fallback
                                .get_or_insert_with(|| dst.consts.push(Const::Undefined)),
                        };
                        out_items.push(m);
                    }
                    mapped[cid.index()] = Some(dst.consts.push(Const::ArrayLiteral(out_items)));
                }
                ConstVisit::FinishTypedArray(cid, tag, items) => {
                    in_progress.remove(&cid);
                    let mut out_items = Vec::with_capacity(items.len());
                    for ch in items {
                        let m = match mapped.get(ch.index()).copied().flatten() {
                            Some(id) => id,
                            None => *undef_fallback
                                .get_or_insert_with(|| dst.consts.push(Const::Undefined)),
                        };
                        out_items.push(m);
                    }
                    mapped[cid.index()] = Some(dst.consts.push(Const::TypedArrayLiteral {
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
                                .get_or_insert_with(|| dst.consts.push(Const::Undefined)),
                        };
                        out_keys.push(m);
                    }
                    let mut out_values = Vec::with_capacity(values.len());
                    for ch in values {
                        let m = match mapped.get(ch.index()).copied().flatten() {
                            Some(id) => id,
                            None => *undef_fallback
                                .get_or_insert_with(|| dst.consts.push(Const::Undefined)),
                        };
                        out_values.push(m);
                    }
                    mapped[cid.index()] = Some(dst.consts.push(Const::ObjectLiteral {
                        keys: out_keys,
                        values: out_values,
                    }));
                }
                ConstVisit::FinishBufferRef(cid, inner) => {
                    in_progress.remove(&cid);
                    let m = match mapped.get(inner.index()).copied().flatten() {
                        Some(id) => id,
                        None => {
                            *undef_fallback.get_or_insert_with(|| dst.consts.push(Const::Undefined))
                        }
                    };
                    mapped[cid.index()] = Some(dst.consts.push(Const::LiteralBufferRef(m)));
                }
            }
        }
    }

    mapped
        .into_iter()
        .map(|opt| opt.unwrap_or_else(|| dst.consts.push(Const::Undefined)))
        .collect()
}

fn remap_ann_val(
    v: &AnnValue,
    src: &Module,
    dst: &mut Module,
    map_const: &impl Fn(ConstId) -> ConstId,
    map_cid: &impl Fn(ClassId) -> ClassId,
) -> AnnValue {
    match v {
        AnnValue::Const(c) => AnnValue::Const(map_const(*c)),
        AnnValue::Class(c) => AnnValue::Class(map_cid(*c)),
        AnnValue::Field(c, f) => AnnValue::Field(map_cid(*c), *f),
        AnnValue::Name(s) => AnnValue::Name(map_sym_from(src, dst, *s)),
    }
}

fn remap_esm(esm: &EsModule, src: &Module, dst: &mut Module) -> EsModule {
    EsModule {
        imports: esm
            .imports
            .iter()
            .map(|imp| match imp {
                ImportDecl::Regular {
                    local_name,
                    import_name,
                    module_request,
                } => ImportDecl::Regular {
                    local_name: map_sym_from(src, dst, *local_name),
                    import_name: map_sym_from(src, dst, *import_name),
                    module_request: map_sym_from(src, dst, *module_request),
                },
                ImportDecl::Namespace {
                    local_name,
                    module_request,
                } => ImportDecl::Namespace {
                    local_name: map_sym_from(src, dst, *local_name),
                    module_request: map_sym_from(src, dst, *module_request),
                },
            })
            .collect(),
        exports: esm
            .exports
            .iter()
            .map(|exp| match exp {
                ExportDecl::Local {
                    local_name,
                    export_name,
                } => ExportDecl::Local {
                    local_name: map_sym_from(src, dst, *local_name),
                    export_name: map_sym_from(src, dst, *export_name),
                },
                ExportDecl::Indirect {
                    export_name,
                    import_name,
                    module_request,
                } => ExportDecl::Indirect {
                    export_name: map_sym_from(src, dst, *export_name),
                    import_name: map_sym_from(src, dst, *import_name),
                    module_request: map_sym_from(src, dst, *module_request),
                },
                ExportDecl::Star { module_request } => ExportDecl::Star {
                    module_request: map_sym_from(src, dst, *module_request),
                },
            })
            .collect(),
        module_requests: esm
            .module_requests
            .iter()
            .map(|r| ModuleRequest {
                specifier: map_sym_from(src, dst, r.specifier),
                lazy: r.lazy,
            })
            .collect(),
    }
}

fn remap_op(
    op: &Op,
    src: &Module,
    dst: &mut Module,
    map_const: &impl Fn(ConstId) -> ConstId,
    map_fid: &impl Fn(FuncId) -> FuncId,
    map_bid: &impl Fn(BlockId) -> BlockId,
) -> Op {
    let mut cloned = op.clone();
    match &mut cloned {
        Op::LoadConst(c) => *c = map_const(*c),
        Op::AllocObject { shape } => *shape = map_const(*shape),
        Op::AllocArray { shape } => *shape = shape.map(map_const),
        Op::AllocRegExp { pattern, .. } => *pattern = map_sym_from(src, dst, *pattern),
        Op::LoadProp { name, .. }
        | Op::StoreProp { name, .. }
        | Op::StoreOwnPropName { name, .. }
        | Op::DefineMethod { name, .. }
        | Op::TryGetGlobal { name, .. }
        | Op::StoreGlobal { name, .. }
        | Op::StoreGlobalRecord { name, .. }
        | Op::TryStoreGlobal { name, .. }
        | Op::ThrowUndefinedIfHoleWithName { name, .. } => {
            *name = map_sym_from(src, dst, *name);
        }
        Op::TestProp {
            key: PropKey::Name(name),
            ..
        } => {
            *name = map_sym_from(src, dst, *name);
        }
        Op::LoadSuper {
            key: SuperKey::Name(name),
            ..
        }
        | Op::StoreSuper {
            key: SuperKey::Name(name),
            ..
        } => {
            *name = map_sym_from(src, dst, *name);
        }
        Op::NewLexEnvWithName { scope_names, .. } => *scope_names = map_const(*scope_names),
        Op::DefineFunc { body, captures, .. } => {
            *body = map_fid(*body);
            for (cap_name, _) in captures {
                *cap_name = map_sym_from(src, dst, *cap_name);
            }
        }
        Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
            cls.ctor = map_fid(cls.ctor);
            cls.members = map_const(cls.members);
        }
        Op::CreatePrivateNames { names, .. } => *names = map_const(*names),
        Op::Branch { dest } => *dest = map_bid(*dest),
        Op::CondBranch {
            true_dest,
            false_dest,
            ..
        } => {
            *true_dest = map_bid(*true_dest);
            *false_dest = map_bid(*false_dest);
        }
        Op::Phi { entries } => {
            for (edge, _) in entries {
                edge.from = map_bid(edge.from);
            }
        }
        _ => {}
    }
    cloned
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::callgraph::CallGraph;
    use crate::dataflow::Rung1AliasOracle;
    use crate::dataflow::ifds::CallGraphOracle;
    use crate::dataflow::pta::{PtaConfig, Rung2AliasOracle, analyze};
    use abcd_ir::module::{FunctionKind, Modifiers};
    use abcd_ir::op::{CallKind, ModuleVarKind};
    use abcd_ir::verify::verify_module;

    fn push_fn_with_params(
        m: &mut Module,
        cid: ClassId,
        name: &str,
        kind: FunctionKind,
        total_params: u16,
    ) -> (FuncId, BlockId, Vec<ValueId>) {
        let nsym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(cid, nsym, kind);
        fd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        let bid = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        fd.blocks.push(bid);
        let mut params = Vec::new();
        for i in 0..total_params {
            let vid = ValueId::new(m.values.len() as u32);
            m.values.push(Value {
                def: ValueDef::Param(i),
                ty: Ty::Any,
            });
            fd.params.push(vid);
            params.push(vid);
        }
        m.functions.push(fd);
        m.classes[cid.index()].methods.push(fid);
        (fid, bid, params)
    }

    fn emit_val(m: &mut Module, b: BlockId, op: Op) -> (InstId, ValueId) {
        let iid = InstId::new(m.insts.len() as u32);
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
        m.blocks[b.index()].insts.push(iid);
        (iid, vid)
    }

    fn emit_void(m: &mut Module, b: BlockId, op: Op) -> InstId {
        let iid = InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op,
            result: None,
            block: b,
            loc: None,
        });
        m.blocks[b.index()].insts.push(iid);
        iid
    }

    #[test]
    fn direct_indirect_star_json_and_cycle_guard() {
        let mut m = Module::new();

        // Record 0: leaf (`L@bundle:com.app/entry/ets/leaf;`)
        let d_leaf = m.sym.intern("L@bundle:com.app/entry/ets/leaf;");
        let n_leaf = m.sym.intern("@bundle:com.app/entry/ets/leaf");
        let c_leaf = ClassId::new(0);
        m.classes.push(ClassData::new(d_leaf, n_leaf));

        // Record 1: cycle (`L@bundle:com.app/entry/ets/cycle;`)
        let d_cycle = m.sym.intern("L@bundle:com.app/entry/ets/cycle;");
        let n_cycle = m.sym.intern("@bundle:com.app/entry/ets/cycle");
        let c_cycle = ClassId::new(1);
        m.classes.push(ClassData::new(d_cycle, n_cycle));

        // Record 2: barrel (`L@bundle:com.app/entry/ets/barrel;`)
        let d_barrel = m.sym.intern("L@bundle:com.app/entry/ets/barrel;");
        let n_barrel = m.sym.intern("@bundle:com.app/entry/ets/barrel");
        let c_barrel = ClassId::new(2);
        m.classes.push(ClassData::new(d_barrel, n_barrel));

        // Record 3: json (`L@bundle:com.app/entry/ets/assets/cfg;`)
        let d_json = m.sym.intern("L@bundle:com.app/entry/ets/assets/cfg;");
        let n_json = m.sym.intern("@bundle:com.app/entry/ets/assets/cfg");
        let mut json_cls = ClassData::new(d_json, n_json);
        let jpayload_sym = m.sym.intern(r#"{"api":"https://example.test"}"#);
        let jconst = m.consts.push(Const::String(jpayload_sym));
        let jfield_name = m.sym.intern("jsonFileContent");
        json_cls.fields.push(FieldData {
            name: jfield_name,
            ty: Ty::Any,
            modifiers: Modifiers::PUBLIC.union(Modifiers::STATIC),
            initial_value: Some(jconst),
            annotations: Vec::new(),
        });
        m.classes.push(json_cls);

        // Record 4: main (`L@bundle:com.app/entry/ets/main;`)
        let d_main = m.sym.intern("L@bundle:com.app/entry/ets/main;");
        let n_main = m.sym.intern("@bundle:com.app/entry/ets/main");
        let c_main = ClassId::new(4);
        m.classes.push(ClassData::new(d_main, n_main));

        // Populate ESM metadata:
        let s_secret = m.sym.intern("secret");
        let s_def_local = m.sym.intern("def_local");
        let s_default = m.sym.intern("default");
        m.classes[c_leaf.index()].es_module = Some(EsModule {
            imports: Vec::new(),
            exports: vec![
                ExportDecl::Local {
                    local_name: s_secret,
                    export_name: s_secret,
                },
                ExportDecl::Local {
                    local_name: s_def_local,
                    export_name: s_default,
                },
            ],
            module_requests: Vec::new(),
        });

        let s_extra = m.sym.intern("extra");
        let s_rel_barrel = m.sym.intern("./barrel");
        m.classes[c_cycle.index()].es_module = Some(EsModule {
            imports: Vec::new(),
            exports: vec![
                ExportDecl::Local {
                    local_name: s_extra,
                    export_name: s_extra,
                },
                ExportDecl::Star {
                    module_request: s_rel_barrel,
                },
            ],
            module_requests: vec![ModuleRequest {
                specifier: s_rel_barrel,
                lazy: false,
            }],
        });

        let s_renamed = m.sym.intern("renamed");
        let s_rel_leaf = m.sym.intern("./leaf");
        let s_rel_cycle = m.sym.intern("./cycle");
        m.classes[c_barrel.index()].es_module = Some(EsModule {
            imports: Vec::new(),
            exports: vec![
                ExportDecl::Indirect {
                    export_name: s_renamed,
                    import_name: s_secret,
                    module_request: s_rel_leaf,
                },
                ExportDecl::Star {
                    module_request: s_rel_leaf,
                },
                ExportDecl::Star {
                    module_request: s_rel_cycle,
                },
            ],
            module_requests: vec![
                ModuleRequest {
                    specifier: s_rel_leaf,
                    lazy: false,
                },
                ModuleRequest {
                    specifier: s_rel_cycle,
                    lazy: false,
                },
            ],
        });

        let s_ohm_barrel = m.sym.intern("@bundle:com.app/entry/ets/barrel");
        let s_rel_json = m.sym.intern("./assets/cfg.json");
        let s_ohos_http = m.sym.intern("@ohos.net.http");
        let s_create_http = m.sym.intern("createHttp");
        let s_ns = m.sym.intern("ns");
        m.classes[c_main.index()].es_module = Some(EsModule {
            imports: vec![
                ImportDecl::Regular {
                    local_name: s_renamed,
                    import_name: s_renamed,
                    module_request: s_ohm_barrel,
                },
                ImportDecl::Regular {
                    local_name: s_extra,
                    import_name: s_extra,
                    module_request: s_rel_barrel,
                },
                ImportDecl::Regular {
                    local_name: s_default,
                    import_name: s_default,
                    module_request: s_rel_barrel,
                },
                ImportDecl::Regular {
                    local_name: s_default,
                    import_name: s_default,
                    module_request: s_rel_json,
                },
                ImportDecl::Regular {
                    local_name: s_create_http,
                    import_name: s_create_http,
                    module_request: s_ohos_http,
                },
                ImportDecl::Namespace {
                    local_name: s_ns,
                    module_request: s_ohm_barrel,
                },
            ],
            exports: Vec::new(),
            module_requests: vec![
                ModuleRequest {
                    specifier: s_ohm_barrel,
                    lazy: false,
                },
                ModuleRequest {
                    specifier: s_rel_json,
                    lazy: false,
                },
                ModuleRequest {
                    specifier: s_ohos_http,
                    lazy: false,
                },
            ],
        });

        // Add `func_main_0` to leaf, cycle, barrel, and main.
        let (f_leaf, b_leaf, _) =
            push_fn_with_params(&mut m, c_leaf, "func_main_0", FunctionKind::Function, 3);
        let c42 = m.consts.push(Const::number(42.0));
        let (_, v42) = emit_val(&mut m, b_leaf, Op::LoadConst(c42));
        emit_void(
            &mut m,
            b_leaf,
            Op::StoreModuleVar {
                index: 0,
                value: v42,
            },
        );
        emit_void(&mut m, b_leaf, Op::Return { value: None });

        let (_, b_cycle, _) =
            push_fn_with_params(&mut m, c_cycle, "func_main_0", FunctionKind::Function, 3);
        let (_, b_cycle_val) = emit_val(&mut m, b_cycle, Op::LoadConst(c42));
        emit_void(
            &mut m,
            b_cycle,
            Op::StoreModuleVar {
                index: 0,
                value: b_cycle_val,
            },
        );
        emit_void(&mut m, b_cycle, Op::Return { value: None });

        let (f_barrel, b_barrel, _) =
            push_fn_with_params(&mut m, c_barrel, "func_main_0", FunctionKind::Function, 3);
        emit_void(&mut m, b_barrel, Op::Return { value: None });

        let (f_main, b_main, _) =
            push_fn_with_params(&mut m, c_main, "func_main_0", FunctionKind::Function, 3);
        emit_void(&mut m, b_main, Op::Return { value: None });

        assert!(verify_module(&m).errors.is_empty());

        let links = ModuleLinkTable::build(&m);
        assert!(links.has_multi_record_esm());

        // Slot 0 (`renamed` -> indirect to leaf's `secret` slot 0).
        let t0 = links.external_load(c_main, 0).expect("slot 0");
        assert!(!t0.unresolved_external);
        assert_eq!(
            t0.slots,
            vec![ModuleSlotRef {
                class_id: c_leaf,
                slot: 0
            }]
        );

        // Slot 1 (`extra` -> star through barrel -> cycle slot 0, cycle-safe).
        let t1 = links.external_load(c_main, 1).expect("slot 1");
        assert!(!t1.unresolved_external);
        assert_eq!(
            t1.slots,
            vec![ModuleSlotRef {
                class_id: c_cycle,
                slot: 0
            }]
        );

        // Slot 2 (`default` from barrel -> ECMA-262 `export *` must NOT forward `default`).
        let t2 = links.external_load(c_main, 2).expect("slot 2");
        assert!(t2.slots.is_empty());
        assert!(t2.unresolved_external);

        // Slot 3 (`default` from `./assets/cfg.json` -> JSON constant).
        let t3 = links.external_load(c_main, 3).expect("slot 3");
        assert!(!t3.unresolved_external);
        assert_eq!(t3.json_consts, vec![jconst]);

        // Slot 4 (`createHttp` from `@ohos.net.http` -> external SDK import).
        let t4 = links.external_load(c_main, 4).expect("slot 4");
        assert!(t4.unresolved_external);
        assert_eq!(t4.external_imports, vec![(s_ohos_http, s_create_http)]);

        // Namespace member resolution (`ns.renamed`, `ns.secret`, `ns.extra`; no `ns.default`).
        assert_eq!(
            links.resolve_namespace_member(c_main, 0, s_renamed),
            Some(
                [ModuleSlotRef {
                    class_id: c_leaf,
                    slot: 0
                }]
                .as_slice()
            )
        );
        assert!(
            links
                .resolve_namespace_member(c_main, 0, s_default)
                .is_none()
        );

        // Topological order: leaf and barrel initialize before main.
        let order = links.init_order();
        let pos_leaf = order.iter().position(|&f| f == f_leaf).expect("leaf");
        let pos_barrel = order.iter().position(|&f| f == f_barrel).expect("barrel");
        let pos_main = order.iter().position(|&f| f == f_main).expect("main");
        assert!(pos_leaf < pos_barrel);
        assert!(pos_barrel < pos_main);
    }

    #[test]
    fn cross_module_callgraph_rung1_and_pta_resolve_closures_and_classes() {
        let mut m = Module::new();
        let d_lib = m.sym.intern("L@bundle:com.app/entry/ets/lib;");
        let n_lib = m.sym.intern("@bundle:com.app/entry/ets/lib");
        let c_lib = ClassId::new(0);
        m.classes.push(ClassData::new(d_lib, n_lib));

        let d_app = m.sym.intern("L@bundle:com.app/entry/ets/app;");
        let n_app = m.sym.intern("@bundle:com.app/entry/ets/app");
        let c_app = ClassId::new(1);
        m.classes.push(ClassData::new(d_app, n_app));

        let s_helper = m.sym.intern("helper");
        let s_box = m.sym.intern("ExportedBox");
        let s_shared = m.sym.intern("sharedObj");
        let s_payload = m.sym.intern("payload");
        let s_rel_lib = m.sym.intern("./lib");

        m.classes[c_lib.index()].es_module = Some(EsModule {
            imports: Vec::new(),
            exports: vec![
                ExportDecl::Local {
                    local_name: s_helper,
                    export_name: s_helper,
                },
                ExportDecl::Local {
                    local_name: s_box,
                    export_name: s_box,
                },
                ExportDecl::Local {
                    local_name: s_shared,
                    export_name: s_shared,
                },
            ],
            module_requests: Vec::new(),
        });
        m.classes[c_app.index()].es_module = Some(EsModule {
            imports: vec![
                ImportDecl::Regular {
                    local_name: s_helper,
                    import_name: s_helper,
                    module_request: s_rel_lib,
                },
                ImportDecl::Regular {
                    local_name: s_box,
                    import_name: s_box,
                    module_request: s_rel_lib,
                },
                ImportDecl::Regular {
                    local_name: s_shared,
                    import_name: s_shared,
                    module_request: s_rel_lib,
                },
            ],
            exports: Vec::new(),
            module_requests: vec![ModuleRequest {
                specifier: s_rel_lib,
                lazy: false,
            }],
        });

        // Helper closure body + ExportedBox constructor (`this.payload = arg0`).
        let (f_helper, b_helper, _) =
            push_fn_with_params(&mut m, c_lib, "helper", FunctionKind::Function, 3);
        emit_void(&mut m, b_helper, Op::Return { value: None });

        let (f_ctor, b_ctor, ctor_params) =
            push_fn_with_params(&mut m, c_lib, "ExportedBox", FunctionKind::Constructor, 4);
        emit_void(
            &mut m,
            b_ctor,
            Op::StoreProp {
                object: ctor_params[2], // `this`
                name: s_payload,
                value: ctor_params[3], // formal 0
            },
        );
        emit_void(&mut m, b_ctor, Op::Return { value: None });

        // lib `func_main_0` exports helper (slot 0), ExportedBox (slot 1), sharedObj (slot 2).
        let (_, b_lib, _) =
            push_fn_with_params(&mut m, c_lib, "func_main_0", FunctionKind::Function, 3);
        let empty_shape = m.consts.push(Const::ObjectLiteral {
            keys: Vec::new(),
            values: Vec::new(),
        });
        let empty_members = m.consts.push(Const::ArrayLiteral(Vec::new()));
        let (_, df_val) = emit_val(
            &mut m,
            b_lib,
            Op::DefineFunc {
                body: f_helper,
                captures: Vec::new(),
                length: 0,
            },
        );
        let (_, clos_val) = emit_val(&mut m, b_lib, Op::AllocClosure { func: df_val });
        emit_void(
            &mut m,
            b_lib,
            Op::StoreModuleVar {
                index: 0,
                value: clos_val,
            },
        );

        let (_, cls_val) = emit_val(
            &mut m,
            b_lib,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: f_ctor,
                heritage: None,
                members: empty_members,
                member_attrs: Vec::new(),
                count: 1,
            })),
        );
        emit_void(
            &mut m,
            b_lib,
            Op::StoreModuleVar {
                index: 1,
                value: cls_val,
            },
        );

        let (shared_alloc_iid, shared_val) =
            emit_val(&mut m, b_lib, Op::AllocObject { shape: empty_shape });
        emit_void(
            &mut m,
            b_lib,
            Op::StoreModuleVar {
                index: 2,
                value: shared_val,
            },
        );
        emit_void(&mut m, b_lib, Op::Return { value: None });

        // app `func_main_0`: imports and invokes helper, constructs ExportedBox(innerObj), reads .payload.
        let (_, b_app, _) =
            push_fn_with_params(&mut m, c_app, "func_main_0", FunctionKind::Function, 3);
        let (_, imp_helper) = emit_val(
            &mut m,
            b_app,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let (call_helper_iid, _) = emit_val(
            &mut m,
            b_app,
            Op::Call {
                callee: imp_helper,
                this: None,
                args: Vec::new(),
                kind: CallKind::Dynamic,
            },
        );

        let (_, imp_box) = emit_val(
            &mut m,
            b_app,
            Op::LoadModuleVar {
                index: 1,
                kind: ModuleVarKind::External,
            },
        );
        let (inner_alloc_iid, inner_obj) =
            emit_val(&mut m, b_app, Op::AllocObject { shape: empty_shape });
        let (new_box_iid, box_inst) = emit_val(
            &mut m,
            b_app,
            Op::Call {
                callee: imp_box,
                this: None,
                args: vec![inner_obj],
                kind: CallKind::New,
            },
        );
        let (load_payload_iid, loaded_payload) = emit_val(
            &mut m,
            b_app,
            Op::LoadProp {
                object: box_inst,
                name: s_payload,
            },
        );
        let (load_shared_iid, imp_shared) = emit_val(
            &mut m,
            b_app,
            Op::LoadModuleVar {
                index: 2,
                kind: ModuleVarKind::External,
            },
        );
        emit_void(&mut m, b_app, Op::Return { value: None });

        assert!(verify_module(&m).errors.is_empty());

        // Rung 0 CallGraph resolves both cross-module helper call and `new ExportedBox`.
        let cg = CallGraph::build(&m);
        assert_eq!(cg.callees_of_call_at(call_helper_iid), &[f_helper]);
        assert_eq!(cg.callees_of_call_at(new_box_iid), &[f_ctor]);

        // Rung 1 alias oracle resolves cross-module `sharedObj` allocation site.
        let r1 = Rung1AliasOracle::new(&m, &cg);
        let shared_ans = r1.query(imp_shared, load_shared_iid);
        assert!(shared_ans.precise_for_keying());
        assert_eq!(
            shared_ans.sites.iter().collect::<Vec<_>>(),
            vec![shared_alloc_iid]
        );

        // Rung 2 PTA resolves `box_inst.payload` across `new ExportedBox(inner_obj)`.
        let outcome = analyze(&m, &cg, &PtaConfig::default());
        let (_, tables, stats) = outcome.into_parts();
        let r2 = Rung2AliasOracle::new(&m, tables, stats);
        let payload_info = r2.site_info_at(loaded_payload, load_payload_iid);
        assert!(!payload_info.has_unknown);
        assert_eq!(
            payload_info.sites.iter().collect::<Vec<_>>(),
            vec![inner_alloc_iid]
        );
    }

    #[test]
    fn merge_ir_modules_links_standalone_modules_and_verifies() {
        // Standalone module 1 (`lib/util`): exports `val`.
        let mut m1 = Module::new();
        let d_glob1 = m1.sym.intern("L_GLOBAL;");
        let n_glob1 = m1.sym.intern("_GLOBAL");
        m1.classes.push(ClassData::new(d_glob1, n_glob1));
        let s_val1 = m1.sym.intern("val");
        m1.exports.push(ExportDecl::Local {
            local_name: s_val1,
            export_name: s_val1,
        });
        let (_, b1, _) = push_fn_with_params(
            &mut m1,
            ClassId::new(0),
            "func_main_0",
            FunctionKind::Function,
            3,
        );
        let sh1 = m1.consts.push(Const::ObjectLiteral {
            keys: Vec::new(),
            values: Vec::new(),
        });
        let (_, v1) = emit_val(&mut m1, b1, Op::AllocObject { shape: sh1 });
        emit_void(
            &mut m1,
            b1,
            Op::StoreModuleVar {
                index: 0,
                value: v1,
            },
        );
        emit_void(&mut m1, b1, Op::Return { value: None });

        // Standalone module 2 (`entry/index`): imports `val` from `../lib/util`.
        let mut m2 = Module::new();
        let d_glob2 = m2.sym.intern("L_GLOBAL;");
        let n_glob2 = m2.sym.intern("_GLOBAL");
        m2.classes.push(ClassData::new(d_glob2, n_glob2));
        let s_val2 = m2.sym.intern("val");
        let s_req2 = m2.sym.intern("../lib/util");
        m2.imports.push(ImportDecl::Regular {
            local_name: s_val2,
            import_name: s_val2,
            module_request: s_req2,
        });
        m2.module_requests.push(ModuleRequest {
            specifier: s_req2,
            lazy: false,
        });
        let (_, b2, _) = push_fn_with_params(
            &mut m2,
            ClassId::new(0),
            "func_main_0",
            FunctionKind::Function,
            3,
        );
        let _ = emit_val(
            &mut m2,
            b2,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        emit_void(&mut m2, b2, Op::Return { value: None });

        let merged = merge_ir_modules(&[("lib/util", &m1), ("entry/index", &m2)]);
        let rep = verify_module(&merged);
        assert!(rep.errors.is_empty(), "verify errors: {:?}", rep.errors);

        let links = ModuleLinkTable::build(&merged);
        let t = links
            .external_load(ClassId::new(1), 0)
            .expect("merged import");
        assert!(!t.unresolved_external);
        assert_eq!(
            t.slots,
            vec![ModuleSlotRef {
                class_id: ClassId::new(0),
                slot: 0
            }]
        );
    }

    #[test]
    fn deep_reexport_init_and_nested_remap_run_on_small_stack() {
        const DEPTH: usize = 300;
        let handle = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut m1 = Module::new();
                let s_val = m1.sym.intern("val");
                for i in 0..DEPTH {
                    let desc = m1.sym.intern(&format!("L@bundle:app/m{i};"));
                    let name = m1.sym.intern(&format!("@bundle:app/m{i}"));
                    let cid = ClassId::new(i as u32);
                    m1.classes.push(ClassData::new(desc, name));
                    let mut exports = Vec::new();
                    let mut requests = Vec::new();
                    let mut imports = Vec::new();
                    if i == 0 {
                        exports.push(ExportDecl::Local {
                            local_name: s_val,
                            export_name: s_val,
                        });
                    } else {
                        let prev = m1.sym.intern(&format!("@bundle:app/m{}", i - 1));
                        exports.push(ExportDecl::Star {
                            module_request: prev,
                        });
                        requests.push(ModuleRequest {
                            specifier: prev,
                            lazy: false,
                        });
                        if i + 1 == DEPTH {
                            imports.push(ImportDecl::Regular {
                                local_name: s_val,
                                import_name: s_val,
                                module_request: prev,
                            });
                        }
                    }
                    m1.classes[cid.index()].es_module = Some(EsModule {
                        imports,
                        exports,
                        module_requests: requests,
                    });
                    let (_, b, _) =
                        push_fn_with_params(&mut m1, cid, "func_main_0", FunctionKind::Function, 3);
                    if i == 0 {
                        let c1 = m1.consts.push(Const::number(1.0));
                        let (_, v) = emit_val(&mut m1, b, Op::LoadConst(c1));
                        emit_void(&mut m1, b, Op::StoreModuleVar { index: 0, value: v });
                    }
                    emit_void(&mut m1, b, Op::Return { value: None });
                }

                // Deeply nested `Ty::Union` and `Const::ArrayLiteral` / `Const::ObjectLiteral`
                // plus `Int64` / `UInt64`, Round 3 literal tags, `TypedArrayLiteral`,
                // `LiteralBufferRef`, `Catch::type_class`, and a cyclic `ConstPool` entry.
                let mut deep_ty = Ty::Static(StaticTy::Reference(ClassId::new(0)));
                let c_key = m1.consts.intern(Const::String(s_val));
                let _ = m1.consts.push(Const::Int8(7));
                let c_i32 = m1.consts.push(Const::Int32(42));
                let _ = m1.consts.push(Const::float32(1.5));
                let _ = m1.consts.push(Const::Int64(-99));
                let _ = m1.consts.push(Const::UInt64(99));
                let _ = m1.consts.push(Const::Accessor(0));
                let _ = m1.consts.push(Const::MethodAffiliate(2));
                let _ = m1.consts.push(Const::BuiltinTypeIndex(3));
                let _ = m1.consts.push(Const::EtsImplements(s_val));
                let _ = m1.consts.push(Const::LitNull(0));
                let _ = m1.consts.push(Const::method_ref_with_kind(
                    FuncId::new(0),
                    abcd_ir::LitMethodKind::Getter,
                ));
                let tarr = m1.consts.push(Const::TypedArrayLiteral {
                    tag: abcd_ir::TypedArrayTag::I32,
                    items: vec![c_i32],
                });
                let _ = m1.consts.push(Const::LiteralBufferRef(tarr));
                let mut deep_cid = c_key;
                for _ in 0..DEPTH {
                    deep_ty = Ty::union(vec![deep_ty]);
                    let arr_cid = m1.consts.push_array(vec![deep_cid]);
                    deep_cid = m1.consts.push_object(vec![c_key], vec![arr_cid]);
                }
                // Malformed self-referential `ArrayLiteral` cycle (`cyc_cid -> cyc_cid`).
                let cyc_cid = ConstId::new(m1.consts.len() as u32);
                let _ = m1.consts.push_array(vec![cyc_cid, deep_cid]);
                m1.values[0].ty = deep_ty;
                let h_bid = m1.functions[0].blocks[0];
                let exc_vid = ValueId::new(m1.values.len() as u32);
                m1.values.push(Value {
                    def: ValueDef::ExceptionParam(h_bid),
                    ty: Ty::Any,
                });
                m1.functions[0].try_regions.push(TryRegion {
                    protected: vec![h_bid],
                    catches: vec![Catch {
                        handler: h_bid,
                        exception: exc_vid,
                        type_class: Some(ClassId::new(1)),
                    }],
                });

                let mut m2 = Module::new();
                let dg = m2.sym.intern("L_GLOBAL;");
                let ng = m2.sym.intern("_GLOBAL");
                m2.classes.push(ClassData::new(dg, ng));

                let merged = merge_ir_modules(&[("bundle", &m1), ("extra", &m2)]);
                let links = ModuleLinkTable::build(&merged);
                assert_eq!(links.init_order().len(), DEPTH);
                let resolved = links
                    .external_load(ClassId::new((DEPTH - 1) as u32), 0)
                    .expect("leaf import");
                assert!(!resolved.unresolved_external);
                assert_eq!(
                    resolved.slots,
                    vec![ModuleSlotRef {
                        class_id: ClassId::new(0),
                        slot: 0
                    }]
                );
            })
            .expect("spawn");
        handle.join().expect("small stack must not overflow");
    }

    fn add_exporting_record(m: &mut Module, raw_record: &str, export_names: &[&str]) -> ClassId {
        let desc = m.sym.intern(&format!("L{raw_record};"));
        let name = m.sym.intern(raw_record);
        let cid = ClassId::new(m.classes.len() as u32);
        m.classes.push(ClassData::new(desc, name));

        let exports: Vec<ExportDecl> = export_names
            .iter()
            .map(|ename| {
                let s = m.sym.intern(ename);
                ExportDecl::Local {
                    local_name: s,
                    export_name: s,
                }
            })
            .collect();
        m.classes[cid.index()].es_module = Some(EsModule {
            imports: Vec::new(),
            exports,
            module_requests: Vec::new(),
        });

        let (_, b, _) = push_fn_with_params(m, cid, "func_main_0", FunctionKind::Function, 3);
        let c1 = m.consts.push(Const::number(1.0));
        for idx in 0..export_names.len() {
            let (_, v) = emit_val(m, b, Op::LoadConst(c1));
            emit_void(
                m,
                b,
                Op::StoreModuleVar {
                    index: idx as u32,
                    value: v,
                },
            );
        }
        emit_void(m, b, Op::Return { value: None });
        cid
    }

    fn add_importing_record(
        m: &mut Module,
        raw_record: &str,
        specs: &[(&str, &str)],
    ) -> (ClassId, Vec<Sym>) {
        let desc = m.sym.intern(&format!("L{raw_record};"));
        let name = m.sym.intern(raw_record);
        let cid = ClassId::new(m.classes.len() as u32);
        m.classes.push(ClassData::new(desc, name));

        let mut imports = Vec::with_capacity(specs.len());
        let mut module_requests = Vec::with_capacity(specs.len());
        let mut req_syms = Vec::with_capacity(specs.len());
        for &(spec, imp_name) in specs {
            let s_req = m.sym.intern(spec);
            let s_imp = m.sym.intern(imp_name);
            imports.push(ImportDecl::Regular {
                local_name: s_imp,
                import_name: s_imp,
                module_request: s_req,
            });
            module_requests.push(ModuleRequest {
                specifier: s_req,
                lazy: false,
            });
            req_syms.push(s_req);
        }
        m.classes[cid.index()].es_module = Some(EsModule {
            imports,
            exports: Vec::new(),
            module_requests,
        });

        let (_, b, _) = push_fn_with_params(m, cid, "func_main_0", FunctionKind::Function, 3);
        emit_void(m, b, Op::Return { value: None });
        (cid, req_syms)
    }

    #[test]
    fn bundle_and_infix_har_resolve_to_dot_encoded_records() {
        let mut m = Module::new();
        let c_main_ability = add_exporting_record(
            &mut m,
            "com.huawei.hmos.photos.phone_photos.ets.MainAbility.MainAbility",
            &["MainAbility"],
        );
        let c_drag_ctrl = add_exporting_record(
            &mut m,
            "com.huawei.hmos.photos.phone_photos@browserCommon.ets.default.controller.DragController",
            &["DragController"],
        );
        let (c_importer, _) = add_importing_record(
            &mut m,
            "com.huawei.hmos.photos.phone_photos.ets.pages.Gallery",
            &[
                (
                    "@bundle:com.huawei.hmos.photos/phone_photos/ets/MainAbility/MainAbility",
                    "MainAbility",
                ),
                (
                    "@bundle:com.huawei.hmos.photos/phone_photos@browserCommon/ets/default/controller/DragController",
                    "DragController",
                ),
            ],
        );

        assert!(verify_module(&m).errors.is_empty());
        let links = ModuleLinkTable::build(&m);

        let t0 = links.external_load(c_importer, 0).expect("slot 0");
        assert!(!t0.unresolved_external);
        assert_eq!(
            t0.slots,
            vec![ModuleSlotRef {
                class_id: c_main_ability,
                slot: 0,
            }]
        );
        assert_eq!(links.namespace_target(c_importer, 0), Some(c_main_ability));

        let t1 = links.external_load(c_importer, 1).expect("slot 1");
        assert!(!t1.unresolved_external);
        assert_eq!(
            t1.slots,
            vec![ModuleSlotRef {
                class_id: c_drag_ctrl,
                slot: 0,
            }]
        );
        assert_eq!(links.namespace_target(c_importer, 1), Some(c_drag_ctrl));
    }

    #[test]
    fn package_ohpm_resolves_to_dot_encoded_records_and_index_fallbacks() {
        let mut m = Module::new();
        let c_clip = add_exporting_record(
            &mut m,
            "pkg_modules..ohpm.@hms-core+media@1.3.1.pkg_modules.@hms-core.media.src.main.ets.Clip",
            &["Clip"],
        );
        let c_media_index = add_exporting_record(
            &mut m,
            "pkg_modules..ohpm.@hms-core+media@1.3.1.pkg_modules.@hms-core.media.index",
            &["MediaHub"],
        );
        let c_slash_index = add_exporting_record(
            &mut m,
            "@package:pkg_modules/.ohpm/@ohos+axios@2.2.0/pkg_modules/@ohos/axios/index",
            &["axios"],
        );
        let c_stem_only = add_exporting_record(
            &mut m,
            "pkg_modules..ohpm.@ohos+crypto@1.0.0.pkg_modules.@ohos.crypto.Crypto",
            &["Crypto"],
        );

        let (c_importer, _) = add_importing_record(
            &mut m,
            "com.demo.entry.ets.pages.Index",
            &[
                (
                    "@package:pkg_modules/.ohpm/@hms-core+media@1.3.1/pkg_modules/@hms-core/media/src/main/ets/Clip",
                    "Clip",
                ),
                (
                    "@package:pkg_modules/.ohpm/@hms-core+media@1.3.1/pkg_modules/@hms-core/media",
                    "MediaHub",
                ),
                (
                    "@package:pkg_modules/.ohpm/@ohos+axios@2.2.0/pkg_modules/@ohos/axios",
                    "axios",
                ),
                (
                    "@package:pkg_modules/.ohpm/@ohos+crypto@1.0.0/pkg_modules/@ohos/crypto/Crypto/index",
                    "Crypto",
                ),
            ],
        );

        assert!(verify_module(&m).errors.is_empty());
        let links = ModuleLinkTable::build(&m);

        for (slot_idx, expected_cid) in [
            (0u32, c_clip),
            (1u32, c_media_index),
            (2u32, c_slash_index),
            (3u32, c_stem_only),
        ] {
            let t = links.external_load(c_importer, slot_idx).expect("slot");
            assert!(!t.unresolved_external, "slot {slot_idx} should resolve");
            assert_eq!(
                t.slots,
                vec![ModuleSlotRef {
                    class_id: expected_cid,
                    slot: 0,
                }]
            );
        }
    }

    #[test]
    fn normalized_ohmurl_bare_ampersand_and_sdk_native_filters() {
        assert_eq!(
            parse_normalized_ohmurl("@normalized:N&entry&com.demo&entry/src/main/ets/Helper&1.0.0"),
            Some(("entry", "com.demo", "entry/src/main/ets/Helper"))
        );
        assert_eq!(
            parse_normalized_ohmurl("@normalized:N&har&com.demo/har/src/main/ets/Api&1.0.0"),
            Some(("har", "", "com.demo/har/src/main/ets/Api"))
        );
        assert_eq!(
            parse_normalized_ohmurl("@normalized:N&entry&&entry/src/main/ets/Helper"),
            Some(("entry", "", "entry/src/main/ets/Helper"))
        );
        assert_eq!(
            parse_normalized_ohmurl("@normalized:N&entry&entry/src/main/ets/Helper"),
            Some(("entry", "", "entry/src/main/ets/Helper"))
        );
        assert_eq!(
            parse_normalized_ohmurl("&entry&com.demo&entry/src/main/ets/Foo&1.0.0"),
            Some(("entry", "com.demo", "entry/src/main/ets/Foo"))
        );
        assert_eq!(
            parse_normalized_ohmurl("&har&com.demo/har/src/main/ets/Api&1.0.0"),
            Some(("har", "", "com.demo/har/src/main/ets/Api"))
        );
        assert_eq!(
            parse_normalized_ohmurl("&com.demo/entry/ets/Foo&1.0.0&"),
            Some(("", "", "com.demo/entry/ets/Foo"))
        );
        assert_eq!(
            parse_normalized_ohmurl("&entry/src/main/ets/Foo&"),
            Some(("", "", "entry/src/main/ets/Foo"))
        );

        let mut m = Module::new();
        // Bare `&` 4-field record matched by 5-field `@normalized:N&...` specifier.
        let c_helper = add_exporting_record(
            &mut m,
            "&entry&com.demo&entry/src/main/ets/Helper&1.0.0",
            &["Helper"],
        );
        // Dot-encoded record matched by 4-field `@normalized:N&har&...` specifier.
        let c_api = add_exporting_record(&mut m, "com.demo.har.src.main.ets.Api", &["callApi"]);
        // 5-field `@normalized:N&...` record matched by bare `&...` specifier.
        let c_model = add_exporting_record(
            &mut m,
            "@normalized:N&entry&com.demo&entry/src/main/ets/Model&1.0.0",
            &["Model"],
        );
        // Internal bundled `@app:` record resolves when present, while absent `@app:` marks external.
        let c_app_internal =
            add_exporting_record(&mut m, "@app:com.demo/entry/BundledLib", &["bundled"]);
        // Bare `&<mod>/<path>&<ver>` HAR record matched by 4-segment `@normalized:N&<mod>&<bundle>/<mod>/<path>&<ver>`.
        let c_shared_har = add_exporting_record(
            &mut m,
            "&shared_har/src/main/ets/DeviceStore&1.0.0",
            &["DeviceStore"],
        );

        let (c_importer, req_syms) = add_importing_record(
            &mut m,
            "&entry&com.demo&entry/src/main/ets/Main&1.0.0",
            &[
                (
                    "@normalized:N&entry&com.demo&entry/src/main/ets/Helper&1.0.0",
                    "Helper",
                ),
                (
                    "@normalized:N&har&com.demo/har/src/main/ets/Api&1.0.0",
                    "callApi",
                ),
                ("&entry&com.demo&entry/src/main/ets/Model&1.0.0", "Model"),
                ("@app:com.demo/entry/BundledLib", "bundled"),
                (
                    "@normalized:N&shared_har&com.demo.app/shared_har/src/main/ets/DeviceStore&1.0.0",
                    "DeviceStore",
                ),
                (
                    "@normalized:Y&entry&com.demo&libentry.so&1.0.0",
                    "nativeCall",
                ),
                ("@hms.core.push.pushService", "pushService"),
                ("@hms:core.account", "account"),
                ("@app:com.demo/entry/MissingNative", "missing"),
            ],
        );

        assert!(verify_module(&m).errors.is_empty());
        let links = ModuleLinkTable::build(&m);

        for (slot_idx, expected_cid) in [
            (0u32, c_helper),
            (1u32, c_api),
            (2u32, c_model),
            (3u32, c_app_internal),
            (4u32, c_shared_har),
        ] {
            let t = links.external_load(c_importer, slot_idx).expect("slot");
            assert!(!t.unresolved_external, "slot {slot_idx} should resolve");
            assert_eq!(
                t.slots,
                vec![ModuleSlotRef {
                    class_id: expected_cid,
                    slot: 0,
                }]
            );
        }

        for slot_idx in 5u32..=8u32 {
            let t = links.external_load(c_importer, slot_idx).expect("ext slot");
            assert!(
                t.unresolved_external,
                "slot {slot_idx} must mark unresolved_external"
            );
            assert!(t.slots.is_empty());
            assert_eq!(t.external_imports.len(), 1);
            assert_eq!(t.external_imports[0].0, req_syms[slot_idx as usize]);
        }
    }

    #[test]
    fn dot_encoded_record_relative_imports() {
        let mut m = Module::new();
        let c_sibling =
            add_exporting_record(&mut m, "com.demo.entry.ets.pages.Sibling", &["Sibling"]);
        let c_util = add_exporting_record(&mut m, "com.demo.entry.ets.common.Util", &["util"]);
        let c_comp_idx =
            add_exporting_record(&mut m, "com.demo.entry.ets.components.index", &["Comp"]);
        let (c_home, _) = add_importing_record(
            &mut m,
            "com.demo.entry.ets.pages.Home",
            &[
                ("./Sibling", "Sibling"),
                ("../common/Util", "util"),
                ("../components", "Comp"),
            ],
        );

        assert!(verify_module(&m).errors.is_empty());
        let links = ModuleLinkTable::build(&m);

        for (slot_idx, expected_cid) in [(0u32, c_sibling), (1u32, c_util), (2u32, c_comp_idx)] {
            let t = links.external_load(c_home, slot_idx).expect("slot");
            assert!(!t.unresolved_external, "slot {slot_idx} should resolve");
            assert_eq!(
                t.slots,
                vec![ModuleSlotRef {
                    class_id: expected_cid,
                    slot: 0,
                }]
            );
        }
    }
}
