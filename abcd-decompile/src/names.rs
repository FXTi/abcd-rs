//! Name resolution for Stage A (design/decompile.md §4.1 "Naming"):
//!
//! 1. [`NameScopes`] — the lexical-environment chain, propagated over the
//!    CFG, resolving `GetLexVar`/`PutLexVar` `{level, slot}` and the
//!    private-name ops to their `NewLexEnvWithName` scope names /
//!    `CreatePrivateNames` registrations. IR gap G1 (registered by
//!    d-P0): unnamed env slots get *cosmetic* synthetic fallbacks
//!    (`v{level}_{slot}`, `ns{index}`) — never fabricated names. Gap G2
//!    (module-local slots) is CLOSED where file evidence exists:
//!    [`module_slot_names`] resolves slot↔name from the TDZ-guard names
//!    and stored definition names; only evidence-free slots keep the
//!    `m{index}` fallback.
//! 2. [`local_name_in`] — `DebugData.local_names` scope extents (mapped
//!    onto lifted instructions by the lift) → temporary names.
//! 3. [`op_name_hint`] — `Sym`s on the defining ops (`LoadProp.name`, …)
//!    as hints.
//!
//! Everything here returns RAW names; legalization/disambiguation is the
//! [`crate::legalize::Legalizer`]'s job at mint time.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use abcd_ir::ValueDef;
use abcd_ir::consts::Const;
use abcd_ir::function::DebugData;
use abcd_ir::id::{BlockId, ClassId, ConstId, FuncId, InstId, ValueId};
use abcd_ir::module::{EsModule, ExportDecl, ImportDecl, Module};
use abcd_ir::op::{ModuleVarKind, Op};

use crate::consts::sym_str;
use crate::legalize::sanitize;

/// Per-record ES module slot bindings for `--split-modules` (#26 Phase 2):
/// separates `External` (`RegularImport`), `Local` (`LocalExport` / `StoreModuleVar`),
/// and `Namespace` (`GetModuleNamespace`) slot indices per owning [`ClassId`].
#[derive(Clone, Debug, Default)]
pub struct RecordModuleEnv {
    /// `ldexternalmodulevar idx` → `idx`-th `ImportDecl::Regular.local_name`.
    pub external_slots: BTreeMap<u32, String>,
    /// `ldlocalmodulevar idx` / `stmodulevar idx` → resolved local binding name.
    pub local_slots: BTreeMap<u32, String>,
    /// `getmodulenamespace idx` → `ImportDecl::Namespace.local_name` matching `module_requests[idx]`.
    pub namespace_slots: BTreeMap<u32, String>,
}

impl RecordModuleEnv {
    /// Resolve an external (imported) module slot index.
    pub fn external_name(&self, idx: u32) -> String {
        self.external_slots
            .get(&idx)
            .cloned()
            .unwrap_or_else(|| format!("ext{idx}"))
    }

    /// Resolve a local (exported/module-scoped) module slot index.
    pub fn local_name(&self, idx: u32) -> String {
        self.local_slots
            .get(&idx)
            .cloned()
            .unwrap_or_else(|| module_slot_fallback(idx))
    }
}

/// Module-wide pre-indexed lookup tables shared across per-function Stage A
/// recovery, `classfold`, and Stage C emission (#29).
///
/// Built once in `O(|Module|)` time (instead of rescanning `module.insts`,
/// `module.blocks`, and `module.functions` per function) and `Sync` for
/// parallel `rayon` recovery.
#[derive(Clone, Debug, Default)]
pub struct DecompileIndex {
    /// `func.index()` → first defining parent function in module order.
    parents: Vec<Option<FuncId>>,
    /// `func.index()` → precomputed inherited lexical-environment chain
    /// captured from `parents[func]` (`None` when empty).
    seed_chains: Vec<Option<Arc<[EnvFrame]>>>,
    /// Resolved G2 module-variable slot names (`module_slot_names(module)`).
    pub slot_names: BTreeMap<u32, String>,
    /// Optional per-class isolated ES module slot tables (`build_split`).
    pub per_class_env: Option<HashMap<ClassId, RecordModuleEnv>>,
    /// Constructors referenced by `DefineClass` / `DefineSendableClass`.
    pub class_ctors: HashSet<FuncId>,
    /// `(level, slot)` → closure bodies stored via `PutLexVar` anywhere in
    /// the module.
    pub lex_closure_stores: HashMap<(u16, u16), BTreeSet<FuncId>>,
}

impl DecompileIndex {
    /// Build all module-wide decompile lookup tables in one linear pass.
    pub fn build(module: &Module) -> Self {
        let mut parents = vec![None; module.functions.len()];
        for (fi, f) in module.functions.iter().enumerate() {
            let p = FuncId::new(fi as u32);
            for &b in &f.blocks {
                let Some(block) = module.block(b) else {
                    continue;
                };
                for &iid in &block.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    for child in defined_children(module, &inst.op) {
                        if child != p
                            && let Some(slot) = parents.get_mut(child.index())
                        {
                            slot.get_or_insert(p);
                        }
                    }
                }
            }
        }

        let seed_chains = precompute_seed_chains(module, &parents);

        let mut class_ctors = HashSet::new();
        for inst in &module.insts {
            if let Op::DefineClass(cls) | Op::DefineSendableClass(cls) = &inst.op {
                class_ctors.insert(cls.ctor);
            }
        }

        let mut lex_closure_stores: HashMap<(u16, u16), BTreeSet<FuncId>> = HashMap::new();
        for block in &module.blocks {
            for &iid in &block.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if let Op::PutLexVar {
                    level,
                    slot,
                    value,
                    kind: abcd_ir::LexEnvKind::Plain | abcd_ir::LexEnvKind::Sendable,
                } = &inst.op
                    && let Some(body) = crate::classfold::peel_closure_body(module, *value)
                {
                    lex_closure_stores
                        .entry((*level, *slot))
                        .or_default()
                        .insert(body);
                }
            }
        }

        Self {
            parents,
            seed_chains,
            slot_names: module_slot_names(module),
            per_class_env: None,
            class_ctors,
            lex_closure_stores,
        }
    }

    /// Build decompile lookup tables with isolated per-record [`RecordModuleEnv`]s
    /// for `--split-modules` (#26 Phase 2).
    pub fn build_split(module: &Module) -> Self {
        let mut base = Self::build(module);
        base.per_class_env = Some(build_per_class_module_envs(module));
        base
    }

    /// Capture parent of `func` (`O(1)` lookup matching `parent_of`).
    #[inline]
    pub fn parent_of(&self, func: FuncId) -> Option<FuncId> {
        self.parents.get(func.index()).copied().flatten()
    }

    /// Precomputed inherited lexical-environment seed chain of `func` (`O(1)`).
    #[inline]
    pub(crate) fn seed_of(&self, func: FuncId) -> &[EnvFrame] {
        self.seed_chains
            .get(func.index())
            .and_then(Option::as_deref)
            .unwrap_or(&[])
    }
}

/// Precompute inherited lexical-environment chains for every child function in
/// `module` in ONE top-down pass over parent functions using an explicit heap
/// workstack and cycle guard (zero call-stack recursion, zero redundant ancestor
/// re-walks).
fn precompute_seed_chains(
    module: &Module,
    parents: &[Option<FuncId>],
) -> Vec<Option<Arc<[EnvFrame]>>> {
    let n = module.functions.len();
    let mut is_parent = vec![false; n];
    for p in parents.iter().flatten() {
        if let Some(flag) = is_parent.get_mut(p.index()) {
            *flag = true;
        }
    }

    // 0 = uncomputed, 1 = on active ancestor stack (cycle guard), 2 = computed.
    let mut state = vec![0u8; n];
    let mut seed_chains: Vec<Option<Arc<[EnvFrame]>>> = vec![None; n];
    let mut work: Vec<FuncId> = Vec::new();

    for start in 0..n {
        if !is_parent[start] || state[start] != 0 {
            continue;
        }
        let mut cur = FuncId::new(start as u32);
        loop {
            let ci = cur.index();
            if ci >= n || state[ci] != 0 {
                break;
            }
            state[ci] = 1;
            work.push(cur);
            match parents[ci] {
                Some(p) => cur = p,
                None => break,
            }
        }

        while let Some(p) = work.pop() {
            let pi = p.index();
            let seed = seed_chains
                .get(pi)
                .and_then(Option::as_deref)
                .unwrap_or(&[]);
            let scopes = NameScopes::build_seeded(module, p, seed, true);
            for (child, chain) in scopes.defines {
                let ci = child.index();
                if ci < n && parents[ci] == Some(p) && state[ci] != 2 && !chain.is_empty() {
                    seed_chains[ci] = Some(chain);
                }
            }
            state[pi] = 2;
        }
    }

    seed_chains
}

/// One lexical-environment frame (one `NewLexEnv*`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EnvFrame {
    /// Slot names (`None` = unnamed slot — gap G1, cosmetic fallback).
    pub slots: Vec<Option<String>>,
    /// Private names registered in this frame by `CreatePrivateNames`.
    pub priv_names: Vec<Option<String>>,
}

/// The propagated lexical-environment chain of one function.
///
/// Construction: forward walk in augmented-RPO (exceptional edges are
/// value-flow edges too); a block's entry chain is the longest common
/// prefix of its already-processed predecessors' exit chains (a
/// conservative meet — chains that disagree are truncated, producing
/// fallbacks, never wrong names). Loops resolve because the back edge's
/// exit chain is simply not a meet input on the first pass; a single
/// pass suffices since NewLexEnv/PopLexEnv discipline is lexical, not
/// loop-carried, in es2abc output — any residual disagreement degrades
/// to the cosmetic fallback.
///
/// The chain is SEEDED with the function's inherited environment: the
/// env stack of the parent function at the site that defines this one
/// (`DefineFunc`/`DefineClass`/`AllocObject` method refs), computed
/// transitively (`inherited_chain`). This makes cross-function captures
/// resolve to the SAME name the owning function stores under (dream
/// gate: for-update-continue-1 — `ldlexvar 2,1` in a nested closure
/// must name the binding the ancestor wrote, not an orphan).
#[derive(Debug)]
pub struct NameScopes {
    /// `(inst, resolved raw name)` for every lexvar/private-name op.
    resolved: BTreeMap<InstId, String>,
    /// Child function → the env chain captured at its definition site
    /// (first site in augmented-RPO wins — deterministic). Populated only
    /// when `record_defines` is enabled, sharing a single [`Arc`] across
    /// sibling functions defined at the same lexical stack state.
    defines: BTreeMap<FuncId, Arc<[EnvFrame]>>,
}

impl NameScopes {
    /// The resolved raw name of a lexvar/private-name instruction.
    pub fn name_of(&self, inst: InstId) -> Option<&str> {
        self.resolved.get(&inst).map(String::as_str)
    }

    /// Whether any resolved raw name in this scope table sanitizes to the
    /// synthetic unnamed-lexenv fallback shape (`v<digits>_<digits>`).
    pub(crate) fn has_fallback_lexenv_name(&self) -> bool {
        self.resolved
            .values()
            .any(|raw| crate::emit::is_fallback_lexenv_name(&sanitize(raw)))
    }

    /// Build the chain of `func` in `module`, seeded with the
    /// function's inherited (captured) environment.
    pub fn build(module: &Module, func_id: FuncId) -> Self {
        Self::build_with_index(module, func_id, None)
    }

    /// [`NameScopes::build`] using a pre-built [`DecompileIndex`] when
    /// available (`O(1)` precomputed seed lookup instead of rescanning and
    /// re-running `build_seeded` on ancestor functions).
    pub fn build_with_index(
        module: &Module,
        func_id: FuncId,
        index: Option<&DecompileIndex>,
    ) -> Self {
        match index {
            Some(idx) => Self::build_seeded(module, func_id, idx.seed_of(func_id), false),
            None => {
                let seed = Self::inherited_chain(module, func_id);
                Self::build_seeded(module, func_id, &seed, false)
            }
        }
    }

    /// The env chain a function INHERITS when no [`DecompileIndex`] is
    /// available: iterative ancestor collection with a cycle guard (malformed
    /// mutually nested functions degrade to no seed), walked top-down with zero
    /// call-stack recursion.
    fn inherited_chain(module: &Module, func: FuncId) -> Arc<[EnvFrame]> {
        let mut chain: Vec<(FuncId, FuncId)> = Vec::new();
        let mut visited: HashSet<FuncId> = HashSet::new();
        visited.insert(func);
        let mut cur = func;
        while let Some(parent) = parent_of(module, cur) {
            if !visited.insert(parent) {
                break;
            }
            chain.push((cur, parent));
            cur = parent;
        }
        let mut seed: Arc<[EnvFrame]> = Arc::from([]);
        for &(child, parent) in chain.iter().rev() {
            let mut scopes = Self::build_seeded(module, parent, &seed, true);
            seed = scopes
                .defines
                .remove(&child)
                .unwrap_or_else(|| Arc::from([]));
        }
        seed
    }

    /// Build with an explicit seed chain (the inherited environment;
    /// empty for functions with no known definition site).
    fn build_seeded(
        module: &Module,
        func_id: FuncId,
        seed: &[EnvFrame],
        record_defines: bool,
    ) -> Self {
        let seed_len = seed.len();
        let mut scopes = NameScopes {
            resolved: BTreeMap::new(),
            defines: BTreeMap::new(),
        };
        let Some(func) = module.func(func_id) else {
            return scopes;
        };
        let order = augmented_rpo(module, func_id);
        let block_set: HashSet<BlockId> = func.blocks.iter().copied().collect();

        // Predecessors (both edge kinds), in-function only.
        let mut preds: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        for &b in &func.blocks {
            if let Some(block) = module.block(b) {
                for e in &block.preds {
                    if block_set.contains(&e.from) {
                        preds.entry(b).or_default().push(e.from);
                    }
                }
            }
        }

        let mut exit_of: BTreeMap<BlockId, Vec<EnvFrame>> = BTreeMap::new();
        for &b in &order {
            // Meet: longest common prefix of the processed preds' exits.
            // Blocks with no processed predecessor (the entry, loop
            // headers on the first pass, unreached blocks) start from
            // the SEED — the inherited chain is every block's floor.
            let mut meet: Option<Vec<EnvFrame>> = None;
            for p in preds.get(&b).into_iter().flatten() {
                if let Some(exit) = exit_of.get(p) {
                    meet = Some(match meet {
                        None => exit.clone(),
                        Some(m) => common_prefix(&m, exit),
                    });
                }
            }
            let mut stack = meet.unwrap_or_else(|| seed.to_vec());
            let mut cached_arc: Option<Arc<[EnvFrame]>> = None;
            if let Some(block) = module.block(b) {
                for &iid in &block.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    step_inst(
                        module,
                        &mut stack,
                        &mut cached_arc,
                        seed_len,
                        record_defines,
                        &inst.op,
                        iid,
                        &mut scopes,
                    );
                }
            }
            exit_of.insert(b, stack);
        }
        scopes
    }
}

/// Longest common prefix of two chains (frame equality).
fn common_prefix(a: &[EnvFrame], b: &[EnvFrame]) -> Vec<EnvFrame> {
    let n = a.iter().zip(b.iter()).take_while(|(x, y)| x == y).count();
    a[..n].to_vec()
}

/// The functions a define op gives a captured environment to:
/// `DefineFunc`'s body, class ctors + member-buffer `MethodRef`s, and
/// object-shape `MethodRef`s (all emitted inline at the site, so their
/// captured chain is the site's env stack).
fn defined_children(module: &Module, op: &Op) -> Vec<FuncId> {
    fn method_refs(module: &Module, root_cid: ConstId, out: &mut Vec<FuncId>) {
        let mut visited: HashSet<ConstId> = HashSet::new();
        if !visited.insert(root_cid) {
            return;
        }
        let mut stack: Vec<ConstId> = vec![root_cid];
        while let Some(cid) = stack.pop() {
            let Some(c) = module.consts.get(cid) else {
                continue;
            };
            match c {
                Const::MethodRef { func, .. } => out.push(*func),
                Const::ArrayLiteral(items) | Const::TypedArrayLiteral { items, .. } => {
                    for &item_cid in items.iter().rev() {
                        if visited.insert(item_cid) {
                            stack.push(item_cid);
                        }
                    }
                }
                Const::ObjectLiteral { keys, values } => {
                    for &child_cid in values.iter().rev().chain(keys.iter().rev()) {
                        if visited.insert(child_cid) {
                            stack.push(child_cid);
                        }
                    }
                }
                Const::LiteralBufferRef(inner) if visited.insert(*inner) => {
                    stack.push(*inner);
                }
                _ => {}
            }
        }
    }
    let mut out = Vec::new();
    match op {
        Op::DefineFunc { body, .. } => out.push(*body),
        Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
            out.push(cls.ctor);
            method_refs(module, cls.members, &mut out);
        }
        Op::AllocObject { shape } => method_refs(module, *shape, &mut out),
        _ => {}
    }
    out
}

/// The first function (in module order) whose body defines `func`
/// (its capture parent). `None` for the entry and for functions whose
/// define site is unreachable/absent — they get no seed.
fn parent_of(module: &Module, func: FuncId) -> Option<FuncId> {
    for i in 0..module.functions.len() {
        let p = FuncId::new(i as u32);
        if p == func {
            continue;
        }
        let Some(f) = module.func(p) else {
            continue;
        };
        for &b in &f.blocks {
            let Some(block) = module.block(b) else {
                continue;
            };
            for &iid in &block.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if defined_children(module, &inst.op).contains(&func) {
                    return Some(p);
                }
            }
        }
    }
    None
}

/// One instruction's effect on the env chain (+ name resolution).
/// `seed_len` marks the inherited prefix: private-name resolution is
/// scoped to the function's OWN frames (the legacy behavior — the
/// private-name printing/class-fold pipeline keys on it), and define
/// ops record the captured chain for their children.
#[allow(clippy::too_many_arguments)]
fn step_inst(
    module: &Module,
    stack: &mut Vec<EnvFrame>,
    cached_arc: &mut Option<Arc<[EnvFrame]>>,
    seed_len: usize,
    record_defines: bool,
    op: &Op,
    iid: InstId,
    scopes: &mut NameScopes,
) {
    // Record the captured chain for defined children BEFORE the op's
    // own effect (define ops do not push/pop the chain).
    if record_defines
        && matches!(
            op,
            Op::DefineFunc { .. }
                | Op::DefineClass(_)
                | Op::DefineSendableClass(_)
                | Op::AllocObject { .. }
        )
    {
        for child in defined_children(module, op) {
            scopes.defines.entry(child).or_insert_with(|| {
                if stack.is_empty() {
                    Arc::from([])
                } else {
                    cached_arc
                        .get_or_insert_with(|| Arc::from(stack.as_slice()))
                        .clone()
                }
            });
        }
    }
    match op {
        Op::NewLexEnv { num_vars, .. } => {
            *cached_arc = None;
            stack.push(EnvFrame {
                slots: vec![None; *num_vars as usize],
                priv_names: Vec::new(),
            });
        }
        Op::NewLexEnvWithName {
            num_vars,
            scope_names,
        } => {
            *cached_arc = None;
            let names = string_array(module, *scope_names).unwrap_or_default();
            let mut slots: Vec<Option<String>> = names.into_iter().map(Some).collect();
            slots.resize(*num_vars as usize, None);
            stack.push(EnvFrame {
                slots,
                priv_names: Vec::new(),
            });
        }
        Op::PopLexEnv => {
            *cached_arc = None;
            stack.pop();
        }
        Op::CreatePrivateNames { names, .. } => {
            if let Some(top) = stack.last_mut() {
                *cached_arc = None;
                for n in string_array(module, *names).unwrap_or_default() {
                    top.priv_names.push(Some(n));
                }
            }
        }
        Op::GetLexVar { level, slot, kind }
        | Op::PutLexVar {
            level, slot, kind, ..
        } => {
            let name = match kind {
                abcd_ir::LexEnvKind::Patch => format!("v999999_{slot}"),
                abcd_ir::LexEnvKind::Plain | abcd_ir::LexEnvKind::Sendable => {
                    resolve_slot(stack, *level, *slot)
                        .unwrap_or_else(|| lex_fallback(stack.len(), *level, *slot))
                }
            };
            scopes.resolved.insert(iid, name);
        }
        Op::LoadPrivate { level, slot, .. }
        | Op::StorePrivate { level, slot, .. }
        | Op::DefinePrivate { level, slot, .. }
        | Op::TestPrivate { level, slot, .. } => {
            // Private names keep the pre-seeding semantics: resolve
            // against the function's OWN frames only.
            let own = &stack[seed_len.min(stack.len())..];
            let name =
                resolve_priv(own, *level, *slot).unwrap_or_else(|| format!("p{}_{}", level, slot));
            scopes.resolved.insert(iid, name);
        }
        _ => {}
    }
}

/// The cosmetic fallback for an UNNAMED slot (gap G1): keyed by the
/// frame's ABSOLUTE index in the seeded chain (`v{abs}_{slot}`) so the
/// owning function and every capturing reader compute the SAME name for
/// the same frame — the relative `v{level}_{slot}` keyed by the access
/// site's depth was only self-consistent when reader and writer happened
/// to sit at the same depth (dream gate: for-update-continue-1,
/// "v2_1 is not defined"/"v2_1$1 is not a function"). When the chain
/// was meet-truncated above the target (frame unknown), the legacy
/// relative form is kept — the module-top orphan predeclarations
/// (`emit::orphan_lexenv_names`) cover those.
fn lex_fallback(stack_len: usize, level: u16, slot: u16) -> String {
    match stack_len.checked_sub(1 + level as usize) {
        Some(abs) => format!("v{abs}_{slot}"),
        None => format!("v{level}_{slot}"),
    }
}

/// Resolve `{level, slot}` against the chain: `level` envs up from the
/// top, `slot` within that frame.
fn resolve_slot(stack: &[EnvFrame], level: u16, slot: u16) -> Option<String> {
    let idx = stack.len().checked_sub(1 + level as usize)?;
    stack.get(idx)?.slots.get(slot as usize)?.clone()
}

/// Resolve a private name `{level, slot}` (slot indexes the frame's
/// private-name table).
fn resolve_priv(stack: &[EnvFrame], level: u16, slot: u16) -> Option<String> {
    let idx = stack.len().checked_sub(1 + level as usize)?;
    stack.get(idx)?.priv_names.get(slot as usize)?.clone()
}

/// Read a `Const::ArrayLiteral` of `Const::String` (scope names / private
/// names); `None` if the const has a different shape.
fn string_array(module: &Module, id: abcd_ir::ConstId) -> Option<Vec<String>> {
    match module.consts.get(id)? {
        Const::ArrayLiteral(items) => items
            .iter()
            .map(|&cid| match module.consts.get(cid)? {
                Const::String(s) => Some(sym_str(module, *s)),
                _ => None,
            })
            .collect(),
        _ => None,
    }
}

/// Augmented (Normal + Exceptional) reverse post-order from the entry;
/// unreached blocks appended in `func.blocks` order (deterministic).
fn augmented_rpo(module: &Module, func_id: FuncId) -> Vec<BlockId> {
    let Some(func) = module.func(func_id) else {
        return Vec::new();
    };
    let block_set: HashSet<BlockId> = func.blocks.iter().copied().collect();
    // Augmented successors: inverse of the stored preds (both kinds).
    let mut succs: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    for &b in &func.blocks {
        if let Some(block) = module.block(b) {
            for e in &block.preds {
                if block_set.contains(&e.from) {
                    succs.entry(e.from).or_default().push(b);
                }
            }
        }
    }
    let mut visited = std::collections::BTreeSet::new();
    let mut post = Vec::new();
    if let Some(entry) = func.entry()
        && visited.insert(entry)
    {
        let mut stack: Vec<(BlockId, usize)> = vec![(entry, 0)];
        while let Some((b, idx)) = stack.last_mut() {
            let cur = *b;
            let next_succ = succs.get(&cur).and_then(|s| s.get(*idx)).copied();
            if let Some(s) = next_succ {
                *idx += 1;
                if visited.insert(s) {
                    stack.push((s, 0));
                }
            } else {
                stack.pop();
                post.push(cur);
            }
        }
    }
    post.reverse();
    for &b in &func.blocks {
        if visited.insert(b) {
            post.push(b);
        }
    }
    post
}

/// The `DebugData.local_names` name whose scope extent contains `inst`
/// (first match in declaration order — deterministic; the extents are
/// the lift's instruction-mapped form of the debug info's start/end).
/// The caller still legalizes and dedups.
pub fn local_name_in(module: &Module, debug: &DebugData, inst: InstId) -> Option<String> {
    for ln in &debug.local_names {
        let Some(scope) = ln.scope else { continue };
        if scope.start <= inst && inst <= scope.end {
            return Some(sym_str(module, ln.name));
        }
    }
    None
}

/// A raw name hint from the defining op's own `Sym` payload (§4.1:
/// "`Sym`s on the defining ops (`LoadProp.name`, etc.) as hints").
pub fn op_name_hint(module: &Module, op: &Op) -> Option<String> {
    match op {
        Op::LoadProp { name, .. }
        | Op::StoreProp { name, .. }
        | Op::StoreOwnPropName { name, .. }
        | Op::TryGetGlobal { name, .. }
        | Op::StoreGlobal { name, .. }
        | Op::StoreGlobalRecord { name, .. }
        | Op::TryStoreGlobal { name, .. } => Some(sym_str(module, *name)),
        Op::DefineFunc { body, .. } => module.func(*body).map(|f| sym_str(module, f.name)),
        Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
            module.func(cls.ctor).map(|f| sym_str(module, f.name))
        }
        _ => None,
    }
}

/// The synthetic fallback for a module-local slot (gap G2 — used only
/// when [`module_slot_names`] finds no consistent file evidence).
pub fn module_slot_fallback(index: u32) -> String {
    format!("m{index}")
}

/// Resolve module-var slot indices to their source-level binding names
/// (gap G2 closure, d-P9). The format carries no slot↔name table (the
/// `_ESSlotNumberAnnotation` records per-function lexenv slot COUNTS —
/// unrelated), but two FILE FACTS pin a slot to its binding name:
///
/// 1. **TDZ guard name** — es2abc emits `throw.undefinedifholewithname
///    "<name>"` on every read of a module-level `let`/`const` binding;
///    a [`Op::ThrowUndefinedIfHoleWithName`] whose checked value is a
///    [`Op::LoadModuleVar`] result names that slot. (The runtime-name
///    form [`Op::ThrowUndefinedIfHole`] resolves likewise when its name
///    operand is a const string.)
/// 2. **Stored named definition** — a top-level `function f`/`class C`
///    compiles to `definefunc`/`defineclass` + `stmodulevar` into the
///    declaration's OWN slot: a [`Op::StoreModuleVar`] whose value
///    traces through `Mov`/`AllocClosure` passthroughs to a
///    `DefineFunc`/`DefineClass`/`DefineSendableClass` binds the slot to
///    that definition's file name.
///
/// Honesty rules (fallback, never fabrication): contradictory names for
/// one slot poison it; one name claimed by two slots poisons BOTH (one
/// binding = one slot); names colliding with an import local or a
/// `StoreGlobal` predeclaration are dropped (the emitted module-scope
/// `let` would be a duplicate declaration).
pub fn module_slot_names(module: &Module) -> BTreeMap<u32, String> {
    // slot → candidate name; `None` = poisoned by contradictory evidence.
    let mut candidates: BTreeMap<u32, Option<String>> = BTreeMap::new();
    for inst in &module.insts {
        match &inst.op {
            Op::ThrowUndefinedIfHoleWithName { name, value } => {
                if let Some(slot) = load_module_slot(module, *value) {
                    consider(&mut candidates, slot, sym_str(module, *name));
                }
            }
            Op::ThrowUndefinedIfHole { name, value } => {
                if let Some(slot) = load_module_slot(module, *value)
                    && let Some(n) = const_string(module, *name)
                {
                    consider(&mut candidates, slot, n);
                }
            }
            Op::StoreModuleVar { index, value } => {
                if let Some(name) = defined_value_name(module, *value) {
                    consider(&mut candidates, *index, name);
                }
            }
            _ => {}
        }
    }

    // Names already bound at module scope by other predeclarations
    // (imports, global-store `var`s): a resolved `let` of the same name
    // would be a duplicate declaration, so the slot keeps its fallback.
    let mut taken: BTreeSet<String> = BTreeSet::new();
    for imp in &module.imports {
        let local = match imp {
            abcd_ir::module::ImportDecl::Regular { local_name, .. }
            | abcd_ir::module::ImportDecl::Namespace { local_name, .. } => *local_name,
        };
        taken.insert(sanitize(&sym_str(module, local)));
    }
    for inst in &module.insts {
        if let Op::StoreGlobal { name, .. }
        | Op::StoreGlobalRecord { name, .. }
        | Op::TryStoreGlobal { name, .. } = &inst.op
        {
            taken.insert(sanitize(&sym_str(module, *name)));
        }
    }

    // One binding = one slot: a name claimed by two distinct slots is
    // contradictory; drop both.
    let mut name_count: BTreeMap<String, usize> = BTreeMap::new();
    for cand in candidates.values().flatten() {
        *name_count.entry(sanitize(cand)).or_insert(0) += 1;
    }

    let mut resolved = BTreeMap::new();
    for (slot, cand) in candidates {
        let Some(name) = cand else { continue };
        let name = sanitize(&name);
        if name_count.get(&name).copied().unwrap_or(0) > 1 || taken.contains(&name) {
            continue;
        }
        resolved.insert(slot, name);
    }
    resolved
}

/// Record a slot↔name candidate; a second DISTINCT name poisons the slot.
fn consider(candidates: &mut BTreeMap<u32, Option<String>>, slot: u32, name: String) {
    match candidates.entry(slot) {
        std::collections::btree_map::Entry::Vacant(v) => {
            v.insert(Some(name));
        }
        std::collections::btree_map::Entry::Occupied(mut o) => {
            if o.get().as_ref() != Some(&name) {
                o.insert(None);
            }
        }
    }
}

/// The defining instruction of an SSA value (params/globals have none).
fn def_inst(module: &Module, v: ValueId) -> Option<&abcd_ir::function::Inst> {
    match module.value(v)?.def {
        ValueDef::Inst(iid) => module.inst(iid),
        _ => None,
    }
}

/// The module slot loaded by the value's defining op, when it is a
/// [`Op::LoadModuleVar`].
fn load_module_slot(module: &Module, v: ValueId) -> Option<u32> {
    match &def_inst(module, v)?.op {
        Op::LoadModuleVar { index, .. } => Some(*index),
        _ => None,
    }
}

/// A const-string value's text (for the runtime-name TDZ form).
fn const_string(module: &Module, v: ValueId) -> Option<String> {
    match &def_inst(module, v)?.op {
        Op::LoadConst(cid) => match module.consts.get(*cid)? {
            Const::String(sym) => Some(sym_str(module, *sym)),
            _ => None,
        },
        _ => None,
    }
}

/// The name of the definition a stored value traces to, following
/// `Mov`/`AllocClosure` passthroughs (bounded, like `closure_of`).
fn defined_value_name(module: &Module, v: ValueId) -> Option<String> {
    let mut cur = v;
    for _ in 0..16 {
        match &def_inst(module, cur)?.op {
            Op::Mov { src } => cur = *src,
            Op::AllocClosure { func } => cur = *func,
            Op::DefineFunc { body, .. } => {
                return module
                    .func(*body)
                    .map(|f| demangle_internal_name(sym_str(module, f.name)));
            }
            Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                return module
                    .func(cls.ctor)
                    .map(|f| demangle_internal_name(sym_str(module, f.name)));
            }
            _ => return None,
        }
    }
    None
}

/// Demangle an es2panda internal function name (12.0.6+/13/24 formats):
/// scope/kind tags are `#`-separated segments (es2panda
/// `util/helpers.h`: `FUNC_NAME_SEPARATOR` `#`, `FUNCTION_TAG` `*`,
/// `CLASS_SCOPE_TAG` `~`, `INDEX_NAME_SPICIFIER` `@`, `CTOR_TAG` `=`),
/// so a module-scope function compiles as `#*#add` and a class ctor as
/// `#~@0=#Box`. The segment after the LAST `#` is the source name (JS
/// identifiers never contain `#`). Unmangled names (≤12.0.2) pass
/// through verbatim. Applied ONLY to the module-slot evidence channel —
/// display names elsewhere keep the file's verbatim bytes.
fn demangle_internal_name(raw: String) -> String {
    match raw.rfind('#') {
        Some(i) if i + 1 < raw.len() => raw[i + 1..].to_string(),
        _ => raw,
    }
}

/// The synthetic fallback for a module namespace slot (gap G2).
pub fn namespace_fallback(index: u32) -> String {
    format!("ns{index}")
}

fn build_per_class_module_envs(module: &Module) -> HashMap<ClassId, RecordModuleEnv> {
    let mut out = HashMap::with_capacity(module.classes.len());
    let standalone_esm = if !module.imports.is_empty()
        || !module.exports.is_empty()
        || !module.module_requests.is_empty()
    {
        Some(EsModule {
            imports: module.imports.clone(),
            exports: module.exports.clone(),
            module_requests: module.module_requests.clone(),
        })
    } else {
        None
    };

    for (ci, cls) in module.classes.iter().enumerate() {
        let cid = ClassId::new(ci as u32);
        let desc = sym_str(module, cls.descriptor);
        let esm = cls.es_module.as_ref().or_else(|| {
            (desc == "L_GLOBAL;")
                .then_some(standalone_esm.as_ref())
                .flatten()
        });

        let mut env = RecordModuleEnv::default();
        let mut taken = BTreeSet::new();

        if let Some(esm) = esm {
            let mut ext_idx = 0u32;
            for imp in &esm.imports {
                match imp {
                    ImportDecl::Regular { local_name, .. } => {
                        let local = sanitize(&sym_str(module, *local_name));
                        taken.insert(local.clone());
                        env.external_slots.insert(ext_idx, local);
                        ext_idx += 1;
                    }
                    ImportDecl::Namespace {
                        local_name,
                        module_request,
                    } => {
                        let local = sanitize(&sym_str(module, *local_name));
                        taken.insert(local.clone());
                        for (ridx, req) in esm.module_requests.iter().enumerate() {
                            if req.specifier == *module_request {
                                env.namespace_slots.insert(ridx as u32, local.clone());
                            }
                        }
                    }
                }
            }
        }

        // Collect local-slot candidates from this class's own functions first.
        let mut candidates: BTreeMap<u32, Option<String>> = BTreeMap::new();
        for &fid in &cls.methods {
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
                        Op::StoreGlobal { name, .. }
                        | Op::StoreGlobalRecord { name, .. }
                        | Op::TryStoreGlobal { name, .. } => {
                            taken.insert(sanitize(&sym_str(module, *name)));
                        }
                        Op::ThrowUndefinedIfHoleWithName { name, value } => {
                            if let Some(slot) = load_local_module_slot(module, *value) {
                                consider(&mut candidates, slot, sym_str(module, *name));
                            }
                        }
                        Op::ThrowUndefinedIfHole { name, value } => {
                            if let Some(slot) = load_local_module_slot(module, *value)
                                && let Some(n) = const_string(module, *name)
                            {
                                consider(&mut candidates, slot, n);
                            }
                        }
                        Op::StoreModuleVar { index, value } => {
                            if let Some(name) = defined_value_name(module, *value) {
                                consider(&mut candidates, *index, name);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        // Supplement unclaimed local slots from `ExportDecl::Local` in unique
        // `local_name` declaration order (upstream `SourceTextModule` local
        // export index assignment).
        if let Some(esm) = esm {
            let mut distinct_locals = Vec::new();
            let mut seen_locals = BTreeSet::new();
            for exp in &esm.exports {
                if let ExportDecl::Local { local_name, .. } = exp {
                    let raw = sym_str(module, *local_name);
                    if seen_locals.insert(raw.clone()) {
                        distinct_locals.push(raw);
                    }
                }
            }
            for (slot_idx, raw_name) in distinct_locals.into_iter().enumerate() {
                candidates.entry(slot_idx as u32).or_insert(Some(raw_name));
            }
        }

        let mut name_count: BTreeMap<String, usize> = BTreeMap::new();
        for cand in candidates.values().flatten() {
            *name_count.entry(sanitize(cand)).or_insert(0) += 1;
        }
        for (slot, cand) in candidates {
            let Some(name) = cand else { continue };
            let name = sanitize(&name);
            if name_count.get(&name).copied().unwrap_or(0) > 1 || taken.contains(&name) {
                continue;
            }
            env.local_slots.insert(slot, name);
        }

        out.insert(cid, env);
    }
    out
}

fn load_local_module_slot(module: &Module, v: ValueId) -> Option<u32> {
    match &def_inst(module, v)?.op {
        Op::LoadModuleVar {
            index,
            kind: ModuleVarKind::Local | ModuleVarKind::SendableLocal | ModuleVarKind::SendableClass,
        } => Some(*index),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use abcd_ir::function::{Block, FunctionData, Inst, Value};
    use abcd_ir::id::ClassId;
    use abcd_ir::module::{ClassData, FunctionKind};
    use abcd_ir::ty::Ty;

    // ── Hand-built module scaffolding (mirrors tests/common) ─────────

    fn mk_module() -> Module {
        let mut m = Module::new();
        let name = m.sym.intern("Ltest;");
        m.classes.push(ClassData::new(name, name));
        m
    }

    /// A fresh function with one empty entry block.
    fn add_fn(m: &mut Module, name: &str) -> FuncId {
        let sym = m.sym.intern(name);
        let id = FuncId::new(m.functions.len() as u32);
        m.functions.push(FunctionData::new(
            ClassId::new(0),
            sym,
            FunctionKind::Function,
        ));
        let b = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(id).unwrap().blocks.push(b);
        id
    }

    fn entry_of(m: &Module, f: FuncId) -> BlockId {
        m.func(f).unwrap().blocks[0]
    }

    fn push_inst(m: &mut Module, b: BlockId, op: Op) -> InstId {
        let id = InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op,
            result: None,
            block: b,
            loc: None,
        });
        m.block_mut(b).unwrap().insts.push(id);
        id
    }

    fn emit_val(m: &mut Module, b: BlockId, op: Op) -> ValueId {
        let inst = push_inst(m, b, op);
        let val = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Inst(inst),
            ty: Ty::Any,
        });
        m.inst_mut(inst).unwrap().result = Some(val);
        val
    }

    fn add_param(m: &mut Module, f: FuncId) -> ValueId {
        let idx = m.func(f).unwrap().params.len() as u16;
        let val = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Param(idx),
            ty: Ty::Any,
        });
        m.func_mut(f).unwrap().params.push(val);
        val
    }

    #[test]
    fn common_prefix_meet() {
        let f = |names: &[&str]| EnvFrame {
            slots: names.iter().map(|s| Some(s.to_string())).collect(),
            priv_names: vec![],
        };
        let a = vec![f(&["x", "y"]), f(&["z"])];
        let b = vec![f(&["x", "y"]), f(&["w"])];
        let m = common_prefix(&a, &b);
        assert_eq!(m, vec![f(&["x", "y"])]);
    }

    // ── CreatePrivateNames with an empty env stack (285) ─────────────

    #[test]
    fn create_private_names_empty_stack() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let nx = m.sym.intern("x");
        let nx_cid = m.consts.intern(Const::String(nx));
        let names = m.consts.push_array(vec![nx_cid]);
        // No NewLexEnv precedes it: there is no frame to register into.
        let iid = push_inst(&mut m, b, Op::CreatePrivateNames { count: 1, names });
        let scopes = NameScopes::build(&m, f);
        // Nothing resolved, no panic.
        assert_eq!(scopes.name_of(iid), None);
    }

    // ── op_name_hint store/global arms (419-423) ─────────────────────

    #[test]
    fn op_name_hint_variants() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let v = add_param(&mut m, f);
        let s = m.sym.intern("hint");
        let cases = [
            Op::LoadProp { object: v, name: s },
            Op::StoreProp {
                object: v,
                name: s,
                value: v,
            },
            Op::StoreOwnPropName {
                object: v,
                name: s,
                value: v,
                kind: abcd_ir::OwnStoreKind::OwnProp,
            },
            Op::TryGetGlobal {
                name: s,
                default: None,
            },
            Op::StoreGlobal { name: s, value: v },
            Op::StoreGlobalRecord {
                name: s,
                value: v,
                is_const: false,
            },
            Op::TryStoreGlobal { name: s, value: v },
        ];
        for op in &cases {
            assert_eq!(op_name_hint(&m, op).as_deref(), Some("hint"), "{op:?}");
        }
        assert_eq!(op_name_hint(&m, &Op::PopLexEnv), None);
        // Define-op hints resolve through the function table.
        let inner = add_fn(&mut m, "inner");
        let define = Op::DefineFunc {
            body: inner,
            captures: Vec::new(),
            length: 0,
        };
        assert_eq!(op_name_hint(&m, &define).as_deref(), Some("inner"));
    }

    // ── Module-slot TDZ evidence (474-476) + const_string (559-567) ──

    #[test]
    fn module_slot_tdz_evidence() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let slot = emit_val(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 7,
                kind: abcd_ir::ModuleVarKind::Local,
            },
        );
        // A runtime-name guard whose name is a const string names slot 7.
        let name = {
            let sym = m.sym.intern("myVar");
            let cid = m.consts.push(Const::String(sym));
            emit_val(&mut m, b, Op::LoadConst(cid))
        };
        push_inst(&mut m, b, Op::ThrowUndefinedIfHole { name, value: slot });
        // A non-string const name: no evidence (const_string 563).
        let num = {
            let cid = m.consts.push(Const::number(1.0));
            emit_val(&mut m, b, Op::LoadConst(cid))
        };
        push_inst(
            &mut m,
            b,
            Op::ThrowUndefinedIfHole {
                name: num,
                value: slot,
            },
        );
        // A name not defined by a LoadConst: no evidence (565).
        let other = emit_val(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 8,
                kind: abcd_ir::ModuleVarKind::Local,
            },
        );
        push_inst(
            &mut m,
            b,
            Op::ThrowUndefinedIfHole {
                name: other,
                value: slot,
            },
        );
        let names = module_slot_names(&m);
        assert_eq!(names, BTreeMap::from([(7u32, "myVar".to_string())]));
    }

    // ── defined_value_name: Mov follow (575) + AllocClosure (576) ────

    #[test]
    fn defined_value_name_passthroughs() {
        let mut m = mk_module();
        let f = add_fn(&mut m, "f");
        let b = entry_of(&m, f);
        let f2 = add_fn(&mut m, "#*#myFunc");
        let f3 = add_fn(&mut m, "other");
        // StoreModuleVar through a Mov of the DefineFunc result.
        let df = emit_val(
            &mut m,
            b,
            Op::DefineFunc {
                body: f2,
                captures: Vec::new(),
                length: 0,
            },
        );
        let mv = emit_val(&mut m, b, Op::Mov { src: df });
        push_inst(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 3,
                value: mv,
            },
        );
        // StoreModuleVar through an AllocClosure passthrough.
        let df3 = emit_val(
            &mut m,
            b,
            Op::DefineFunc {
                body: f3,
                captures: Vec::new(),
                length: 0,
            },
        );
        let clo = emit_val(&mut m, b, Op::AllocClosure { func: df3 });
        push_inst(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 4,
                value: clo,
            },
        );
        let names = module_slot_names(&m);
        // The es2panda-mangled `#*#myFunc` demangles to `myFunc`.
        assert_eq!(
            names,
            BTreeMap::from([(3u32, "myFunc".to_string()), (4u32, "other".to_string())])
        );
    }

    #[test]
    fn name_scopes_cached_index_matches_uncached_and_survives_deep_chain_on_256k_stack() {
        let mut m = mk_module();
        let depth = 3_000usize;
        // Build reverse-numbered functions so parents have HIGHER FuncId than children,
        // exercising out-of-order top-down seed precomputation in `DecompileIndex::build`.
        let fids: Vec<FuncId> = (0..depth)
            .map(|i| add_fn(&mut m, &format!("nest_{i}")))
            .collect();
        let outer_sym = m.sym.intern("capturedOuter");
        let outer_cid = m.consts.intern(Const::String(outer_sym));
        let scope_arr = m.consts.push_array(vec![outer_cid]);

        // Root is `fids[depth - 1]`, defining `fids[depth - 2]` -> ... -> `fids[0]`.
        let root_b = entry_of(&m, fids[depth - 1]);
        let _ = emit_val(
            &mut m,
            root_b,
            Op::NewLexEnvWithName {
                num_vars: 1,
                scope_names: scope_arr,
            },
        );
        for k in (1..depth).rev() {
            let b = entry_of(&m, fids[k]);
            let _ = emit_val(
                &mut m,
                b,
                Op::DefineFunc {
                    body: fids[k - 1],
                    captures: Vec::new(),
                    length: 0,
                },
            );
            push_inst(&mut m, b, Op::Return { value: None });
        }
        let leaf_b = entry_of(&m, fids[0]);
        let leaf_get = push_inst(
            &mut m,
            leaf_b,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        push_inst(&mut m, leaf_b, Op::Return { value: None });

        // Also add a mutual cycle (`cyc_a <-> cyc_b`) to verify cycle safety.
        let cyc_a = add_fn(&mut m, "cyc_a");
        let cyc_b = add_fn(&mut m, "cyc_b");
        for (src, dst) in [(cyc_a, cyc_b), (cyc_b, cyc_a)] {
            let b = entry_of(&m, src);
            let _ = emit_val(
                &mut m,
                b,
                Op::DefineFunc {
                    body: dst,
                    captures: Vec::new(),
                    length: 0,
                },
            );
            push_inst(&mut m, b, Op::Return { value: None });
        }

        std::thread::scope(|s| {
            let handle = std::thread::Builder::new()
                .name("names-256k-stack".to_string())
                .stack_size(256 * 1024)
                .spawn_scoped(s, || {
                    let index = DecompileIndex::build(&m);
                    let cached = NameScopes::build_with_index(&m, fids[0], Some(&index));
                    assert_eq!(cached.name_of(leaf_get), Some("capturedOuter"));
                    assert!(!cached.has_fallback_lexenv_name());

                    let uncached = NameScopes::build(&m, fids[0]);
                    assert_eq!(uncached.name_of(leaf_get), Some("capturedOuter"));

                    let _ = NameScopes::build_with_index(&m, cyc_a, Some(&index));
                    let _ = NameScopes::build(&m, cyc_a);
                })
                .expect("spawn 256k scoped thread");
            handle.join().expect("256k thread must not stack-overflow");
        });
    }

    #[test]
    fn round3_patch_lexenv_and_literal_buffer_ref_children() {
        use abcd_ir::consts::TypedArrayTag;

        let mut m = mk_module();
        let child_a = add_fn(&mut m, "child_a");
        let child_b = add_fn(&mut m, "child_b");
        let parent = add_fn(&mut m, "parent");
        let pb = entry_of(&m, parent);

        // Push `NewLexEnvWithName` before defining children so the children
        // capture `parentNamed` at their definition sites.
        let named_sym = m.sym.intern("parentNamed");
        let named_cid = m.consts.intern(Const::String(named_sym));
        let scope_arr = m.consts.push_array(vec![named_cid]);
        let _ = emit_val(
            &mut m,
            pb,
            Op::NewLexEnvWithName {
                num_vars: 1,
                scope_names: scope_arr,
            },
        );

        // `parent` defines `child_a` through `LiteralBufferRef -> TypedArrayLiteral -> MethodRef`
        // and `child_b` through `DefineClass` members behind `LiteralBufferRef`.
        let ma = m.consts.intern(Const::method_ref(child_a));
        let tarr = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::I32,
            items: vec![ma],
        });
        let bref_a = m.consts.push(Const::LiteralBufferRef(tarr));
        let _ = emit_val(&mut m, pb, Op::AllocObject { shape: bref_a });

        let mb = m.consts.intern(Const::method_ref(child_b));
        let arr_b = m.consts.push_array(vec![mb]);
        let bref_b = m.consts.push(Const::LiteralBufferRef(arr_b));
        let ctor = add_fn(&mut m, "C");
        let _ = emit_val(
            &mut m,
            pb,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor,
                heritage: None,
                members: bref_b,
                member_attrs: vec![],
                count: 0,
            })),
        );
        push_inst(&mut m, pb, Op::Return { value: None });

        for child in [child_a, child_b] {
            let cb = entry_of(&m, child);
            let get_plain = push_inst(
                &mut m,
                cb,
                Op::GetLexVar {
                    level: 0,
                    slot: 0,
                    kind: abcd_ir::LexEnvKind::Plain,
                },
            );
            let get_patch = push_inst(
                &mut m,
                cb,
                Op::GetLexVar {
                    level: 0,
                    slot: 0,
                    kind: abcd_ir::LexEnvKind::Patch,
                },
            );
            push_inst(&mut m, cb, Op::Return { value: None });
            let index = DecompileIndex::build(&m);
            let scopes = NameScopes::build_with_index(&m, child, Some(&index));
            assert_eq!(scopes.name_of(get_plain), Some("parentNamed"));
            assert_eq!(scopes.name_of(get_patch), Some("v999999_0"));
            assert!(scopes.has_fallback_lexenv_name());
        }
    }
}
