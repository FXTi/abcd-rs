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

use std::collections::{BTreeMap, BTreeSet};

use abcd_ir::ValueDef;
use abcd_ir::consts::Const;
use abcd_ir::function::DebugData;
use abcd_ir::id::{BlockId, ConstId, FuncId, InstId, ValueId};
use abcd_ir::module::Module;
use abcd_ir::op::Op;

use crate::consts::sym_str;
use crate::legalize::sanitize;

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
    /// (first site in augmented-RPO wins — deterministic).
    defines: BTreeMap<FuncId, Vec<EnvFrame>>,
}

impl NameScopes {
    /// The resolved raw name of a lexvar/private-name instruction.
    pub fn name_of(&self, inst: InstId) -> Option<&str> {
        self.resolved.get(&inst).map(String::as_str)
    }

    /// Build the chain of `func` in `module`, seeded with the
    /// function's inherited (captured) environment.
    pub fn build(module: &Module, func_id: FuncId) -> Self {
        let mut visiting = Vec::new();
        let seed = Self::inherited_chain(module, func_id, &mut visiting);
        Self::build_seeded(module, func_id, seed)
    }

    /// The env chain a function INHERITS: the parent's env stack at the
    /// definition site. `visiting` guards define-site cycles (a malformed
    /// module could nest functions mutually; degrade to no seed).
    fn inherited_chain(module: &Module, func: FuncId, visiting: &mut Vec<FuncId>) -> Vec<EnvFrame> {
        if visiting.contains(&func) {
            return Vec::new();
        }
        let Some(parent) = parent_of(module, func) else {
            return Vec::new();
        };
        if visiting.contains(&parent) {
            return Vec::new();
        }
        visiting.push(func);
        let seed = Self::inherited_chain(module, parent, visiting);
        visiting.pop();
        let scopes = Self::build_seeded(module, parent, seed);
        scopes.defines.get(&func).cloned().unwrap_or_default()
    }

    /// Build with an explicit seed chain (the inherited environment;
    /// empty for functions with no known definition site).
    fn build_seeded(module: &Module, func_id: FuncId, seed: Vec<EnvFrame>) -> Self {
        let seed_len = seed.len();
        let mut scopes = NameScopes {
            resolved: BTreeMap::new(),
            defines: BTreeMap::new(),
        };
        let Some(func) = module.func(func_id) else {
            return scopes;
        };
        let order = augmented_rpo(module, func_id);

        // Predecessors (both edge kinds), in-function only.
        let mut preds: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        for &b in &func.blocks {
            if let Some(block) = module.block(b) {
                for e in &block.preds {
                    if func.blocks.contains(&e.from) {
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
            let mut stack = meet.unwrap_or_else(|| seed.clone());
            if let Some(block) = module.block(b) {
                for &iid in &block.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    step_inst(
                        module,
                        &mut stack,
                        seed_len,
                        inst.op.clone(),
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
    fn method_refs(module: &Module, cid: ConstId, out: &mut Vec<FuncId>) {
        if let Some(c) = module.consts.get(cid) {
            method_refs_const(module, c, out);
        }
    }
    fn method_refs_const(module: &Module, c: &Const, out: &mut Vec<FuncId>) {
        match c {
            Const::MethodRef(f) => out.push(*f),
            Const::ArrayLiteral(items) => {
                for i in items {
                    method_refs_const(module, i, out);
                }
            }
            Const::ObjectLiteral { keys, values } => {
                for i in keys.iter().chain(values.iter()) {
                    method_refs_const(module, i, out);
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    match op {
        Op::DefineFunc { body, .. } => out.push(*body),
        Op::DefineClass { ctor, members, .. } | Op::DefineSendableClass { ctor, members, .. } => {
            out.push(*ctor);
            method_refs(module, *members, &mut out);
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
fn step_inst(
    module: &Module,
    stack: &mut Vec<EnvFrame>,
    seed_len: usize,
    op: Op,
    iid: InstId,
    scopes: &mut NameScopes,
) {
    // Record the captured chain for defined children BEFORE the op's
    // own effect (define ops do not push/pop the chain).
    for child in defined_children(module, &op) {
        scopes.defines.entry(child).or_insert_with(|| stack.clone());
    }
    match &op {
        Op::NewLexEnv { num_vars } => {
            stack.push(EnvFrame {
                slots: vec![None; *num_vars as usize],
                priv_names: Vec::new(),
            });
        }
        Op::NewLexEnvWithName {
            num_vars,
            scope_names,
        } => {
            let names = string_array(module, *scope_names).unwrap_or_default();
            let mut slots: Vec<Option<String>> = names.into_iter().map(Some).collect();
            slots.resize(*num_vars as usize, None);
            stack.push(EnvFrame {
                slots,
                priv_names: Vec::new(),
            });
        }
        Op::PopLexEnv => {
            stack.pop();
        }
        Op::CreatePrivateNames { names, .. } => {
            if let Some(top) = stack.last_mut() {
                for n in string_array(module, *names).unwrap_or_default() {
                    top.priv_names.push(Some(n));
                }
            }
        }
        Op::GetLexVar { level, slot } | Op::PutLexVar { level, slot, .. } => {
            let name = resolve_slot(stack, *level, *slot)
                .unwrap_or_else(|| lex_fallback(stack.len(), *level, *slot));
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
            .map(|c| match c {
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
    // Augmented successors: inverse of the stored preds (both kinds).
    let mut succs: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    for &b in &func.blocks {
        if let Some(block) = module.block(b) {
            for e in &block.preds {
                if func.blocks.contains(&e.from) {
                    succs.entry(e.from).or_default().push(b);
                }
            }
        }
    }
    let mut visited = std::collections::BTreeSet::new();
    let mut post = Vec::new();
    fn dfs(
        b: BlockId,
        succs: &BTreeMap<BlockId, Vec<BlockId>>,
        visited: &mut std::collections::BTreeSet<BlockId>,
        post: &mut Vec<BlockId>,
    ) {
        if !visited.insert(b) {
            return;
        }
        if let Some(s) = succs.get(&b) {
            for &s in s {
                dfs(s, succs, visited, post);
            }
        }
        post.push(b);
    }
    if let Some(entry) = func.entry() {
        dfs(entry, &succs, &mut visited, &mut post);
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
        | Op::TryStoreGlobal { name, .. } => Some(sym_str(module, *name)),
        Op::DefineFunc { body, .. } => module.func(*body).map(|f| sym_str(module, f.name)),
        Op::DefineClass { ctor, .. } | Op::DefineSendableClass { ctor, .. } => {
            module.func(*ctor).map(|f| sym_str(module, f.name))
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
        if let Op::StoreGlobal { name, .. } | Op::TryStoreGlobal { name, .. } = &inst.op {
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
fn def_inst<'m>(module: &'m Module, v: ValueId) -> Option<&'m abcd_ir::function::Inst> {
    match module.value(v)?.def {
        ValueDef::Inst(iid) => module.inst(iid),
        _ => None,
    }
}

/// The module slot loaded by the value's defining op, when it is a
/// [`Op::LoadModuleVar`].
fn load_module_slot(module: &Module, v: ValueId) -> Option<u32> {
    match &def_inst(module, v)?.op {
        Op::LoadModuleVar { index } => Some(*index),
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
            Op::DefineClass { ctor, .. } | Op::DefineSendableClass { ctor, .. } => {
                return module
                    .func(*ctor)
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

#[cfg(test)]
mod tests {
    use super::*;

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
}
