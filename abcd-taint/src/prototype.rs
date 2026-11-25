//! Receiver-type approximation for prototype-keyed summary lookup
//! (`design/analysis.md` — keying method calls on allocation kind,
//! constant def chains, and constructor/global provenance to prototype
//! families).
//!
//! ## The gap this closes
//!
//! A method call `recv.m(...)` whose callee resolved through a
//! `LoadProp` chain produces only a *user-global-qualified* name
//! candidate (`a.pop`, `s.charCodeAt`) — never the prototype key the
//! builtin is registered under (`Array.prototype.pop`). At rung 0 the
//! receiver type was unknown, so these sites could only fall through
//! the fallback ladder (the probe-suite miss-counter top hits:
//! `s.next` ×54, `s.charCodeAt` ×36, `a.pop` ×18).
//!
//! ## What a receiver type IS at bytecode level
//!
//! There are no static types; the approximation is the receiver
//! value's **provenance**, gathered from four sources:
//!
//! 1. **Allocation-site kinds** — the rung-selected oracle's
//!    `site_info_at(recv, at)` (rung 1: the demand-driven engine's
//!    memoized interprocedural answer; rung 0: the local def chain).
//!    Each site's defining op gives a family: `AllocArray` →
//!    `Array.prototype`, `AllocObject` → `Object.prototype`,
//!    `AllocRegExp` → `RegExp.prototype`, `AllocClosure` →
//!    `Function.prototype`.
//! 2. **Constant def chains** — `LoadConst(String/Number/Bool)` (or a
//!    `ValueDef::Const`) types the primitive wrappers:
//!    `String/Number/Boolean.prototype`. This is what types the
//!    corpus' `let s = "…"; s.charCodeAt(…)` shape once the global
//!    hop below reaches the literal store.
//! 3. **Global-store provenance** — a `TryGetGlobal(name)` receiver is
//!    opaque to points-to (globals are mutable across scripts), but
//!    top-level script code stores locals into global bindings
//!    (`sttoglobalrecord`/`stconsttoglobalrecord` →
//!    `Op::StoreGlobalRecord` — the global LEXICAL record (N72-C4);
//!    `stglobalvar` → `Op::StoreGlobal` — the global OBJECT property)
//!    and reads them back at
//!    every use site. The resolver scans the module's stores of
//!    `name` and unions the stored values' families — the SAME
//!    flow-insensitive discipline the fact model already applies to
//!    `Global` bases (never killed). Answers involving a global hop
//!    are marked imprecise (another script could store anything).
//! 4. **`GetIterator`** — a `getiterator` result (for-of protocol
//!    object) whose iterable's families are all builtin array/string
//!    types is typed `Iterator.prototype`: the protocol object of a
//!    builtin iterable. Any other iterable (user object with a custom
//!    `@@iterator`, unknown source) types NOTHING — the family is
//!    never invented.
//! 5. **Constructor results** — `new <global>(...)` where the
//!    callee's def chain bottoms out at `TryGetGlobal(name)` with
//!    `name` a KNOWN builtin constructor (`Array`/`Object`/`RegExp`/
//!    `String`/`Number`/`Boolean`) types the result with that
//!    constructor's family. This is the arm the corpus' RegExp
//!    literals need: es2abc lowers `/a+/g` to an explicit
//!    `new RegExp("a+", "g")` CALL (all six corpus versions — the
//!    `createregexpwithliteral` → `AllocRegExp` lift never fires on
//!    this corpus), so a literal-regexp receiver (`r.test(...)`,
//!    regexp.js ×18) is a call result the alloc-kind arm cannot see.
//!    The constructor name is a mutable global binding (user code can
//!    shadow `RegExp`), so the answer is marked IMPRECISE — the same
//!    may-direction discipline as global-store provenance (and
//!    prototype-path application is additive-only either way). User
//!    classes and unknown callees contribute NOTHING — the family is
//!    never invented.
//!
//! ## What is honestly NOT recoverable
//!
//! - **Class instances**: `new Foo()` is a call result; the fresh
//!   object is allocated by the VM's construct machinery, not by a
//!   keyed `Alloc*` op, so no alloc site (and no class link) exists
//!   for the engine to find. `AllocObject`'s shape constant carries
//!   literal keys/values, not a class. Class-typed receivers stay
//!   unknown.
//! - **Generators**: `let s = seq()` types `s` through the call
//!   result; generator calls through global loads are unresolved
//!   (and even resolved, the VM — not the body — manufactures the
//!   generator object: `creategeneratorobj` inside the body is not a
//!   keyed alloc). The corpus' `s.next` ×54 stays a named miss.
//! - **Prototype-chain walks**: a receiver typed `Object` does not
//!   mean "walk to `Array.prototype`" — with no hierarchy
//!   information the walk would be invention. Families are exact
//!   kinds, not hierarchy roots.
//! - **Own-property shadows**: at rungs 0/1, `a.pop = function () {…}`
//!   on an array is invisible at the method load (store-to-load of
//!   function values is opaque), so the builtin summary fires anyway;
//!   at rung 2, store-to-load function resolution resolves the user
//!   body, which takes precedence over prototype-path summaries.
//!
//! ## Multi-site answers
//!
//! A phi/merge receiver yields the UNION of its sites' families; every
//! family's prototype key is tried and every hit's flows apply (the
//! summary flows are additive — all prototype-path summaries are
//! registered non-exclusive, so application can only ever ADD flows,
//! never kill: the over-approximation is may-direction only). An
//! empty/unknown answer produces NO lookup — the site falls through
//! to the existing fallback ladder unchanged.

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};

use abcd_analysis::module_link::ModuleLinkTable;
use abcd_ir::{Const, FuncId, InstId, Module, Op, Sym, ValueDef, ValueId};

use crate::names::{ClassPropStores, callee_name_candidates, callee_name_candidates_indexed};
use crate::oracle::Oracle;

/// A prototype family — the receiver-type approximation unit. The
/// registry key is `family.key()` + the method leaf
/// (`Array.prototype.pop`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProtoFamily {
    /// `AllocArray` receivers.
    Array,
    /// `AllocObject` receivers (no class link is recoverable — see
    /// module docs).
    Object,
    /// `AllocRegExp` receivers.
    RegExp,
    /// `AllocClosure` receivers.
    Function,
    /// String constants (and the string wrapper).
    Str,
    /// Number constants (and the number wrapper).
    Num,
    /// Boolean constants (and the boolean wrapper).
    Bool,
    /// `GetIterator` results over builtin array/string iterables.
    Iterator,
    /// `Promise` instances (`new Promise`, `Promise.resolve`, `async` calls, `@ohos.*` async APIs).
    Promise,
}

impl ProtoFamily {
    /// The registry-key prefix (`Array.prototype.pop`'s
    /// `Array.prototype`).
    pub fn key(self) -> &'static str {
        match self {
            ProtoFamily::Array => "Array.prototype",
            ProtoFamily::Object => "Object.prototype",
            ProtoFamily::RegExp => "RegExp.prototype",
            ProtoFamily::Function => "Function.prototype",
            ProtoFamily::Str => "String.prototype",
            ProtoFamily::Num => "Number.prototype",
            ProtoFamily::Bool => "Boolean.prototype",
            ProtoFamily::Iterator => "Iterator.prototype",
            ProtoFamily::Promise => "Promise.prototype",
        }
    }
}

/// The receiver-type answer: the union of prototype families the
/// receiver may be an instance of, plus a precision flag
/// (informational — prototype-path summaries are additive either way;
/// the flag records whether the answer is complete or a
/// global-provenance/engine may-answer, for reports and future rungs).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FamilyAnswer {
    /// The families found (empty = no receiver type recoverable — the
    /// caller must fall through, never invent).
    pub families: BTreeSet<ProtoFamily>,
    /// Whether the answer is complete (no unknowns, no global hop, no
    /// engine fallback). False = may-answer.
    pub precise: bool,
}

/// The family of a keyed alloc op, if it is one.
fn family_of_alloc(op: &Op) -> Option<ProtoFamily> {
    match op {
        Op::AllocObject { .. } => Some(ProtoFamily::Object),
        Op::AllocArray { .. } => Some(ProtoFamily::Array),
        Op::AllocClosure { .. } => Some(ProtoFamily::Function),
        Op::AllocRegExp { .. } => Some(ProtoFamily::RegExp),
        _ => None,
    }
}

/// The family of a constant value (the primitive wrappers).
fn family_of_const(c: &Const) -> Option<ProtoFamily> {
    match c {
        Const::String(_) => Some(ProtoFamily::Str),
        Const::Number(_) | Const::Int64(_) | Const::UInt64(_) => Some(ProtoFamily::Num),
        Const::Bool(_) => Some(ProtoFamily::Bool),
        _ => None,
    }
}

/// The resolver: module + the rung-selected oracle + a memo (owned by
/// the caller so one memo serves a whole analysis run — engine answers
/// are point-independent, so keying by receiver value is sound at
/// rung 1; see `abcd_analysis::dataflow::alias` module docs).
pub struct PrototypeResolver<'o, 'm> {
    module: &'m Module,
    oracle: &'o Oracle<'m>,
    memo: &'o RefCell<HashMap<ValueId, FamilyAnswer>>,
    links: Option<&'o ModuleLinkTable>,
    prop_stores: Option<&'o ClassPropStores>,
    global_stores: Option<&'o HashMap<Sym, Vec<ValueId>>>,
}

enum ProtoStep {
    StartCompute { value: ValueId, at: InstId },
    FinishCompute,
    FinishGetIterator,
    FinishPromiseChain,
    Walk(ValueId),
}

impl<'o, 'm> PrototypeResolver<'o, 'm> {
    /// A resolver over `module` typing receivers through `oracle`,
    /// memoized into `memo`.
    pub fn new(
        module: &'m Module,
        oracle: &'o Oracle<'m>,
        memo: &'o RefCell<HashMap<ValueId, FamilyAnswer>>,
    ) -> Self {
        PrototypeResolver {
            module,
            oracle,
            memo,
            links: None,
            prop_stores: None,
            global_stores: None,
        }
    }

    /// Build a resolver wired with precomputed module linkage and store indexes
    /// so `call_return_family` and `global_store_families` run in `O(1)` per hop.
    pub(crate) fn with_indexes(
        module: &'m Module,
        oracle: &'o Oracle<'m>,
        memo: &'o RefCell<HashMap<ValueId, FamilyAnswer>>,
        links: &'o ModuleLinkTable,
        prop_stores: &'o ClassPropStores,
        global_stores: &'o HashMap<Sym, Vec<ValueId>>,
    ) -> Self {
        PrototypeResolver {
            module,
            oracle,
            memo,
            links: Some(links),
            prop_stores: Some(prop_stores),
            global_stores: Some(global_stores),
        }
    }

    /// The prototype families of a receiver value at a program point.
    pub fn families_of(&self, value: ValueId, at: InstId) -> FamilyAnswer {
        if let Some(a) = self.memo.borrow().get(&value) {
            return a.clone();
        }
        let ans = self.compute_iterative(value, at);
        self.memo.borrow_mut().insert(value, ans.clone());
        ans
    }

    /// Iterative explicit-stack answer computation; `visiting` is shared across
    /// the whole walk so phi back-edge cycles terminate (marked imprecise) with
    /// zero call-stack recursion.
    fn compute_iterative(&self, root_value: ValueId, root_at: InstId) -> FamilyAnswer {
        let mut visiting = HashSet::new();
        let mut ans_stack: Vec<FamilyAnswer> = Vec::new();
        let mut steps: Vec<ProtoStep> = vec![ProtoStep::StartCompute {
            value: root_value,
            at: root_at,
        }];

        while let Some(step) = steps.pop() {
            match step {
                ProtoStep::StartCompute { value, at } => {
                    let mut ans = FamilyAnswer {
                        families: BTreeSet::new(),
                        precise: true,
                    };
                    // 1. Site kinds, rung-aware (the engine's interprocedural
                    //    answer when it is precise, else the local walk).
                    let info = self.oracle.site_info_at(value, at);
                    for site in info.sites.iter() {
                        if let Some(f) = self.module.inst(site).and_then(|i| family_of_alloc(&i.op))
                        {
                            ans.families.insert(f);
                        }
                    }
                    if info.has_unknown {
                        ans.precise = false;
                    }
                    // 1b. The MAY-direction arm: resolution-complete fan-out answers.
                    for site in self.oracle.may_sites_at(value, at).iter() {
                        if info.sites.iter().any(|s| s == site) {
                            continue;
                        }
                        if let Some(f) = self.module.inst(site).and_then(|i| family_of_alloc(&i.op))
                        {
                            ans.families.insert(f);
                            ans.precise = false;
                        }
                    }
                    ans_stack.push(ans);
                    steps.push(ProtoStep::FinishCompute);
                    steps.push(ProtoStep::Walk(value));
                }
                ProtoStep::FinishCompute => {
                    if let Some(top) = ans_stack.last_mut()
                        && top.families.is_empty()
                    {
                        top.precise = false;
                    }
                }
                ProtoStep::FinishGetIterator => {
                    let src = ans_stack.pop().unwrap_or_default();
                    if let Some(parent) = ans_stack.last_mut() {
                        if !src.families.is_empty()
                            && src
                                .families
                                .iter()
                                .all(|f| matches!(f, ProtoFamily::Array | ProtoFamily::Str))
                        {
                            parent.families.insert(ProtoFamily::Iterator);
                        } else {
                            parent.precise = false;
                        }
                    }
                }
                ProtoStep::FinishPromiseChain => {
                    let recv = ans_stack.pop().unwrap_or_default();
                    if let Some(parent) = ans_stack.last_mut()
                        && recv.families.contains(&ProtoFamily::Promise)
                    {
                        parent.families.insert(ProtoFamily::Promise);
                    }
                }
                ProtoStep::Walk(value) => {
                    if !visiting.insert(value) {
                        if let Some(top) = ans_stack.last_mut() {
                            top.precise = false;
                        }
                        continue;
                    }
                    let Some(v) = self.module.value(value) else {
                        if let Some(top) = ans_stack.last_mut() {
                            top.precise = false;
                        }
                        continue;
                    };
                    match v.def {
                        ValueDef::Const(c) => {
                            if let Some(f) = self.module.consts.get(c).and_then(family_of_const)
                                && let Some(top) = ans_stack.last_mut()
                            {
                                top.families.insert(f);
                            }
                        }
                        ValueDef::Param(_) | ValueDef::ExceptionParam(_) => {
                            if let Some(top) = ans_stack.last_mut() {
                                top.precise = false;
                            }
                        }
                        ValueDef::Inst(iid) => match self.module.inst(iid).map(|i| &i.op) {
                            Some(Op::Mov { src }) => steps.push(ProtoStep::Walk(*src)),
                            Some(Op::Phi { entries }) => {
                                for (_, incoming) in entries.iter().rev() {
                                    steps.push(ProtoStep::Walk(*incoming));
                                }
                            }
                            Some(Op::LoadConst(c)) => {
                                if let Some(f) =
                                    self.module.consts.get(*c).and_then(family_of_const)
                                    && let Some(top) = ans_stack.last_mut()
                                {
                                    top.families.insert(f);
                                }
                            }
                            Some(Op::GetIterator { obj }) => {
                                steps.push(ProtoStep::FinishGetIterator);
                                steps.push(ProtoStep::StartCompute {
                                    value: *obj,
                                    at: iid,
                                });
                            }
                            Some(Op::TryGetGlobal { name, .. }) => {
                                if let Some(top) = ans_stack.last_mut() {
                                    top.precise = false;
                                }
                                let stored = self.global_stored_values(*name);
                                for sv in stored.into_iter().rev() {
                                    steps.push(ProtoStep::Walk(sv));
                                }
                            }
                            Some(Op::Call {
                                kind: abcd_ir::CallKind::New,
                                callee,
                                ..
                            }) => {
                                if let Some(top) = ans_stack.last_mut() {
                                    self.constructor_family(*callee, &mut visiting, top);
                                }
                            }
                            Some(Op::Call { callee, args, .. }) => {
                                if let Some(chain_recv) =
                                    self.call_return_family(*callee, args, iid, &mut ans_stack)
                                {
                                    steps.push(ProtoStep::FinishPromiseChain);
                                    steps.push(ProtoStep::StartCompute {
                                        value: chain_recv.0,
                                        at: chain_recv.1,
                                    });
                                }
                            }
                            Some(op) if family_of_alloc(op).is_some() => {
                                if let Some(f) = family_of_alloc(op)
                                    && let Some(top) = ans_stack.last_mut()
                                {
                                    top.families.insert(f);
                                }
                            }
                            Some(_) | None => {
                                if let Some(top) = ans_stack.last_mut() {
                                    top.precise = false;
                                }
                            }
                        },
                    }
                }
            }
        }

        ans_stack.pop().unwrap_or_default()
    }

    /// Constructor-result arm: `callee` of a `kind: New` call
    /// is walked through `Mov`/`Phi` to a `TryGetGlobal(name)` leaf; a
    /// KNOWN builtin constructor name types the constructed value with
    /// the matching family.
    fn constructor_family(
        &self,
        callee: ValueId,
        visiting: &mut HashSet<ValueId>,
        ans: &mut FamilyAnswer,
    ) {
        ans.precise = false;
        let mut stack = vec![callee];
        let mut mov_seen = HashSet::new();
        while let Some(cur) = stack.pop() {
            if !mov_seen.insert(cur) {
                continue;
            }
            let Some(v) = self.module.value(cur) else {
                continue;
            };
            let ValueDef::Inst(iid) = v.def else {
                continue;
            };
            match self.module.inst(iid).map(|i| &i.op) {
                Some(Op::Mov { src }) => stack.push(*src),
                Some(Op::Phi { entries }) => {
                    let mut next = Vec::new();
                    for (_, incoming) in entries {
                        if visiting.insert(*incoming) {
                            next.push(*incoming);
                        }
                    }
                    for inc in next.into_iter().rev() {
                        stack.push(inc);
                    }
                }
                Some(Op::TryGetGlobal { name, .. }) => {
                    let family = match self.module.sym.resolve(*name) {
                        Some("Array") => Some(ProtoFamily::Array),
                        Some("Object") => Some(ProtoFamily::Object),
                        Some("RegExp") => Some(ProtoFamily::RegExp),
                        Some("String") => Some(ProtoFamily::Str),
                        Some("Number") => Some(ProtoFamily::Num),
                        Some("Boolean") => Some(ProtoFamily::Bool),
                        Some("Promise") => Some(ProtoFamily::Promise),
                        _ => None,
                    };
                    if let Some(f) = family {
                        ans.families.insert(f);
                    }
                }
                _ => {}
            }
        }
    }

    /// Infer `ProtoFamily::Promise` for `Promise.resolve`/`all`/`race`,
    /// chained `.then`/`.catch`/`.finally`, calls to `async` functions, and
    /// Promise-returning `@ohos.*` / `@kit.*` calls (when not passed a
    /// trailing `(err, data)` callback). Returns `Some((recv_obj, load_inst))`
    /// when a chained `.then`/`.catch`/`.finally` receiver needs to be computed.
    fn call_return_family(
        &self,
        callee: ValueId,
        args: &[ValueId],
        at: InstId,
        ans_stack: &mut [FamilyAnswer],
    ) -> Option<(ValueId, InstId)> {
        let ans = ans_stack.last_mut()?;
        ans.precise = false;
        let cands = match self.links {
            Some(links) => {
                let caller = links.inst_func(self.module, at).unwrap_or(FuncId::new(0));
                callee_name_candidates_indexed(self.module, links, self.prop_stores, caller, callee)
            }
            None => callee_name_candidates(self.module, callee),
        };
        for c in &cands {
            if matches!(
                c.as_str(),
                "Promise.resolve" | "Promise.reject" | "Promise.all" | "Promise.race"
            ) {
                ans.families.insert(ProtoFamily::Promise);
                return None;
            }
            // `@ohos.*` / `@kit.*` async calls return a Promise unless called in
            // synchronous (`*Sync`) or trailing-callback form.
            if (c.starts_with("@ohos.") || c.starts_with("@kit."))
                && !c.ends_with("Sync")
                && !c.ends_with("createHttp")
                && !c.ends_with("getSystemPasteboard")
            {
                let has_cb_arg = args.last().is_some_and(|&last| {
                    !crate::gap::resolve_callback_funcs(self.module, self.oracle, last, at)
                        .is_empty()
                });
                if !has_cb_arg {
                    ans.families.insert(ProtoFamily::Promise);
                    return None;
                }
            }
        }
        // Chained `.then` / `.catch` / `.finally` on a Promise receiver.
        if let Some(ValueDef::Inst(ciid)) = self.module.value(callee).map(|v| v.def) {
            match self.module.inst(ciid).map(|i| &i.op) {
                Some(Op::LoadProp { object, name }) => {
                    if matches!(
                        self.module.sym.resolve(*name),
                        Some("then" | "catch" | "finally")
                    ) {
                        return Some((*object, ciid));
                    }
                }
                Some(Op::DefineFunc { body, .. }) => {
                    if self.module.func(*body).is_some_and(|fd| {
                        matches!(
                            fd.kind,
                            abcd_ir::FunctionKind::Async | abcd_ir::FunctionKind::AsyncArrow
                        )
                    }) {
                        ans.families.insert(ProtoFamily::Promise);
                    }
                }
                Some(Op::AllocClosure { func }) => {
                    if let Some(ValueDef::Inst(df_iid)) = self.module.value(*func).map(|v| v.def)
                        && let Some(Op::DefineFunc { body, .. }) =
                            self.module.inst(df_iid).map(|i| &i.op)
                        && self.module.func(*body).is_some_and(|fd| {
                            matches!(
                                fd.kind,
                                abcd_ir::FunctionKind::Async | abcd_ir::FunctionKind::AsyncArrow
                            )
                        })
                    {
                        ans.families.insert(ProtoFamily::Promise);
                    }
                }
                Some(Op::LoadConst(cid)) => {
                    if let Some(Const::MethodRef(f)) = self.module.consts.get(*cid)
                        && self.module.func(*f).is_some_and(|fd| {
                            matches!(
                                fd.kind,
                                abcd_ir::FunctionKind::Async | abcd_ir::FunctionKind::AsyncArrow
                            )
                        })
                    {
                        ans.families.insert(ProtoFamily::Promise);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Global-store provenance values for `name` (flow-insensitive — uses the
    /// precomputed map when available, otherwise scans `self.module` once).
    fn global_stored_values(&self, name: Sym) -> Vec<ValueId> {
        if let Some(gs) = self.global_stores {
            return gs.get(&name).cloned().unwrap_or_default();
        }
        let mut stored: Vec<ValueId> = Vec::new();
        for f in &self.module.functions {
            for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    let Some(inst) = self.module.inst(iid) else {
                        continue;
                    };
                    match &inst.op {
                        Op::StoreGlobal { name: n, value }
                        | Op::StoreGlobalRecord { name: n, value, .. }
                        | Op::TryStoreGlobal { name: n, value }
                            if *n == name =>
                        {
                            stored.push(*value);
                        }
                        _ => {}
                    }
                }
            }
        }
        stored
    }
}
