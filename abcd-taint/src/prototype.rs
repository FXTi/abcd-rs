//! Receiver-type approximation for prototype-keyed summary lookup
//! (design/flowdroid/summaries.md §2.3 — FlowDroid's SummaryResolver
//! 4-level lookup, keyed here on alloc-kind → prototype family instead
//! of Java types; t-P3).
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
//!    top-level script code stores locals into the global record
//!    (`sttoglobalrecord` → `Op::StoreGlobal`) and reads them back at
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
//! 5. **Constructor results** (t-P5) — `new <global>(...)` where the
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
//!   kinds, not hierarchy roots (FlowDroid's hierarchy level needs
//!   the rung-2 whole-program PTA).
//! - **Own-property shadows**: `a.pop = function () {…}` on an array
//!   is invisible at the method load (store-to-load of function
//!   values is opaque), so the builtin summary fires anyway — the
//!   c2 lesson, structurally; probe `e7-own-method-shadow` records
//!   the expected FP (closes at rung 2 with store-to-load function
//!   resolution).
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

use abcd_ir::{Const, InstId, Module, Op, Sym, ValueDef, ValueId};

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
        Const::Number(_) => Some(ProtoFamily::Num),
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
        }
    }

    /// The prototype families of a receiver value at a program point.
    pub fn families_of(&self, value: ValueId, at: InstId) -> FamilyAnswer {
        if let Some(a) = self.memo.borrow().get(&value) {
            return a.clone();
        }
        let mut visiting = HashSet::new();
        let ans = self.compute(value, at, &mut visiting);
        self.memo.borrow_mut().insert(value, ans.clone());
        ans
    }

    /// The unmemoized answer; `visiting` is shared across the whole
    /// recursive walk so phi back-edge cycles terminate (marked
    /// imprecise).
    fn compute(&self, value: ValueId, at: InstId, visiting: &mut HashSet<ValueId>) -> FamilyAnswer {
        let mut ans = FamilyAnswer {
            families: BTreeSet::new(),
            precise: true,
        };
        // 1. Site kinds, rung-aware (the engine's interprocedural
        //    answer when it is precise, else the local walk).
        let info = self.oracle.site_info_at(value, at);
        for site in info.sites.iter() {
            if let Some(f) = self.module.inst(site).and_then(|i| family_of_alloc(&i.op)) {
                ans.families.insert(f);
            }
        }
        if info.has_unknown {
            ans.precise = false;
        }
        // 1b. The MAY-direction arm (t-P4): the engine's
        //    resolution-complete fan-out answers (unbalanced — a param
        //    receiver whose callers are all recorded in the call graph)
        //    type receivers for the ADDITIVE prototype path, exactly the
        //    consumer discipline of `CallGraph::refine_with_points_to`
        //    (callee resolution accepts the same answers). Sites the
        //    precise arm already reported contribute nothing new;
        //    anything beyond them marks the answer imprecise.
        for site in self.oracle.may_sites_at(value, at).iter() {
            if info.sites.iter().any(|s| s == site) {
                continue;
            }
            if let Some(f) = self.module.inst(site).and_then(|i| family_of_alloc(&i.op)) {
                ans.families.insert(f);
                ans.precise = false;
            }
        }
        // 2. The def-chain walk for the non-site sources (constants,
        //    global-store provenance, GetIterator).
        self.walk(value, visiting, &mut ans);
        if ans.families.is_empty() {
            ans.precise = false;
        }
        ans
    }

    /// The def-chain walk for the families `site_info_at` cannot
    /// carry: constants, global stores, iterator protocol objects.
    /// `Mov`/`Phi` pass through; keyed allocs insert their kind
    /// directly (values reached through a NESTED hop never pass the
    /// site walk above); everything else marks the answer imprecise
    /// without inventing a family.
    fn walk(&self, value: ValueId, visiting: &mut HashSet<ValueId>, ans: &mut FamilyAnswer) {
        if !visiting.insert(value) {
            ans.precise = false;
            return;
        }
        let Some(v) = self.module.value(value) else {
            ans.precise = false;
            return;
        };
        match v.def {
            ValueDef::Const(c) => {
                if let Some(f) = self.module.consts.get(c).and_then(family_of_const) {
                    ans.families.insert(f);
                }
            }
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => {
                ans.precise = false;
            }
            ValueDef::Inst(iid) => match self.module.inst(iid).map(|i| &i.op) {
                Some(Op::Mov { src }) => self.walk(*src, visiting, ans),
                Some(Op::Phi { entries }) => {
                    for (_, incoming) in entries {
                        self.walk(*incoming, visiting, ans);
                    }
                }
                Some(Op::LoadConst(c)) => {
                    if let Some(f) = self.module.consts.get(*c).and_then(family_of_const) {
                        ans.families.insert(f);
                    }
                }
                Some(Op::GetIterator { obj }) => {
                    // The iterator protocol object of a BUILTIN
                    // iterable only: a user object with a custom
                    // @@iterator (family Object) or an unknown source
                    // types nothing. The shared `visiting` set guards
                    // phi back-edge cycles.
                    let src = self.compute(*obj, iid, visiting);
                    if !src.families.is_empty()
                        && src
                            .families
                            .iter()
                            .all(|f| matches!(f, ProtoFamily::Array | ProtoFamily::Str))
                    {
                        ans.families.insert(ProtoFamily::Iterator);
                    } else {
                        ans.precise = false;
                    }
                }
                Some(Op::TryGetGlobal { name, .. }) => {
                    self.global_store_families(*name, visiting, ans);
                }
                Some(Op::Call {
                    kind: abcd_ir::CallKind::New,
                    callee,
                    ..
                }) => {
                    // `new <builtin ctor>(...)` — t-P5 constructor-
                    // result arm (module docs §5): es2abc lowers regexp
                    // literals to `new RegExp(...)`, so this is the arm
                    // that types the corpus' `r.test` receivers.
                    self.constructor_family(*callee, visiting, ans);
                }
                Some(op) if family_of_alloc(op).is_some() => {
                    // Insert directly: values reached through a NESTED
                    // hop (global-store provenance, GetIterator's
                    // iterable) never pass through the site walk
                    // above, which runs only on the top-level
                    // receiver (idempotent for direct receivers).
                    if let Some(f) = family_of_alloc(op) {
                        ans.families.insert(f);
                    }
                }
                Some(_) => {
                    ans.precise = false;
                }
                None => {
                    ans.precise = false;
                }
            },
        }
    }

    /// The t-P5 constructor-result arm: `callee` of a `kind: New` call
    /// is walked through `Mov`/`Phi` to a `TryGetGlobal(name)` leaf; a
    /// KNOWN builtin constructor name types the constructed value with
    /// the matching family. Imprecise by construction (the constructor
    /// binding is a mutable global — a shadowed `RegExp` defeats it;
    /// the same may-direction discipline as global-store provenance).
    /// Anything else (user class, computed callee, unknown name)
    /// contributes no family.
    fn constructor_family(
        &self,
        callee: ValueId,
        visiting: &mut HashSet<ValueId>,
        ans: &mut FamilyAnswer,
    ) {
        ans.precise = false;
        let Some(v) = self.module.value(callee) else {
            return;
        };
        let ValueDef::Inst(iid) = v.def else {
            return;
        };
        match self.module.inst(iid).map(|i| &i.op) {
            Some(Op::Mov { src }) => self.constructor_family(*src, visiting, ans),
            Some(Op::Phi { entries }) => {
                for (_, incoming) in entries {
                    if visiting.insert(*incoming) {
                        self.constructor_family(*incoming, visiting, ans);
                    }
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
                    _ => None,
                };
                if let Some(f) = family {
                    ans.families.insert(f);
                }
            }
            _ => {}
        }
    }

    /// Global-store provenance: union the families of every value the
    /// module stores into `name` (flow-insensitive — the fact model's
    /// `Global`-base discipline). No stores (host-provided global) or
    /// any untypable store = imprecise; the answer NEVER gets a
    /// precise flag through a global hop (cross-script mutation).
    fn global_store_families(
        &self,
        name: Sym,
        visiting: &mut HashSet<ValueId>,
        ans: &mut FamilyAnswer,
    ) {
        ans.precise = false;
        let mut stored: Vec<ValueId> = Vec::new();
        for f in &self.module.functions {
            for &b in &f.blocks {
                for &iid in &self.module.blocks[b.index()].insts {
                    match &self.module.insts[iid.index()].op {
                        Op::StoreGlobal { name: n, value }
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
        for value in stored {
            self.walk(value, visiting, ans);
        }
    }
}
