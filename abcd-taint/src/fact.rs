//! The taint fact model (`design/analysis.md`): access-path discipline
//! over `abcd-analysis`'s heap and environment keys.
//!
//! A taint fact is an **access path**: a *base* plus a k-capped
//! [`FieldChain`] below it. Bases come in five kinds:
//!
//! - [`TaintBase::Local`] — an SSA value (the value *is* the taint
//!   key, e.g. `x.f.g` rooted at local SSA value `x`).
//! - [`TaintBase::Heap`] — a set of allocation sites (the rung-0 heap
//!   key of `abcd-analysis::dataflow::heap`): taint written through
//!   `obj.f = tainted` is re-keyed by the alloc sites of `obj`, so a
//!   store through `x` and a load through `y` meet iff the def chains of
//!   `x`/`y` share a site. Heap facts are function-global state: they
//!   pass through calls, returns, and phis unchanged.
//! - [`TaintBase::Global`] — a named global binding (`StoreGlobal` /
//!   `TryGetGlobal`). Globals are mutable across scripts, so global
//!   facts are NEVER killed (always weak).
//! - [`TaintBase::ModuleVar`] — a module-variable slot
//!   (`StoreModuleVar` / `LoadModuleVar`).
//! - [`TaintBase::LexVar`] — a lexical-environment slot keyed by
//!   `(level, slot)` only, deliberately NOT by function: closure bodies
//!   read outer slots through shifted levels, so a per-function key
//!   would break capture propagation. At rung 2, precise accesses refine
//!   this to `NewLexEnv` allocation sites (`design/analysis.md`).
//!
//! ## Weak updates
//!
//! Stores never remove taint from the *solver state* — propagation is a
//! monotone set union, so "killing" is expressible only as a flow
//! function dropping the incoming fact. A store performs a **strong**
//! kill of a matching heap/local-field fact only when
//! [`abcd_analysis::dataflow::heap::update_kind`] says `Strong` (single
//! site, no phi, no unknown in the base's def chain — the SSA substitute
//! for a must-alias proof). Everything else is a weak update: the old
//! fact survives alongside the new one.
//!
//! ## The zero fact
//!
//! [`Fact::Zero`] is the IFDS `Λ` placeholder representing unconditional
//! reachability ("rest of the program state"). It is distinct from every
//! real taint fact by construction and auto-propagated by the solver.

use abcd_analysis::dataflow::heap::{AllocSiteSet, FieldChain, FieldKey};
use abcd_ir::{ClassId, Sym, ValueId};

/// The base of an access path (see module docs).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TaintBase {
    /// An SSA value.
    Local(ValueId),
    /// Heap objects by allocation site (rung-0 key).
    Heap(AllocSiteSet),
    /// A named global binding.
    Global(Sym),
    /// A per-record module-variable slot `(record ClassId, local_slot)`.
    ModuleVar(ClassId, u32),
    /// A lexical-environment slot `(level, slot)` — function-agnostic
    /// (see module docs).
    LexVar(u16, u16),
}

/// A taint fact: `base` + k-capped field chain (access path).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TaintFact {
    /// The access-path base.
    pub base: TaintBase,
    /// The field chain below the base (empty = the base value itself).
    pub fields: FieldChain,
}

impl TaintFact {
    /// A fact on a bare SSA value (empty chain).
    pub fn local(value: ValueId) -> Self {
        TaintFact {
            base: TaintBase::Local(value),
            fields: FieldChain::new(),
        }
    }

    /// This fact with one more field step, k-capped.
    pub fn pushed(&self, key: FieldKey, cap: usize) -> Self {
        TaintFact {
            base: self.base.clone(),
            fields: self.fields.pushed(key, cap),
        }
    }

    /// This fact re-based onto `base`, keeping the field chain intact.
    pub fn rebased(&self, base: TaintBase) -> Self {
        TaintFact {
            base,
            fields: self.fields.clone(),
        }
    }

    /// This fact with the field chain replaced (call/return mapping).
    pub fn with_fields(&self, fields: FieldChain) -> Self {
        TaintFact {
            base: self.base.clone(),
            fields,
        }
    }

    /// The base SSA value, iff this is a local-based fact.
    pub fn local_base(&self) -> Option<ValueId> {
        match &self.base {
            TaintBase::Local(v) => Some(*v),
            _ => None,
        }
    }

    /// Whether the base is function-global state (heap/global/module/
    /// lexical): such facts pass through call and return edges
    /// unchanged, unlike SSA locals which die at function boundaries.
    pub fn is_state_base(&self) -> bool {
        !matches!(self.base, TaintBase::Local(_))
    }
}

/// The IFDS fact: Λ or a taint access path.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Fact {
    /// The zero (`Λ`) fact — unconditional reachability anchor.
    Zero,
    /// A real taint fact.
    Taint(TaintFact),
}

impl Fact {
    /// The taint fact inside, if any.
    pub fn taint(&self) -> Option<&TaintFact> {
        match self {
            Fact::Zero => None,
            Fact::Taint(t) => Some(t),
        }
    }

    /// Wrap a taint fact.
    pub fn of(taint: TaintFact) -> Self {
        Fact::Taint(taint)
    }
}
