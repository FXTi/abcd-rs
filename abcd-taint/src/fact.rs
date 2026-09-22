//! The taint fact model (design/flowdroid/soot-infoflow.md §3 access-path
//! discipline over `abcd-analysis`'s rung-0 heap keys).
//!
//! A taint fact is an **access path**: a *base* plus a k-capped
//! [`FieldChain`] below it. Bases come in five kinds:
//!
//! - [`TaintBase::Local`] — an SSA value (T1: the value *is* the taint
//!   key). This is the soot-infoflow `x.f.g` case with a local base.
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
//!   would break capture propagation. The cross-function merge is a
//!   documented rung-0 over-approximation (the precision ladder pointer
//!   is in the README).
//!
//! ## Weak updates
//!
//! Stores never remove taint from the *solver state* — propagation is a
//! monotone set union, so "killing" is expressible only as a flow
//! function dropping the incoming fact. A store performs a **strong**
//! kill of a matching heap/local-field fact only when
//! [`abcd_analysis::dataflow::heap::update_kind`] says `Strong` (single
//! site, no phi, no unknown in the base's def chain — the SSA substitute
//! for a must-alias proof, infoflow.md §9 item 3). Everything else is a
//! weak update: the old fact survives alongside the new one.
//!
//! ## The zero fact
//!
//! [`Fact::Zero`] is heros' Λ — the "rest of the program state"
//! placeholder. It is distinct from every real fact by construction
//! (heros.md §2 item 4) and the solver auto-propagates it.

use abcd_analysis::dataflow::heap::{AllocSiteSet, FieldChain, FieldKey};
use abcd_ir::{Sym, ValueId};

/// The base of an access path (see module docs).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TaintBase {
    /// An SSA value.
    Local(ValueId),
    /// Heap objects by allocation site (rung-0 key).
    Heap(AllocSiteSet),
    /// A named global binding.
    Global(Sym),
    /// A module-variable slot.
    ModuleVar(u32),
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

    /// A fact on a bare global (empty chain).
    pub fn global(name: Sym) -> Self {
        TaintFact {
            base: TaintBase::Global(name),
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

    /// This fact re-based onto `base`, keeping the field chain (the
    /// taint substitution of soot-infoflow's
    /// `AccessPathFactory.copyWithNewValue`).
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
    /// The zero (Λ) fact — heros' "rest of the program state".
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
