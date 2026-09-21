//! The v0.2 type lattice (design/ir-v0.2.md §5.4, design/ir.md §5).
//!
//! Dynamic-first: JS/TS values lift to [`Ty::Any`] / [`Ty::DynPrim`];
//! ArkTS static types are *annotations* on the same instruction stream and
//! never change dynamic semantics. File-bound payloads are illegal by
//! construction: [`StaticTy::Reference`] carries a [`ClassId`] into the
//! module's own class table — never a file string-pool index (N46).
//!
//! `Signature` (a declaration, see [`crate::module::Signature`]) is kept
//! separate from `Ty` (an analysis value).

use crate::id::ClassId;

/// An SSA value's type.
///
/// `Union` members are flat (no nested unions) and deduplicated; neither
/// `Any` nor `Unknown` ever appears inside a `Union`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    /// The full dynamic JS type (v0.1 `Tagged` folds into this).
    Any,
    /// A single dynamic primitive class.
    DynPrim(DynPrim),
    /// A static (ArkTS) annotation.
    Static(StaticTy),
    /// A finite set of possibilities.
    Union(Vec<Ty>),
    /// Not yet computed / no information (the join identity).
    Unknown,
}

/// The dynamic primitive classes of JavaScript.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DynPrim {
    /// `undefined`.
    Undefined,
    /// `null`.
    Null,
    /// A boolean.
    Bool,
    /// A number (f64).
    Number,
    /// A string.
    String,
    /// A symbol.
    Symbol,
    /// A BigInt.
    BigInt,
    /// Any object (incl. arrays, functions).
    Object,
}

/// A static (ArkTS declaration) type. There is deliberately no `Tagged`
/// variant: that is [`Ty::Any`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum StaticTy {
    /// 1-bit unsigned.
    U1,
    /// 8-bit signed.
    I8,
    /// 8-bit unsigned.
    U8,
    /// 16-bit signed.
    I16,
    /// 16-bit unsigned.
    U16,
    /// 32-bit signed.
    I32,
    /// 32-bit unsigned.
    U32,
    /// 64-bit signed.
    I64,
    /// 64-bit unsigned.
    U64,
    /// 32-bit float.
    F32,
    /// 64-bit float.
    F64,
    /// A reference to a class in the module's own class table. Never a
    /// file pool index (N46 is impossible by construction).
    Reference(ClassId),
    /// No value (void methods).
    Void,
}

impl Default for Ty {
    fn default() -> Self {
        Ty::Any
    }
}

/// Integer/float shape of a numeric static type:
/// `(is_float, is_signed, width_bits)`.
fn numeric_shape(t: StaticTy) -> Option<(bool, bool, u32)> {
    use StaticTy::*;
    Some(match t {
        U1 => (false, false, 1),
        I8 => (false, true, 8),
        U8 => (false, false, 8),
        I16 => (false, true, 16),
        U16 => (false, false, 16),
        I32 => (false, true, 32),
        U32 => (false, false, 32),
        I64 => (false, true, 64),
        U64 => (false, false, 64),
        F32 => (true, true, 32),
        F64 => (true, true, 64),
        Reference(_) | Void => return None,
    })
}

/// Join two distinct numeric statics along the numeric tower; `None`
/// means the tower does not cover the pair (caller falls back to
/// `DynPrim(Number)`).
fn numeric_join(a: StaticTy, b: StaticTy) -> Option<StaticTy> {
    let (af, asg, aw) = numeric_shape(a)?;
    let (bf, bsg, bw) = numeric_shape(b)?;
    match (af, bf) {
        (true, true) => Some(if aw >= bw { a } else { b }),
        // int ⊔ float: F64 only exactly covers ints up to 53 bits, F32 up
        // to 24; wider ints leave the tower.
        (true, false) | (false, true) => {
            let (fw, _isigned, iw) = if af { (aw, asg, bw) } else { (bw, bsg, aw) };
            let exact = iw <= if fw == 64 { 53 } else { 24 };
            if exact {
                Some(if fw == 64 {
                    StaticTy::F64
                } else {
                    StaticTy::F32
                })
            } else {
                None
            }
        }
        (false, false) => match (asg, bsg) {
            // Same signedness: widen.
            (true, true) | (false, false) => Some(if aw >= bw { a } else { b }),
            // Mixed signedness: the signed side must strictly cover the
            // unsigned side, otherwise the tower has no answer.
            (true, false) => (aw > bw).then_some(a),
            (false, true) => (bw > aw).then_some(b),
        },
    }
}

/// Join of two distinct statics: numeric tower, else `Any`.
fn static_join(a: StaticTy, b: StaticTy) -> Ty {
    if numeric_shape(a).is_some() && numeric_shape(b).is_some() {
        match numeric_join(a, b) {
            Some(s) => Ty::Static(s),
            // The tower tops out at the dynamic Number (design/ir.md §5).
            None => Ty::DynPrim(DynPrim::Number),
        }
    } else {
        Ty::Any
    }
}

impl Ty {
    /// Least upper bound in the documented lattice:
    ///
    /// - `Unknown ⊔ x = x` (identity), `Any ⊔ x = Any` (top);
    /// - equal types keep;
    /// - distinct static numerics widen along the numeric tower; pairs the
    ///   tower cannot cover fall back to `DynPrim(Number)`;
    /// - distinct non-numeric statics, and distinct dynamic primitives,
    ///   fall back to `Any`;
    /// - `Static(numeric) ⊔ DynPrim(Number) = DynPrim(Number)` — static
    ///   annotations widen into their dynamic class, never the reverse;
    /// - `Union`s join pointwise and re-normalize (flat, deduplicated,
    ///   collapsing to a single member or `Any`).
    pub fn join(&self, other: &Ty) -> Ty {
        if self == other {
            return self.clone();
        }
        match (self, other) {
            (Ty::Unknown, x) | (x, Ty::Unknown) => x.clone(),
            (Ty::Any, _) | (_, Ty::Any) => Ty::Any,
            (Ty::Union(ms), Ty::Union(ns)) => union_join(ms.iter().chain(ns.iter())),
            (Ty::Union(ms), x) | (x, Ty::Union(ms)) => union_join(ms.iter().chain([x])),
            (Ty::Static(a), Ty::Static(b)) => static_join(*a, *b),
            (Ty::Static(s), Ty::DynPrim(d)) | (Ty::DynPrim(d), Ty::Static(s)) => {
                if *d == DynPrim::Number && numeric_shape(*s).is_some() {
                    Ty::DynPrim(DynPrim::Number)
                } else {
                    Ty::Any
                }
            }
            (Ty::DynPrim(_), Ty::DynPrim(_)) => Ty::Any,
        }
    }

    /// Normalize into canonical form: flatten nested unions, deduplicate,
    /// collapse singletons, and map unions containing `Any` to `Any`.
    /// Returns `None` for an empty union.
    fn normalized(members: Vec<Ty>) -> Option<Ty> {
        fn flatten(m: Ty, out: &mut Vec<Ty>) {
            match m {
                Ty::Union(inner) => {
                    for x in inner {
                        flatten(x, out);
                    }
                }
                other => out.push(other),
            }
        }
        let mut flat: Vec<Ty> = Vec::new();
        for m in members {
            flatten(m, &mut flat);
        }
        flat.retain(|m| *m != Ty::Unknown);
        if flat.iter().any(|m| *m == Ty::Any) {
            return Some(Ty::Any);
        }
        flat.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
        flat.dedup();
        match flat.len() {
            0 => None,
            1 => flat.pop(),
            _ => Some(Ty::Union(flat)),
        }
    }
}

/// Pointwise join of a union's members, then normalize.
fn union_join<'a>(members: impl Iterator<Item = &'a Ty>) -> Ty {
    let mut acc = Ty::Unknown;
    for m in members {
        acc = acc.join(m);
    }
    match acc {
        Ty::Union(ms) => Ty::normalized(ms).unwrap_or(Ty::Unknown),
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(t: StaticTy) -> Ty {
        Ty::Static(t)
    }
    fn d(p: DynPrim) -> Ty {
        Ty::DynPrim(p)
    }

    #[test]
    fn join_table() {
        use DynPrim::*;
        use StaticTy::*;
        // Top and identity.
        assert_eq!(Ty::Any.join(&d(Number)), Ty::Any);
        assert_eq!(d(String).join(&Ty::Any), Ty::Any);
        assert_eq!(Ty::Unknown.join(&d(Bool)), d(Bool));
        assert_eq!(s(I32).join(&Ty::Unknown), s(I32));
        // Equal types keep.
        assert_eq!(s(I32).join(&s(I32)), s(I32));
        assert_eq!(d(Number).join(&d(Number)), d(Number));
        assert_eq!(s(Void).join(&s(Void)), s(Void));
        // Numeric tower: same-signedness widening.
        assert_eq!(s(I8).join(&s(I16)), s(I16));
        assert_eq!(s(U32).join(&s(U8)), s(U32));
        // Mixed signedness: signed must strictly cover.
        assert_eq!(s(U8).join(&s(I16)), s(I16));
        assert_eq!(s(U32).join(&s(I32)), d(Number));
        // int ⊔ float.
        assert_eq!(s(I32).join(&s(F64)), s(F64));
        assert_eq!(s(F32).join(&s(F64)), s(F64));
        assert_eq!(s(I64).join(&s(F64)), d(Number)); // tower tops out
        // Numeric static widens into its dynamic class.
        assert_eq!(s(I32).join(&d(Number)), d(Number));
        // Non-numeric mismatches.
        assert_eq!(s(Reference(ClassId::new(0))).join(&s(I32)), Ty::Any);
        assert_eq!(s(Void).join(&s(I32)), Ty::Any);
        assert_eq!(d(Number).join(&d(String)), Ty::Any);
        assert_eq!(s(Reference(ClassId::new(0))).join(&d(Object)), Ty::Any);
    }

    #[test]
    fn join_unions_normalize() {
        use DynPrim::*;
        let u = Ty::Union(vec![d(Number), d(Bool)]);
        // Pointwise: Number⊔String = Any, Bool⊔String = Any → Any.
        assert_eq!(u.join(&d(String)), Ty::Any);
        // Number⊔Number = Number, Bool⊔Number = Any → Any.
        assert_eq!(u.join(&d(Number)), Ty::Any);
        // Union ⊔ identical union keeps it normalized.
        assert_eq!(u.join(&u), u);
        // Union inside a union flattens.
        let nested = Ty::Union(vec![u.clone(), d(Null)]);
        match Ty::normalized(vec![nested]).unwrap() {
            Ty::Union(ms) => assert_eq!(ms.len(), 3),
            other => panic!("expected union, got {other:?}"),
        }
    }
}
