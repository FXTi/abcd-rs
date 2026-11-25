//! The IR type lattice (`design/ir.md`).
//!
//! Dynamic-first: JS/TS values lift to [`Ty::Any`] / [`Ty::DynPrim`];
//! ArkTS static types are *annotations* on the same instruction stream and
//! never change dynamic semantics. File-bound payloads are illegal by
//! construction: [`StaticTy::Reference`] carries a [`ClassId`] into the
//! module's own class table — never a file string-pool index
//! (`design/decisions.md` N46).
//!
//! `Signature` (a declaration, see [`crate::module::Signature`]) is kept
//! separate from `Ty` (an analysis value).

use std::fmt;
use std::hash::{Hash, Hasher};

use crate::id::ClassId;

/// An SSA value's type.
///
/// `Union` members are flat (no nested unions) and deduplicated in normal form;
/// neither `Any` nor `Unknown` ever appears inside a normalized `Union`.
/// `Drop`, `Clone`, `PartialEq`, `Eq`, `Hash`, and `Debug` are implemented
/// iteratively over explicit heap workstacks so arbitrarily nested unions never
/// overflow the call stack.
#[derive(Default)]
pub enum Ty {
    /// The full dynamic JS tagged type.
    #[default]
    Any,
    /// A single dynamic primitive class.
    DynPrim(DynPrim),
    /// A static (ArkTS) annotation.
    Static(StaticTy),
    /// A finite set of possibilities.
    Union(Box<[Ty]>),
    /// Not yet computed / no information.
    Unknown,
}

impl Ty {
    /// Construct a [`Ty::Union`] from any slice/vec/array convertible into `Box<[Ty]>`.
    #[must_use]
    pub fn union(members: impl Into<Box<[Ty]>>) -> Self {
        Self::Union(members.into())
    }
}

impl Drop for Ty {
    fn drop(&mut self) {
        let Ty::Union(children) = self else {
            return;
        };
        if !children.iter().any(|t| matches!(t, Ty::Union(_))) {
            return;
        }
        let mut stack: Vec<Box<[Ty]>> = Vec::new();
        for elem in children.iter_mut() {
            if let Ty::Union(nested) = elem {
                let taken = std::mem::take(nested);
                if !taken.is_empty() {
                    stack.push(taken);
                }
            }
        }
        while let Some(mut slice) = stack.pop() {
            for elem in slice.iter_mut() {
                if let Ty::Union(nested) = elem {
                    let taken = std::mem::take(nested);
                    if !taken.is_empty() {
                        stack.push(taken);
                    }
                }
            }
        }
    }
}

impl Clone for Ty {
    fn clone(&self) -> Self {
        match self {
            Ty::Any => Ty::Any,
            Ty::DynPrim(p) => Ty::DynPrim(*p),
            Ty::Static(s) => Ty::Static(*s),
            Ty::Unknown => Ty::Unknown,
            Ty::Union(root) => {
                if !root.iter().any(|t| matches!(t, Ty::Union(_))) {
                    let mut flat = Vec::with_capacity(root.len());
                    for item in root.iter() {
                        flat.push(match item {
                            Ty::Any => Ty::Any,
                            Ty::DynPrim(p) => Ty::DynPrim(*p),
                            Ty::Static(s) => Ty::Static(*s),
                            Ty::Unknown => Ty::Unknown,
                            Ty::Union(_) => unreachable!(),
                        });
                    }
                    return Ty::Union(flat.into_boxed_slice());
                }
                let mut frames: Vec<(&[Ty], usize, Vec<Ty>)> =
                    vec![(root, 0, Vec::with_capacity(root.len()))];
                loop {
                    let Some((src, idx, built)) = frames.last_mut() else {
                        return Ty::Any;
                    };
                    if *idx < src.len() {
                        let i = *idx;
                        *idx += 1;
                        match &src[i] {
                            Ty::Any => built.push(Ty::Any),
                            Ty::DynPrim(p) => built.push(Ty::DynPrim(*p)),
                            Ty::Static(s) => built.push(Ty::Static(*s)),
                            Ty::Unknown => built.push(Ty::Unknown),
                            Ty::Union(sub) => {
                                frames.push((sub, 0, Vec::with_capacity(sub.len())));
                            }
                        }
                    } else {
                        let Some((_, _, done)) = frames.pop() else {
                            return Ty::Any;
                        };
                        let node = Ty::Union(done.into_boxed_slice());
                        if let Some((_, _, parent_built)) = frames.last_mut() {
                            parent_built.push(node);
                        } else {
                            return node;
                        }
                    }
                }
            }
        }
    }
}

impl PartialEq for Ty {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Ty::Any, Ty::Any) | (Ty::Unknown, Ty::Unknown) => true,
            (Ty::DynPrim(a), Ty::DynPrim(b)) => a == b,
            (Ty::Static(a), Ty::Static(b)) => a == b,
            (Ty::Union(xs), Ty::Union(ys)) => {
                if xs.len() != ys.len() {
                    return false;
                }
                let mut stack: Vec<(&[Ty], &[Ty], usize)> = vec![(xs, ys, 0)];
                while let Some((a, b, idx)) = stack.last_mut() {
                    if *idx == a.len() {
                        stack.pop();
                        continue;
                    }
                    let i = *idx;
                    *idx += 1;
                    match (&a[i], &b[i]) {
                        (Ty::Any, Ty::Any) | (Ty::Unknown, Ty::Unknown) => {}
                        (Ty::DynPrim(x), Ty::DynPrim(y)) if x == y => {}
                        (Ty::Static(x), Ty::Static(y)) if x == y => {}
                        (Ty::Union(sa), Ty::Union(sb)) if sa.len() == sb.len() => {
                            if !sa.is_empty() {
                                stack.push((sa, sb, 0));
                            }
                        }
                        _ => return false,
                    }
                }
                true
            }
            _ => false,
        }
    }
}

impl Eq for Ty {}

impl Hash for Ty {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Ty::Any => 0u8.hash(state),
            Ty::DynPrim(p) => {
                1u8.hash(state);
                p.hash(state);
            }
            Ty::Static(s) => {
                2u8.hash(state);
                s.hash(state);
            }
            Ty::Unknown => 4u8.hash(state),
            Ty::Union(xs) => {
                3u8.hash(state);
                xs.len().hash(state);
                let mut stack: Vec<(&[Ty], usize)> = vec![(xs, 0)];
                while let Some((slice, idx)) = stack.last_mut() {
                    if *idx == slice.len() {
                        stack.pop();
                        continue;
                    }
                    let i = *idx;
                    *idx += 1;
                    match &slice[i] {
                        Ty::Any => 0u8.hash(state),
                        Ty::DynPrim(p) => {
                            1u8.hash(state);
                            p.hash(state);
                        }
                        Ty::Static(s) => {
                            2u8.hash(state);
                            s.hash(state);
                        }
                        Ty::Unknown => 4u8.hash(state),
                        Ty::Union(sub) => {
                            3u8.hash(state);
                            sub.len().hash(state);
                            if !sub.is_empty() {
                                stack.push((sub, 0));
                            }
                        }
                    }
                }
            }
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Any => f.write_str("Any"),
            Ty::DynPrim(p) => f.debug_tuple("DynPrim").field(p).finish(),
            Ty::Static(s) => f.debug_tuple("Static").field(s).finish(),
            Ty::Unknown => f.write_str("Unknown"),
            Ty::Union(xs) => {
                f.write_str("Union([")?;
                let mut stack: Vec<(&[Ty], usize)> = vec![(xs, 0)];
                while let Some((slice, idx)) = stack.last_mut() {
                    if *idx == slice.len() {
                        stack.pop();
                        f.write_str("])")?;
                        continue;
                    }
                    let i = *idx;
                    *idx += 1;
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    match &slice[i] {
                        Ty::Any => f.write_str("Any")?,
                        Ty::DynPrim(p) => f.debug_tuple("DynPrim").field(p).finish()?,
                        Ty::Static(s) => f.debug_tuple("Static").field(s).finish()?,
                        Ty::Unknown => f.write_str("Unknown")?,
                        Ty::Union(sub) => {
                            f.write_str("Union([")?;
                            stack.push((sub, 0));
                        }
                    }
                }
                Ok(())
            }
        }
    }
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
    /// A reference to a class in the module's own class table — never a
    /// file pool index (`design/decisions.md` N46).
    Reference(ClassId),
    /// No value (void methods).
    Void,
}
