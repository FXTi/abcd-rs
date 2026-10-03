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
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub enum Ty {
    /// The full dynamic JS type (v0.1 `Tagged` folds into this).
    #[default]
    Any,
    /// A single dynamic primitive class.
    DynPrim(DynPrim),
    /// A static (ArkTS) annotation.
    Static(StaticTy),
    /// A finite set of possibilities.
    Union(Vec<Ty>),
    /// Not yet computed / no information.
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
