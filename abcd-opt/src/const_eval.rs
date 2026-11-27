//! Shared ECMA-262 constant-evaluation kernel, branch-folding helper, and
//! non-recursive SSA utility routines (`design/ir.md`, `design/decisions.md`
//! `N23`, `N36`–`N42`, `ADR-19`, `#60`, `#93`).
//!
//! Both [`crate::peephole::Peephole`] and [`crate::sccp::Sccp`] evaluate
//! constants exclusively through this module so their ECMAScript numeric,
//! bitwise, equality, coercion, truthiness, and branch-rewriting semantics can
//! never drift.

use std::collections::{HashMap, HashSet};

use abcd_ir::{
    BinOp, BlockId, CmpOp, Const, ConstId, Edge, EdgeKind, FuncId, InstId, LocalScope, Module, Op,
    Sym, SymbolTable, Ty, UnOp, ValueDef, ValueId,
};

/// Canonical quiet `NaN` bit pattern (`+qNaN`, `#60`).
pub const CANONICAL_NAN_BITS: u64 = 0x7ff8_0000_0000_0000;

/// ECMA-262 `ToInt32`, shared by all constant-fold consumers (`N42`).
///
/// Rust's `n as i32` saturates out-of-range floats to `±2^31`; ECMAScript
/// bitwise and shift operators wrap modulo `2^32` and map `NaN` / `±Infinity`
/// to `+0`, matching vendored `base::NumberHelper::DoubleToInt(d, INT32_BITS)`.
#[must_use]
pub fn to_int32(n: f64) -> i32 {
    if !n.is_finite() || n == 0.0 {
        return 0;
    }
    let wrapped = n.trunc() % 4_294_967_296.0;
    let positive = if wrapped < 0.0 {
        wrapped + 4_294_967_296.0
    } else {
        wrapped
    };
    (positive as u32) as i32
}

/// ECMA-262 `ToUint32` — modular `2^32` wrap reinterpreted unsigned (`N42`).
/// Shift count masking (`& 0x1f`) applies *after* this conversion so negative
/// shift counts wrap before masking (e.g. `-1 -> 31`).
#[must_use]
#[inline]
pub fn to_uint32(n: f64) -> u32 {
    to_int32(n) as u32
}

/// Normalize an `f64` produced by constant folding so any `NaN` maps to
/// [`CANONICAL_NAN_BITS`] while `-0.0` (`0x8000_0000_0000_0000`) and all finite
/// or infinite bit patterns survive verbatim (`#60`, `N37`).
#[must_use]
#[inline]
pub fn canonicalize_f64_bits(v: f64) -> u64 {
    if v.is_nan() {
        CANONICAL_NAN_BITS
    } else {
        v.to_bits()
    }
}

/// Construct a [`Const::Number`] with canonicalized `NaN` bits (`#60`).
#[must_use]
#[inline]
pub fn canonical_number_const(v: f64) -> Const {
    Const::Number(canonicalize_f64_bits(v))
}

/// Whether `x` is a finite odd integer in IEEE-754 `f64`. Any finite integer
/// with `|x| >= 2^53` (`9007199254740992.0`) has ULP `>= 2` and is even.
#[inline]
fn is_odd_integral(x: f64) -> bool {
    if !x.is_finite() || x.trunc() != x {
        return false;
    }
    let abs = x.abs();
    if abs >= 9_007_199_254_740_992.0 {
        return false;
    }
    (abs as u64) & 1 == 1
}

/// ECMA-262 §6.1.6.1.3 `Number::exponentiate(base, exponent)` (`ADR-19`,
/// `R3-H6`), delegating general finite cases to pure-Rust `libm::pow` with
/// canonicalized `NaN` bits (`#60`).
#[must_use]
pub fn ecma_pow(base: f64, exponent: f64) -> f64 {
    let nan = f64::from_bits(CANONICAL_NAN_BITS);
    if exponent.is_nan() {
        return nan;
    }
    if exponent == 0.0 {
        return 1.0;
    }
    if base.is_nan() {
        return nan;
    }
    if exponent == f64::INFINITY {
        let abs_b = base.abs();
        return if abs_b > 1.0 {
            f64::INFINITY
        } else if abs_b == 1.0 {
            nan
        } else {
            0.0
        };
    }
    if exponent == f64::NEG_INFINITY {
        let abs_b = base.abs();
        return if abs_b > 1.0 {
            0.0
        } else if abs_b == 1.0 {
            nan
        } else {
            f64::INFINITY
        };
    }
    if base == f64::INFINITY {
        return if exponent > 0.0 { f64::INFINITY } else { 0.0 };
    }
    if base == f64::NEG_INFINITY {
        let odd = is_odd_integral(exponent);
        return if exponent > 0.0 {
            if odd {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            }
        } else if odd {
            -0.0
        } else {
            0.0
        };
    }
    if base == 0.0 {
        if !base.is_sign_negative() {
            return if exponent > 0.0 { 0.0 } else { f64::INFINITY };
        }
        let odd = is_odd_integral(exponent);
        return if exponent > 0.0 {
            if odd { -0.0 } else { 0.0 }
        } else if odd {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        };
    }
    if base < 0.0 && exponent.is_finite() && exponent.trunc() != exponent {
        return nan;
    }
    let r = libm::pow(base, exponent);
    f64::from_bits(canonicalize_f64_bits(r))
}

/// Whether `inst_id`'s result or any of its operands carries a static ArkTS
/// [`Ty::Static`] annotation (`R3-A11` / `#36` — dynamic JS `f64` / `ToInt32`
/// folds must not rewrite static integer/float ops).
#[must_use]
pub fn has_static_ty(module: &Module, inst_id: InstId) -> bool {
    let Some(inst) = module.inst(inst_id) else {
        return false;
    };
    if let Some(res) = inst.result
        && matches!(module.value(res).map(|v| &v.ty), Some(Ty::Static(_)))
    {
        return true;
    }
    let mut static_operand = false;
    inst.op.for_each_operand(|v| {
        if !static_operand && matches!(module.value(v).map(|val| &val.ty), Some(Ty::Static(_))) {
            static_operand = true;
        }
    });
    static_operand
}

/// Whether `c` is a scalar [`Const`] legal inside [`Op::LoadConst`] per
/// [`abcd_ir::verify_module`].
#[must_use]
#[inline]
pub const fn is_loadable_scalar_const(c: &Const) -> bool {
    !matches!(
        c,
        Const::Accessor(_)
            | Const::MethodAffiliate(_)
            | Const::BuiltinTypeIndex(_)
            | Const::ArrayLiteral(_)
            | Const::TypedArrayLiteral { .. }
            | Const::ObjectLiteral { .. }
            | Const::LiteralBufferRef(_)
            | Const::MethodRef { .. }
    )
}

/// Whether `c` enters `Sccp`'s scalar constant lattice (`Const::Hole` and
/// literal/metadata tags stay `Bottom` so TDZ holes and heap shapes are never
/// replaced by scalar loads).
#[must_use]
#[inline]
pub const fn is_sccp_lattice_const(c: &Const) -> bool {
    matches!(
        c,
        Const::Undefined
            | Const::Null
            | Const::Bool(_)
            | Const::Int8(_)
            | Const::Int32(_)
            | Const::Float32(_)
            | Const::Number(_)
            | Const::Int64(_)
            | Const::UInt64(_)
            | Const::String(_)
            | Const::BigInt(_)
    )
}

/// Borrow a constant directly carried by `val` (`ValueDef::Const` or
/// `Op::LoadConst`) without cloning composite literal buffers.
#[must_use]
#[inline]
pub fn const_ref_of_value(module: &Module, val: ValueId) -> Option<&Const> {
    let cid: ConstId = match module.value(val)?.def {
        ValueDef::Const(c) => c,
        ValueDef::Inst(inst) => match &module.inst(inst)?.op {
            Op::LoadConst(c) => *c,
            _ => return None,
        },
        _ => return None,
    };
    module.consts.get(cid)
}

/// Resolve a constant directly carried by `val` (`ValueDef::Const` or
/// `Op::LoadConst`).
#[must_use]
pub fn const_of_value(module: &Module, val: ValueId) -> Option<Const> {
    const_ref_of_value(module, val).cloned()
}

/// ECMA-262 `ToNumber` over primitive scalar constants (`Number`, `Float32`,
/// `Int8`, `Int32`, `Bool`, `Null -> +0.0`, `Undefined -> NaN`).
///
/// Strings, BigInts, 64-bit static integers, TDZ holes, and literal buffers
/// return `None`.
#[must_use]
pub fn const_to_number(c: &Const) -> Option<f64> {
    match c {
        Const::Number(bits) => Some(f64::from_bits(*bits)),
        Const::Float32(bits) => Some(f64::from(f32::from_bits(*bits))),
        Const::Int8(v) => Some(f64::from(*v)),
        Const::Int32(v) => Some(f64::from(*v as i32)),
        Const::Bool(true) => Some(1.0),
        Const::Bool(false) | Const::Null => Some(0.0),
        Const::Undefined => Some(f64::from_bits(CANONICAL_NAN_BITS)),
        _ => None,
    }
}

/// Parse a `Const::BigInt` text representation and return its ECMA-262
/// `ToBoolean` truthiness (`0n` is `false`, any non-zero BigInt is `true`).
#[must_use]
pub fn bigint_str_is_truthy(s: &str) -> Option<bool> {
    let trimmed = s.trim();
    let body = trimmed
        .strip_prefix('-')
        .or_else(|| trimmed.strip_prefix('+'))
        .unwrap_or(trimmed);
    let (digits, radix) =
        if let Some(d) = body.strip_prefix("0x").or_else(|| body.strip_prefix("0X")) {
            (d, 16)
        } else if let Some(d) = body.strip_prefix("0b").or_else(|| body.strip_prefix("0B")) {
            (d, 2)
        } else if let Some(d) = body.strip_prefix("0o").or_else(|| body.strip_prefix("0O")) {
            (d, 8)
        } else {
            (body, 10)
        };
    if digits.is_empty() || !digits.chars().all(|ch| ch.is_digit(radix)) {
        return None;
    }
    Some(digits.bytes().any(|b| b != b'0'))
}

/// Normalize a decimal `BigInt` text to canonical `"-digits"` / `"digits"` form
/// (`"-0"` / `"+0"` / `"00"` -> `"0"`) for exact BigInt `===` comparison.
fn normalize_decimal_bigint(s: &str) -> Option<(bool, &str)> {
    let trimmed = s.trim();
    let (neg, body) = if let Some(rest) = trimmed.strip_prefix('-') {
        (true, rest)
    } else if let Some(rest) = trimmed.strip_prefix('+') {
        (false, rest)
    } else {
        (false, trimmed)
    };
    if body.is_empty() || !body.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let stripped = body.trim_start_matches('0');
    if stripped.is_empty() {
        Some((false, "0"))
    } else {
        Some((neg, stripped))
    }
}

/// ECMA-262 §7.1.2 `ToBoolean` over [`Const`] entries:
/// - `Bool(b)` -> `b`
/// - `Null` / `Undefined` -> `false`
/// - `Int8` / `Int32` / `Int64` / `UInt64` -> `!= 0`
/// - `Float32` / `Number` -> `!= ±0.0 && !is_nan()`
/// - `String` -> `!is_empty()` (`""` is `false`, non-empty is `true`)
/// - `BigInt` -> `!= 0n` (`"0"` is `false`, non-zero is `true`)
/// - Object / array / typed-array / method-closure shapes -> `true`
/// - `Hole` and internal metadata tags -> `None`
#[must_use]
pub fn const_to_boolean(sym_table: &SymbolTable, c: &Const) -> Option<bool> {
    match c {
        Const::Bool(b) => Some(*b),
        Const::Null | Const::Undefined => Some(false),
        Const::Int8(v) => Some(*v != 0),
        Const::Int32(v) => Some(*v != 0),
        Const::Int64(v) => Some(*v != 0),
        Const::UInt64(v) => Some(*v != 0),
        Const::Float32(bits) => {
            let n = f32::from_bits(*bits);
            Some(n != 0.0 && !n.is_nan())
        }
        Const::Number(bits) => {
            let n = f64::from_bits(*bits);
            Some(n != 0.0 && !n.is_nan())
        }
        Const::String(sym) => sym_table.resolve(*sym).map(|s| !s.is_empty()),
        Const::BigInt(sym) => sym_table.as_str(*sym).and_then(bigint_str_is_truthy),
        Const::ArrayLiteral(_)
        | Const::TypedArrayLiteral { .. }
        | Const::ObjectLiteral { .. }
        | Const::MethodRef { .. } => Some(true),
        Const::Hole
        | Const::Accessor(_)
        | Const::MethodAffiliate(_)
        | Const::BuiltinTypeIndex(_)
        | Const::EtsImplements(_)
        | Const::LitNull(_)
        | Const::LiteralBufferRef(_) => None,
    }
}

/// Whether `val` (tracing bounded `Op::Mov` chains iteratively) is defined by
/// an instruction that unconditionally produces a non-null ECMAScript object,
/// array, closure, or `RegExp` (`ToBoolean == true`).
#[must_use]
pub fn value_known_truthy_alloc(module: &Module, val: ValueId) -> bool {
    let mut cur = val;
    let bound = module.values.len().min(32);
    for _ in 0..=bound {
        let Some(v) = module.value(cur) else {
            return false;
        };
        match v.def {
            ValueDef::Const(cid) => {
                return matches!(
                    module.consts.get(cid),
                    Some(
                        Const::ArrayLiteral(_)
                            | Const::TypedArrayLiteral { .. }
                            | Const::ObjectLiteral { .. }
                            | Const::MethodRef { .. }
                    )
                );
            }
            ValueDef::Inst(iid) => {
                let Some(inst) = module.inst(iid) else {
                    return false;
                };
                match &inst.op {
                    Op::Mov { src } => {
                        if *src == cur {
                            return false;
                        }
                        cur = *src;
                    }
                    Op::AllocObject { .. }
                    | Op::AllocArray { .. }
                    | Op::AllocClosure { .. }
                    | Op::AllocRegExp { .. }
                    | Op::CreateIterResultObj { .. } => return true,
                    _ => return false,
                }
            }
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return false,
        }
    }
    false
}

/// Unified ECMA-262 `ToBoolean` query combining known scalar/shape constants
/// with allocation-site truthiness (`AllocObject` / `AllocArray` /
/// `AllocClosure` / `AllocRegExp`).
#[must_use]
pub fn eval_truthiness(
    module: &Module,
    operand: ValueId,
    known_const: Option<&Const>,
) -> Option<bool> {
    if let Some(c) = known_const
        && let Some(b) = const_to_boolean(&module.sym, c)
    {
        return Some(b);
    }
    if value_known_truthy_alloc(module, operand) {
        return Some(true);
    }
    None
}

/// Evaluate an [`Op::BinaryOp`] over constant inputs, honoring ArkCompiler's
/// `vreg OP acc` (`right_vreg OP left_acc`, `N36`) evaluation order, `-0.0`
/// bit preservation (`N37`), canonical `NaN` bits (`#60`), `ecma_pow` (`**`,
/// `ADR-19`), and `ToInt32`/`ToUint32` modular wrapping (`N42`).
#[must_use]
pub fn eval_binary_op(op: BinOp, left_acc: &Const, right_vreg: &Const) -> Option<Const> {
    let a = const_to_number(right_vreg)?;
    let b = const_to_number(left_acc)?;
    let res = match op {
        BinOp::Add => a + b,
        BinOp::Sub => a - b,
        BinOp::Mul => a * b,
        BinOp::Div => a / b,
        BinOp::Mod => a % b,
        BinOp::Exp => ecma_pow(a, b),
        BinOp::Shl => f64::from(to_int32(a) << (to_uint32(b) & 0x1f)),
        BinOp::Shr => f64::from((to_int32(a) as u32) >> (to_uint32(b) & 0x1f)),
        BinOp::Ashr => f64::from(to_int32(a) >> (to_uint32(b) & 0x1f)),
        BinOp::BitAnd => f64::from(to_int32(a) & to_int32(b)),
        BinOp::BitOr => f64::from(to_int32(a) | to_int32(b)),
        BinOp::BitXor => f64::from(to_int32(a) ^ to_int32(b)),
    };
    Some(canonical_number_const(res))
}

#[derive(Clone, Copy)]
enum JsPrimVal {
    Undefined,
    Null,
    Bool(bool),
    Number(f64),
    String(Sym),
    BigInt(Sym),
}

fn classify_js_prim(sym_table: &SymbolTable, c: &Const) -> Option<JsPrimVal> {
    match c {
        Const::Undefined => Some(JsPrimVal::Undefined),
        Const::Null => Some(JsPrimVal::Null),
        Const::Bool(b) => Some(JsPrimVal::Bool(*b)),
        Const::Number(bits) => Some(JsPrimVal::Number(f64::from_bits(*bits))),
        Const::Float32(bits) => Some(JsPrimVal::Number(f64::from(f32::from_bits(*bits)))),
        Const::Int8(v) => Some(JsPrimVal::Number(f64::from(*v))),
        Const::Int32(v) => Some(JsPrimVal::Number(f64::from(*v as i32))),
        Const::String(s) if sym_table.resolve(*s).is_some() => Some(JsPrimVal::String(*s)),
        Const::BigInt(s) if sym_table.as_str(*s).is_some() => Some(JsPrimVal::BigInt(*s)),
        _ => None,
    }
}

fn strings_equal(sym_table: &SymbolTable, a: Sym, b: Sym) -> Option<bool> {
    if a == b {
        return sym_table.resolve(a).map(|_| true);
    }
    Some(sym_table.utf16_units(a)? == sym_table.utf16_units(b)?)
}

/// ECMA-262 §7.2.16 `IsStrictlyEqual(x, y)` (`N40`).
fn eval_strict_eq(sym_table: &SymbolTable, a: &Const, b: &Const) -> Option<bool> {
    let va = classify_js_prim(sym_table, a)?;
    let vb = classify_js_prim(sym_table, b)?;
    match (va, vb) {
        (JsPrimVal::Undefined, JsPrimVal::Undefined) | (JsPrimVal::Null, JsPrimVal::Null) => {
            Some(true)
        }
        (JsPrimVal::Bool(x), JsPrimVal::Bool(y)) => Some(x == y),
        // N40: IEEE-754 `==` (`+0.0 === -0.0` is `true`, `NaN === NaN` is `false`).
        (JsPrimVal::Number(x), JsPrimVal::Number(y)) => Some(x == y),
        (JsPrimVal::String(sx), JsPrimVal::String(sy)) => strings_equal(sym_table, sx, sy),
        (JsPrimVal::BigInt(bx), JsPrimVal::BigInt(by)) => {
            if bx == by {
                return Some(true);
            }
            let sa = sym_table.as_str(bx)?;
            let sb = sym_table.as_str(by)?;
            Some(normalize_decimal_bigint(sa)? == normalize_decimal_bigint(sb)?)
        }
        // Distinct JS primitive types are never strictly equal.
        _ => Some(false),
    }
}

/// Evaluate an [`Op::Compare`] over constant inputs, honoring ArkCompiler's
/// `vreg CMP acc` (`right_vreg CMP left_acc`, `N36`) order, IEEE-754 `===`/`!==`
/// (`N40`), and the nullish loose-equality non-coercion rule (`N38(iii)` / `N41`).
#[must_use]
pub fn eval_compare_op(
    sym_table: &SymbolTable,
    op: CmpOp,
    left_acc: &Const,
    right_vreg: &Const,
) -> Option<Const> {
    let lhs = right_vreg;
    let rhs = left_acc;
    match op {
        CmpOp::StrictEq => eval_strict_eq(sym_table, lhs, rhs).map(Const::Bool),
        CmpOp::StrictNotEq => eval_strict_eq(sym_table, lhs, rhs).map(|eq| Const::Bool(!eq)),
        CmpOp::Eq | CmpOp::NotEq => {
            // N38(iii) / N41: never ToNumber-coerce nullish operands in loose `==` / `!=`.
            if matches!(lhs, Const::Null | Const::Undefined | Const::LitNull(_))
                || matches!(rhs, Const::Null | Const::Undefined | Const::LitNull(_))
            {
                return None;
            }
            if let (Const::String(sa), Const::String(sb)) = (lhs, rhs) {
                let eq = strings_equal(sym_table, *sa, *sb)?;
                return Some(Const::Bool(if op == CmpOp::Eq { eq } else { !eq }));
            }
            let a = const_to_number(lhs)?;
            let b = const_to_number(rhs)?;
            Some(Const::Bool(if op == CmpOp::Eq { a == b } else { a != b }))
        }
        CmpOp::Less => Some(Const::Bool(const_to_number(lhs)? < const_to_number(rhs)?)),
        CmpOp::LessEq => Some(Const::Bool(const_to_number(lhs)? <= const_to_number(rhs)?)),
        CmpOp::Greater => Some(Const::Bool(const_to_number(lhs)? > const_to_number(rhs)?)),
        CmpOp::GreaterEq => Some(Const::Bool(const_to_number(lhs)? >= const_to_number(rhs)?)),
        CmpOp::In | CmpOp::InstanceOf => None,
    }
}

/// ArkCompiler raw `jeqz` predicate (`#61` `R3-X1`): `true` iff `false` or
/// numeric `±0` (`NaN`, nullish, strings, bigints, and objects are `false`).
#[must_use]
pub fn eval_jump_eqz(c: &Const) -> Option<bool> {
    match c {
        Const::Bool(b) => Some(!*b),
        Const::Int8(v) => Some(*v == 0),
        Const::Int32(v) => Some(*v == 0),
        Const::Float32(bits) => Some(f32::from_bits(*bits) == 0.0),
        Const::Number(bits) => Some(f64::from_bits(*bits) == 0.0),
        Const::Null
        | Const::Undefined
        | Const::String(_)
        | Const::BigInt(_)
        | Const::ArrayLiteral(_)
        | Const::TypedArrayLiteral { .. }
        | Const::ObjectLiteral { .. }
        | Const::MethodRef { .. } => Some(false),
        _ => None,
    }
}

/// ArkCompiler raw `jnez` predicate (`#61` `R3-X1`): `true` iff `true` or
/// numeric `!= 0` (**`true` for `NaN`**; nullish, strings, bigints, and objects
/// are `false`).
#[must_use]
pub fn eval_jump_nez(c: &Const) -> Option<bool> {
    match c {
        Const::Bool(b) => Some(*b),
        Const::Int8(v) => Some(*v != 0),
        Const::Int32(v) => Some(*v != 0),
        Const::Float32(bits) => Some(f32::from_bits(*bits) != 0.0),
        Const::Number(bits) => Some(f64::from_bits(*bits) != 0.0),
        Const::Null
        | Const::Undefined
        | Const::String(_)
        | Const::BigInt(_)
        | Const::ArrayLiteral(_)
        | Const::TypedArrayLiteral { .. }
        | Const::ObjectLiteral { .. }
        | Const::MethodRef { .. } => Some(false),
        _ => None,
    }
}

/// Evaluate an [`Op::UnaryOp`] over a constant or known-truthy allocation
/// input (`N37`, `N39`, `N42`, `#60`, `#61`).
#[must_use]
pub fn eval_unary_op(
    module: &Module,
    op: UnOp,
    operand: ValueId,
    known_const: Option<&Const>,
) -> Option<Const> {
    match op {
        UnOp::Minus => {
            let n = const_to_number(known_const?)?;
            Some(canonical_number_const(-n))
        }
        UnOp::BitNot => {
            let n = const_to_number(known_const?)?;
            Some(canonical_number_const(f64::from(!to_int32(n))))
        }
        UnOp::ToNumber | UnOp::ToNumeric => {
            let n = const_to_number(known_const?)?;
            Some(canonical_number_const(n))
        }
        UnOp::LogicalNot => eval_truthiness(module, operand, known_const).map(|b| Const::Bool(!b)),
        UnOp::IsTrue => eval_truthiness(module, operand, known_const).map(Const::Bool),
        UnOp::IsFalse => eval_truthiness(module, operand, known_const).map(|b| Const::Bool(!b)),
        UnOp::JumpEqz => {
            if let Some(c) = known_const {
                eval_jump_eqz(c).map(Const::Bool)
            } else if value_known_truthy_alloc(module, operand) {
                Some(Const::Bool(false))
            } else {
                None
            }
        }
        UnOp::JumpNez => {
            if let Some(c) = known_const {
                eval_jump_nez(c).map(Const::Bool)
            } else if value_known_truthy_alloc(module, operand) {
                Some(Const::Bool(false))
            } else {
                None
            }
        }
        UnOp::ToPropertyKey => match known_const? {
            Const::String(sym) if module.sym.resolve(*sym).is_some() => Some(Const::String(*sym)),
            _ => None,
        },
        UnOp::Void => {
            if known_const.is_some_and(is_sccp_lattice_const)
                || value_known_truthy_alloc(module, operand)
            {
                Some(Const::Undefined)
            } else {
                None
            }
        }
        UnOp::Inc | UnOp::Dec | UnOp::TypeOf => None,
    }
}

// ─── Shared Branch-Folding & SSA Utility Helpers ─────────────────────────────

/// Return the leading [`Op::Phi`] instruction IDs of `bb`.
#[must_use]
pub(crate) fn block_phis(module: &Module, bb: BlockId) -> Vec<InstId> {
    module
        .block(bb)
        .map(|b| {
            b.insts
                .iter()
                .copied()
                .take_while(|&id| module.inst(id).is_some_and(|i| i.op.is_phi()))
                .collect()
        })
        .unwrap_or_default()
}

/// Rewrite a block-ending [`Op::CondBranch`] (`term_iid` in `bb`) to
/// `Op::Branch { dest: target }` while keeping predecessor lists and leading
/// [`Op::Phi`] incoming entries verifier-clean (`N23` / `N27`):
///
/// - When `dead != target`: removes `Edge { from: bb, kind: EdgeKind::Normal }`
///   from `dead.preds` and from every leading `Op::Phi` in `dead`.
/// - When `dead == target` (`CondBranch(c, t, t)`): deduplicates any repeated
///   `Edge { from: bb, kind: EdgeKind::Normal }` entry on `target.preds` and on
///   `target`'s leading `Op::Phi`s so `preds` and `Phi` arities stay 1-to-1.
///
/// If `cond` was produced by an instruction with observable effects (such as a
/// throwing call or getter load), that producer instruction remains intact in
/// `bb` ahead of `Branch { dest: target }`, and `Adce` preserves it via
/// `Effects::is_removable_if_unused()`.
pub(crate) fn fold_cond_branch_to_jump(
    module: &mut Module,
    bb: BlockId,
    term_iid: InstId,
    target: BlockId,
    dead: BlockId,
) -> bool {
    let Some(inst) = module.inst_mut(term_iid) else {
        return false;
    };
    inst.op = Op::Branch { dest: target };
    let norm_edge = Edge {
        from: bb,
        kind: EdgeKind::Normal,
    };
    if dead != target {
        if let Some(dead_block) = module.block_mut(dead) {
            dead_block.preds.retain(|e| *e != norm_edge);
        }
        for phi_id in block_phis(module, dead) {
            if let Some(phi_inst) = module.inst_mut(phi_id)
                && let Op::Phi { entries } = &mut phi_inst.op
            {
                entries.retain(|(edge, _)| *edge != norm_edge);
            }
        }
    } else {
        if let Some(target_block) = module.block_mut(target) {
            let mut seen_norm = false;
            target_block.preds.retain(|e| {
                if *e == norm_edge {
                    if seen_norm {
                        return false;
                    }
                    seen_norm = true;
                }
                true
            });
        }
        for phi_id in block_phis(module, target) {
            if let Some(phi_inst) = module.inst_mut(phi_id)
                && let Op::Phi { entries } = &mut phi_inst.op
            {
                let mut seen_norm = false;
                entries.retain(|(edge, _)| {
                    if *edge == norm_edge {
                        if seen_norm {
                            return false;
                        }
                        seen_norm = true;
                    }
                    true
                });
            }
        }
    }
    true
}

/// Follow a chain in `replacements` (`a -> b -> c`), bounded by map length so a
/// degenerate self or mutual cycle never loops infinitely.
#[must_use]
#[inline]
pub(crate) fn resolve_subst(replacements: &HashMap<ValueId, ValueId>, mut v: ValueId) -> ValueId {
    for _ in 0..=replacements.len() {
        match replacements.get(&v) {
            Some(&next) if next != v => v = next,
            _ => break,
        }
    }
    v
}

/// Apply a batch of value substitutions across `func_id` in a single pass via
/// [`Op::for_each_operand_mut`], resolving transitive chains first.
pub(crate) fn replace_uses_map_in_func(
    module: &mut Module,
    func_id: FuncId,
    replacements: &HashMap<ValueId, ValueId>,
) -> usize {
    if replacements.is_empty() {
        return 0;
    }
    let Some(func) = module.func(func_id) else {
        return 0;
    };
    let num_blocks = func.blocks.len();
    let mut count = 0;
    for bi in 0..num_blocks {
        let Some(bb) = module.func(func_id).and_then(|f| f.blocks.get(bi).copied()) else {
            break;
        };
        let inst_len = module.block(bb).map_or(0, |b| b.insts.len());
        for ii in 0..inst_len {
            let Some(inst_id) = module.block(bb).and_then(|b| b.insts.get(ii).copied()) else {
                break;
            };
            let Some(inst) = module.inst_mut(inst_id) else {
                continue;
            };
            inst.op.for_each_operand_mut(|v| {
                let target = resolve_subst(replacements, *v);
                if target != *v {
                    *v = target;
                    count += 1;
                }
            });
        }
    }
    count
}

/// Prune dead or out-of-function [`InstId`] references from `func_id`'s
/// [`abcd_ir::DebugData`] (`line_table`, `column_table`, and `local_names`
/// [`LocalScope`] extents) so [`abcd_ir::verify_module`]'s
/// `DebugInstNotInFunc` / `InstOutOfArena` invariants hold after instruction or
/// block removal (`N20`).
pub(crate) fn prune_func_debug_data(module: &mut Module, func_id: FuncId) -> bool {
    let has_debug = module
        .func(func_id)
        .and_then(|f| f.debug.as_ref())
        .is_some_and(|dbg| {
            !dbg.line_table.is_empty()
                || !dbg.column_table.is_empty()
                || dbg.local_names.iter().any(|ln| ln.scope.is_some())
        });
    if !has_debug {
        return false;
    }

    let blocks: Vec<BlockId> = module
        .func(func_id)
        .map(|f| f.blocks.clone())
        .unwrap_or_default();
    let mut live_set: HashSet<InstId> = HashSet::new();
    let mut sorted_live: Vec<InstId> = Vec::new();
    for bb in blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &iid in &block.insts {
            if module.inst(iid).is_some() && live_set.insert(iid) {
                sorted_live.push(iid);
            }
        }
    }
    sorted_live.sort_unstable_by_key(|id| id.index());

    let Some(dbg) = module.func_mut(func_id).and_then(|f| f.debug.as_mut()) else {
        return false;
    };
    let mut changed = false;

    let old_lines = dbg.line_table.len();
    dbg.line_table
        .retain(|entry| live_set.contains(&entry.inst));
    if dbg.line_table.len() != old_lines {
        changed = true;
    }

    let old_cols = dbg.column_table.len();
    dbg.column_table
        .retain(|entry| live_set.contains(&entry.inst));
    if dbg.column_table.len() != old_cols {
        changed = true;
    }

    for ln in &mut dbg.local_names {
        let Some(scope) = ln.scope else {
            continue;
        };
        if live_set.contains(&scope.start) && live_set.contains(&scope.end) {
            continue;
        }
        let s_idx = sorted_live.partition_point(|&id| id < scope.start);
        let e_idx = sorted_live.partition_point(|&id| id <= scope.end);
        let new_scope = if s_idx < e_idx {
            let start = sorted_live[s_idx];
            let end = sorted_live[e_idx - 1];
            (start.index() <= end.index()).then_some(LocalScope { start, end })
        } else {
            None
        };
        if new_scope != ln.scope {
            ln.scope = new_scope;
            changed = true;
        }
    }

    changed
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn to_boolean_covers_all_scalar_and_shape_variants() {
        let mut sym = SymbolTable::new();
        let empty = sym.intern("");
        let nonempty = sym.intern("abc");
        let zero_big = sym.intern("0");
        let neg_zero_big = sym.intern("-0");
        let nz_big = sym.intern("123456789012345678901234567890");

        assert_eq!(const_to_boolean(&sym, &Const::Bool(true)), Some(true));
        assert_eq!(const_to_boolean(&sym, &Const::Bool(false)), Some(false));
        assert_eq!(const_to_boolean(&sym, &Const::Null), Some(false));
        assert_eq!(const_to_boolean(&sym, &Const::Undefined), Some(false));
        assert_eq!(const_to_boolean(&sym, &Const::Hole), None);

        assert_eq!(const_to_boolean(&sym, &Const::Int8(0)), Some(false));
        assert_eq!(const_to_boolean(&sym, &Const::Int8(1)), Some(true));
        assert_eq!(const_to_boolean(&sym, &Const::Int32(0)), Some(false));
        assert_eq!(const_to_boolean(&sym, &Const::Int32(42)), Some(true));
        assert_eq!(const_to_boolean(&sym, &Const::Int64(0)), Some(false));
        assert_eq!(const_to_boolean(&sym, &Const::Int64(-1)), Some(true));
        assert_eq!(const_to_boolean(&sym, &Const::UInt64(0)), Some(false));
        assert_eq!(const_to_boolean(&sym, &Const::UInt64(9)), Some(true));

        assert_eq!(const_to_boolean(&sym, &Const::float32(0.0)), Some(false));
        assert_eq!(const_to_boolean(&sym, &Const::float32(-0.0)), Some(false));
        assert_eq!(
            const_to_boolean(&sym, &Const::float32(f32::NAN)),
            Some(false)
        );
        assert_eq!(const_to_boolean(&sym, &Const::float32(1.5)), Some(true));

        assert_eq!(const_to_boolean(&sym, &Const::number(0.0)), Some(false));
        assert_eq!(const_to_boolean(&sym, &Const::number(-0.0)), Some(false));
        assert_eq!(
            const_to_boolean(&sym, &Const::number(f64::NAN)),
            Some(false)
        );
        assert_eq!(const_to_boolean(&sym, &Const::number(-2.5)), Some(true));

        assert_eq!(const_to_boolean(&sym, &Const::String(empty)), Some(false));
        assert_eq!(const_to_boolean(&sym, &Const::String(nonempty)), Some(true));
        assert_eq!(
            const_to_boolean(&sym, &Const::BigInt(zero_big)),
            Some(false)
        );
        assert_eq!(
            const_to_boolean(&sym, &Const::BigInt(neg_zero_big)),
            Some(false)
        );
        assert_eq!(const_to_boolean(&sym, &Const::BigInt(nz_big)), Some(true));

        assert_eq!(
            const_to_boolean(&sym, &Const::ArrayLiteral(Vec::new())),
            Some(true)
        );
        assert_eq!(
            const_to_boolean(
                &sym,
                &Const::ObjectLiteral {
                    keys: Vec::new(),
                    values: Vec::new()
                }
            ),
            Some(true)
        );
        assert_eq!(
            const_to_boolean(&sym, &Const::method_ref(FuncId::new(0))),
            Some(true)
        );
    }
}
