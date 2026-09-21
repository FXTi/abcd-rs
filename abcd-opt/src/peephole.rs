//! Peephole optimization: constant folding and identity elimination
//! (v0.1 `opt::peephole`, ported to the v0.2 op taxonomy).
//!
//! v0.2 port notes:
//!
//! - v0.1's comparisons lived in `InstData::BinaryOp`; v0.2 splits them
//!   into [`Op::Compare`] ([`CmpOp`]). The fold rules are unchanged.
//! - v0.1's `IsTrue`/`IsFalse` instructions are [`UnOp::IsTrue`]/
//!   [`UnOp::IsFalse`] in v0.2.
//! - Folded results become [`Op::LoadConst`] of a freshly pooled
//!   [`Const`] (append-only pool; the instruction keeps its result value,
//!   so no use rewrites are needed).
//! - Constants are read from BOTH constant-carrying definitions:
//!   [`Op::LoadConst`] instructions and [`ValueDef::Const`] values
//!   (v0.2's frame-initial values are const-defined, not seeded
//!   instructions — a constant is a constant).

use abcd_ir2::{BinOp, BlockId, CmpOp, Const, FuncId, InstId, Module, Op, UnOp, ValueDef, ValueId};

use crate::FuncPass;
use crate::{to_int32, to_uint32};

/// The peephole pass: constant folding over local instruction patterns.
pub struct Peephole;

impl FuncPass for Peephole {
    fn run(&self, module: &mut Module, func: FuncId) -> bool {
        let mut changed = false;
        let Some(func_data) = module.func(func) else {
            return false;
        };
        let blocks: Vec<BlockId> = func_data.blocks.clone();

        for bb in blocks {
            let Some(block) = module.block(bb) else {
                continue;
            };
            let insts: Vec<InstId> = block.insts.clone();
            for inst_id in insts {
                if let Some(folded) = try_fold(module, inst_id) {
                    let cid = module.consts.push(folded);
                    if let Some(inst) = module.inst_mut(inst_id) {
                        inst.op = Op::LoadConst(cid);
                        changed = true;
                    }
                }
            }
        }
        changed
    }
}

/// Try to fold an instruction into a constant. The caller pools the
/// returned [`Const`] and rewrites the instruction to [`Op::LoadConst`]
/// (the pool is append-only, so this never disturbs other ids).
fn try_fold(module: &Module, inst_id: InstId) -> Option<Const> {
    let inst = module.inst(inst_id)?;
    let op = &inst.op;
    match op {
        // BinaryOp(op, Lit(a), Lit(b)) → Lit(eval(op, a, b)).
        //
        // Operand order (N36): the IR convention is `left` = acc
        // operand, `right` = register operand (lift `binary_op`), while
        // every vendored `*2` handler computes `vreg OP acc` (e.g. div2
        // interpreter_assembly.cpp:1095-1096: `left = GET_VREG_VALUE(v0);
        // right = acc`). The true semantic is therefore `right OP left`
        // in IR field terms — evaluate a = right, b = left.
        Op::BinaryOp { op, left, right } => {
            let a = as_number(module, *right)?;
            let b = as_number(module, *left)?;
            let result = eval_binop(*op, a, b)?;
            Some(Const::number(result))
        }

        // Compare(op, Lit(a), Lit(b)) → Bool constant.
        Op::Compare { op, left, right } => try_fold_comparison(*op, module, *left, *right),

        // UnOp(Minus, Lit(n)) → Lit(-n) — bit-exact: -0.0 folds to -0.0
        // and NaN payloads propagate (N37; Const::Number stores raw bits).
        Op::UnaryOp {
            op: UnOp::Minus,
            operand,
        } => {
            let n = as_number(module, *operand)?;
            Some(Const::number(-n))
        }

        // UnOp(BitNot, Lit(n)) → Lit(~ToInt32(n)) — wrap, not saturate (N42).
        Op::UnaryOp {
            op: UnOp::BitNot,
            operand,
        } => {
            let n = as_number(module, *operand)?;
            Some(Const::number(!to_int32(n) as f64))
        }

        // UnOp(LogicalNot, Lit(b)) → Lit(!b) (the BOOLEAN not — N39:
        // vendor `not` is BitNot, lifted distinctly).
        Op::UnaryOp {
            op: UnOp::LogicalNot,
            operand,
        } => {
            let b = as_bool(module, *operand)?;
            Some(Const::Bool(!b))
        }

        // IsTrue(Lit(b)) → Lit(b)
        Op::UnaryOp {
            op: UnOp::IsTrue,
            operand,
        } => {
            let b = as_bool(module, *operand)?;
            Some(Const::Bool(b))
        }

        // IsFalse(Lit(b)) → Lit(!b)
        Op::UnaryOp {
            op: UnOp::IsFalse,
            operand,
        } => {
            let b = as_bool(module, *operand)?;
            Some(Const::Bool(!b))
        }

        _ => None,
    }
}

/// Try to fold a comparison with constant operands into a Bool constant.
///
/// Operand order (N36): `left` is the acc operand, `right` the register
/// operand, and the vendored handlers compute `vreg CMP acc` (e.g. less
/// interpreter_assembly.cpp:1188-1189: `left = GET_VREG_VALUE(v0);
/// right = GET_ACC()`), so `a` is extracted from `right` and `b` from
/// `left`. (For the symmetric Eq/NotEq/StrictEq/StrictNotEq the order is
/// immaterial but kept uniform.)
fn try_fold_comparison(op: CmpOp, module: &Module, left: ValueId, right: ValueId) -> Option<Const> {
    match op {
        CmpOp::Eq => {
            let a = as_number(module, right)?;
            let b = as_number(module, left)?;
            Some(Const::Bool(a == b))
        }
        CmpOp::NotEq => {
            let a = as_number(module, right)?;
            let b = as_number(module, left)?;
            Some(Const::Bool(a != b))
        }
        CmpOp::StrictEq => {
            // StrictEq requires same type — only fold when both are numbers or both are bools.
            // N40: JS strict equality on numbers is plain ==, NOT a bit
            // comparison: `0 === -0` is true and `NaN === NaN` is false.
            if let (Some(a), Some(b)) = (
                as_number_strict(module, left),
                as_number_strict(module, right),
            ) {
                return Some(Const::Bool(a == b));
            }
            if let (Some(a), Some(b)) =
                (as_bool_strict(module, left), as_bool_strict(module, right))
            {
                return Some(Const::Bool(a == b));
            }
            None
        }
        CmpOp::StrictNotEq => {
            if let (Some(a), Some(b)) = (
                as_number_strict(module, left),
                as_number_strict(module, right),
            ) {
                return Some(Const::Bool(a != b));
            }
            if let (Some(a), Some(b)) =
                (as_bool_strict(module, left), as_bool_strict(module, right))
            {
                return Some(Const::Bool(a != b));
            }
            None
        }
        CmpOp::Less => {
            let a = as_number(module, right)?;
            let b = as_number(module, left)?;
            Some(Const::Bool(a < b))
        }
        CmpOp::LessEq => {
            let a = as_number(module, right)?;
            let b = as_number(module, left)?;
            Some(Const::Bool(a <= b))
        }
        CmpOp::Greater => {
            let a = as_number(module, right)?;
            let b = as_number(module, left)?;
            Some(Const::Bool(a > b))
        }
        CmpOp::GreaterEq => {
            let a = as_number(module, right)?;
            let b = as_number(module, left)?;
            Some(Const::Bool(a >= b))
        }
        // In / InstanceOf cannot be folded at compile time.
        _ => None,
    }
}

/// The constant a value carries, from either constant-carrying
/// definition form ([`Op::LoadConst`] instruction or
/// [`ValueDef::Const`]).
fn const_of(module: &Module, val: ValueId) -> Option<Const> {
    let cid = match module.value(val)?.def {
        ValueDef::Const(c) => c,
        ValueDef::Inst(inst) => match &module.inst(inst)?.op {
            Op::LoadConst(c) => *c,
            _ => return None,
        },
        _ => return None,
    };
    module.consts.get(cid).cloned()
}

/// Extract a constant number only if the value is a Number constant.
/// (Does not coerce bools/null — used for strict equality checks.)
fn as_number_strict(module: &Module, val: ValueId) -> Option<f64> {
    match const_of(module, val)? {
        Const::Number(bits) => Some(f64::from_bits(bits)),
        _ => None,
    }
}

/// Extract a constant bool only if the value is a Bool constant.
fn as_bool_strict(module: &Module, val: ValueId) -> Option<bool> {
    match const_of(module, val)? {
        Const::Bool(b) => Some(b),
        _ => None,
    }
}

/// Try to extract a constant number from a value.
///
/// N41: `Const::Null` is NOT coerced to 0.0 here — doing so folded
/// `null == 0` to true where JS loose equality says false (null equals
/// only null/undefined), and folded null arithmetic through a zero the
/// program never computes. (ToNumber(null) IS 0 for the arithmetic
/// slow path, but a compile-time fold through coercion was proven
/// unsound by P3-T19 — no eq-nullish fold lives in peephole.)
fn as_number(module: &Module, val: ValueId) -> Option<f64> {
    match const_of(module, val)? {
        Const::Number(bits) => Some(f64::from_bits(bits)),
        Const::Bool(true) => Some(1.0),
        Const::Bool(false) => Some(0.0),
        _ => None,
    }
}

/// Try to extract a constant bool (truthiness) from a value.
fn as_bool(module: &Module, val: ValueId) -> Option<bool> {
    match const_of(module, val)? {
        Const::Bool(b) => Some(b),
        Const::Number(bits) => {
            let n = f64::from_bits(bits);
            Some(n != 0.0 && !n.is_nan())
        }
        Const::Null | Const::Undefined => Some(false),
        Const::String(s) => Some(!module.sym.resolve(s).unwrap_or("").is_empty()),
        _ => None,
    }
}

/// Evaluate a binary operation on two constant numbers.
fn eval_binop(op: BinOp, a: f64, b: f64) -> Option<f64> {
    Some(match op {
        BinOp::Add => a + b,
        BinOp::Sub => a - b,
        BinOp::Mul => a * b,
        BinOp::Div => a / b,
        BinOp::Mod => a % b,
        BinOp::Exp => a.powf(b),
        // Bitwise/shift operands convert with ECMA-262 ToInt32/ToUint32
        // (N42): WRAP mod 2^32 with NaN/±Infinity → 0, NOT Rust's
        // saturating `as` casts — matches vendored DoubleToInt
        // (number_helper.cpp:1137). The shift count is masked `& 0x1f`
        // AFTER the wrap (vendored HandleShl2Imm8V8:
        // `static_cast<uint32_t>(opNumber1) & 0x1f`), so -1 shifts by 31.
        BinOp::Shl => (to_int32(a) << (to_uint32(b) & 0x1f)) as f64,
        // JS `>>>`: vendored shr2 is the LOGICAL (unsigned) shift
        // (interpreter_assembly.cpp HandleShr2Imm8V8: (uint32)ToInt32(v)
        // >> shift — the unsigned reinterpret goes through i32; a direct
        // `as u32` float cast would saturate negatives to 0).
        BinOp::Shr => ((to_int32(a) as u32) >> (to_uint32(b) & 0x1f)) as f64,
        // JS `>>`: vendored ashr2 is the ARITHMETIC (signed) shift
        // (HandleAshr2Imm8V8: int32 >> shift). The two arms were inverted.
        BinOp::Ashr => (to_int32(a) >> (to_uint32(b) & 0x1f)) as f64,
        BinOp::BitAnd => (to_int32(a) & to_int32(b)) as f64,
        BinOp::BitOr => (to_int32(a) | to_int32(b)) as f64,
        BinOp::BitXor => (to_int32(a) ^ to_int32(b)) as f64,
    })
}
