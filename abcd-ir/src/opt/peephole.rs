//! Peephole optimization: constant folding and identity elimination.

use crate::entity::{Block, FuncId, Inst, Value};
use crate::inst::{BinOp, InstData, UnOp};
use crate::module::Module;

use super::FuncPass;

pub struct Peephole;

impl FuncPass for Peephole {
    fn run(&self, module: &mut Module, func: FuncId) -> bool {
        let mut changed = false;
        let blocks: Vec<Block> = module.func(func).blocks.clone();

        for bb in blocks {
            let insts: Vec<Inst> = module.block(bb).insts.clone();
            for inst_id in insts {
                if let Some(replacement) = try_fold(module, inst_id) {
                    module.inst_mut(inst_id).data = replacement;
                    changed = true;
                }
            }
        }
        changed
    }
}

/// Try to fold an instruction into a simpler form.
fn try_fold(module: &Module, inst_id: Inst) -> Option<InstData> {
    let data = &module.inst(inst_id).data;
    match data {
        // BinOp(op, Lit(a), Lit(b)) → Lit(eval(op, a, b))
        InstData::BinaryOp { op, left, right } => {
            // Comparison ops → LiteralBool
            if let Some(result) = try_fold_comparison(*op, module, *left, *right) {
                return Some(result);
            }
            // Arithmetic ops → LiteralNumber
            let a = as_number(module, *left)?;
            let b = as_number(module, *right)?;
            let result = eval_binop(*op, a, b)?;
            Some(InstData::LiteralNumber(result))
        }

        // UnOp(Minus, Lit(n)) → Lit(-n)
        InstData::UnaryOp {
            op: UnOp::Minus,
            operand,
        } => {
            let n = as_number(module, *operand)?;
            Some(InstData::LiteralNumber(-n))
        }

        // UnOp(BitNot, Lit(n)) → Lit(~n)
        InstData::UnaryOp {
            op: UnOp::BitNot,
            operand,
        } => {
            let n = as_number(module, *operand)?;
            Some(InstData::LiteralNumber(!(n as i32) as f64))
        }

        // UnOp(LogicalNot, Lit(b)) → Lit(!b)
        InstData::UnaryOp {
            op: UnOp::LogicalNot,
            operand,
        } => {
            let b = as_bool(module, *operand)?;
            Some(InstData::LiteralBool(!b))
        }

        // IsTrue(Lit(b)) → Lit(b)
        InstData::IsTrue { operand } => {
            let b = as_bool(module, *operand)?;
            Some(InstData::LiteralBool(b))
        }

        // IsFalse(Lit(b)) → Lit(!b)
        InstData::IsFalse { operand } => {
            let b = as_bool(module, *operand)?;
            Some(InstData::LiteralBool(!b))
        }

        _ => None,
    }
}

/// Try to fold a comparison BinOp with constant operands into LiteralBool.
fn try_fold_comparison(op: BinOp, module: &Module, left: Value, right: Value) -> Option<InstData> {
    match op {
        BinOp::Eq => {
            let a = as_number(module, left)?;
            let b = as_number(module, right)?;
            Some(InstData::LiteralBool(a == b))
        }
        BinOp::NotEq => {
            let a = as_number(module, left)?;
            let b = as_number(module, right)?;
            Some(InstData::LiteralBool(a != b))
        }
        BinOp::StrictEq => {
            // StrictEq requires same type — only fold when both are numbers or both are bools.
            if let (Some(a), Some(b)) = (
                as_number_strict(module, left),
                as_number_strict(module, right),
            ) {
                return Some(InstData::LiteralBool(a.to_bits() == b.to_bits()));
            }
            if let (Some(a), Some(b)) =
                (as_bool_strict(module, left), as_bool_strict(module, right))
            {
                return Some(InstData::LiteralBool(a == b));
            }
            None
        }
        BinOp::StrictNotEq => {
            if let (Some(a), Some(b)) = (
                as_number_strict(module, left),
                as_number_strict(module, right),
            ) {
                return Some(InstData::LiteralBool(a.to_bits() != b.to_bits()));
            }
            if let (Some(a), Some(b)) =
                (as_bool_strict(module, left), as_bool_strict(module, right))
            {
                return Some(InstData::LiteralBool(a != b));
            }
            None
        }
        BinOp::Less => {
            let a = as_number(module, left)?;
            let b = as_number(module, right)?;
            Some(InstData::LiteralBool(a < b))
        }
        BinOp::LessEq => {
            let a = as_number(module, left)?;
            let b = as_number(module, right)?;
            Some(InstData::LiteralBool(a <= b))
        }
        BinOp::Greater => {
            let a = as_number(module, left)?;
            let b = as_number(module, right)?;
            Some(InstData::LiteralBool(a > b))
        }
        BinOp::GreaterEq => {
            let a = as_number(module, left)?;
            let b = as_number(module, right)?;
            Some(InstData::LiteralBool(a >= b))
        }
        // In / InstanceOf cannot be folded at compile time.
        _ => None,
    }
}

/// Extract a constant number only if the defining instruction is LiteralNumber.
/// (Does not coerce bools/null — used for strict equality checks.)
fn as_number_strict(module: &Module, val: Value) -> Option<f64> {
    let vd = module.value(val);
    match vd.def {
        crate::module::ValueDef::Inst(inst) => match &module.inst(inst).data {
            InstData::LiteralNumber(n) => Some(*n),
            _ => None,
        },
        _ => None,
    }
}

/// Extract a constant bool only if the defining instruction is LiteralBool.
fn as_bool_strict(module: &Module, val: Value) -> Option<bool> {
    let vd = module.value(val);
    match vd.def {
        crate::module::ValueDef::Inst(inst) => match &module.inst(inst).data {
            InstData::LiteralBool(b) => Some(*b),
            _ => None,
        },
        _ => None,
    }
}

/// Try to extract a constant number from a value's defining instruction.
fn as_number(module: &Module, val: Value) -> Option<f64> {
    let vd = module.value(val);
    match vd.def {
        crate::module::ValueDef::Inst(inst) => match &module.inst(inst).data {
            InstData::LiteralNumber(n) => Some(*n),
            InstData::LiteralBool(true) => Some(1.0),
            InstData::LiteralBool(false) => Some(0.0),
            InstData::LiteralNull => Some(0.0),
            _ => None,
        },
        _ => None,
    }
}

/// Try to extract a constant bool from a value's defining instruction.
fn as_bool(module: &Module, val: Value) -> Option<bool> {
    let vd = module.value(val);
    match vd.def {
        crate::module::ValueDef::Inst(inst) => match &module.inst(inst).data {
            InstData::LiteralBool(b) => Some(*b),
            InstData::LiteralNumber(n) => Some(*n != 0.0 && !n.is_nan()),
            InstData::LiteralNull | InstData::LiteralUndefined => Some(false),
            InstData::LiteralString(s) => Some(!module.strings.get(*s).is_empty()),
            _ => None,
        },
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
        BinOp::Shl => ((a as i32) << (b as u32 & 0x1f)) as f64,
        BinOp::Shr => ((a as i32) >> (b as u32 & 0x1f)) as f64,
        BinOp::Ashr => ((a as u32) >> (b as u32 & 0x1f)) as f64,
        BinOp::BitAnd => ((a as i32) & (b as i32)) as f64,
        BinOp::BitOr => ((a as i32) | (b as i32)) as f64,
        BinOp::BitXor => ((a as i32) ^ (b as i32)) as f64,
        // Comparison ops return 0.0/1.0 but we can't fold them to LiteralNumber
        // since the result type is bool. Return None for now.
        BinOp::Eq
        | BinOp::NotEq
        | BinOp::StrictEq
        | BinOp::StrictNotEq
        | BinOp::Less
        | BinOp::LessEq
        | BinOp::Greater
        | BinOp::GreaterEq
        | BinOp::In
        | BinOp::InstanceOf => return None,
    })
}
