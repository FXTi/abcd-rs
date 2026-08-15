//! Bytecode → IR translation for each instruction variant.

use abcd_file::File;
use abcd_isa::{Bytecode, Reg};

use crate::entity::{Block, Value};
use crate::inst::{BinOp, CallKind, InstData, PropKind, UnOp};
use crate::module::Module;

use super::cfg;
use super::ssa::SsaBuilder;
use super::{
    LiftError, emit_val, emit_void, label_block, read_acc, read_reg, resolve, write_acc, write_reg,
};
use std::collections::HashMap;

/// Translate a single bytecode instruction into IR.
#[allow(clippy::too_many_arguments)]
pub(super) fn translate_bytecode(
    bc: &Bytecode,
    idx: usize,
    block: Block,
    file: &File,
    module: &mut Module,
    ssa: &mut SsaBuilder,
    block_map: &HashMap<usize, Block>,
    raw_cfg: &cfg::RawCfg,
) -> Result<(), LiftError> {
    let loc = Some(idx as u32);

    match bc {
        // ── Data movement (SSA aliases only) ─────────────────────────
        Bytecode::Lda(r) => {
            let v = read_reg(ssa, *r, block, module);
            write_acc(ssa, block, v);
        }
        Bytecode::Sta(r) => {
            let v = read_acc(ssa, block, module);
            write_reg(ssa, *r, block, v);
        }
        Bytecode::Mov(dst, src) => {
            let v = read_reg(ssa, *src, block, module);
            write_reg(ssa, *dst, block, v);
        }

        // ── Literals ─────────────────────────────────────────────────
        Bytecode::Ldundefined => {
            let v = emit_val(module, block, InstData::LiteralUndefined, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Ldnull => {
            let v = emit_val(module, block, InstData::LiteralNull, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Ldtrue => {
            let v = emit_val(module, block, InstData::LiteralBool(true), loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Ldfalse => {
            let v = emit_val(module, block, InstData::LiteralBool(false), loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Ldai(imm) => {
            let v = emit_val(module, block, InstData::LiteralNumber(imm.0 as f64), loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Fldai(imm) => {
            let v = emit_val(
                module,
                block,
                InstData::LiteralNumber(f64::from_bits(imm.0 as u64)),
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::LdaStr(eid) => {
            let s = resolve(file, module, *eid)?;
            let v = emit_val(module, block, InstData::LiteralString(s), loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Ldbigint(eid) => {
            let s = resolve(file, module, *eid)?;
            let v = emit_val(module, block, InstData::LiteralString(s), loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Ldnan => {
            let v = emit_val(module, block, InstData::LiteralNaN, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Ldinfinity => {
            let v = emit_val(module, block, InstData::LiteralInfinity, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Ldhole => {
            let v = emit_val(module, block, InstData::LiteralHole, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Ldsymbol => {
            let s = module.strings.intern("Symbol");
            let v = emit_val(
                module,
                block,
                InstData::TryLoadGlobalByName { name: s },
                loc,
            );
            write_acc(ssa, block, v);
        }

        // ── Binary operations (acc = acc OP reg, IC slot discarded) ──
        Bytecode::Add2(_ic, r) => binary_op(BinOp::Add, r, block, loc, module, ssa),
        Bytecode::Sub2(_ic, r) => binary_op(BinOp::Sub, r, block, loc, module, ssa),
        Bytecode::Mul2(_ic, r) => binary_op(BinOp::Mul, r, block, loc, module, ssa),
        Bytecode::Div2(_ic, r) => binary_op(BinOp::Div, r, block, loc, module, ssa),
        Bytecode::Mod2(_ic, r) => binary_op(BinOp::Mod, r, block, loc, module, ssa),
        Bytecode::Exp(_ic, r) => binary_op(BinOp::Exp, r, block, loc, module, ssa),
        Bytecode::Eq(_ic, r) => binary_op(BinOp::Eq, r, block, loc, module, ssa),
        Bytecode::Noteq(_ic, r) => binary_op(BinOp::NotEq, r, block, loc, module, ssa),
        Bytecode::Less(_ic, r) => binary_op(BinOp::Less, r, block, loc, module, ssa),
        Bytecode::Lesseq(_ic, r) => binary_op(BinOp::LessEq, r, block, loc, module, ssa),
        Bytecode::Greater(_ic, r) => binary_op(BinOp::Greater, r, block, loc, module, ssa),
        Bytecode::Greatereq(_ic, r) => binary_op(BinOp::GreaterEq, r, block, loc, module, ssa),
        Bytecode::Shl2(_ic, r) => binary_op(BinOp::Shl, r, block, loc, module, ssa),
        Bytecode::Shr2(_ic, r) => binary_op(BinOp::Shr, r, block, loc, module, ssa),
        Bytecode::Ashr2(_ic, r) => binary_op(BinOp::Ashr, r, block, loc, module, ssa),
        Bytecode::And2(_ic, r) => binary_op(BinOp::BitAnd, r, block, loc, module, ssa),
        Bytecode::Or2(_ic, r) => binary_op(BinOp::BitOr, r, block, loc, module, ssa),
        Bytecode::Xor2(_ic, r) => binary_op(BinOp::BitXor, r, block, loc, module, ssa),
        Bytecode::Isin(_ic, r) => binary_op(BinOp::In, r, block, loc, module, ssa),
        Bytecode::Instanceof(_ic, r) => binary_op(BinOp::InstanceOf, r, block, loc, module, ssa),
        Bytecode::Stricteq(_ic, r) => binary_op(BinOp::StrictEq, r, block, loc, module, ssa),
        Bytecode::Strictnoteq(_ic, r) => binary_op(BinOp::StrictNotEq, r, block, loc, module, ssa),

        // ── Unary operations (acc = OP acc, IC slot discarded) ───────
        Bytecode::Neg(_ic) => unary_op(UnOp::Minus, block, loc, module, ssa),
        Bytecode::Not(_ic) => unary_op(UnOp::LogicalNot, block, loc, module, ssa),
        Bytecode::Inc(_ic) => unary_op(UnOp::Inc, block, loc, module, ssa),
        Bytecode::Dec(_ic) => unary_op(UnOp::Dec, block, loc, module, ssa),
        Bytecode::Typeof(_ic) => unary_op(UnOp::TypeOf, block, loc, module, ssa),
        Bytecode::Tonumber(_ic) => unary_op(UnOp::ToNumber, block, loc, module, ssa),
        Bytecode::Tonumeric(_ic) => unary_op(UnOp::ToNumeric, block, loc, module, ssa),
        Bytecode::Istrue => {
            let acc = read_acc(ssa, block, module);
            let v = emit_val(module, block, InstData::IsTrue { operand: acc }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Isfalse => {
            let acc = read_acc(ssa, block, module);
            let v = emit_val(module, block, InstData::IsFalse { operand: acc }, loc);
            write_acc(ssa, block, v);
        }

        // ── Object / Array creation ──────────────────────────────────
        Bytecode::Createemptyobject => {
            let v = emit_val(module, block, InstData::CreateEmptyObject, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Createemptyarray(_ic) => {
            let v = emit_val(module, block, InstData::CreateEmptyArray, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Createarraywithbuffer(_ic, eid) => {
            let s = resolve(file, module, *eid)?;
            let v = emit_val(
                module,
                block,
                InstData::CreateArrayWithBuffer { literal_array: s.0 },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Createobjectwithbuffer(_ic, eid) => {
            let s = resolve(file, module, *eid)?;
            let v = emit_val(
                module,
                block,
                InstData::CreateObjectWithBuffer { literal_array: s.0 },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Createregexpwithliteral(_ic, eid, flags_imm) => {
            let pattern = resolve(file, module, *eid)?;
            let flags_str = format!("{}", flags_imm.0);
            let flags = module.strings.intern(&flags_str);
            let v = emit_val(
                module,
                block,
                InstData::CreateRegExp { pattern, flags },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Createobjectwithexcludedkeys(num, obj_reg, start_reg)
        | Bytecode::WideCreateobjectwithexcludedkeys(num, obj_reg, start_reg) => {
            let obj = read_reg(ssa, *obj_reg, block, module);
            let count = num.0 as u16;
            let keys = read_reg_range(ssa, start_reg.0, count, block, module);
            let v = emit_val(
                module,
                block,
                InstData::CreateObjectWithExcludedKeys { obj, keys },
                loc,
            );
            write_acc(ssa, block, v);
        }

        // ── Property access ──────────────────────────────────────────
        Bytecode::Ldobjbyname(_ic, eid) => {
            let name = resolve(file, module, *eid)?;
            let obj = read_acc(ssa, block, module);
            let v = emit_val(
                module,
                block,
                InstData::LoadProperty {
                    object: obj,
                    key: PropKind::ByName(name),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Stobjbyname(_ic, eid, obj_reg) => {
            let name = resolve(file, module, *eid)?;
            let value = read_acc(ssa, block, module);
            let obj = read_reg(ssa, *obj_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreProperty {
                    object: obj,
                    key: PropKind::ByName(name),
                    value,
                },
                loc,
            );
        }
        Bytecode::Ldobjbyvalue(_ic, obj_reg) => {
            let key = read_acc(ssa, block, module);
            let obj = read_reg(ssa, *obj_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::LoadProperty {
                    object: obj,
                    key: PropKind::ByValue(key),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Stobjbyvalue(_ic, obj_reg, val_reg) => {
            let key = read_acc(ssa, block, module);
            let obj = read_reg(ssa, *obj_reg, block, module);
            let value = read_reg(ssa, *val_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreProperty {
                    object: obj,
                    key: PropKind::ByValue(key),
                    value,
                },
                loc,
            );
        }
        Bytecode::Ldobjbyindex(_, index) | Bytecode::WideLdobjbyindex(index) => {
            let obj = read_acc(ssa, block, module);
            let v = emit_val(
                module,
                block,
                InstData::LoadProperty {
                    object: obj,
                    key: PropKind::ByIndex(index.0 as u32),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Stobjbyindex(_ic, obj_reg, index) => {
            let value = read_acc(ssa, block, module);
            let obj = read_reg(ssa, *obj_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreProperty {
                    object: obj,
                    key: PropKind::ByIndex(index.0 as u32),
                    value,
                },
                loc,
            );
        }
        Bytecode::WideStobjbyindex(obj_reg, index) => {
            let value = read_acc(ssa, block, module);
            let obj = read_reg(ssa, *obj_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreProperty {
                    object: obj,
                    key: PropKind::ByIndex(index.0 as u32),
                    value,
                },
                loc,
            );
        }
        Bytecode::Stownbyname(_ic, eid, obj_reg)
        | Bytecode::Stownbynamewithnameset(_ic, eid, obj_reg) => {
            let name = resolve(file, module, *eid)?;
            let value = read_acc(ssa, block, module);
            let obj = read_reg(ssa, *obj_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreOwnProperty {
                    object: obj,
                    key: PropKind::ByName(name),
                    value,
                },
                loc,
            );
        }
        Bytecode::Stownbyvalue(_ic, obj_reg, key_reg)
        | Bytecode::Stownbyvaluewithnameset(_ic, obj_reg, key_reg) => {
            let value = read_acc(ssa, block, module);
            let obj = read_reg(ssa, *obj_reg, block, module);
            let key = read_reg(ssa, *key_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreOwnProperty {
                    object: obj,
                    key: PropKind::ByValue(key),
                    value,
                },
                loc,
            );
        }
        Bytecode::Stownbyindex(_, obj_reg, index) | Bytecode::WideStownbyindex(obj_reg, index) => {
            let value = read_acc(ssa, block, module);
            let obj = read_reg(ssa, *obj_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreOwnProperty {
                    object: obj,
                    key: PropKind::ByIndex(index.0 as u32),
                    value,
                },
                loc,
            );
        }
        Bytecode::Ldthisbyname(_ic, eid) => {
            let name = resolve(file, module, *eid)?;
            let this = emit_val(module, block, InstData::LoadThis, loc);
            let v = emit_val(
                module,
                block,
                InstData::LoadProperty {
                    object: this,
                    key: PropKind::ByName(name),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Stthisbyname(_ic, eid) => {
            let name = resolve(file, module, *eid)?;
            let value = read_acc(ssa, block, module);
            let this = emit_val(module, block, InstData::LoadThis, loc);
            emit_void(
                module,
                block,
                InstData::StoreProperty {
                    object: this,
                    key: PropKind::ByName(name),
                    value,
                },
                loc,
            );
        }
        Bytecode::Ldthisbyvalue(_ic) => {
            let key = read_acc(ssa, block, module);
            let this = emit_val(module, block, InstData::LoadThis, loc);
            let v = emit_val(
                module,
                block,
                InstData::LoadProperty {
                    object: this,
                    key: PropKind::ByValue(key),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Stthisbyvalue(_ic, val_reg) => {
            let key = read_acc(ssa, block, module);
            let this = emit_val(module, block, InstData::LoadThis, loc);
            let value = read_reg(ssa, *val_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreProperty {
                    object: this,
                    key: PropKind::ByValue(key),
                    value,
                },
                loc,
            );
        }
        Bytecode::Ldsuperbyname(_ic, eid) => {
            let name = resolve(file, module, *eid)?;
            let v = emit_val(
                module,
                block,
                InstData::LoadSuperProperty {
                    key: PropKind::ByName(name),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Stsuperbyname(_ic, eid, val_reg) => {
            let name = resolve(file, module, *eid)?;
            let value = read_reg(ssa, *val_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreSuperProperty {
                    key: PropKind::ByName(name),
                    value,
                },
                loc,
            );
        }
        Bytecode::Ldsuperbyvalue(_ic, key_reg) => {
            let key = read_reg(ssa, *key_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::LoadSuperProperty {
                    key: PropKind::ByValue(key),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Stsuperbyvalue(_ic, key_reg, val_reg) => {
            let key = read_reg(ssa, *key_reg, block, module);
            let value = read_reg(ssa, *val_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreSuperProperty {
                    key: PropKind::ByValue(key),
                    value,
                },
                loc,
            );
        }
        Bytecode::Delobjprop(key_reg) => {
            let obj = read_acc(ssa, block, module);
            let key = read_reg(ssa, *key_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::DeleteProperty { object: obj, key },
                loc,
            );
            write_acc(ssa, block, v);
        }

        // ── Private properties ───────────────────────────────────────
        Bytecode::Ldprivateproperty(_ic, level, slot) => {
            let obj = read_acc(ssa, block, module);
            let index = (level.0 as u32) << 16 | (slot.0 as u32);
            let v = emit_val(
                module,
                block,
                InstData::LoadProperty {
                    object: obj,
                    key: PropKind::ByIndex(index),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Stprivateproperty(_ic, level, slot, val_reg) => {
            let obj = read_acc(ssa, block, module);
            let value = read_reg(ssa, *val_reg, block, module);
            let index = (level.0 as u32) << 16 | (slot.0 as u32);
            emit_void(
                module,
                block,
                InstData::StoreProperty {
                    object: obj,
                    key: PropKind::ByIndex(index),
                    value,
                },
                loc,
            );
        }
        Bytecode::Testin(_ic, level, slot) => {
            let obj = read_acc(ssa, block, module);
            let index = (level.0 as u32) << 16 | (slot.0 as u32);
            let v = emit_val(
                module,
                block,
                InstData::LoadProperty {
                    object: obj,
                    key: PropKind::ByIndex(index),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }

        // ── Define field/property by name ────────────────────────────
        Bytecode::Definefieldbyname(_ic, eid, obj_reg)
        | Bytecode::Definepropertybyname(_ic, eid, obj_reg) => {
            let name = resolve(file, module, *eid)?;
            let value = read_acc(ssa, block, module);
            let obj = read_reg(ssa, *obj_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreOwnProperty {
                    object: obj,
                    key: PropKind::ByName(name),
                    value,
                },
                loc,
            );
        }

        // ── Global variables ─────────────────────────────────────────
        Bytecode::Ldglobalvar(_ic, eid) => {
            let name = resolve(file, module, *eid)?;
            let v = emit_val(module, block, InstData::LoadGlobalVar { name }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Stglobalvar(_ic, eid) => {
            let name = resolve(file, module, *eid)?;
            let value = read_acc(ssa, block, module);
            emit_void(module, block, InstData::StoreGlobalVar { name, value }, loc);
        }
        Bytecode::Tryldglobalbyname(_ic, eid) => {
            let name = resolve(file, module, *eid)?;
            let v = emit_val(module, block, InstData::TryLoadGlobalByName { name }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Trystglobalbyname(_ic, eid) => {
            let name = resolve(file, module, *eid)?;
            let value = read_acc(ssa, block, module);
            emit_void(
                module,
                block,
                InstData::TryStoreGlobalByName { name, value },
                loc,
            );
        }
        Bytecode::Stconsttoglobalrecord(_ic, eid) | Bytecode::Sttoglobalrecord(_ic, eid) => {
            let name = resolve(file, module, *eid)?;
            let value = read_acc(ssa, block, module);
            emit_void(module, block, InstData::StoreGlobalVar { name, value }, loc);
        }

        // ── Lexical variables ────────────────────────────────────────
        Bytecode::Ldlexvar(level, slot) | Bytecode::WideLdlexvar(level, slot) => {
            let v = emit_val(
                module,
                block,
                InstData::LoadLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Stlexvar(level, slot) | Bytecode::WideStlexvar(level, slot) => {
            let value = read_acc(ssa, block, module);
            emit_void(
                module,
                block,
                InstData::StoreLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    value,
                },
                loc,
            );
        }
        Bytecode::Newlexenv(num) | Bytecode::WideNewlexenv(num) => {
            let v = emit_val(
                module,
                block,
                InstData::NewLexEnv {
                    num_vars: num.0 as u32,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Newlexenvwithname(num, eid) | Bytecode::WideNewlexenvwithname(num, eid) => {
            let scope_name = resolve(file, module, *eid)?;
            let v = emit_val(
                module,
                block,
                InstData::NewLexEnvWithName {
                    num_vars: num.0 as u32,
                    scope_name,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Poplexenv => {
            emit_void(module, block, InstData::PopLexEnv, loc);
        }

        // ── Module variables ─────────────────────────────────────────
        Bytecode::Ldlocalmodulevar(index) | Bytecode::WideLdlocalmodulevar(index) => {
            let v = emit_val(
                module,
                block,
                InstData::LoadLocalModuleVar {
                    index: index.0 as u32,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Ldexternalmodulevar(index) | Bytecode::WideLdexternalmodulevar(index) => {
            let v = emit_val(
                module,
                block,
                InstData::LoadExternalModuleVar {
                    index: index.0 as u32,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Stmodulevar(index) | Bytecode::WideStmodulevar(index) => {
            let value = read_acc(ssa, block, module);
            emit_void(
                module,
                block,
                InstData::StoreModuleVar {
                    index: index.0 as u32,
                    value,
                },
                loc,
            );
        }
        Bytecode::Getmodulenamespace(index) | Bytecode::WideGetmodulenamespace(index) => {
            let v = emit_val(
                module,
                block,
                InstData::GetModuleNamespace {
                    index: index.0 as u32,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Dynamicimport => {
            let specifier = read_acc(ssa, block, module);
            let v = emit_val(module, block, InstData::DynamicImport { specifier }, loc);
            write_acc(ssa, block, v);
        }

        // ── Function / Class definition ──────────────────────────────
        Bytecode::Definefunc(_ic, eid, length) => {
            let method_id = resolve(file, module, *eid)?;
            let v = emit_val(
                module,
                block,
                InstData::DefineFunc {
                    method_id,
                    length: length.0 as u16,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Definemethod(_ic, eid, length) => {
            let method_id = resolve(file, module, *eid)?;
            let home_object = read_acc(ssa, block, module);
            let v = emit_val(
                module,
                block,
                InstData::DefineMethod {
                    method_id,
                    length: length.0 as u16,
                    home_object,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Defineclasswithbuffer(_ic, method_eid, lit_eid, _count, base_reg) => {
            let method_id = resolve(file, module, *method_eid)?;
            let lit_s = resolve(file, module, *lit_eid)?;
            let base = read_reg(ssa, *base_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::DefineClassWithBuffer {
                    method_id,
                    literal_array: lit_s.0,
                    base,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Definegettersetterbyvalue(obj_reg, key_reg, getter_reg, setter_reg) => {
            let obj = read_reg(ssa, *obj_reg, block, module);
            let key = read_reg(ssa, *key_reg, block, module);
            let getter = read_reg(ssa, *getter_reg, block, module);
            let setter = read_reg(ssa, *setter_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::DefineGetterSetterByValue {
                    obj,
                    key,
                    getter,
                    setter,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }

        // ── Calls ────────────────────────────────────────────────────
        Bytecode::Callarg0(_ic) => {
            let callee = read_acc(ssa, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Call,
                    callee,
                    args: vec![],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Callarg1(_ic, a0) => {
            let callee = read_acc(ssa, block, module);
            let arg0 = read_reg(ssa, *a0, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Call,
                    callee,
                    args: vec![arg0],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Callargs2(_ic, a0, a1) => {
            let callee = read_acc(ssa, block, module);
            let arg0 = read_reg(ssa, *a0, block, module);
            let arg1 = read_reg(ssa, *a1, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Call,
                    callee,
                    args: vec![arg0, arg1],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Callargs3(_ic, a0, a1, a2) => {
            let callee = read_acc(ssa, block, module);
            let arg0 = read_reg(ssa, *a0, block, module);
            let arg1 = read_reg(ssa, *a1, block, module);
            let arg2 = read_reg(ssa, *a2, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Call,
                    callee,
                    args: vec![arg0, arg1, arg2],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Callrange(_, argc, start) | Bytecode::WideCallrange(argc, start) => {
            let callee = read_acc(ssa, block, module);
            let args = read_reg_range(ssa, start.0, argc.0 as u16, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Call,
                    callee,
                    args,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Callthis0(_ic, this_reg) => {
            let callee = read_acc(ssa, block, module);
            let this = read_reg(ssa, *this_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::CallThis,
                    callee,
                    args: vec![this],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Callthis1(_ic, this_reg, a0) => {
            let callee = read_acc(ssa, block, module);
            let this = read_reg(ssa, *this_reg, block, module);
            let arg0 = read_reg(ssa, *a0, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::CallThis,
                    callee,
                    args: vec![this, arg0],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Callthis2(_ic, this_reg, a0, a1) => {
            let callee = read_acc(ssa, block, module);
            let this = read_reg(ssa, *this_reg, block, module);
            let arg0 = read_reg(ssa, *a0, block, module);
            let arg1 = read_reg(ssa, *a1, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::CallThis,
                    callee,
                    args: vec![this, arg0, arg1],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Callthis3(_ic, this_reg, a0, a1, a2) => {
            let callee = read_acc(ssa, block, module);
            let this = read_reg(ssa, *this_reg, block, module);
            let arg0 = read_reg(ssa, *a0, block, module);
            let arg1 = read_reg(ssa, *a1, block, module);
            let arg2 = read_reg(ssa, *a2, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::CallThis,
                    callee,
                    args: vec![this, arg0, arg1, arg2],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Callthisrange(_, argc, start) | Bytecode::WideCallthisrange(argc, start) => {
            let callee = read_acc(ssa, block, module);
            // first reg is `this`, rest are args
            let args = read_reg_range(ssa, start.0, argc.0 as u16, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::CallThis,
                    callee,
                    args,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Supercallthisrange(_, argc, start)
        | Bytecode::WideSupercallthisrange(argc, start) => {
            let callee = read_acc(ssa, block, module);
            let args = read_reg_range(ssa, start.0, argc.0 as u16, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::SuperCall,
                    callee,
                    args,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Supercallarrowrange(_, argc, start)
        | Bytecode::WideSupercallarrowrange(argc, start) => {
            let callee = read_acc(ssa, block, module);
            let args = read_reg_range(ssa, start.0, argc.0 as u16, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::SuperCallArrow,
                    callee,
                    args,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Supercallspread(_ic, arg_reg) => {
            let callee = read_acc(ssa, block, module);
            let arg = read_reg(ssa, *arg_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::SuperCallSpread,
                    callee,
                    args: vec![arg],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Apply(_ic, this_reg, args_reg) => {
            let callee = read_acc(ssa, block, module);
            let this = read_reg(ssa, *this_reg, block, module);
            let args_arr = read_reg(ssa, *args_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Apply,
                    callee,
                    args: vec![this, args_arr],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Newobjrange(_, argc, start) | Bytecode::WideNewobjrange(argc, start) => {
            let args = read_reg_range(ssa, start.0, argc.0 as u16, block, module);
            // first arg is the constructor
            let callee = if args.is_empty() {
                read_acc(ssa, block, module)
            } else {
                args[0]
            };
            let rest = if args.len() > 1 {
                args[1..].to_vec()
            } else {
                vec![]
            };
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Call,
                    callee,
                    args: rest,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Newobjapply(_ic, obj_reg) => {
            let callee = read_acc(ssa, block, module);
            let arg = read_reg(ssa, *obj_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Apply,
                    callee,
                    args: vec![arg],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }

        // ── Special value loaders ────────────────────────────────────
        Bytecode::Ldthis => {
            let v = emit_val(module, block, InstData::LoadThis, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Ldnewtarget => {
            let v = emit_val(module, block, InstData::LoadNewTarget, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Ldglobal => {
            let v = emit_val(module, block, InstData::LoadGlobalObject, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Ldfunction => {
            let v = emit_val(module, block, InstData::LoadFunction, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Getunmappedargs => {
            let v = emit_val(module, block, InstData::GetUnmappedArgs, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Copyrestargs(index) | Bytecode::WideCopyrestargs(index) => {
            let v = emit_val(
                module,
                block,
                InstData::CopyRestArgs {
                    start_index: index.0 as u32,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }

        // ── Iterators ────────────────────────────────────────────────
        Bytecode::Getiterator(_ic) => {
            let obj = read_acc(ssa, block, module);
            let v = emit_val(module, block, InstData::GetIterator { obj }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Getasynciterator(_ic) => {
            let obj = read_acc(ssa, block, module);
            let v = emit_val(module, block, InstData::GetAsyncIterator { obj }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Getpropiterator => {
            let obj = read_acc(ssa, block, module);
            let v = emit_val(module, block, InstData::GetPropIterator { obj }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Closeiterator(_ic, iter_reg) => {
            let iterator = read_reg(ssa, *iter_reg, block, module);
            let v = emit_val(module, block, InstData::CloseIterator { iterator }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Getnextpropname(iter_reg) => {
            let iterator = read_reg(ssa, *iter_reg, block, module);
            // Reuse GetPropIterator to advance; semantically it's "next prop name"
            let v = emit_val(
                module,
                block,
                InstData::GetPropIterator { obj: iterator },
                loc,
            );
            write_acc(ssa, block, v);
        }

        // ── Generator / Async ────────────────────────────────────────
        Bytecode::Creategeneratorobj(func_reg) => {
            let func = read_reg(ssa, *func_reg, block, module);
            let v = emit_val(module, block, InstData::CreateGeneratorObj { func }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Createasyncgeneratorobj(func_reg) => {
            let func = read_reg(ssa, *func_reg, block, module);
            let v = emit_val(module, block, InstData::CreateGeneratorObj { func }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Suspendgenerator(val_reg) => {
            let value = read_reg(ssa, *val_reg, block, module);
            let v = emit_val(module, block, InstData::SuspendGenerator { value }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Resumegenerator => {
            let v = emit_val(module, block, InstData::ResumeGenerator, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Getresumemode => {
            // GetResumeMode returns a number; model as ResumeGenerator (same SSA value)
            let v = emit_val(module, block, InstData::ResumeGenerator, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Setgeneratorstate(_imm) => {
            // State bookkeeping — no IR side effect needed
        }
        Bytecode::Asyncfunctionenter => {
            let v = emit_val(module, block, InstData::AsyncFunctionEnter, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Asyncfunctionawaituncaught(val_reg) => {
            let value = read_reg(ssa, *val_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::AsyncFunctionAwaitUncaught { value },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Asyncfunctionresolve(val_reg) => {
            let value = read_reg(ssa, *val_reg, block, module);
            let v = emit_val(module, block, InstData::AsyncFunctionResolve { value }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Asyncfunctionreject(val_reg) => {
            let value = read_reg(ssa, *val_reg, block, module);
            let v = emit_val(module, block, InstData::AsyncFunctionReject { value }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Asyncgeneratorresolve(val_reg, done_reg, _next_reg) => {
            let value = read_reg(ssa, *val_reg, block, module);
            let done = read_reg(ssa, *done_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::CreateIterResultObj { value, done },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Asyncgeneratorreject(val_reg) => {
            let value = read_reg(ssa, *val_reg, block, module);
            let v = emit_val(module, block, InstData::AsyncFunctionReject { value }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::Createiterresultobj(val_reg, done_reg) => {
            let value = read_reg(ssa, *val_reg, block, module);
            let done = read_reg(ssa, *done_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::CreateIterResultObj { value, done },
                loc,
            );
            write_acc(ssa, block, v);
        }

        // ── Misc ─────────────────────────────────────────────────────
        Bytecode::Gettemplateobject(_ic) => {
            let obj = read_acc(ssa, block, module);
            // Template object is essentially the tagged template array
            let v = emit_val(
                module,
                block,
                InstData::LoadProperty {
                    object: obj,
                    key: PropKind::ByIndex(0),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::Setobjectwithproto(_ic, proto_reg) => {
            let obj = read_acc(ssa, block, module);
            let proto = read_reg(ssa, *proto_reg, block, module);
            let name = module.strings.intern("__proto__");
            emit_void(
                module,
                block,
                InstData::StoreProperty {
                    object: obj,
                    key: PropKind::ByName(name),
                    value: proto,
                },
                loc,
            );
        }
        Bytecode::Starrayspread(arr_reg, index_reg) => {
            let value = read_acc(ssa, block, module);
            let arr = read_reg(ssa, *arr_reg, block, module);
            let idx = read_reg(ssa, *index_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreProperty {
                    object: arr,
                    key: PropKind::ByValue(idx),
                    value,
                },
                loc,
            );
        }
        Bytecode::Copydataproperties(src_reg) => {
            let dst = read_acc(ssa, block, module);
            let src = read_reg(ssa, *src_reg, block, module);
            // Model as a call-like operation; dst stays in acc
            let name = module.strings.intern("[[CopyDataProperties]]");
            emit_void(
                module,
                block,
                InstData::StoreProperty {
                    object: dst,
                    key: PropKind::ByName(name),
                    value: src,
                },
                loc,
            );
        }

        // ── Control flow — jumps ─────────────────────────────────────
        Bytecode::Jmp(label) => {
            let dest = label_block(*label, raw_cfg, block_map);
            emit_void(module, block, InstData::Branch { dest }, loc);
        }
        Bytecode::Jeqz(label) => {
            cond_branch_acc(
                false, *label, idx, block, loc, module, ssa, block_map, raw_cfg,
            );
        }
        Bytecode::Jnez(label) => {
            cond_branch_acc(
                true, *label, idx, block, loc, module, ssa, block_map, raw_cfg,
            );
        }
        Bytecode::Jstricteqz(label) => {
            // acc === 0 → branch
            cond_branch_acc(
                false, *label, idx, block, loc, module, ssa, block_map, raw_cfg,
            );
        }
        Bytecode::Jnstricteqz(label) => {
            cond_branch_acc(
                true, *label, idx, block, loc, module, ssa, block_map, raw_cfg,
            );
        }
        Bytecode::Jeqnull(label) | Bytecode::Jstricteqnull(label) => {
            cond_branch_acc(
                false, *label, idx, block, loc, module, ssa, block_map, raw_cfg,
            );
        }
        Bytecode::Jnenull(label) | Bytecode::Jnstricteqnull(label) => {
            cond_branch_acc(
                true, *label, idx, block, loc, module, ssa, block_map, raw_cfg,
            );
        }
        Bytecode::Jequndefined(label) | Bytecode::Jstrictequndefined(label) => {
            cond_branch_acc(
                false, *label, idx, block, loc, module, ssa, block_map, raw_cfg,
            );
        }
        Bytecode::Jneundefined(label) | Bytecode::Jnstrictequndefined(label) => {
            cond_branch_acc(
                true, *label, idx, block, loc, module, ssa, block_map, raw_cfg,
            );
        }
        Bytecode::Jeq(reg, label) => {
            let acc = read_acc(ssa, block, module);
            let other = read_reg(ssa, *reg, block, module);
            let cond = emit_val(
                module,
                block,
                InstData::BinaryOp {
                    op: BinOp::Eq,
                    left: acc,
                    right: other,
                },
                loc,
            );
            let true_dest = label_block(*label, raw_cfg, block_map);
            let false_dest = fallthrough_block(idx, raw_cfg, block_map);
            emit_void(
                module,
                block,
                InstData::CondBranch {
                    cond,
                    true_dest,
                    false_dest,
                },
                loc,
            );
        }
        Bytecode::Jne(reg, label) => {
            let acc = read_acc(ssa, block, module);
            let other = read_reg(ssa, *reg, block, module);
            let cond = emit_val(
                module,
                block,
                InstData::BinaryOp {
                    op: BinOp::NotEq,
                    left: acc,
                    right: other,
                },
                loc,
            );
            let true_dest = label_block(*label, raw_cfg, block_map);
            let false_dest = fallthrough_block(idx, raw_cfg, block_map);
            emit_void(
                module,
                block,
                InstData::CondBranch {
                    cond,
                    true_dest,
                    false_dest,
                },
                loc,
            );
        }
        Bytecode::Jstricteq(reg, label) => {
            let acc = read_acc(ssa, block, module);
            let other = read_reg(ssa, *reg, block, module);
            let cond = emit_val(
                module,
                block,
                InstData::BinaryOp {
                    op: BinOp::StrictEq,
                    left: acc,
                    right: other,
                },
                loc,
            );
            let true_dest = label_block(*label, raw_cfg, block_map);
            let false_dest = fallthrough_block(idx, raw_cfg, block_map);
            emit_void(
                module,
                block,
                InstData::CondBranch {
                    cond,
                    true_dest,
                    false_dest,
                },
                loc,
            );
        }
        Bytecode::Jnstricteq(reg, label) => {
            let acc = read_acc(ssa, block, module);
            let other = read_reg(ssa, *reg, block, module);
            let cond = emit_val(
                module,
                block,
                InstData::BinaryOp {
                    op: BinOp::StrictNotEq,
                    left: acc,
                    right: other,
                },
                loc,
            );
            let true_dest = label_block(*label, raw_cfg, block_map);
            let false_dest = fallthrough_block(idx, raw_cfg, block_map);
            emit_void(
                module,
                block,
                InstData::CondBranch {
                    cond,
                    true_dest,
                    false_dest,
                },
                loc,
            );
        }

        // ── Return ───────────────────────────────────────────────────
        Bytecode::Return => {
            let value = read_acc(ssa, block, module);
            emit_void(module, block, InstData::Return { value: Some(value) }, loc);
        }
        Bytecode::Returnundefined => {
            emit_void(module, block, InstData::Return { value: None }, loc);
        }

        // ── Exception handling ───────────────────────────────────────
        Bytecode::Throw => {
            let value = read_acc(ssa, block, module);
            emit_void(module, block, InstData::Throw { value }, loc);
        }
        Bytecode::ThrowNotexists => {
            emit_void(module, block, InstData::ThrowNotExists, loc);
        }
        Bytecode::ThrowPatternnoncoercible => {
            emit_void(module, block, InstData::ThrowPatternNonCoercible, loc);
        }
        Bytecode::ThrowDeletesuperproperty => {
            emit_void(module, block, InstData::ThrowDeleteSuperProperty, loc);
        }
        Bytecode::ThrowConstassignment(name_reg) => {
            // The register holds the variable name as a string value
            // We model this with a synthetic StringId
            let name_val = read_reg(ssa, *name_reg, block, module);
            let s = module
                .strings
                .intern(&format!("const_assign_{}", name_val.0));
            emit_void(
                module,
                block,
                InstData::ThrowConstAssignment { name: s },
                loc,
            );
        }
        Bytecode::ThrowIfnotobject(val_reg) => {
            let value = read_reg(ssa, *val_reg, block, module);
            emit_void(module, block, InstData::ThrowIfNotObject { value }, loc);
        }
        Bytecode::ThrowUndefinedifhole(name_reg, val_reg) => {
            let value = read_reg(ssa, *val_reg, block, module);
            let name_val = read_reg(ssa, *name_reg, block, module);
            let s = module.strings.intern(&format!("hole_check_{}", name_val.0));
            emit_void(
                module,
                block,
                InstData::ThrowUndefinedIfHole { name: s, value },
                loc,
            );
        }
        Bytecode::ThrowUndefinedifholewithname(eid) => {
            let name = resolve(file, module, *eid)?;
            let acc = read_acc(ssa, block, module);
            emit_void(
                module,
                block,
                InstData::ThrowUndefinedIfHole { name, value: acc },
                loc,
            );
        }
        Bytecode::ThrowIfsupernotcorrectcall(imm) => {
            let value = emit_val(module, block, InstData::LiteralNumber(imm.0 as f64), loc);
            emit_void(
                module,
                block,
                InstData::ThrowIfSuperNotCorrectCall { value },
                loc,
            );
        }

        // ── Debug ────────────────────────────────────────────────────
        Bytecode::Debugger => {
            emit_void(module, block, InstData::Debugger, loc);
        }
        Bytecode::Nop => { /* no-op */ }

        // ── Callruntime variants ─────────────────────────────────────
        // These are internal runtime calls; model as no-ops or simple pass-throughs
        // where they have observable effects.
        Bytecode::CallruntimeNotifyconcurrentresult | Bytecode::CallruntimeTopropertykey => {
            // acc stays unchanged or is a pass-through
        }
        Bytecode::CallruntimeDefinefieldbyvalue(_ic, obj_reg, key_reg) => {
            let value = read_acc(ssa, block, module);
            let obj = read_reg(ssa, *obj_reg, block, module);
            let key = read_reg(ssa, *key_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreOwnProperty {
                    object: obj,
                    key: PropKind::ByValue(key),
                    value,
                },
                loc,
            );
        }
        Bytecode::CallruntimeDefinefieldbyindex(_ic, index, obj_reg) => {
            let value = read_acc(ssa, block, module);
            let obj = read_reg(ssa, *obj_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreOwnProperty {
                    object: obj,
                    key: PropKind::ByIndex(index.0 as u32),
                    value,
                },
                loc,
            );
        }
        Bytecode::CallruntimeCreateprivateproperty(_count, eid) => {
            let _name = resolve(file, module, *eid)?;
            // Private property creation — bookkeeping, no IR side effect
        }
        Bytecode::CallruntimeDefineprivateproperty(_ic, level, slot, val_reg) => {
            let obj = read_acc(ssa, block, module);
            let value = read_reg(ssa, *val_reg, block, module);
            let index = (level.0 as u32) << 16 | (slot.0 as u32);
            emit_void(
                module,
                block,
                InstData::StoreOwnProperty {
                    object: obj,
                    key: PropKind::ByIndex(index),
                    value,
                },
                loc,
            );
        }
        Bytecode::CallruntimeCallinit(_ic, this_reg) => {
            let callee = read_acc(ssa, block, module);
            let this = read_reg(ssa, *this_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::CallThis,
                    callee,
                    args: vec![this],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::CallruntimeDefinesendableclass(_ic, method_eid, lit_eid, _count, base_reg) => {
            let method_id = resolve(file, module, *method_eid)?;
            let lit_s = resolve(file, module, *lit_eid)?;
            let base = read_reg(ssa, *base_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::DefineClassWithBuffer {
                    method_id,
                    literal_array: lit_s.0,
                    base,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::CallruntimeLdsendableclass(index)
        | Bytecode::CallruntimeLdsendableexternalmodulevar(index)
        | Bytecode::CallruntimeWideldsendableexternalmodulevar(index)
        | Bytecode::CallruntimeLdsendablelocalmodulevar(index)
        | Bytecode::CallruntimeWideldsendablelocalmodulevar(index) => {
            let v = emit_val(
                module,
                block,
                InstData::LoadExternalModuleVar {
                    index: index.0 as u32,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::CallruntimeNewsendableenv(num) | Bytecode::CallruntimeWidenewsendableenv(num) => {
            let v = emit_val(
                module,
                block,
                InstData::NewLexEnv {
                    num_vars: num.0 as u32,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::CallruntimeStsendablevar(level, slot)
        | Bytecode::CallruntimeWidestsendablevar(level, slot) => {
            let value = read_acc(ssa, block, module);
            emit_void(
                module,
                block,
                InstData::StoreLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    value,
                },
                loc,
            );
        }
        Bytecode::CallruntimeLdsendablevar(level, slot)
        | Bytecode::CallruntimeWideldsendablevar(level, slot) => {
            let v = emit_val(
                module,
                block,
                InstData::LoadLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::CallruntimeIstrue(_ic) => {
            let acc = read_acc(ssa, block, module);
            let v = emit_val(module, block, InstData::IsTrue { operand: acc }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::CallruntimeIsfalse(_ic) => {
            let acc = read_acc(ssa, block, module);
            let v = emit_val(module, block, InstData::IsFalse { operand: acc }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::CallruntimeLdlazymodulevar(index)
        | Bytecode::CallruntimeWideldlazymodulevar(index)
        | Bytecode::CallruntimeLdlazysendablemodulevar(index)
        | Bytecode::CallruntimeWideldlazysendablemodulevar(index) => {
            let v = emit_val(
                module,
                block,
                InstData::LoadExternalModuleVar {
                    index: index.0 as u32,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::CallruntimeSupercallforwardallargs(this_reg) => {
            let callee = read_acc(ssa, block, module);
            let this = read_reg(ssa, *this_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::SuperCall,
                    callee,
                    args: vec![this],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }

        // ── Patch var (for hot-reload) ───────────────────────────────
        Bytecode::WideLdpatchvar(index) => {
            let v = emit_val(
                module,
                block,
                InstData::LoadLexVar {
                    level: 0,
                    slot: index.0 as u16,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::WideStpatchvar(index) => {
            let value = read_acc(ssa, block, module);
            emit_void(
                module,
                block,
                InstData::StoreLexVar {
                    level: 0,
                    slot: index.0 as u16,
                    value,
                },
                loc,
            );
        }

        // ── Deprecated variants ──────────────────────────────────────
        // Map deprecated instructions to the same IR as their modern equivalents.
        Bytecode::DeprecatedLdlexenv | Bytecode::DeprecatedLdhomeobject => {
            // These load environment/home object into acc — model as LoadFunction
            let v = emit_val(module, block, InstData::LoadFunction, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedPoplexenv => {
            emit_void(module, block, InstData::PopLexEnv, loc);
        }
        Bytecode::DeprecatedGetiteratornext(iter_reg, _step_reg) => {
            let iterator = read_reg(ssa, *iter_reg, block, module);
            let v = emit_val(module, block, InstData::GetIterator { obj: iterator }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedCreatearraywithbuffer(idx)
        | Bytecode::DeprecatedCreateobjectwithbuffer(idx) => {
            let v = emit_val(
                module,
                block,
                InstData::CreateArrayWithBuffer {
                    literal_array: idx.0 as u32,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedTonumber(dst) | Bytecode::DeprecatedTonumeric(dst) => {
            let val = read_reg(ssa, *dst, block, module);
            let v = emit_val(
                module,
                block,
                InstData::UnaryOp {
                    op: UnOp::ToNumber,
                    operand: val,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedNeg(src) => {
            let val = read_reg(ssa, *src, block, module);
            let v = emit_val(
                module,
                block,
                InstData::UnaryOp {
                    op: UnOp::Minus,
                    operand: val,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedNot(src) => {
            let val = read_reg(ssa, *src, block, module);
            let v = emit_val(
                module,
                block,
                InstData::UnaryOp {
                    op: UnOp::LogicalNot,
                    operand: val,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedInc(src) => {
            let val = read_reg(ssa, *src, block, module);
            let v = emit_val(
                module,
                block,
                InstData::UnaryOp {
                    op: UnOp::Inc,
                    operand: val,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedDec(src) => {
            let val = read_reg(ssa, *src, block, module);
            let v = emit_val(
                module,
                block,
                InstData::UnaryOp {
                    op: UnOp::Dec,
                    operand: val,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedCallarg0(callee_reg) => {
            let callee = read_reg(ssa, *callee_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Call,
                    callee,
                    args: vec![],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedCallarg1(callee_reg, a0) => {
            let callee = read_reg(ssa, *callee_reg, block, module);
            let arg0 = read_reg(ssa, *a0, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Call,
                    callee,
                    args: vec![arg0],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedCallargs2(callee_reg, a0, a1) => {
            let callee = read_reg(ssa, *callee_reg, block, module);
            let arg0 = read_reg(ssa, *a0, block, module);
            let arg1 = read_reg(ssa, *a1, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Call,
                    callee,
                    args: vec![arg0, arg1],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedCallargs3(callee_reg, a0, a1, a2) => {
            let callee = read_reg(ssa, *callee_reg, block, module);
            let arg0 = read_reg(ssa, *a0, block, module);
            let arg1 = read_reg(ssa, *a1, block, module);
            let arg2 = read_reg(ssa, *a2, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Call,
                    callee,
                    args: vec![arg0, arg1, arg2],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedCallrange(argc, start) => {
            let callee = read_acc(ssa, block, module);
            let args = read_reg_range(ssa, start.0, argc.0 as u16, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Call,
                    callee,
                    args,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedCallspread(callee_reg, args_reg, _undef_reg) => {
            let callee = read_reg(ssa, *callee_reg, block, module);
            let args_arr = read_reg(ssa, *args_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::Apply,
                    callee,
                    args: vec![args_arr],
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedCallthisrange(argc, start) => {
            let callee = read_acc(ssa, block, module);
            let args = read_reg_range(ssa, start.0, argc.0 as u16, block, module);
            let v = emit_val(
                module,
                block,
                InstData::Call {
                    kind: CallKind::CallThis,
                    callee,
                    args,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedDefineclasswithbuffer(
            method_eid,
            lit_idx,
            _count,
            base_reg,
            _env_reg,
        ) => {
            let method_id = resolve(file, module, *method_eid)?;
            let base = read_reg(ssa, *base_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::DefineClassWithBuffer {
                    method_id,
                    literal_array: lit_idx.0 as u32,
                    base,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedResumegenerator(gen_reg) => {
            let _gen = read_reg(ssa, *gen_reg, block, module);
            let v = emit_val(module, block, InstData::ResumeGenerator, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedGetresumemode(gen_reg) => {
            let _gen = read_reg(ssa, *gen_reg, block, module);
            let v = emit_val(module, block, InstData::ResumeGenerator, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedGettemplateobject(tpl_reg) => {
            let obj = read_reg(ssa, *tpl_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::LoadProperty {
                    object: obj,
                    key: PropKind::ByIndex(0),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedDelobjprop(obj_reg, key_reg) => {
            let obj = read_reg(ssa, *obj_reg, block, module);
            let key = read_reg(ssa, *key_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::DeleteProperty { object: obj, key },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedSuspendgenerator(gen_reg, val_reg) => {
            let _gen = read_reg(ssa, *gen_reg, block, module);
            let value = read_reg(ssa, *val_reg, block, module);
            let v = emit_val(module, block, InstData::SuspendGenerator { value }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedAsyncfunctionawaituncaught(async_reg, val_reg) => {
            let _async_obj = read_reg(ssa, *async_reg, block, module);
            let value = read_reg(ssa, *val_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::AsyncFunctionAwaitUncaught { value },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedCopydataproperties(dst_reg, src_reg) => {
            let dst = read_reg(ssa, *dst_reg, block, module);
            let src = read_reg(ssa, *src_reg, block, module);
            let name = module.strings.intern("[[CopyDataProperties]]");
            emit_void(
                module,
                block,
                InstData::StoreProperty {
                    object: dst,
                    key: PropKind::ByName(name),
                    value: src,
                },
                loc,
            );
        }
        Bytecode::DeprecatedSetobjectwithproto(proto_reg, obj_reg) => {
            let proto = read_reg(ssa, *proto_reg, block, module);
            let obj = read_reg(ssa, *obj_reg, block, module);
            let name = module.strings.intern("__proto__");
            emit_void(
                module,
                block,
                InstData::StoreProperty {
                    object: obj,
                    key: PropKind::ByName(name),
                    value: proto,
                },
                loc,
            );
        }
        Bytecode::DeprecatedLdobjbyvalue(obj_reg, key_reg) => {
            let obj = read_reg(ssa, *obj_reg, block, module);
            let key = read_reg(ssa, *key_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::LoadProperty {
                    object: obj,
                    key: PropKind::ByValue(key),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedLdsuperbyvalue(obj_reg, key_reg) => {
            let _obj = read_reg(ssa, *obj_reg, block, module);
            let key = read_reg(ssa, *key_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::LoadSuperProperty {
                    key: PropKind::ByValue(key),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedLdobjbyindex(obj_reg, index) => {
            let obj = read_reg(ssa, *obj_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::LoadProperty {
                    object: obj,
                    key: PropKind::ByIndex(index.0 as u32),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedAsyncfunctionresolve(async_reg, val_reg, _can_suspend_reg) => {
            let _async_obj = read_reg(ssa, *async_reg, block, module);
            let value = read_reg(ssa, *val_reg, block, module);
            let v = emit_val(module, block, InstData::AsyncFunctionResolve { value }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedAsyncfunctionreject(async_reg, val_reg, _can_suspend_reg) => {
            let _async_obj = read_reg(ssa, *async_reg, block, module);
            let value = read_reg(ssa, *val_reg, block, module);
            let v = emit_val(module, block, InstData::AsyncFunctionReject { value }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedStlexvar(level, slot, val_reg) => {
            let value = read_reg(ssa, *val_reg, block, module);
            emit_void(
                module,
                block,
                InstData::StoreLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    value,
                },
                loc,
            );
        }
        Bytecode::DeprecatedGetmodulenamespace(eid) => {
            let name = resolve(file, module, *eid)?;
            let v = emit_val(
                module,
                block,
                InstData::GetModuleNamespace { index: name.0 },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedStmodulevar(eid) => {
            let name = resolve(file, module, *eid)?;
            let value = read_acc(ssa, block, module);
            emit_void(
                module,
                block,
                InstData::StoreModuleVar {
                    index: name.0,
                    value,
                },
                loc,
            );
        }
        Bytecode::DeprecatedLdobjbyname(eid, obj_reg) => {
            let name = resolve(file, module, *eid)?;
            let obj = read_reg(ssa, *obj_reg, block, module);
            let v = emit_val(
                module,
                block,
                InstData::LoadProperty {
                    object: obj,
                    key: PropKind::ByName(name),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedLdsuperbyname(eid, _obj_reg) => {
            let name = resolve(file, module, *eid)?;
            let v = emit_val(
                module,
                block,
                InstData::LoadSuperProperty {
                    key: PropKind::ByName(name),
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedLdmodulevar(eid, _flag) => {
            let name = resolve(file, module, *eid)?;
            let v = emit_val(
                module,
                block,
                InstData::LoadExternalModuleVar { index: name.0 },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedStconsttoglobalrecord(eid)
        | Bytecode::DeprecatedStlettoglobalrecord(eid)
        | Bytecode::DeprecatedStclasstoglobalrecord(eid) => {
            let name = resolve(file, module, *eid)?;
            let value = read_acc(ssa, block, module);
            emit_void(module, block, InstData::StoreGlobalVar { name, value }, loc);
        }
        Bytecode::DeprecatedCreateobjecthavingmethod(idx) => {
            let v = emit_val(
                module,
                block,
                InstData::CreateObjectWithBuffer {
                    literal_array: idx.0 as u32,
                },
                loc,
            );
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedDynamicimport(spec_reg) => {
            let specifier = read_reg(ssa, *spec_reg, block, module);
            let v = emit_val(module, block, InstData::DynamicImport { specifier }, loc);
            write_acc(ssa, block, v);
        }
        Bytecode::DeprecatedAsyncgeneratorreject(gen_reg, val_reg) => {
            let _gen = read_reg(ssa, *gen_reg, block, module);
            let value = read_reg(ssa, *val_reg, block, module);
            let v = emit_val(module, block, InstData::AsyncFunctionReject { value }, loc);
            write_acc(ssa, block, v);
        }
    }

    Ok(())
}

// ─── Helper functions ────────────────────────────────────────────────────────

/// Emit a binary operation: acc = acc OP reg.
fn binary_op(
    op: BinOp,
    r: &Reg,
    block: Block,
    loc: Option<u32>,
    module: &mut Module,
    ssa: &mut SsaBuilder,
) {
    let left = read_acc(ssa, block, module);
    let right = read_reg(ssa, *r, block, module);
    let v = emit_val(module, block, InstData::BinaryOp { op, left, right }, loc);
    write_acc(ssa, block, v);
}

/// Emit a unary operation: acc = OP acc.
fn unary_op(op: UnOp, block: Block, loc: Option<u32>, module: &mut Module, ssa: &mut SsaBuilder) {
    let operand = read_acc(ssa, block, module);
    let v = emit_val(module, block, InstData::UnaryOp { op, operand }, loc);
    write_acc(ssa, block, v);
}

/// Read a range of consecutive registers starting at `start` for `count` registers.
fn read_reg_range(
    ssa: &mut SsaBuilder,
    start: u16,
    count: u16,
    block: Block,
    module: &mut Module,
) -> Vec<Value> {
    (0..count)
        .map(|i| {
            let reg = Reg(start + i);
            read_reg(ssa, reg, block, module)
        })
        .collect()
}

/// Emit a conditional branch based on the accumulator value.
/// If `truthy` is true, branch to `label` when acc is truthy (jnez-like).
/// If `truthy` is false, branch to `label` when acc is falsy (jeqz-like).
fn cond_branch_acc(
    truthy: bool,
    label: abcd_isa::Label,
    idx: usize,
    block: Block,
    loc: Option<u32>,
    module: &mut Module,
    ssa: &mut SsaBuilder,
    block_map: &HashMap<usize, Block>,
    raw_cfg: &cfg::RawCfg,
) {
    let acc = read_acc(ssa, block, module);
    let cond = if truthy {
        emit_val(module, block, InstData::IsTrue { operand: acc }, loc)
    } else {
        emit_val(module, block, InstData::IsFalse { operand: acc }, loc)
    };
    let jump_dest = label_block(label, raw_cfg, block_map);
    let fall_dest = fallthrough_block(idx, raw_cfg, block_map);
    if truthy {
        emit_void(
            module,
            block,
            InstData::CondBranch {
                cond,
                true_dest: jump_dest,
                false_dest: fall_dest,
            },
            loc,
        );
    } else {
        // jeqz: branch when acc == 0 (falsy), so the "false test" result being true means we branch
        emit_void(
            module,
            block,
            InstData::CondBranch {
                cond,
                true_dest: jump_dest,
                false_dest: fall_dest,
            },
            loc,
        );
    }
}

/// Get the fall-through block (the block containing the instruction after `idx`).
fn fallthrough_block(
    idx: usize,
    raw_cfg: &cfg::RawCfg,
    block_map: &HashMap<usize, Block>,
) -> Block {
    let next_idx = idx + 1;
    // Find which raw block contains next_idx
    for (bi, rb) in raw_cfg.blocks.iter().enumerate() {
        if next_idx >= rb.start && next_idx < rb.end {
            return block_map[&bi];
        }
    }
    // If next_idx is a leader of a new block
    if let Some(&bi) = raw_cfg.leader_to_block.get(&next_idx) {
        return block_map[&bi];
    }
    // Fallback: return the last block (shouldn't happen in well-formed bytecode)
    let last_bi = raw_cfg.blocks.len() - 1;
    block_map[&last_bi]
}
