use std::collections::HashMap;

use abcd_file::literal::{LiteralArray, LiteralTag, LiteralValue};
use abcd_ir::expr::{BinOp, Expr, PropKey, UnOp};
use abcd_ir::instruction::Instruction;
use abcd_ir::stmt::Stmt;
use abcd_isa::{Bytecode as B, EntityId};

/// Resolves entity IDs to strings/names and literal arrays.
pub trait StringResolver {
    fn resolve_string(&self, method_off: EntityId, entity_id: EntityId) -> Option<String>;
    fn resolve_offset(&self, method_off: EntityId, entity_id: EntityId) -> Option<EntityId>;
    fn resolve_literal_array(
        &self,
        _method_off: EntityId,
        _entity_id: EntityId,
    ) -> Option<LiteralArray> {
        None
    }
    fn get_string_at_offset(&self, _offset: EntityId) -> Option<String> {
        None
    }
    fn resolve_method_name(&self, _method_off: EntityId, _entity_id: EntityId) -> Option<String> {
        None
    }
}

/// Result of recovering expressions from a basic block.
pub struct BlockRecovery {
    pub stmts: Vec<Stmt>,
    pub final_acc: Expr,
    pub final_regs: HashMap<u16, Expr>,
}

/// Recover expressions from a sequence of instructions within a basic block.
pub fn recover_block(
    instructions: &[Instruction],
    resolver: &dyn StringResolver,
    method_off: EntityId,
    num_vregs: u32,
    num_args: u32,
) -> BlockRecovery {
    let mut state = ExprState::new(num_vregs, num_args);
    let mut stmts = Vec::new();
    for insn in instructions {
        process_insn(insn, &mut state, &mut stmts, resolver, method_off);
    }
    BlockRecovery {
        stmts,
        final_acc: state.acc,
        final_regs: state.regs,
    }
}

struct ExprState {
    acc: Expr,
    regs: HashMap<u16, Expr>,
    num_vregs: u32,
    num_args: u32,
}

impl ExprState {
    fn new(num_vregs: u32, num_args: u32) -> Self {
        ExprState {
            acc: Expr::Undefined,
            regs: HashMap::new(),
            num_vregs,
            num_args,
        }
    }
    fn with_state(num_vregs: u32, num_args: u32, acc: Expr, regs: HashMap<u16, Expr>) -> Self {
        ExprState {
            acc,
            regs,
            num_vregs,
            num_args,
        }
    }
    fn get_reg(&self, r: u16) -> Expr {
        self.regs
            .get(&r)
            .cloned()
            .unwrap_or_else(|| arg_or_var(r, self.num_vregs, self.num_args))
    }
    fn set_reg(&mut self, r: u16, e: Expr) {
        self.regs.insert(r, e);
    }
}

pub fn recover_block_with_state(
    instructions: &[Instruction],
    resolver: &dyn StringResolver,
    method_off: EntityId,
    num_vregs: u32,
    num_args: u32,
    initial_acc: Expr,
    initial_regs: HashMap<u16, Expr>,
) -> BlockRecovery {
    let mut state = ExprState::with_state(num_vregs, num_args, initial_acc, initial_regs);
    let mut stmts = Vec::new();
    for insn in instructions {
        process_insn(insn, &mut state, &mut stmts, resolver, method_off);
    }
    BlockRecovery {
        stmts,
        final_acc: state.acc,
        final_regs: state.regs,
    }
}

fn arg_or_var(r: u16, num_vregs: u32, _num_args: u32) -> Expr {
    let r32 = r as u32;
    if r32 < num_vregs {
        Expr::Var(format!("r{}", r32 + 1))
    } else if r32 == num_vregs {
        Expr::Var("__func__".into())
    } else if r32 == num_vregs + 1 {
        Expr::NewTarget
    } else if r32 == num_vregs + 2 {
        Expr::This
    } else {
        Expr::Var(format!("p{}", r32 - num_vregs - 2))
    }
}

fn resolve_str(resolver: &dyn StringResolver, method_off: EntityId, id: EntityId) -> String {
    resolver
        .resolve_string(method_off, id)
        .unwrap_or_else(|| format!("@{:#x}", id.0))
}

fn resolve_method_or_str(
    resolver: &dyn StringResolver,
    method_off: EntityId,
    id: EntityId,
) -> String {
    resolver
        .resolve_method_name(method_off, id)
        .or_else(|| resolver.resolve_string(method_off, id))
        .unwrap_or_else(|| format!("@{:#x}", id.0))
}

fn flush_acc_side_effects(state: &mut ExprState, stmts: &mut Vec<Stmt>) {
    match &state.acc {
        Expr::Call { .. } | Expr::New { .. } | Expr::SuperCall { .. } => {
            stmts.push(Stmt::Expr(state.acc.clone()));
            state.acc = Expr::Undefined;
        }
        _ => {}
    }
}

fn is_acc_replacing(bc: &B) -> bool {
    matches!(
        bc,
        B::Ldundefined
            | B::Ldnull
            | B::Ldtrue
            | B::Ldfalse
            | B::Ldai(..)
            | B::Fldai(..)
            | B::LdaStr(..)
            | B::Ldhole
            | B::Ldinfinity
            | B::Ldnan
            | B::Ldsymbol
            | B::Createemptyobject
            | B::Createemptyarray(..)
            | B::Createobjectwithbuffer(..)
            | B::Createarraywithbuffer(..)
            | B::Createregexpwithliteral(..)
    )
}

fn binary_op(state: &mut ExprState, reg: u16, op: BinOp) {
    let rhs = state.get_reg(reg);
    state.acc = Expr::BinaryOp {
        op,
        lhs: Box::new(state.acc.clone()),
        rhs: Box::new(rhs),
    };
}

fn unary_op(state: &mut ExprState, op: UnOp) {
    state.acc = Expr::UnaryOp {
        op,
        expr: Box::new(state.acc.clone()),
    };
}

fn process_insn(
    insn: &Instruction,
    state: &mut ExprState,
    stmts: &mut Vec<Stmt>,
    resolver: &dyn StringResolver,
    method_off: EntityId,
) {
    if is_acc_replacing(&insn.opcode) {
        flush_acc_side_effects(state, stmts);
    }

    match insn.opcode {
        // === Load constants ===
        B::Ldundefined => state.acc = Expr::Undefined,
        B::Ldnull => state.acc = Expr::Null,
        B::Ldtrue => state.acc = Expr::BoolLit(true),
        B::Ldfalse => state.acc = Expr::BoolLit(false),
        B::Ldai(imm) => state.acc = Expr::NumberLit(imm.0 as f64),
        B::Fldai(imm) => state.acc = Expr::NumberLit(f64::from_bits(imm.0 as u64)),
        B::LdaStr(id) => {
            state.acc = Expr::StringLit(resolve_str(resolver, method_off, id));
        }
        B::Lda(reg) => state.acc = state.get_reg(reg.0),
        B::Sta(reg) => state.set_reg(reg.0, state.acc.clone()),
        B::Mov(dst, src) => state.set_reg(dst.0, state.get_reg(src.0)),

        // === Lexical variables ===
        B::Ldlexvar(level, slot) | B::WideLdlexvar(level, slot) => {
            state.acc = Expr::Var(format!("x_{}_{}", level.0 + 1, slot.0 + 1));
        }
        B::Stlexvar(level, slot) | B::WideStlexvar(level, slot) => {
            stmts.push(Stmt::Assign {
                target: Expr::Var(format!("x_{}_{}", level.0 + 1, slot.0 + 1)),
                value: state.acc.clone(),
            });
        }
        B::Newlexenv(..)
        | B::Newlexenvwithname(..)
        | B::WideNewlexenv(..)
        | B::WideNewlexenvwithname(..)
        | B::Poplexenv => {}

        // === Global/module access ===
        B::Tryldglobalbyname(_, id) | B::Ldglobalvar(_, id) => {
            state.acc = Expr::Var(resolve_str(resolver, method_off, id));
        }
        B::Trystglobalbyname(_, id) | B::Stglobalvar(_, id) => {
            stmts.push(Stmt::Assign {
                target: Expr::Var(resolve_str(resolver, method_off, id)),
                value: state.acc.clone(),
            });
        }
        B::Ldexternalmodulevar(idx) | B::WideLdexternalmodulevar(idx) => {
            state.acc = Expr::Var(format!("__module_{}", idx.0));
        }
        B::Ldlocalmodulevar(idx) | B::WideLdlocalmodulevar(idx) => {
            state.acc = Expr::Var(format!("__local_module_{}", idx.0));
        }
        B::Stmodulevar(idx) | B::WideStmodulevar(idx) => {
            stmts.push(Stmt::Assign {
                target: Expr::Var(format!("__export_{}", idx.0)),
                value: state.acc.clone(),
            });
        }

        // === Property access ===
        B::Ldobjbyname(_, id) => {
            state.acc = Expr::MemberAccess {
                object: Box::new(state.acc.clone()),
                property: resolve_str(resolver, method_off, id),
            };
        }
        B::Stobjbyname(_, id, obj) => {
            stmts.push(Stmt::Assign {
                target: Expr::MemberAccess {
                    object: Box::new(state.get_reg(obj.0)),
                    property: resolve_str(resolver, method_off, id),
                },
                value: state.acc.clone(),
            });
        }
        B::Ldobjbyvalue(_, obj) => {
            state.acc = Expr::ComputedAccess {
                object: Box::new(state.get_reg(obj.0)),
                index: Box::new(state.acc.clone()),
            };
        }
        B::Stobjbyvalue(_, obj, key) => {
            stmts.push(Stmt::Assign {
                target: Expr::ComputedAccess {
                    object: Box::new(state.get_reg(obj.0)),
                    index: Box::new(state.get_reg(key.0)),
                },
                value: state.acc.clone(),
            });
        }
        B::Ldobjbyindex(_, idx) => {
            state.acc = Expr::ComputedAccess {
                object: Box::new(state.acc.clone()),
                index: Box::new(Expr::NumberLit(idx.0 as f64)),
            };
        }
        B::Stobjbyindex(_, obj, idx) => {
            stmts.push(Stmt::Assign {
                target: Expr::ComputedAccess {
                    object: Box::new(state.get_reg(obj.0)),
                    index: Box::new(Expr::NumberLit(idx.0 as f64)),
                },
                value: state.acc.clone(),
            });
        }
        B::Stownbyname(_, id, obj) | B::Definepropertybyname(_, id, obj) => {
            stmts.push(Stmt::Assign {
                target: Expr::MemberAccess {
                    object: Box::new(state.get_reg(obj.0)),
                    property: resolve_str(resolver, method_off, id),
                },
                value: state.acc.clone(),
            });
        }
        B::Stownbyindex(_, obj, idx) => {
            stmts.push(Stmt::Assign {
                target: Expr::ComputedAccess {
                    object: Box::new(state.get_reg(obj.0)),
                    index: Box::new(Expr::NumberLit(idx.0 as f64)),
                },
                value: state.acc.clone(),
            });
        }

        // === Binary operations ===
        B::Add2(_, r) => binary_op(state, r.0, BinOp::Add),
        B::Sub2(_, r) => binary_op(state, r.0, BinOp::Sub),
        B::Mul2(_, r) => binary_op(state, r.0, BinOp::Mul),
        B::Div2(_, r) => binary_op(state, r.0, BinOp::Div),
        B::Mod2(_, r) => binary_op(state, r.0, BinOp::Mod),
        B::Exp(_, r) => binary_op(state, r.0, BinOp::Exp),
        B::Eq(_, r) => binary_op(state, r.0, BinOp::Eq),
        B::Noteq(_, r) => binary_op(state, r.0, BinOp::NotEq),
        B::Stricteq(_, r) => binary_op(state, r.0, BinOp::StrictEq),
        B::Strictnoteq(_, r) => binary_op(state, r.0, BinOp::StrictNotEq),
        B::Less(_, r) => binary_op(state, r.0, BinOp::Lt),
        B::Greater(_, r) => binary_op(state, r.0, BinOp::Gt),
        B::Lesseq(_, r) => binary_op(state, r.0, BinOp::Le),
        B::Greatereq(_, r) => binary_op(state, r.0, BinOp::Ge),
        B::And2(_, r) => binary_op(state, r.0, BinOp::BitAnd),
        B::Or2(_, r) => binary_op(state, r.0, BinOp::BitOr),
        B::Xor2(_, r) => binary_op(state, r.0, BinOp::BitXor),
        B::Shl2(_, r) => binary_op(state, r.0, BinOp::Shl),
        B::Shr2(_, r) => binary_op(state, r.0, BinOp::Shr),
        B::Ashr2(_, r) => binary_op(state, r.0, BinOp::UShr),
        B::Instanceof(_, r) => {
            let obj = state.get_reg(r.0);
            state.acc = Expr::BinaryOp {
                op: BinOp::InstanceOf,
                lhs: Box::new(obj),
                rhs: Box::new(state.acc.clone()),
            };
        }
        B::Isin(_, r) => {
            let prop = state.get_reg(r.0);
            state.acc = Expr::BinaryOp {
                op: BinOp::In,
                lhs: Box::new(prop),
                rhs: Box::new(state.acc.clone()),
            };
        }

        // === Unary operations ===
        B::Neg(..) => unary_op(state, UnOp::Neg),
        B::Not(..) => unary_op(state, UnOp::Not),
        B::Tonumeric(..) | B::Tonumber(..) => {}
        B::Typeof(..) => {
            state.acc = Expr::TypeOf(Box::new(state.acc.clone()));
        }
        B::Inc(..) => unary_op(state, UnOp::Inc),
        B::Dec(..) => unary_op(state, UnOp::Dec),

        // === Calls ===
        B::Callarg0(_) => {
            let callee = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(callee),
                args: vec![],
            };
        }
        B::Callarg1(_, a0) => {
            let callee = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(callee),
                args: vec![state.get_reg(a0.0)],
            };
        }
        B::Callargs2(_, a0, a1) => {
            let callee = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(callee),
                args: vec![state.get_reg(a0.0), state.get_reg(a1.0)],
            };
        }
        B::Callargs3(_, a0, a1, a2) => {
            let callee = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(callee),
                args: vec![
                    state.get_reg(a0.0),
                    state.get_reg(a1.0),
                    state.get_reg(a2.0),
                ],
            };
        }
        B::Callrange(_, count, start) => {
            let callee = state.acc.clone();
            let args: Vec<Expr> = (0..count.0 as u16)
                .map(|i| state.get_reg(start.0 + i))
                .collect();
            state.acc = Expr::Call {
                callee: Box::new(callee),
                args,
            };
        }
        B::WideCallrange(count, start) => {
            let callee = state.acc.clone();
            let args: Vec<Expr> = (0..count.0 as u16)
                .map(|i| state.get_reg(start.0 + i))
                .collect();
            state.acc = Expr::Call {
                callee: Box::new(callee),
                args,
            };
        }
        B::Callthis0(_, this) => {
            let _this_val = state.get_reg(this.0);
            let method = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(method),
                args: vec![],
            };
        }
        B::Callthis1(_, this, a0) => {
            let _this_val = state.get_reg(this.0);
            let method = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(method),
                args: vec![state.get_reg(a0.0)],
            };
        }
        B::Callthis2(_, _this, a0, a1) => {
            let method = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(method),
                args: vec![state.get_reg(a0.0), state.get_reg(a1.0)],
            };
        }
        B::Callthis3(_, _this, a0, a1, a2) => {
            let method = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(method),
                args: vec![
                    state.get_reg(a0.0),
                    state.get_reg(a1.0),
                    state.get_reg(a2.0),
                ],
            };
        }
        B::Callthisrange(_, count, start) => {
            let args: Vec<Expr> = (1..count.0 as u16)
                .map(|i| state.get_reg(start.0 + i))
                .collect();
            let method = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(method),
                args,
            };
        }
        B::WideCallthisrange(count, start) => {
            let args: Vec<Expr> = (1..count.0 as u16)
                .map(|i| state.get_reg(start.0 + i))
                .collect();
            let method = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(method),
                args,
            };
        }
        B::Supercallarrowrange(_, count, start) | B::Supercallthisrange(_, count, start) => {
            let args: Vec<Expr> = (0..count.0 as u16)
                .map(|i| state.get_reg(start.0 + i))
                .collect();
            state.acc = Expr::SuperCall { args };
        }
        B::WideSupercallarrowrange(count, start) | B::WideSupercallthisrange(count, start) => {
            let args: Vec<Expr> = (0..count.0 as u16)
                .map(|i| state.get_reg(start.0 + i))
                .collect();
            state.acc = Expr::SuperCall { args };
        }
        B::Supercallspread(_, arg) => {
            state.acc = Expr::SuperCall {
                args: vec![Expr::Spread(Box::new(state.get_reg(arg.0)))],
            };
        }
        B::Apply(_, this_reg, args_reg) => {
            let this_val = state.get_reg(this_reg.0);
            let args_arr = state.get_reg(args_reg.0);
            let callee = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(Expr::MemberAccess {
                    object: Box::new(callee),
                    property: "apply".to_string(),
                }),
                args: vec![this_val, args_arr],
            };
        }

        // === New ===
        B::Newobjrange(_, count, start) => {
            let ctor = state.get_reg(start.0);
            let args: Vec<Expr> = (1..count.0 as u16)
                .map(|i| state.get_reg(start.0 + i))
                .collect();
            state.acc = Expr::New {
                callee: Box::new(ctor),
                args,
            };
        }
        B::WideNewobjrange(count, start) => {
            let ctor = state.get_reg(start.0);
            let args: Vec<Expr> = (1..count.0 as u16)
                .map(|i| state.get_reg(start.0 + i))
                .collect();
            state.acc = Expr::New {
                callee: Box::new(ctor),
                args,
            };
        }

        // === Object/Array creation ===
        B::Createemptyobject => state.acc = Expr::ObjectLit(vec![]),
        B::Createemptyarray(_) => state.acc = Expr::ArrayLit(vec![]),
        B::Createobjectwithbuffer(_, lit_id) | B::Createarraywithbuffer(_, lit_id) => {
            let is_array = matches!(insn.opcode, B::Createarraywithbuffer(..));
            if let Some(lit_arr) = resolver.resolve_literal_array(method_off, lit_id) {
                state.acc = if is_array {
                    resolve_array_buffer(&lit_arr, resolver)
                } else {
                    resolve_object_buffer(&lit_arr, resolver)
                };
            } else {
                state.acc = if is_array {
                    Expr::ArrayLit(vec![Expr::Unknown("...buffer".into())])
                } else {
                    Expr::ObjectLit(vec![(
                        PropKey::Ident("...buffer".into()),
                        Expr::Unknown("...".into()),
                    )])
                };
            }
        }
        B::Copyrestargs(idx) => {
            state.acc = Expr::Spread(Box::new(Expr::Var(format!("__rest_{}", idx.0))));
        }

        // === Returns ===
        B::Return => stmts.push(Stmt::Return(Some(state.acc.clone()))),
        B::Returnundefined => stmts.push(Stmt::Return(None)),

        // === Throw ===
        B::Throw => stmts.push(Stmt::Throw(state.acc.clone())),
        B::ThrowUndefinedifholewithname(..)
        | B::ThrowUndefinedifhole(..)
        | B::ThrowIfsupernotcorrectcall(..)
        | B::ThrowIfnotobject(..)
        | B::ThrowConstassignment(..)
        | B::ThrowNotexists
        | B::ThrowPatternnoncoercible
        | B::ThrowDeletesuperproperty => {}

        // === Boolean coercion ===
        B::CallruntimeIsfalse(..) => {
            state.acc = Expr::UnaryOp {
                op: UnOp::Not,
                expr: Box::new(state.acc.clone()),
            };
        }
        B::CallruntimeIstrue(..) => {}

        // === Function/class definition ===
        B::Definefunc(_, id, _) | B::Definemethod(_, id, _) => {
            let name = resolve_method_or_str(resolver, method_off, id);
            let clean = clean_abc_name(&name);
            let prefix = if matches!(insn.opcode, B::Definefunc(..)) {
                "func"
            } else {
                "method"
            };
            state.acc = Expr::Var(format!("/* {prefix} {clean} */"));
        }
        B::Defineclasswithbuffer(_, id, _, _, _) => {
            let name = resolve_method_or_str(resolver, method_off, id);
            state.acc = Expr::Var(format!("/* class */ {}", clean_abc_name(&name)));
        }

        // === Misc ===
        B::Ldhole => state.acc = Expr::Undefined,
        B::Ldfunction => state.acc = Expr::Var("__currentFunc".into()),
        B::Ldnewtarget => state.acc = Expr::NewTarget,
        B::Ldthis => state.acc = Expr::This,
        B::Debugger => stmts.push(Stmt::Debugger),
        B::Getpropiterator | B::Getiterator(..) | B::Getnextpropname(..) => {}
        B::Closeiterator(..) => {}
        B::Createregexpwithliteral(_, pattern_id, flags) => {
            let pattern = resolve_str(resolver, method_off, pattern_id);
            state.acc = Expr::Unknown(format!("/{pattern}/{}", decode_regex_flags(flags.0 as u32)));
        }
        B::Copydataproperties(src) => {
            state.acc = Expr::Call {
                callee: Box::new(Expr::MemberAccess {
                    object: Box::new(Expr::Var("Object".into())),
                    property: "assign".into(),
                }),
                args: vec![state.acc.clone(), state.get_reg(src.0)],
            };
        }
        B::Delobjprop(obj) => {
            stmts.push(Stmt::Expr(Expr::UnaryOp {
                op: UnOp::Delete,
                expr: Box::new(Expr::ComputedAccess {
                    object: Box::new(state.get_reg(obj.0)),
                    index: Box::new(state.acc.clone()),
                }),
            }));
        }
        B::Createobjectwithexcludedkeys(_, _count, start)
        | B::WideCreateobjectwithexcludedkeys(_, _count, start) => {
            let src = state.get_reg(start.0);
            state.acc = Expr::Call {
                callee: Box::new(Expr::MemberAccess {
                    object: Box::new(Expr::Var("Object".into())),
                    property: "assign".into(),
                }),
                args: vec![Expr::ObjectLit(vec![]), src],
            };
        }
        B::Definegettersetterbyvalue(obj, key, getter, setter) => {
            stmts.push(Stmt::Expr(Expr::Call {
                callee: Box::new(Expr::MemberAccess {
                    object: Box::new(Expr::Var("Object".into())),
                    property: "defineProperty".into(),
                }),
                args: vec![
                    state.get_reg(obj.0),
                    state.get_reg(key.0),
                    Expr::ObjectLit(vec![
                        (PropKey::Ident("get".into()), state.get_reg(getter.0)),
                        (PropKey::Ident("set".into()), state.get_reg(setter.0)),
                    ]),
                ],
            }));
        }

        // === Super property access ===
        B::Ldsuperbyname(_, id) => {
            state.acc = Expr::MemberAccess {
                object: Box::new(Expr::Var("super".into())),
                property: resolve_str(resolver, method_off, id),
            };
        }
        B::Stsuperbyname(_, id, _) => {
            stmts.push(Stmt::Assign {
                target: Expr::MemberAccess {
                    object: Box::new(Expr::Var("super".into())),
                    property: resolve_str(resolver, method_off, id),
                },
                value: state.acc.clone(),
            });
        }
        B::Ldsuperbyvalue(_, key) => {
            state.acc = Expr::ComputedAccess {
                object: Box::new(Expr::Var("super".into())),
                index: Box::new(state.get_reg(key.0)),
            };
        }

        // === Async/generator ===
        B::Asyncfunctionenter => {}
        B::Asyncfunctionresolve(..) => {}
        B::Asyncfunctionawaituncaught(..) => {
            state.acc = Expr::Await(Box::new(state.acc.clone()));
        }
        B::Asyncfunctionreject(..) => {}
        B::Suspendgenerator(..) => {
            state.acc = Expr::Yield(Box::new(state.acc.clone()));
        }
        B::Resumegenerator => {}
        B::Getresumemode => {}
        B::Asyncgeneratorresolve(..) => {
            state.acc = Expr::Yield(Box::new(state.acc.clone()));
        }
        B::Asyncgeneratorreject(..) => {}

        // === Dynamic import ===
        B::Dynamicimport => {
            state.acc = Expr::Call {
                callee: Box::new(Expr::Var("import".into())),
                args: vec![state.acc.clone()],
            };
        }

        // === Module ===
        B::Getmodulenamespace(idx) | B::WideGetmodulenamespace(idx) => {
            state.acc = Expr::Var(format!("__namespace_{}", idx.0));
        }
        B::CallruntimeLdlazymodulevar(idx) | B::CallruntimeLdlazysendablemodulevar(idx) => {
            state.acc = Expr::Var(format!("__lazy_module_{}", idx.0));
        }
        B::CallruntimeLdsendableexternalmodulevar(idx) => {
            state.acc = Expr::Var(format!("__sendable_module_{}", idx.0));
        }

        // === Misc ===
        B::Getunmappedargs => state.acc = Expr::Var("arguments".into()),
        B::Ldglobal => state.acc = Expr::Var("globalThis".into()),
        B::Stownbyvaluewithnameset(_, obj, key) => {
            stmts.push(Stmt::Assign {
                target: Expr::ComputedAccess {
                    object: Box::new(state.get_reg(obj.0)),
                    index: Box::new(state.get_reg(key.0)),
                },
                value: state.acc.clone(),
            });
        }
        B::Stownbynamewithnameset(_, id, obj) => {
            stmts.push(Stmt::Assign {
                target: Expr::MemberAccess {
                    object: Box::new(state.get_reg(obj.0)),
                    property: resolve_str(resolver, method_off, id),
                },
                value: state.acc.clone(),
            });
        }
        B::CallruntimeDefinesendableclass(..) | B::CallruntimeLdsendableclass(..) => {
            state.acc = Expr::Unknown("/* sendable class */".into());
        }
        B::CallruntimeDefinefieldbyvalue(..) | B::CallruntimeDefinefieldbyindex(..) => {}
        B::CallruntimeStsendablevar(_, idx) | B::CallruntimeWidestsendablevar(_, idx) => {
            stmts.push(Stmt::Assign {
                target: Expr::Var(format!("__sendable_{}", idx.0)),
                value: state.acc.clone(),
            });
        }
        B::CallruntimeLdsendablevar(_, idx) | B::CallruntimeWideldsendablevar(_, idx) => {
            state.acc = Expr::Var(format!("__sendable_{}", idx.0));
        }
        B::CallruntimeNotifyconcurrentresult | B::CallruntimeNewsendableenv(..) => {}
        B::Ldinfinity => state.acc = Expr::Var("Infinity".into()),
        B::Ldnan => state.acc = Expr::Var("NaN".into()),
        B::Ldsymbol => state.acc = Expr::Var("Symbol".into()),
        B::Starrayspread(..) => {}
        B::Nop => {}

        // === Jumps (handled by CFG) ===
        _ if insn.opcode.is_jump() => {}

        // === Catch all ===
        _ => {
            stmts.push(Stmt::Comment(format!("{}", insn.opcode)));
        }
    }
}

fn resolve_object_buffer(lit: &LiteralArray, resolver: &dyn StringResolver) -> Expr {
    let mut props = Vec::new();
    let entries = &lit.entries;
    let mut i = 0;
    while i + 1 < entries.len() {
        let (key_tag, key_val) = &entries[i];
        let (val_tag, val_val) = &entries[i + 1];
        if *key_tag == LiteralTag::MethodAffiliate || *val_tag == LiteralTag::MethodAffiliate {
            i += 2;
            continue;
        }
        let key = match key_val {
            LiteralValue::String(off) => {
                let s = resolver
                    .get_string_at_offset(*off)
                    .unwrap_or_else(|| format!("@{}", off.0));
                PropKey::Ident(s)
            }
            LiteralValue::Integer(n) => PropKey::Computed(Expr::NumberLit(*n as f64)),
            LiteralValue::Double(d) => PropKey::Computed(Expr::NumberLit(*d)),
            _ => PropKey::Computed(literal_value_to_expr(key_tag, key_val, resolver)),
        };
        let val = literal_value_to_expr(val_tag, val_val, resolver);
        props.push((key, val));
        i += 2;
    }
    Expr::ObjectLit(props)
}

fn resolve_array_buffer(lit: &LiteralArray, resolver: &dyn StringResolver) -> Expr {
    let mut elems = Vec::new();
    let entries = &lit.entries;
    let mut i = 0;
    while i + 1 < entries.len() {
        let (val_tag, val_val) = &entries[i + 1];
        elems.push(literal_value_to_expr(val_tag, val_val, resolver));
        i += 2;
    }
    Expr::ArrayLit(elems)
}

fn literal_value_to_expr(
    _tag: &LiteralTag,
    val: &LiteralValue,
    resolver: &dyn StringResolver,
) -> Expr {
    match val {
        LiteralValue::Bool(b) => Expr::BoolLit(*b),
        LiteralValue::Integer(n) => Expr::NumberLit(*n as f64),
        LiteralValue::Float(f) => Expr::NumberLit(*f as f64),
        LiteralValue::Double(d) => Expr::NumberLit(*d),
        LiteralValue::String(off) => {
            let s = resolver
                .get_string_at_offset(*off)
                .unwrap_or_else(|| format!("@{}", off.0));
            Expr::StringLit(s)
        }
        LiteralValue::Method(off) => Expr::Var(format!("/* method@{} */", off.0)),
        LiteralValue::Null => Expr::Null,
        LiteralValue::MethodAffiliate(_) => Expr::NumberLit(0.0),
        LiteralValue::TagValue(v) => Expr::NumberLit(*v as f64),
    }
}

fn decode_regex_flags(bits: u32) -> String {
    let mut flags = String::new();
    if bits & 0x01 != 0 {
        flags.push('g');
    }
    if bits & 0x02 != 0 {
        flags.push('i');
    }
    if bits & 0x04 != 0 {
        flags.push('m');
    }
    if bits & 0x08 != 0 {
        flags.push('s');
    }
    if bits & 0x10 != 0 {
        flags.push('u');
    }
    if bits & 0x20 != 0 {
        flags.push('y');
    }
    if bits & 0x40 != 0 {
        flags.push('d');
    }
    flags
}

pub fn clean_abc_name(name: &str) -> String {
    if let Some(pos) = name.rfind("=#") {
        return name[pos + 2..].to_string();
    }
    if let Some(pos) = name.rfind(">#") {
        let rest = &name[pos + 2..];
        if !rest.starts_with('@') && !rest.is_empty() {
            return sanitize_ident(rest);
        }
    }
    if name == "#*#" {
        return "anonymous".to_string();
    }
    if let Some(rest) = name.strip_prefix("#*#^") {
        return format!("anonymous_{}", sanitize_ident(rest));
    }
    if name.contains("*#") {
        if let Some(at_pos) = name.rfind('@') {
            let after_at = &name[at_pos + 1..];
            if let Some(star_pos) = after_at.find("*#") {
                let id = sanitize_ident(&after_at[..star_pos]);
                let suffix = &after_at[star_pos + 2..];
                return if suffix.is_empty() {
                    format!("anonymous_0x{id}")
                } else {
                    format!("anonymous_0x{}_{}", id, sanitize_ident(suffix))
                };
            }
        }
    }
    let cleaned = name
        .strip_prefix("#%#")
        .or_else(|| name.strip_prefix("#*#"))
        .or_else(|| name.strip_prefix("#"))
        .unwrap_or(name);
    sanitize_ident(cleaned)
}

fn sanitize_ident(s: &str) -> String {
    s.chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' || c == '$' {
                c
            } else {
                '_'
            }
        })
        .collect()
}
