use std::collections::HashMap;

use abcd_ir::expr::{BinOp, Expr, PropKey, UnOp};
use abcd_ir::instruction::{Instruction, Operand};
use abcd_ir::stmt::Stmt;
use abcd_parser::literal::{LiteralArray, LiteralTag, LiteralValue};

/// Resolves entity IDs to strings/names and literal arrays.
pub trait StringResolver {
    fn resolve_string(&self, method_off: u32, entity_id: u32) -> Option<String>;
    fn resolve_offset(&self, method_off: u32, entity_id: u32) -> Option<u32>;
    /// Resolve a literal array by its entity ID.
    fn resolve_literal_array(&self, _method_off: u32, _entity_id: u32) -> Option<LiteralArray> {
        None
    }
    /// Read a string at a raw file offset.
    fn get_string_at_offset(&self, _offset: u32) -> Option<String> {
        None
    }
    /// Resolve a method entity ID to its name.
    fn resolve_method_name(&self, _method_off: u32, _entity_id: u32) -> Option<String> {
        None
    }
}

/// Result of recovering expressions from a basic block.
pub struct BlockRecovery {
    pub stmts: Vec<Stmt>,
    /// The accumulator expression at the end of the block.
    pub final_acc: Expr,
    /// Register state at the end of the block.
    pub final_regs: HashMap<u16, Expr>,
}

/// Recover expressions from a sequence of instructions within a basic block.
pub fn recover_block(
    instructions: &[Instruction],
    resolver: &dyn StringResolver,
    method_off: u32,
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

/// Symbolic state: maps accumulator and registers to expressions.
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

/// Recover expressions with initial state from a predecessor block.
pub fn recover_block_with_state(
    instructions: &[Instruction],
    resolver: &dyn StringResolver,
    method_off: u32,
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
    // ArkCompiler register layout:
    // [v0..v(num_vregs-1)] [funcObj] [newTarget] [this] [arg0, arg1, ...]
    let r32 = r as u32;
    if r32 < num_vregs {
        // Local variable register
        Expr::Var(format!("r{}", r32 + 1))
    } else if r32 == num_vregs {
        // funcObj — internal, rarely referenced directly
        Expr::Var("__func__".into())
    } else if r32 == num_vregs + 1 {
        // newTarget
        Expr::NewTarget
    } else if r32 == num_vregs + 2 {
        // this
        Expr::This
    } else {
        // User parameters: p1, p2, ...
        let param_idx = r32 - num_vregs - 2;
        Expr::Var(format!("p{param_idx}"))
    }
}

fn get_imm(op: &Operand) -> i64 {
    match op {
        Operand::Imm(v) => *v,
        _ => 0,
    }
}

fn get_reg(op: &Operand) -> u16 {
    match op {
        Operand::Reg(r) => *r,
        _ => 0,
    }
}

fn get_entity_id(op: &Operand) -> u32 {
    match op {
        Operand::EntityId(id) => *id,
        _ => 0,
    }
}

fn resolve_str(resolver: &dyn StringResolver, method_off: u32, op: &Operand) -> String {
    if let Operand::EntityId(id) = op {
        resolver
            .resolve_string(method_off, *id)
            .unwrap_or_else(|| format!("@{id:#x}"))
    } else {
        format!("{op:?}")
    }
}

fn resolve_method_or_str(resolver: &dyn StringResolver, method_off: u32, op: &Operand) -> String {
    if let Operand::EntityId(id) = op {
        // Try method name resolution first, fall back to string resolution
        resolver
            .resolve_method_name(method_off, *id)
            .or_else(|| resolver.resolve_string(method_off, *id))
            .unwrap_or_else(|| format!("@{id:#x}"))
    } else {
        format!("{op:?}")
    }
}

/// Check if the current accumulator holds a side-effectful expression (call, new, etc.)
/// that would be lost if overwritten. If so, emit it as a statement.
fn flush_acc_side_effects(state: &mut ExprState, stmts: &mut Vec<Stmt>) {
    match &state.acc {
        Expr::Call { .. } | Expr::New { .. } | Expr::SuperCall { .. } => {
            stmts.push(Stmt::Expr(state.acc.clone()));
            state.acc = Expr::Undefined;
        }
        _ => {}
    }
}

/// Returns true if the instruction loads a constant/literal into acc,
/// discarding whatever was there before. This is the pattern where
/// side-effectful expressions (calls) get lost.
fn is_acc_replacing(mn: &str) -> bool {
    matches!(
        mn,
        "ldundefined"
            | "ldnull"
            | "ldtrue"
            | "ldfalse"
            | "ldai"
            | "fldai"
            | "lda.str"
            | "ldhole"
            | "ldinfinity"
            | "ldnan"
            | "ldsymbol"
            | "createemptyobject"
            | "createemptyarray"
            | "createobjectwithbuffer"
            | "createarraywithbuffer"
            | "wide.createobjectwithbuffer"
            | "wide.createarraywithbuffer"
            | "createregexpwithliteral"
    )
}

fn process_insn(
    insn: &Instruction,
    state: &mut ExprState,
    stmts: &mut Vec<Stmt>,
    resolver: &dyn StringResolver,
    method_off: u32,
) {
    let mn = insn.opcode.mnemonic();
    let ops = &insn.operands;

    // If this instruction will replace acc with a non-derived value,
    // flush any side-effectful expression currently in acc.
    if is_acc_replacing(mn) {
        flush_acc_side_effects(state, stmts);
    }

    match mn {
        // === Load constants ===
        "ldundefined" => state.acc = Expr::Undefined,
        "ldnull" => state.acc = Expr::Null,
        "ldtrue" => state.acc = Expr::BoolLit(true),
        "ldfalse" => state.acc = Expr::BoolLit(false),
        "ldai" => state.acc = Expr::NumberLit(get_imm(&ops[0]) as f64),
        "fldai" => {
            if let Operand::FloatImm(f) = &ops[0] {
                state.acc = Expr::NumberLit(*f);
            }
        }
        "lda.str" => {
            let s = resolve_str(resolver, method_off, &ops[0]);
            state.acc = Expr::StringLit(s);
        }
        "lda" => {
            let r = get_reg(&ops[0]);
            state.acc = state.get_reg(r);
        }
        "sta" => {
            let r = get_reg(&ops[0]);
            state.set_reg(r, state.acc.clone());
        }
        "mov" => {
            let dst = get_reg(&ops[0]);
            let src = get_reg(&ops[1]);
            state.set_reg(dst, state.get_reg(src));
        }

        // === Lexical variables ===
        "ldlexvar" => {
            let level = get_imm(&ops[0]);
            let slot = get_imm(&ops[1]);
            state.acc = Expr::Var(format!("x_{}_{}", level + 1, slot + 1));
        }
        "stlexvar" => {
            let level = get_imm(&ops[0]);
            let slot = get_imm(&ops[1]);
            stmts.push(Stmt::Assign {
                target: Expr::Var(format!("x_{}_{}", level + 1, slot + 1)),
                value: state.acc.clone(),
            });
        }
        "newlexenv" | "newlexenvwithname" => {
            // Creates a new lexical environment — we track this as a comment
        }
        "poplexenv" => {}

        // === Global/module access ===
        "tryldglobalbyname" | "ldglobalvar" => {
            // ops[0] = IC slot, ops[1] = string ID
            let name = resolve_str(resolver, method_off, &ops[1]);
            state.acc = Expr::Var(name);
        }
        "trystglobalbyname" | "stglobalvar" => {
            let name = resolve_str(resolver, method_off, &ops[1]);
            stmts.push(Stmt::Assign {
                target: Expr::Var(name),
                value: state.acc.clone(),
            });
        }
        "ldexternalmodulevar" | "wide.ldexternalmodulevar" => {
            let idx = get_imm(&ops[0]);
            state.acc = Expr::Var(format!("__module_{idx}"));
        }
        "ldlocalmodulevar" | "wide.ldlocalmodulevar" => {
            let idx = get_imm(&ops[0]);
            state.acc = Expr::Var(format!("__local_module_{idx}"));
        }
        "stmodulevar" | "wide.stmodulevar" => {
            let idx = get_imm(&ops[0]);
            stmts.push(Stmt::Assign {
                target: Expr::Var(format!("__export_{idx}")),
                value: state.acc.clone(),
            });
        }

        // === Property access ===
        "ldobjbyname" => {
            // ops[0] = IC slot, ops[1] = string ID
            let name = resolve_str(resolver, method_off, &ops[1]);
            state.acc = Expr::MemberAccess {
                object: Box::new(state.acc.clone()),
                property: name,
            };
        }
        "stobjbyname" => {
            let name = resolve_str(resolver, method_off, &ops[1]);
            let obj = state.get_reg(get_reg(&ops[2]));
            stmts.push(Stmt::Assign {
                target: Expr::MemberAccess {
                    object: Box::new(obj),
                    property: name,
                },
                value: state.acc.clone(),
            });
        }
        "ldobjbyvalue" => {
            let obj = state.get_reg(get_reg(&ops[1]));
            state.acc = Expr::ComputedAccess {
                object: Box::new(obj),
                index: Box::new(state.acc.clone()),
            };
        }
        "stobjbyvalue" => {
            let obj = state.get_reg(get_reg(&ops[1]));
            let key = state.get_reg(get_reg(&ops[2]));
            stmts.push(Stmt::Assign {
                target: Expr::ComputedAccess {
                    object: Box::new(obj),
                    index: Box::new(key),
                },
                value: state.acc.clone(),
            });
        }
        "ldobjbyindex" => {
            let idx = get_imm(&ops[0]);
            state.acc = Expr::ComputedAccess {
                object: Box::new(state.acc.clone()),
                index: Box::new(Expr::NumberLit(idx as f64)),
            };
        }
        "stobjbyindex" => {
            let idx = get_imm(&ops[1]);
            let obj = state.get_reg(get_reg(&ops[2]));
            stmts.push(Stmt::Assign {
                target: Expr::ComputedAccess {
                    object: Box::new(obj),
                    index: Box::new(Expr::NumberLit(idx as f64)),
                },
                value: state.acc.clone(),
            });
        }
        "stownbyname" => {
            let name = resolve_str(resolver, method_off, &ops[1]);
            let obj = state.get_reg(get_reg(&ops[2]));
            stmts.push(Stmt::Assign {
                target: Expr::MemberAccess {
                    object: Box::new(obj),
                    property: name,
                },
                value: state.acc.clone(),
            });
        }
        "stownbyindex" => {
            let idx = get_imm(&ops[1]);
            let obj = state.get_reg(get_reg(&ops[2]));
            stmts.push(Stmt::Assign {
                target: Expr::ComputedAccess {
                    object: Box::new(obj),
                    index: Box::new(Expr::NumberLit(idx as f64)),
                },
                value: state.acc.clone(),
            });
        }
        "definepropertybyname" => {
            let name = resolve_str(resolver, method_off, &ops[1]);
            let obj = state.get_reg(get_reg(&ops[2]));
            stmts.push(Stmt::Assign {
                target: Expr::MemberAccess {
                    object: Box::new(obj),
                    property: name,
                },
                value: state.acc.clone(),
            });
        }

        // === Binary operations ===
        "add2" => binary_op(state, ops, BinOp::Add),
        "sub2" => binary_op(state, ops, BinOp::Sub),
        "mul2" => binary_op(state, ops, BinOp::Mul),
        "div2" => binary_op(state, ops, BinOp::Div),
        "mod2" => binary_op(state, ops, BinOp::Mod),
        "exp" => binary_op(state, ops, BinOp::Exp),
        "eq" => binary_op(state, ops, BinOp::Eq),
        "noteq" => binary_op(state, ops, BinOp::NotEq),
        "stricteq" => binary_op(state, ops, BinOp::StrictEq),
        "strictnoteq" => binary_op(state, ops, BinOp::StrictNotEq),
        "less" => binary_op(state, ops, BinOp::Lt),
        "greater" => binary_op(state, ops, BinOp::Gt),
        "lesseq" => binary_op(state, ops, BinOp::Le),
        "greatereq" => binary_op(state, ops, BinOp::Ge),
        "and2" => binary_op(state, ops, BinOp::BitAnd),
        "or2" => binary_op(state, ops, BinOp::BitOr),
        "xor2" => binary_op(state, ops, BinOp::BitXor),
        "shl2" => binary_op(state, ops, BinOp::Shl),
        "shr2" => binary_op(state, ops, BinOp::Shr),
        "ashr2" => binary_op(state, ops, BinOp::UShr),
        "in" => binary_op(state, ops, BinOp::In),
        "instanceof" => {
            // instanceof: acc = (v_reg instanceof acc)
            let obj = state.get_reg(get_reg(&ops[1]));
            state.acc = Expr::BinaryOp {
                op: BinOp::InstanceOf,
                lhs: Box::new(obj),
                rhs: Box::new(state.acc.clone()),
            };
        }

        // === Unary operations ===
        "neg" => unary_op(state, UnOp::Neg),
        "not" => unary_op(state, UnOp::Not),
        "tonumeric" | "tonumber" => { /* type coercion, keep acc */ }
        "typeof" | "typeof.imm8" | "typeof.imm16" => {
            state.acc = Expr::TypeOf(Box::new(state.acc.clone()));
        }
        "inc" => unary_op(state, UnOp::Inc),
        "dec" => unary_op(state, UnOp::Dec),

        // === Calls ===
        "callarg0" => {
            // callarg0 ic_slot — call acc with no args
            let callee = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(callee),
                args: vec![],
            };
        }
        "callarg1" => {
            // callarg1 ic_slot, v0
            let callee = state.acc.clone();
            let a0 = state.get_reg(get_reg(&ops[1]));
            state.acc = Expr::Call {
                callee: Box::new(callee),
                args: vec![a0],
            };
        }
        "callargs2" => {
            let callee = state.acc.clone();
            let a0 = state.get_reg(get_reg(&ops[1]));
            let a1 = state.get_reg(get_reg(&ops[2]));
            state.acc = Expr::Call {
                callee: Box::new(callee),
                args: vec![a0, a1],
            };
        }
        "callargs3" => {
            let callee = state.acc.clone();
            let a0 = state.get_reg(get_reg(&ops[1]));
            let a1 = state.get_reg(get_reg(&ops[2]));
            let a2 = state.get_reg(get_reg(&ops[3]));
            state.acc = Expr::Call {
                callee: Box::new(callee),
                args: vec![a0, a1, a2],
            };
        }
        "callrange" | "wide.callrange" => {
            // callrange ic_slot, imm_count, v_start
            let callee = state.acc.clone();
            let count = get_imm(&ops[1]) as u16;
            let start = get_reg(&ops[2]);
            let args: Vec<Expr> = (0..count).map(|i| state.get_reg(start + i)).collect();
            state.acc = Expr::Call {
                callee: Box::new(callee),
                args,
            };
        }
        "callthis0" => {
            // callthis0 ic_slot, v_this
            let _this_reg = get_reg(&ops[1]);
            let _this_val = state.get_reg(_this_reg);
            // acc holds the method reference (from ldobjbyname)
            let method = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(method),
                args: vec![],
            };
        }
        "callthis1" => {
            let _this_reg = get_reg(&ops[1]);
            let a0 = state.get_reg(get_reg(&ops[2]));
            let method = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(method),
                args: vec![a0],
            };
        }
        "callthis2" => {
            let a0 = state.get_reg(get_reg(&ops[2]));
            let a1 = state.get_reg(get_reg(&ops[3]));
            let method = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(method),
                args: vec![a0, a1],
            };
        }
        "callthis3" => {
            let a0 = state.get_reg(get_reg(&ops[2]));
            let a1 = state.get_reg(get_reg(&ops[3]));
            let a2 = state.get_reg(get_reg(&ops[4]));
            let method = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(method),
                args: vec![a0, a1, a2],
            };
        }
        "callthisrange" | "wide.callthisrange" => {
            let count = get_imm(&ops[1]) as u16;
            let start = get_reg(&ops[2]);
            // first reg is `this`, rest are args
            let args: Vec<Expr> = (1..count).map(|i| state.get_reg(start + i)).collect();
            let method = state.acc.clone();
            state.acc = Expr::Call {
                callee: Box::new(method),
                args,
            };
        }
        "supercallarrowrange"
        | "wide.supercallarrowrange"
        | "supercallthisrange"
        | "wide.supercallthisrange" => {
            let count = get_imm(&ops[1]) as u16;
            let start = get_reg(&ops[2]);
            let args: Vec<Expr> = (0..count).map(|i| state.get_reg(start + i)).collect();
            state.acc = Expr::SuperCall { args };
        }
        "supercallspread" => {
            let arg = state.get_reg(get_reg(&ops[1]));
            state.acc = Expr::SuperCall {
                args: vec![Expr::Spread(Box::new(arg))],
            };
        }
        "apply" => {
            let this_val = state.get_reg(get_reg(&ops[1]));
            let args_arr = state.get_reg(get_reg(&ops[2]));
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
        "newobjrange" | "wide.newobjrange" => {
            let count = get_imm(&ops[1]) as u16;
            let start = get_reg(&ops[2]);
            // First reg is the constructor, rest are args
            let ctor = state.get_reg(start);
            let args: Vec<Expr> = (1..count).map(|i| state.get_reg(start + i)).collect();
            state.acc = Expr::New {
                callee: Box::new(ctor),
                args,
            };
        }

        // === Object/Array creation ===
        "createemptyobject" => {
            state.acc = Expr::ObjectLit(vec![]);
        }
        "createemptyarray" => {
            state.acc = Expr::ArrayLit(vec![]);
        }
        "createobjectwithbuffer"
        | "createarraywithbuffer"
        | "wide.createobjectwithbuffer"
        | "wide.createarraywithbuffer" => {
            // ops[0] = IC slot, ops[1] = literal array ID
            let lit_id = if ops.len() >= 2 {
                get_entity_id(&ops[1])
            } else {
                0
            };
            if let Some(lit_arr) = resolver.resolve_literal_array(method_off, lit_id) {
                if mn.contains("array") {
                    state.acc = resolve_array_buffer(&lit_arr, resolver);
                } else {
                    state.acc = resolve_object_buffer(&lit_arr, resolver);
                }
            } else {
                state.acc = if mn.contains("array") {
                    Expr::ArrayLit(vec![Expr::Unknown("...buffer".into())])
                } else {
                    Expr::ObjectLit(vec![(
                        PropKey::Ident("...buffer".into()),
                        Expr::Unknown("...".into()),
                    )])
                };
            }
        }
        "copyrestargs" => {
            let idx = get_imm(&ops[0]);
            state.acc = Expr::Spread(Box::new(Expr::Var(format!("__rest_{idx}"))));
        }

        // === Returns ===
        "return" => {
            stmts.push(Stmt::Return(Some(state.acc.clone())));
        }
        "returnundefined" => {
            stmts.push(Stmt::Return(None));
        }

        // === Throw ===
        "throw" => {
            stmts.push(Stmt::Throw(state.acc.clone()));
        }
        "throw.undefinedifholewithname" | "throw.undefinedifhole" => {
            // TDZ check — we can skip this in output, it's a runtime check
        }
        "throw.ifsupernotcorrectcall"
        | "throw.ifnotobject"
        | "throw.constassignment"
        | "throw.notexists"
        | "throw.patternnoncoercible"
        | "throw.deletesuperproperty" => {
            // Runtime checks — skip in decompiled output
        }

        // === Boolean coercion ===
        "callruntime.isfalse" => {
            // isfalse(x) returns true if x is falsy → equivalent to !x
            state.acc = Expr::UnaryOp {
                op: UnOp::Not,
                expr: Box::new(state.acc.clone()),
            };
        }
        "callruntime.istrue" => {
            // istrue(x) returns true if x is truthy → keep acc as-is (boolean coercion)
        }

        // === Function/class definition ===
        "definefunc" | "wide.definefunc" => {
            let name = resolve_method_or_str(resolver, method_off, &ops[1]);
            let clean = clean_abc_name(&name);
            state.acc = Expr::Var(format!("/* func {clean} */"));
        }
        "definemethod" | "wide.definemethod" => {
            let name = resolve_method_or_str(resolver, method_off, &ops[1]);
            let clean = clean_abc_name(&name);
            state.acc = Expr::Var(format!("/* method {clean} */"));
        }
        "defineclasswithbuffer" | "wide.defineclasswithbuffer" => {
            let name = resolve_method_or_str(resolver, method_off, &ops[1]);
            let clean = clean_abc_name(&name);
            state.acc = Expr::Var(format!("/* class */ {clean}"));
        }

        // === Misc ===
        "ldhole" => state.acc = Expr::Undefined,
        "ldfunction" => state.acc = Expr::Var("__currentFunc".into()),
        "ldnewtarget" => state.acc = Expr::NewTarget,
        "ldthis" => state.acc = Expr::This,
        "debugger" => stmts.push(Stmt::Debugger),
        "getpropiterator" | "getiterator" | "getnextpropname" => {
            // Iterator ops — keep acc, will be structured later
        }
        "closeiterator" => {}
        "createregexpwithliteral" => {
            let pattern = resolve_str(resolver, method_off, &ops[1]);
            let flags_bits = get_imm(&ops[2]) as u32;
            let flags = decode_regex_flags(flags_bits);
            state.acc = Expr::Unknown(format!("/{pattern}/{flags}"));
        }
        "isin" => {
            let prop = state.get_reg(get_reg(&ops[1]));
            state.acc = Expr::BinaryOp {
                op: BinOp::In,
                lhs: Box::new(prop),
                rhs: Box::new(state.acc.clone()),
            };
        }
        "isundefined" | "isundefinedornull" => {
            state.acc = Expr::BinaryOp {
                op: BinOp::StrictEq,
                lhs: Box::new(state.acc.clone()),
                rhs: Box::new(Expr::Undefined),
            };
        }
        "copydataproperties" => {
            // copydataproperties v_src — Object.assign(acc, v_src)
            let src = state.get_reg(get_reg(&ops[0]));
            state.acc = Expr::Call {
                callee: Box::new(Expr::MemberAccess {
                    object: Box::new(Expr::Var("Object".into())),
                    property: "assign".into(),
                }),
                args: vec![state.acc.clone(), src],
            };
        }
        "delobjprop" => {
            let obj = state.get_reg(get_reg(&ops[0]));
            stmts.push(Stmt::Expr(Expr::UnaryOp {
                op: UnOp::Delete,
                expr: Box::new(Expr::ComputedAccess {
                    object: Box::new(obj),
                    index: Box::new(state.acc.clone()),
                }),
            }));
        }
        "createobjectwithexcludedkeys" | "wide.createobjectwithexcludedkeys" => {
            // Create object from source excluding certain keys
            let _count = get_imm(&ops[0]) as u16;
            let start = get_reg(&ops[1]);
            let src = state.get_reg(start);
            state.acc = Expr::Call {
                callee: Box::new(Expr::MemberAccess {
                    object: Box::new(Expr::Var("Object".into())),
                    property: "assign".into(),
                }),
                args: vec![Expr::ObjectLit(vec![]), src],
            };
        }

        // === Conditional jumps (handled by CFG, but we note the condition) ===
        "jeqz" | "jnez" | "jmp" | "jstricteqz" | "jnstricteqz" | "jeqnull" | "jnenull"
        | "jstricteq" | "jnstricteq" | "jeq" | "jne" | "jlt" | "jle" | "jgt" | "jge"
        | "wide.jeqz" | "wide.jnez" | "wide.jmp" => {
            // Control flow — handled at CFG level
        }

        // === No-ops and runtime checks ===
        "nop" => {}

        // === Getter/setter ===
        "definegettersetterbyvalue" => {
            // definegettersetterbyvalue v_obj, v_key, v_getter, v_setter (acc = needSet flag)
            let obj = state.get_reg(get_reg(&ops[0]));
            let key = state.get_reg(get_reg(&ops[1]));
            let getter = state.get_reg(get_reg(&ops[2]));
            let setter = state.get_reg(get_reg(&ops[3]));
            stmts.push(Stmt::Expr(Expr::Call {
                callee: Box::new(Expr::MemberAccess {
                    object: Box::new(Expr::Var("Object".into())),
                    property: "defineProperty".into(),
                }),
                args: vec![
                    obj,
                    key,
                    Expr::ObjectLit(vec![
                        (abcd_ir::expr::PropKey::Ident("get".into()), getter),
                        (abcd_ir::expr::PropKey::Ident("set".into()), setter),
                    ]),
                ],
            }));
        }

        // === Super property access ===
        "ldsuperbyname" => {
            let name = resolve_str(resolver, method_off, &ops[1]);
            state.acc = Expr::MemberAccess {
                object: Box::new(Expr::Var("super".into())),
                property: name,
            };
        }
        "stsuperbyname" => {
            let name = resolve_str(resolver, method_off, &ops[1]);
            stmts.push(Stmt::Assign {
                target: Expr::MemberAccess {
                    object: Box::new(Expr::Var("super".into())),
                    property: name,
                },
                value: state.acc.clone(),
            });
        }
        "ldsuperbyvalue" => {
            let key = state.get_reg(get_reg(&ops[1]));
            state.acc = Expr::ComputedAccess {
                object: Box::new(Expr::Var("super".into())),
                index: Box::new(key),
            };
        }

        // === Array spread ===
        "starrayspread" => {
            // starrayspread v_array, v_index — spread acc into array
            // Keep acc as-is, this is an internal operation
        }

        // === Async/generator ===
        "asyncfunctionenter" => {}
        "asyncfunctionresolve" => {
            // Async function resolve — the acc is the resolved value
        }
        "asyncfunctionawaituncaught" => {
            // asyncfunctionawaituncaught v_asyncGen — await acc
            // acc holds the promise to await, v_asyncGen is the async generator object
            state.acc = Expr::Await(Box::new(state.acc.clone()));
        }
        "asyncfunctionreject" => {}
        "suspendgenerator" => {
            // suspendgenerator v_genObj — yield acc
            state.acc = Expr::Yield(Box::new(state.acc.clone()));
        }
        "resumegenerator" => {
            // Result of yield — keep acc
        }
        "getresumemode" => {
            // Internal generator resume mode check
        }
        "asyncgeneratorresolve" => {
            // yield in async generator
            state.acc = Expr::Yield(Box::new(state.acc.clone()));
        }
        "asyncgeneratorreject" => {}

        // === Dynamic import ===
        "dynamicimport" => {
            state.acc = Expr::Call {
                callee: Box::new(Expr::Var("import".into())),
                args: vec![state.acc.clone()],
            };
        }

        // === Module ===
        "getmodulenamespace" | "wide.getmodulenamespace" => {
            let idx = get_imm(&ops[0]);
            state.acc = Expr::Var(format!("__namespace_{idx}"));
        }
        "callruntime.ldlazymodulevar" | "callruntime.ldlazysendablemodulevar" => {
            let idx = get_imm(&ops[0]);
            state.acc = Expr::Var(format!("__lazy_module_{idx}"));
        }
        "callruntime.ldsendableexternalmodulevar" => {
            let idx = get_imm(&ops[0]);
            state.acc = Expr::Var(format!("__sendable_module_{idx}"));
        }

        // === Misc ===
        "getunmappedargs" => {
            state.acc = Expr::Var("arguments".into());
        }
        "ldglobal" => {
            state.acc = Expr::Var("globalThis".into());
        }
        "stownbyvaluewithnameset" | "stownbynamewithnameset" => {
            // Similar to stownbyname but sets the function name
            if mn.contains("byvalue") {
                let obj = state.get_reg(get_reg(&ops[1]));
                let key = state.get_reg(get_reg(&ops[2]));
                stmts.push(Stmt::Assign {
                    target: Expr::ComputedAccess {
                        object: Box::new(obj),
                        index: Box::new(key),
                    },
                    value: state.acc.clone(),
                });
            } else {
                let name = resolve_str(resolver, method_off, &ops[1]);
                let obj = state.get_reg(get_reg(&ops[2]));
                stmts.push(Stmt::Assign {
                    target: Expr::MemberAccess {
                        object: Box::new(obj),
                        property: name,
                    },
                    value: state.acc.clone(),
                });
            }
        }
        "callruntime.definesendableclass" | "callruntime.ldsendableclass" => {
            state.acc = Expr::Unknown(format!("/* sendable class */"));
        }
        "callruntime.definefieldbyvalue" | "callruntime.definefieldbyindex" => {
            // Field definition — similar to definepropertybyname
        }
        "callruntime.stsendablevar" | "callruntime.ldsendablevar" => {
            let idx = get_imm(&ops[0]);
            if mn.contains("st") {
                stmts.push(Stmt::Assign {
                    target: Expr::Var(format!("__sendable_{idx}")),
                    value: state.acc.clone(),
                });
            } else {
                state.acc = Expr::Var(format!("__sendable_{idx}"));
            }
        }
        "callruntime.notifyconcurrentresult" | "callruntime.newsendableenv" => {}
        "wide.stlexvar" => {
            let level = get_imm(&ops[0]);
            let slot = get_imm(&ops[1]);
            stmts.push(Stmt::Assign {
                target: Expr::Var(format!("x_{}_{}", level + 1, slot + 1)),
                value: state.acc.clone(),
            });
        }
        "wide.ldlexvar" => {
            let level = get_imm(&ops[0]);
            let slot = get_imm(&ops[1]);
            state.acc = Expr::Var(format!("x_{}_{}", level + 1, slot + 1));
        }
        "wide.newlexenv" | "wide.newlexenvwithname" => {}
        "ldinfinity" => {
            state.acc = Expr::Var("Infinity".into());
        }
        "ldnan" => {
            state.acc = Expr::Var("NaN".into());
        }
        "ldsymbol" => {
            state.acc = Expr::Var("Symbol".into());
        }

        // === Catch all ===
        _ => {
            // Emit as unknown for opcodes we haven't handled yet
            let ops_str: Vec<String> = ops.iter().map(|o| format!("{o:?}")).collect();
            stmts.push(Stmt::Comment(format!("{mn} {}", ops_str.join(", "))));
        }
    }
}

fn binary_op(state: &mut ExprState, ops: &[Operand], op: BinOp) {
    // Binary ops: acc = acc op v_reg
    // Format: op ic_slot, v_reg
    let rhs_idx = if ops.len() >= 2 { 1 } else { 0 };
    let rhs = if let Some(Operand::Reg(r)) = ops.get(rhs_idx) {
        state.get_reg(*r)
    } else {
        Expr::Unknown("?".into())
    };
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

/// Convert a literal array into an Expr::ObjectLit.
/// Entries come in pairs: [key_tag, key_val, value_tag, value_val, ...]
/// Method entries are followed by MethodAffiliate entries (skip those).
fn resolve_object_buffer(lit: &LiteralArray, resolver: &dyn StringResolver) -> Expr {
    let mut props = Vec::new();
    let entries = &lit.entries;
    let mut i = 0;
    while i + 1 < entries.len() {
        let (key_tag, key_val) = &entries[i];
        let (val_tag, val_val) = &entries[i + 1];

        // Skip MethodAffiliate entries (they follow Method entries)
        if *key_tag == LiteralTag::MethodAffiliate || *val_tag == LiteralTag::MethodAffiliate {
            i += 2;
            continue;
        }

        let key = match key_val {
            LiteralValue::String(off) => {
                let s = resolver
                    .get_string_at_offset(*off)
                    .unwrap_or_else(|| format!("@{off:#x}"));
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

/// Convert a literal array into an Expr::ArrayLit.
/// Entries come in pairs: [index_tag, index_val, value_tag, value_val, ...]
/// We only care about the values (odd-indexed entries).
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
                .unwrap_or_else(|| format!("@{off:#x}"));
            Expr::StringLit(s)
        }
        LiteralValue::Method(off) => Expr::Var(format!("/* method@{off:#x} */")),
        LiteralValue::Null => Expr::Null,
        LiteralValue::MethodAffiliate(_) => Expr::NumberLit(0.0),
        LiteralValue::TagValue(v) => Expr::NumberLit(*v as f64),
    }
}

/// Decode regex flag bitmask to flag string.
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

/// Clean up ABC internal names to readable form.
pub fn clean_abc_name(name: &str) -> String {
    // Constructor: `=#ClassName`
    if let Some(pos) = name.rfind("=#") {
        return name[pos + 2..].to_string();
    }
    // Named method: `>#methodName` (not followed by @)
    if let Some(pos) = name.rfind(">#") {
        let rest = &name[pos + 2..];
        if !rest.starts_with('@') && !rest.is_empty() {
            return sanitize_ident(rest);
        }
    }
    // Anonymous patterns
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
    // General cleanup: strip common prefixes and sanitize
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
