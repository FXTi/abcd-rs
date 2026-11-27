//! Instruction-to-statement lowering and iterative `RecStep` expression recovery.

use super::*;

impl<'a> Recover<'a> {
    /// One instruction → statement(s) (or nothing, when inlined/dead).
    pub(super) fn step_inst(
        &mut self,
        iid: InstId,
        op: &Op,
        loc: Option<Loc>,
        block: BlockId,
        out: &mut Vec<Stmt>,
        phi_tail: &mut Vec<PendingPhiAssign>,
    ) {
        // 0. Guards that must stay EXECUTABLE (N74-W4): the blanket
        //    elision below is only sound when the emitted source
        //    reproduces the guard's semantics, which fails for:
        //    - `ThrowConstAssignment`: es2abc emits it at a const-store
        //      site; it fires unconditionally when reached. The elision
        //      reason claims "the const binding is reconstructed", but
        //      d-P8 reconstructs lexical bindings as `let`, so the store
        //      would silently succeed (test262 class/name-binding/const).
        //    - `ThrowUndefinedIfHole{,WithName}` whose checked value is
        //      PROVABLY the hole constant: the read IS the TDZ
        //      violation, firing unconditionally (test262 let/const
        //      *-before-initialization rows). A guard whose value is not
        //      provably the hole keeps the §5 elision (the common case:
        //      reads es2abc could not prove post-init statically).
        match op {
            Op::ThrowConstAssignment { name } => {
                self.record(op, Outcome::Expressed);
                let label = match &self.expr_of(*name) {
                    Expr::Lit(Lit::String(s)) => format!(" '{s}'"),
                    _ => String::new(),
                };
                out.push(Stmt::Throw(new_error(
                    "TypeError",
                    format!("Assignment to constant variable{label}."),
                )));
                return;
            }
            Op::ThrowUndefinedIfHoleWithName { name, value }
                if provably_hole(self.module, *value) =>
            {
                self.record(op, Outcome::Expressed);
                let n = sym_str(self.module, *name);
                out.push(Stmt::Throw(new_error(
                    "ReferenceError",
                    format!("Cannot access '{n}' before initialization"),
                )));
                return;
            }
            Op::ThrowUndefinedIfHole { name, value } if provably_hole(self.module, *value) => {
                self.record(op, Outcome::Expressed);
                let label = match &self.expr_of(*name) {
                    Expr::Lit(Lit::String(s)) => s.clone(),
                    _ => "binding".to_string(),
                };
                out.push(Stmt::Throw(new_error(
                    "ReferenceError",
                    format!("Cannot access '{label}' before initialization"),
                )));
                return;
            }
            Op::ThrowNotExists => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Throw(new_error(
                    "ReferenceError",
                    "Variable does not exist".to_string(),
                )));
                return;
            }
            Op::ThrowPatternNonCoercible => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Throw(new_error(
                    "TypeError",
                    "Cannot destructure undefined or null".to_string(),
                )));
                return;
            }
            _ => {}
        }

        // 1. Deliberately elided ops (guards, async entry).
        if let Some(reason) = elision_reason(op) {
            self.record(op, Outcome::Elided);
            out.push(Stmt::Elided {
                op: op_name(op),
                reason,
                loc,
            });
            // AsyncFunctionEnter has a result; if something unexpectedly
            // uses it, bind a loud fallback temp.
            if let Some(result) = self.inst_result(iid)
                && !self.chains.all_users(result).is_empty()
            {
                let name = self.mint_temp(result);
                out.push(Stmt::Declare {
                    name,
                    mutable: false,
                    value: Expr::Fallback {
                        op: op_name(op),
                        note: "async-context value used after elided AsyncFunctionEnter",
                        operands: vec![],
                    },
                    value_id: result,
                });
            }
            return;
        }

        // 1b. B2 class-field fold: the ctor's instance-initializer call
        // is elided when the fold moved its constant private-field
        // definitions into class-field declarations (emit prints
        // `#name = <const>;` — JS class fields initialize at
        // construction, when the ctor ran the initializer).
        if matches!(op, Op::Call { .. }) && self.folded_init_call(iid) {
            self.record(op, Outcome::Elided);
            out.push(Stmt::Elided {
                op: op_name(op),
                reason: "instance-initializer call — es2abc class-field lowering reversed (constant #field definitions are class-field declarations)",
                loc,
            });
            return;
        }

        // 2. Phi → temporary + per-predecessor assignments.
        if let Op::Phi { entries } = op {
            self.record(op, Outcome::Expressed);
            let Some(result) = self.inst_result(iid) else {
                return;
            };
            let name = self.mint_temp(result);
            out.push(Stmt::PhiDecl {
                name: name.clone(),
                value_id: result,
            });
            for (edge, v) in entries {
                let value = if edge.kind == EdgeKind::Exceptional
                    && self.is_derived_ctor
                    && matches!(
                        self.module.value(chase_mov(self.module, *v)),
                        Some(Value {
                            def: ValueDef::Param(i),
                            ..
                        }) if self.param_names.get(*i as usize).is_some_and(|n| n == "this")
                    ) {
                    Expr::Lit(Lit::Undefined)
                } else {
                    self.expr_of(*v)
                };
                phi_tail.push(PendingPhiAssign {
                    pred: edge.from,
                    to: block,
                    exceptional: edge.kind == EdgeKind::Exceptional,
                    target: name.clone(),
                    value,
                });
            }
            return;
        }

        // 3. Statement-level ops (scope markers, control, throws,
        //    stores).
        if is_statement_op(op) {
            self.step_statement_op(iid, op, loc, out);
            return;
        }

        // 4. Result-producing ops: inline / temporary /
        //    expression-statement / dead-pure.
        let Some(result) = self.inst_result(iid) else {
            // A result-less op that escaped the statement classification
            // (defensive — the classification is total): loud fallback.
            self.record(op, Outcome::Fallback);
            out.push(Stmt::Fallback {
                op: op_name(op),
                note: "result-less op outside statement classification",
                loc,
            });
            return;
        };
        if self.inline.contains(&result) || self.alias.contains_key(&result) {
            self.record(op, base_outcome(op));
            return;
        }
        let users = self.chains.all_users(result);
        if users.is_empty() {
            // `CopyRestArgs` is never dead: it carries the rest-param
            // evidence (`...rest` reconstruction, N74-W4) even when the
            // rest array itself is unused (`function(...args) {}` —
            // `.length` still observes it).
            if !op.effects().is_removable_if_unused() || matches!(op, Op::CopyRestArgs { .. }) {
                self.record(op, base_outcome(op));
                let value = self.expr_for(iid, op);
                out.push(Stmt::Expr(value));
            } else {
                self.record(op, Outcome::DeadPure);
            }
            return;
        }
        self.record(op, base_outcome(op));
        let name = self.mint_temp(result);
        let value = self.expr_for(iid, op);
        out.push(Stmt::Declare {
            name,
            mutable: false,
            value,
            value_id: result,
        });
    }

    fn inst_result(&self, iid: InstId) -> Option<ValueId> {
        self.module.inst(iid).and_then(|i| i.result)
    }

    /// B2: `iid` is the ctor's instance-initializer call, folded into
    /// class-field declarations (lazy [`crate::classfold::plan`]).
    fn folded_init_call(&mut self, iid: InstId) -> bool {
        self.class_fold
            .get_or_insert_with(|| {
                crate::classfold::plan_with_index(self.module, self.func, self.index)
            })
            .as_ref()
            .is_some_and(|fold| fold.call_insts.contains(&iid))
    }

    /// Statement-level ops (scope markers, control, throws, stores).
    fn step_statement_op(&mut self, iid: InstId, op: &Op, loc: Option<Loc>, out: &mut Vec<Stmt>) {
        match op {
            Op::NewLexEnv { num_vars, .. } => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::ScopePush {
                    names: vec![None; *num_vars as usize],
                });
                self.emit_env_result_if_used(iid, op, out);
            }
            Op::NewLexEnvWithName {
                num_vars,
                scope_names,
            } => {
                self.record(op, Outcome::Expressed);
                let mut names: Vec<Option<String>> = lit_of(self.module, *scope_names)
                    .and_then(Lit::into_array)
                    .map(|items| items.into_iter().map(Lit::into_string).collect())
                    .unwrap_or_default();
                names.resize(*num_vars as usize, None);
                out.push(Stmt::ScopePush { names });
                self.emit_env_result_if_used(iid, op, out);
            }
            Op::PopLexEnv => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::ScopePop);
            }
            Op::CreatePrivateNames { names, .. } => {
                self.record(op, Outcome::Expressed);
                let names = lit_of(self.module, *names)
                    .and_then(Lit::into_array)
                    .map(|items| items.into_iter().filter_map(Lit::into_string).collect())
                    .unwrap_or_default();
                out.push(Stmt::PrivateNames { names });
            }
            Op::StoreProp {
                object,
                name,
                value,
            }
            | Op::StoreOwnPropName {
                object,
                name,
                value,
                ..
            } => {
                self.record(op, Outcome::Expressed);
                let own = matches!(op, Op::StoreOwnPropName { .. });
                if let Some(s) = self.module.sym.as_str(*name) {
                    let raw = s.to_string();
                    out.push(Stmt::StoreProp {
                        object: self.expr_of(*object),
                        dot_legal: is_legal_ident(&raw),
                        name: raw,
                        value: self.expr_of(*value),
                        own,
                    });
                } else {
                    out.push(Stmt::StoreDyn {
                        object: self.expr_of(*object),
                        key: Expr::Lit(lit_of_sym(self.module, *name)),
                        value: self.expr_of(*value),
                        own,
                    });
                }
            }
            Op::StorePropIdx {
                object,
                index,
                value,
            }
            | Op::StoreOwnPropIdx {
                object,
                index,
                value,
                ..
            } => {
                self.record(op, Outcome::Expressed);
                let own = matches!(op, Op::StoreOwnPropIdx { .. });
                out.push(Stmt::StoreIndex {
                    object: self.expr_of(*object),
                    index: self.expr_of(*index),
                    value: self.expr_of(*value),
                    own,
                });
            }
            Op::StorePropDyn { object, key, value }
            | Op::StoreOwnPropDyn {
                object, key, value, ..
            } => {
                self.record(op, Outcome::Expressed);
                let own = matches!(op, Op::StoreOwnPropDyn { .. });
                out.push(Stmt::StoreDyn {
                    object: self.expr_of(*object),
                    key: self.expr_of(*key),
                    value: self.expr_of(*value),
                    own,
                });
            }
            Op::DefineMethod {
                object,
                name,
                func,
                length,
            } => {
                self.record(op, Outcome::Plumbing);
                out.push(Stmt::DefineMethod {
                    object: self.expr_of(*object),
                    name: sym_str(self.module, *name),
                    func: self.expr_of(*func),
                    length: *length,
                });
            }
            Op::DefineGetterSetterByValue {
                obj,
                key,
                getter,
                setter,
                ..
            } => {
                self.record(op, Outcome::Plumbing);
                // Resolve an `undefined` constant THROUGH the temp
                // indirection: the emitter must see the absence
                // literally, or `get: undefined` clobbers an existing
                // accessor (dream gate: local/class-accessors).
                let undef_through = |v: &ValueId| -> Option<Expr> {
                    let ValueDef::Inst(iid) = self.module.value(*v)?.def else {
                        return None;
                    };
                    let Op::LoadConst(cid) = self.module.inst(iid)?.op else {
                        return None;
                    };
                    match self.module.consts.get(cid)? {
                        abcd_ir::Const::Undefined => Some(Expr::Lit(Lit::Undefined)),
                        _ => None,
                    }
                };
                let getter = undef_through(getter).unwrap_or_else(|| self.expr_of(*getter));
                let setter = undef_through(setter).unwrap_or_else(|| self.expr_of(*setter));
                out.push(Stmt::Expr(Expr::DefineGetterSetter {
                    obj: Box::new(self.expr_of(*obj)),
                    key: Box::new(self.expr_of(*key)),
                    getter: Box::new(getter),
                    setter: Box::new(setter),
                }));
            }
            Op::CopyDataProps { dst, src } => {
                self.record(op, Outcome::Plumbing);
                out.push(Stmt::Expr(Expr::CopyDataProps {
                    dst: Box::new(self.expr_of(*dst)),
                    src: Box::new(self.expr_of(*src)),
                }));
            }
            Op::SetObjectWithProto { proto, obj } => {
                self.record(op, Outcome::Plumbing);
                out.push(Stmt::Expr(Expr::SetObjectWithProto {
                    obj: Box::new(self.expr_of(*obj)),
                    proto: Box::new(self.expr_of(*proto)),
                }));
            }
            Op::StorePrivate { obj, value, .. } | Op::DefinePrivate { obj, value, .. } => {
                self.record(op, Outcome::Expressed);
                let define = matches!(op, Op::DefinePrivate { .. });
                let name = self
                    .scopes
                    .name_of(iid)
                    .map(str::to_string)
                    .unwrap_or_else(|| "p?".to_string());
                out.push(Stmt::StorePrivate {
                    object: self.expr_of(*obj),
                    name,
                    value: self.expr_of(*value),
                    define,
                });
            }
            Op::StoreSuper { key, value, .. } => {
                self.record(op, Outcome::Expressed);
                let (name, key) = match key {
                    SuperKey::Name(s) => (Some(sym_str(self.module, *s)), None),
                    SuperKey::Dynamic(k) => (None, Some(self.expr_of(*k))),
                };
                out.push(Stmt::StoreSuper {
                    name,
                    key,
                    value: self.expr_of(*value),
                });
            }
            Op::PutLexVar {
                level,
                slot,
                value,
                kind,
            } => {
                self.record(op, Outcome::Expressed);
                let name =
                    self.scopes
                        .name_of(iid)
                        .map(str::to_string)
                        .unwrap_or_else(|| match kind {
                            abcd_ir::LexEnvKind::Patch => format!("v999999_{slot}"),
                            abcd_ir::LexEnvKind::Plain | abcd_ir::LexEnvKind::Sendable => {
                                format!("v{level}_{slot}")
                            }
                        });
                let (eff_level, own) = match kind {
                    abcd_ir::LexEnvKind::Patch => (u16::MAX, false),
                    abcd_ir::LexEnvKind::Plain | abcd_ir::LexEnvKind::Sendable => {
                        (*level, self.scopes.is_own_lex(iid))
                    }
                };
                out.push(Stmt::LexStore {
                    level: eff_level,
                    slot: *slot,
                    own,
                    name,
                    value: self.expr_of(*value),
                });
            }
            Op::StoreGlobal { name, value }
            | Op::StoreGlobalRecord { name, value, .. }
            | Op::TryStoreGlobal { name, value } => {
                self.record(op, Outcome::Expressed);
                let tolerant = matches!(op, Op::TryStoreGlobal { .. });
                out.push(Stmt::GlobalStore {
                    name: sym_str(self.module, *name),
                    value: self.expr_of(*value),
                    tolerant,
                });
            }
            Op::StoreModuleVar { index, value } => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::ModuleStore {
                    index: *index,
                    name: self.module_slot_name(*index),
                    value: self.expr_of(*value),
                });
            }
            Op::Throw { value } => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Throw(self.expr_of(*value)));
            }
            Op::ThrowDeleteSuperProperty => {
                self.record(op, Outcome::Fallback);
                out.push(Stmt::Fallback {
                    op: op_name(op),
                    note: fallback_note(op),
                    loc,
                });
            }
            Op::Branch { dest } => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Branch { dest: *dest });
            }
            Op::CondBranch {
                cond,
                true_dest,
                false_dest,
            } => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::CondBranch {
                    cond: self.expr_of(*cond),
                    true_dest: *true_dest,
                    false_dest: *false_dest,
                });
            }
            Op::Return { value } => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Return(value.map(|v| self.expr_of(v))));
            }
            Op::Unreachable => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Unreachable);
            }
            Op::Debugger => {
                self.record(op, Outcome::Expressed);
                out.push(Stmt::Debugger);
            }
            other => {
                // A statement-op classification miss: loud fallback,
                // never silent (the classification is total, so this arm
                // is defensive).
                self.record(other, Outcome::Fallback);
                out.push(Stmt::Fallback {
                    op: op_name(other),
                    note: "statement-op classification miss",
                    loc,
                });
            }
        }
    }

    /// `NewLexEnv*` yields the environment value; SSA consumers are not
    /// expected (the env is implicit), but if one appears, bind it to a
    /// loud fallback temp rather than dropping it.
    fn emit_env_result_if_used(&mut self, iid: InstId, op: &Op, out: &mut Vec<Stmt>) {
        if let Some(result) = self.inst_result(iid)
            && !self.chains.all_users(result).is_empty()
        {
            let name = self.mint_temp(result);
            out.push(Stmt::Declare {
                name,
                mutable: false,
                value: Expr::Fallback {
                    op: op_name(op),
                    note: "lexenv value used as an SSA operand (unexpected)",
                    operands: vec![],
                },
                value_id: result,
            });
        }
    }

    /// The expression for an SSA value: alias/inline/temp resolution.
    pub(super) fn expr_of(&mut self, v: ValueId) -> Expr {
        self.run_expr_steps(RecStep::Val(v))
    }

    /// Build the expression tree of one instruction's op.
    fn expr_for(&mut self, iid: InstId, op: &Op) -> Expr {
        self.run_expr_steps(RecStep::Inst(iid, op.clone()))
    }

    #[allow(
        clippy::too_many_lines,
        reason = "iterative Stage-A expression tree builder dispatches across all IR Op variants on an explicit heap workstack"
    )]
    fn run_expr_steps(&mut self, root: RecStep) -> Expr {
        let pop_expr = |vals: &mut Vec<Expr>| vals.pop().unwrap_or(Expr::SuperMarker);
        let mut steps: Vec<RecStep> = vec![root];
        let mut vals: Vec<Expr> = Vec::new();
        let mut active_inlines: HashSet<InstId> = HashSet::new();
        let max_aliases = self.module.values.len().max(1);

        while let Some(step) = steps.pop() {
            match step {
                RecStep::PopInline(iid) => {
                    active_inlines.remove(&iid);
                }
                RecStep::Val(mut v) => {
                    for _ in 0..max_aliases {
                        if let Some(&target) = self.alias.get(&v)
                            && target != v
                        {
                            v = target;
                        } else {
                            break;
                        }
                    }
                    let Some(value) = self.module.value(v) else {
                        vals.push(Expr::Fallback {
                            op: "<value>",
                            note: "unknown ValueId (data, not a panic)",
                            operands: vec![],
                        });
                        continue;
                    };
                    match value.def {
                        ValueDef::Param(i) => {
                            let i = i as usize;
                            // Hidden ABI slots read directly: map `new.target` and `funcobj`
                            // under the active `FrameSlots` layout (`#87.4`).
                            if let Some(slots) = self.frame_slots
                                && i < self.hidden_params
                            {
                                let func_idx = slots.func.then_some(0usize);
                                let new_target_idx =
                                    slots.new_target.then_some(slots.func as usize);
                                if new_target_idx == Some(i) {
                                    vals.push(Expr::NewTarget);
                                    continue;
                                }
                                if func_idx == Some(i) {
                                    vals.push(Expr::Fallback {
                                        op: "Param(funcobj)",
                                        note: "the hidden function-object slot has no JS surface form",
                                        operands: vec![],
                                    });
                                    continue;
                                }
                            }
                            vals.push(Expr::Ident(
                                self.param_names
                                    .get(i)
                                    .cloned()
                                    .unwrap_or_else(|| format!("p{i}")),
                            ));
                        }
                        ValueDef::Const(cid) => match lit_of(self.module, cid) {
                            Some(lit) => vals.push(Expr::Lit(lit)),
                            None => vals.push(Expr::Fallback {
                                op: "<const>",
                                note: "unknown ConstId (data, not a panic)",
                                operands: vec![],
                            }),
                        },
                        ValueDef::ExceptionParam(_) => {
                            let name = match self.catch_names.get(&v) {
                                Some(n) => n.clone(),
                                None => {
                                    let n =
                                        self.legal.mint_avoiding("e", &self.referenced_bare_names);
                                    self.catch_names.insert(v, n.clone());
                                    n
                                }
                            };
                            vals.push(Expr::Ident(name));
                        }
                        ValueDef::Inst(iid) => {
                            if self.inline.contains(&v) && active_inlines.insert(iid) {
                                match self.module.inst(iid).map(|i| i.op.clone()) {
                                    Some(op) => {
                                        steps.push(RecStep::PopInline(iid));
                                        steps.push(RecStep::Inst(iid, op));
                                    }
                                    None => {
                                        active_inlines.remove(&iid);
                                        vals.push(Expr::Fallback {
                                            op: "<inst>",
                                            note: "unknown InstId (data, not a panic)",
                                            operands: vec![],
                                        });
                                    }
                                }
                            } else {
                                vals.push(Expr::Temp {
                                    value: v,
                                    name: self.mint_temp(v),
                                });
                            }
                        }
                    }
                }
                RecStep::Inst(iid, op) => match &op {
                    Op::BinaryOp { op, left, right } => {
                        // Operand order (N36): semantic expression is `right OP left`.
                        steps.push(RecStep::BuildBinary(*op));
                        steps.push(RecStep::Val(*left));
                        steps.push(RecStep::Val(*right));
                    }
                    Op::UnaryOp { op, operand } => {
                        steps.push(RecStep::BuildUnary(*op));
                        steps.push(RecStep::Val(*operand));
                    }
                    Op::Compare { op, left, right } => {
                        steps.push(RecStep::BuildCompare(*op));
                        steps.push(RecStep::Val(*left));
                        steps.push(RecStep::Val(*right));
                    }
                    Op::Mov { src } => steps.push(RecStep::Val(*src)),
                    Op::LoadConst(cid) => vals.push(match lit_of(self.module, *cid) {
                        Some(lit) => Expr::Lit(lit),
                        None => Expr::Fallback {
                            op: "LoadConst",
                            note: "unknown ConstId",
                            operands: vec![],
                        },
                    }),
                    Op::AllocObject { shape } => {
                        let expr = match lit_of(self.module, *shape) {
                            Some(mut lit) => match &mut lit {
                                Lit::Object(entries) => Expr::ObjectLit {
                                    entries: std::mem::take(entries),
                                },
                                Lit::Array(items) => match self.parse_shape_buffer(items) {
                                    Some(expr) => expr,
                                    None => Expr::Fallback {
                                        op: "AllocObject",
                                        note: "shape buffer is not a flat key/value array",
                                        operands: vec![],
                                    },
                                },
                                _ => Expr::Fallback {
                                    op: "AllocObject",
                                    note: "shape constant is not an ObjectLiteral",
                                    operands: vec![],
                                },
                            },
                            None => Expr::Fallback {
                                op: "AllocObject",
                                note: "shape constant is not an ObjectLiteral",
                                operands: vec![],
                            },
                        };
                        vals.push(expr);
                    }
                    Op::AllocArray { shape } => {
                        let expr = match shape {
                            None => Expr::ArrayLit { elements: vec![] },
                            Some(cid) => {
                                match lit_of(self.module, *cid).and_then(Lit::into_array) {
                                    Some(elements) => Expr::ArrayLit { elements },
                                    None => Expr::Fallback {
                                        op: "AllocArray",
                                        note: "shape constant is not an ArrayLiteral",
                                        operands: vec![],
                                    },
                                }
                            }
                        };
                        vals.push(expr);
                    }
                    Op::AllocRegExp { pattern, flags } => vals.push(Expr::RegExp {
                        pattern: sym_regexp_pattern(self.module, *pattern),
                        flags: render_regexp_flags(*flags),
                    }),
                    Op::AllocClosure { func } => self.push_closure_of_steps(*func, &mut steps),
                    Op::LoadProp { object, name } => {
                        if let Some(s) = self.module.sym.as_str(*name) {
                            let raw = s.to_string();
                            let dot_legal = is_legal_ident(&raw);
                            steps.push(RecStep::BuildPropName {
                                name: raw,
                                dot_legal,
                            });
                            steps.push(RecStep::Val(*object));
                        } else {
                            let key = Expr::Lit(lit_of_sym(self.module, *name));
                            steps.push(RecStep::BuildPropDynConstKey(Box::new(key)));
                            steps.push(RecStep::Val(*object));
                        }
                    }
                    Op::LoadPropIdx { object, index } => {
                        steps.push(RecStep::BuildPropIndex);
                        steps.push(RecStep::Val(*index));
                        steps.push(RecStep::Val(*object));
                    }
                    Op::LoadPropDyn { object, key } => {
                        steps.push(RecStep::BuildPropDyn);
                        steps.push(RecStep::Val(*key));
                        steps.push(RecStep::Val(*object));
                    }
                    Op::DeleteProp { object, key } => {
                        steps.push(RecStep::BuildDeletePropDyn);
                        steps.push(RecStep::Val(*key));
                        steps.push(RecStep::Val(*object));
                    }
                    Op::TestProp { object, key } => match key {
                        PropKey::Name(s) => {
                            let key_expr = Expr::Lit(lit_of_sym(self.module, *s));
                            steps.push(RecStep::BuildTestPropNamed(Box::new(key_expr)));
                            steps.push(RecStep::Val(*object));
                        }
                        PropKey::Index(k) | PropKey::Dynamic(k) => {
                            steps.push(RecStep::BuildCompare(CmpOp::In));
                            steps.push(RecStep::Val(*object));
                            steps.push(RecStep::Val(*k));
                        }
                    },
                    Op::GetTemplateObject { literal } => {
                        let (raw, cooked) = self.template_strings_of(*literal);
                        vals.push(Expr::TemplateObject { raw, cooked });
                    }
                    Op::CreateIterResultObj { value, done } => {
                        steps.push(RecStep::BuildIterResultObj);
                        steps.push(RecStep::Val(*done));
                        steps.push(RecStep::Val(*value));
                    }
                    Op::GetIterator { obj } => {
                        self.push_iter_step(IterOp::GetIterator, *obj, &mut steps)
                    }
                    Op::GetAsyncIterator { obj } => {
                        self.push_iter_step(IterOp::GetAsyncIterator, *obj, &mut steps)
                    }
                    Op::IteratorNext { iterator } => {
                        self.push_iter_step(IterOp::Next, *iterator, &mut steps)
                    }
                    Op::IteratorReturn { iterator } => {
                        self.push_iter_step(IterOp::Return, *iterator, &mut steps)
                    }
                    Op::IteratorThrow { iterator } => {
                        self.push_iter_step(IterOp::Throw, *iterator, &mut steps)
                    }
                    Op::GetPropIterator { obj } => {
                        self.push_iter_step(IterOp::GetPropIterator, *obj, &mut steps)
                    }
                    Op::NextPropName { iterator } => {
                        self.push_iter_step(IterOp::NextPropName, *iterator, &mut steps)
                    }
                    Op::GetLexVar { .. } => {
                        let name = self
                            .scopes
                            .name_of(iid)
                            .map(str::to_string)
                            .unwrap_or_else(|| "v?".to_string());
                        vals.push(Expr::Ident(sanitize(&name)));
                    }
                    Op::TryGetGlobal { name, .. } => {
                        let expr = if let Some(s) = self.module.sym.as_str(*name) {
                            let raw = s.to_string();
                            if is_legal_ident(&raw) {
                                Expr::Ident(raw)
                            } else {
                                Expr::PropIndex {
                                    object: Box::new(Expr::GlobalThis),
                                    index: Box::new(Expr::Lit(Lit::String(raw))),
                                }
                            }
                        } else {
                            Expr::PropIndex {
                                object: Box::new(Expr::GlobalThis),
                                index: Box::new(Expr::Lit(lit_of_sym(self.module, *name))),
                            }
                        };
                        vals.push(expr);
                    }
                    Op::LoadModuleVar { index, kind } => {
                        vals.push(Expr::Ident(self.load_module_var_name(*index, *kind)));
                    }
                    Op::GetModuleNamespace { index } => {
                        let expr = if let Some(env) = self.record_env()
                            && let Some(ns) = env.namespace_slots.get(index)
                        {
                            Expr::Ident(ns.clone())
                        } else {
                            Expr::ModuleNamespace { index: *index }
                        };
                        vals.push(expr);
                    }
                    Op::DynamicImport { specifier } => {
                        steps.push(RecStep::BuildDynamicImport);
                        steps.push(RecStep::Val(*specifier));
                    }
                    Op::Call {
                        callee,
                        this,
                        args,
                        kind,
                    } => {
                        let super_callee = matches!(
                            kind,
                            CallKind::Super
                                | CallKind::SuperArrow
                                | CallKind::SuperSpread
                                | CallKind::SuperForwardAllArgs
                        );
                        steps.push(RecStep::BuildCall {
                            has_this: this.is_some(),
                            arg_count: args.len(),
                            kind: *kind,
                            super_callee,
                        });
                        for a in args.iter().rev() {
                            steps.push(RecStep::Val(*a));
                        }
                        if let Some(t) = this {
                            steps.push(RecStep::Val(*t));
                        }
                        if !super_callee {
                            steps.push(RecStep::Val(*callee));
                        }
                    }
                    Op::DefineFunc { body, captures, .. } => {
                        self.push_closure_node_steps(*body, captures, &mut steps);
                    }
                    Op::DefineClass(cls) => {
                        self.push_class_node_steps(
                            cls.ctor,
                            cls.heritage,
                            cls.members,
                            cls.member_attrs.clone(),
                            false,
                            &mut steps,
                            &mut vals,
                        );
                    }
                    Op::DefineSendableClass(cls) => {
                        self.push_class_node_steps(
                            cls.ctor,
                            cls.heritage,
                            cls.members,
                            cls.member_attrs.clone(),
                            true,
                            &mut steps,
                            &mut vals,
                        );
                    }
                    Op::LoadPrivate { obj, .. } => {
                        let name = self
                            .scopes
                            .name_of(iid)
                            .map(str::to_string)
                            .unwrap_or_else(|| "p?".to_string());
                        steps.push(RecStep::BuildPrivate { name, test: false });
                        steps.push(RecStep::Val(*obj));
                    }
                    Op::TestPrivate { obj, .. } => {
                        let name = self
                            .scopes
                            .name_of(iid)
                            .map(str::to_string)
                            .unwrap_or_else(|| "p?".to_string());
                        steps.push(RecStep::BuildPrivate { name, test: true });
                        steps.push(RecStep::Val(*obj));
                    }
                    Op::CreateGenerator { func } | Op::CreateAsyncGenerator { func } => {
                        steps.push(RecStep::BuildCreateGenerator);
                        steps.push(RecStep::Val(*func));
                    }
                    Op::SuspendGenerator { value, .. } => {
                        steps.push(RecStep::BuildYield);
                        steps.push(RecStep::Val(*value));
                    }
                    Op::ResumeGenerator { genobj } => {
                        steps.push(RecStep::BuildGenDriver(true));
                        steps.push(RecStep::Val(*genobj));
                    }
                    Op::GetResumeMode { genobj } => {
                        steps.push(RecStep::BuildGenDriver(false));
                        steps.push(RecStep::Val(*genobj));
                    }
                    Op::Await { value } => {
                        steps.push(RecStep::BuildAwait(false));
                        steps.push(RecStep::Val(*value));
                    }
                    Op::AwaitUncaught { value, .. } => {
                        steps.push(RecStep::BuildAwait(true));
                        steps.push(RecStep::Val(*value));
                    }
                    Op::AsyncResolve { value, .. } => {
                        steps.push(RecStep::BuildAsyncDriver(true));
                        steps.push(RecStep::Val(*value));
                    }
                    Op::AsyncReject { value, .. } | Op::AsyncGeneratorReject { value, .. } => {
                        steps.push(RecStep::BuildAsyncDriver(false));
                        steps.push(RecStep::Val(*value));
                    }
                    Op::AsyncGeneratorResolve {
                        genobj,
                        value,
                        done,
                    } => {
                        steps.push(RecStep::BuildAsyncGenResolve);
                        steps.push(RecStep::Val(*done));
                        steps.push(RecStep::Val(*value));
                        steps.push(RecStep::Val(*genobj));
                    }
                    Op::LoadSymbol => vals.push(Expr::Ident("Symbol".to_string())),
                    Op::LoadNewTarget => vals.push(Expr::NewTarget),
                    Op::LoadGlobalObject => vals.push(Expr::GlobalThis),
                    Op::LoadFunction => {
                        let name = self
                            .module
                            .func(self.func)
                            .map(|f| sym_str(self.module, f.name))
                            .unwrap_or_default();
                        vals.push(Expr::SelfFunction(name));
                    }
                    Op::GetUnmappedArgs => vals.push(Expr::Arguments),
                    Op::CopyRestArgs { start_index } => vals.push(Expr::RestArgs {
                        start_index: *start_index,
                    }),
                    Op::LoadSuper { key, .. } => match key {
                        SuperKey::Name(s) => vals.push(Expr::SuperProp {
                            name: Some(sym_str(self.module, *s)),
                            key: None,
                        }),
                        SuperKey::Dynamic(k) => {
                            steps.push(RecStep::BuildSuperDyn);
                            steps.push(RecStep::Val(*k));
                        }
                    },
                    Op::ArraySpread { dst, index, src } => {
                        steps.push(RecStep::BuildArraySpread);
                        steps.push(RecStep::Val(*src));
                        steps.push(RecStep::Val(*index));
                        steps.push(RecStep::Val(*dst));
                    }
                    Op::CreateObjectWithExcludedKeys { obj, keys } => {
                        steps.push(RecStep::BuildRestObject(keys.len()));
                        for k in keys.iter().rev() {
                            steps.push(RecStep::Val(*k));
                        }
                        steps.push(RecStep::Val(*obj));
                    }
                    other => {
                        let op_s = op_name(other);
                        let note_s = fallback_note(other);
                        let ops = other.operands();
                        steps.push(RecStep::BuildFallback {
                            op: op_s,
                            note: note_s,
                            count: ops.len(),
                        });
                        for v in ops.iter().rev() {
                            steps.push(RecStep::Val(*v));
                        }
                    }
                },
                RecStep::BuildBinary(op) => {
                    let right = Box::new(pop_expr(&mut vals));
                    let left = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Binary { op, left, right });
                }
                RecStep::BuildUnary(op) => {
                    let operand = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Unary { op, operand });
                }
                RecStep::BuildCompare(op) => {
                    let right = Box::new(pop_expr(&mut vals));
                    let left = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Compare { op, left, right });
                }
                RecStep::BuildPropName { name, dot_legal } => {
                    let object = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::PropName {
                        object,
                        name,
                        dot_legal,
                    });
                }
                RecStep::BuildPropDynConstKey(key) => {
                    let object = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::PropDyn { object, key });
                }
                RecStep::BuildPropIndex => {
                    let index = Box::new(pop_expr(&mut vals));
                    let object = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::PropIndex { object, index });
                }
                RecStep::BuildPropDyn => {
                    let key = Box::new(pop_expr(&mut vals));
                    let object = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::PropDyn { object, key });
                }
                RecStep::BuildDeletePropDyn => {
                    let key = Box::new(pop_expr(&mut vals));
                    let object = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Delete {
                        target: Box::new(Expr::PropDyn { object, key }),
                    });
                }
                RecStep::BuildTestPropNamed(left) => {
                    let right = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Compare {
                        op: CmpOp::In,
                        left,
                        right,
                    });
                }
                RecStep::BuildIterResultObj => {
                    let done = Box::new(pop_expr(&mut vals));
                    let value = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::IterResultObj { value, done });
                }
                RecStep::BuildIter { op, status } => {
                    let obj = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Iter { op, obj, status });
                }
                RecStep::BuildDynamicImport => {
                    let specifier = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::DynamicImport { specifier });
                }
                RecStep::BuildCall {
                    has_this,
                    arg_count,
                    kind,
                    super_callee,
                } => {
                    let start = vals.len().saturating_sub(arg_count);
                    let args = vals.split_off(start);
                    let this = has_this.then(|| Box::new(pop_expr(&mut vals)));
                    let callee = if super_callee {
                        Box::new(Expr::SuperMarker)
                    } else {
                        Box::new(pop_expr(&mut vals))
                    };
                    vals.push(Expr::Call {
                        callee,
                        this,
                        args,
                        kind,
                    });
                }
                RecStep::BuildClosure {
                    body,
                    name,
                    kind,
                    cap_names,
                } => {
                    let start = vals.len().saturating_sub(cap_names.len());
                    let mut drain = vals.drain(start..);
                    let mut captures = Vec::with_capacity(cap_names.len());
                    for cname in cap_names {
                        captures.push((cname, drain.next().unwrap_or(Expr::SuperMarker)));
                    }
                    drop(drain);
                    vals.push(Expr::Closure {
                        body,
                        name,
                        kind,
                        captures,
                    });
                }
                RecStep::BuildClassWithHeritage {
                    ctor,
                    name,
                    members,
                    member_attrs,
                    sendable,
                } => {
                    let heritage = Some(Box::new(pop_expr(&mut vals)));
                    vals.push(Expr::Class {
                        ctor,
                        name,
                        heritage,
                        members,
                        member_attrs,
                        sendable,
                    });
                }
                RecStep::BuildPrivate { name, test } => {
                    let object = Box::new(pop_expr(&mut vals));
                    vals.push(if test {
                        Expr::PrivateTest { object, name }
                    } else {
                        Expr::PrivateLoad { object, name }
                    });
                }
                RecStep::BuildCreateGenerator => {
                    let func = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::CreateGenerator { func });
                }
                RecStep::BuildYield => {
                    let value = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Yield { value });
                }
                RecStep::BuildGenDriver(resume) => {
                    let genobj = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::GeneratorDriver { resume, genobj });
                }
                RecStep::BuildAwait(uncaught) => {
                    let value = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::Await { value, uncaught });
                }
                RecStep::BuildAsyncDriver(resolve) => {
                    let value = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::AsyncDriver { resolve, value });
                }
                RecStep::BuildAsyncGenResolve => {
                    let done = Box::new(pop_expr(&mut vals));
                    let value = Box::new(pop_expr(&mut vals));
                    let genobj = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::AsyncGeneratorResolve {
                        genobj,
                        value,
                        done,
                    });
                }
                RecStep::BuildSuperDyn => {
                    let key = Some(Box::new(pop_expr(&mut vals)));
                    vals.push(Expr::SuperProp { name: None, key });
                }
                RecStep::BuildArraySpread => {
                    let src = Box::new(pop_expr(&mut vals));
                    let index = Box::new(pop_expr(&mut vals));
                    let dst = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::ArraySpread { dst, index, src });
                }
                RecStep::BuildRestObject(count) => {
                    let start = vals.len().saturating_sub(count);
                    let excluded = vals.split_off(start);
                    let obj = Box::new(pop_expr(&mut vals));
                    vals.push(Expr::RestObject { obj, excluded });
                }
                RecStep::BuildFallback { op, note, count } => {
                    let start = vals.len().saturating_sub(count);
                    let operands = vals.split_off(start);
                    vals.push(Expr::Fallback { op, note, operands });
                }
            }
        }

        pop_expr(&mut vals)
    }

    /// Mint (once) the temporary name of an SSA value:
    /// `DebugData.local_names` scope hit → defining-op `Sym` hint →
    /// module/namespace slot fallback → `v{n}`.
    fn mint_temp(&mut self, v: ValueId) -> String {
        if let Some(n) = self.temp_names.get(&v) {
            return n.clone();
        }
        let mut raw: Option<String> = None;
        if let Some(Value {
            def: ValueDef::Inst(iid),
            ..
        }) = self.module.value(v)
        {
            if let Some(d) = self.module.func(self.func).and_then(|f| f.debug.as_ref()) {
                raw = local_name_in(self.module, d, *iid);
            }
            if raw.is_none()
                && let Some(inst) = self.module.inst(*iid)
            {
                raw = match &inst.op {
                    Op::LoadModuleVar { index, kind } => {
                        Some(self.load_module_var_name(*index, *kind))
                    }
                    Op::GetModuleNamespace { index } => Some(self.module_namespace_name(*index)),
                    Op::GetLexVar { .. } => self.scopes.name_of(*iid).map(str::to_string),
                    other => op_name_hint(self.module, other),
                };
            }
        }
        let fallback = format!("v{}", v.index());
        let name = self.legal.mint(raw.as_deref().unwrap_or(&fallback));
        self.temp_names.insert(v, name.clone());
        name
    }

    /// Parse a `createobjectwithbuffer` flat shape buffer: plain
    /// `[key, value]` pairs, plus `[name, MethodRef, attrs]` method
    /// entries (attrs dropped — runtime metadata). Pure key/value
    /// buffers stay [`Expr::ObjectLit`]; method-bearing buffers become
    /// [`Expr::ObjectBuild`] directly. `None` when the shape is
    /// unrecognizable (the caller falls back loudly).
    fn parse_shape_buffer(&mut self, items: &[Lit]) -> Option<Expr> {
        let mut plain: Vec<(Lit, Lit)> = Vec::new();
        let mut build: Vec<ObjEntry> = Vec::new();
        let mut has_methods = false;
        let mut i = 0;
        while i < items.len() {
            let key = match &items[i] {
                Lit::String(s) => s.clone(),
                Lit::Number(_) | Lit::Int64(_) | Lit::UInt64(_) => {
                    // Numeric key of a plain pair.
                    if i + 1 < items.len() && !matches!(items[i + 1], Lit::MethodRef(_)) {
                        plain.push((items[i].clone(), items[i + 1].clone()));
                        build.push(ObjEntry::KeyValue(
                            items[i].clone(),
                            Expr::Lit(items[i + 1].clone()),
                        ));
                        i += 2;
                        continue;
                    }
                    return None;
                }
                _ => return None,
            };
            match items.get(i + 1) {
                Some(Lit::MethodRef(fid)) => {
                    has_methods = true;
                    let name = self
                        .module
                        .func(*fid)
                        .map(|f| sym_str(self.module, f.name))
                        .unwrap_or_else(|| format!("m${}", fid.index()));
                    // Bug A: body evidence over the metadata gap.
                    let kind = effective_kind(self.module, *fid);
                    build.push(ObjEntry::Method(
                        key,
                        Expr::Closure {
                            body: *fid,
                            name,
                            kind,
                            captures: Vec::new(),
                        },
                    ));
                    // Skip the trailing attributes payload when present.
                    i += if matches!(
                        items.get(i + 2),
                        Some(Lit::Number(_) | Lit::Int64(_) | Lit::UInt64(_))
                    ) {
                        3
                    } else {
                        2
                    };
                }
                Some(v) => {
                    plain.push((items[i].clone(), v.clone()));
                    build.push(ObjEntry::KeyValue(items[i].clone(), Expr::Lit(v.clone())));
                    i += 2;
                }
                None => return None,
            }
        }
        if has_methods {
            Some(Expr::ObjectBuild { entries: build })
        } else {
            Some(Expr::ObjectLit { entries: plain })
        }
    }

    /// Push iteration-plumbing steps onto `steps` (hard-7 members flagged Fallback).
    fn push_iter_step(&self, op: IterOp, obj: ValueId, steps: &mut Vec<RecStep>) {
        let status = match op {
            IterOp::Return | IterOp::Throw => NodeStatus::Fallback,
            _ => NodeStatus::Plumbing,
        };
        steps.push(RecStep::BuildIter { op, status });
        steps.push(RecStep::Val(obj));
    }

    /// `AllocClosure`: pair with the `DefineFunc` def (through `Mov`s).
    fn push_closure_of_steps(&self, func: ValueId, steps: &mut Vec<RecStep>) {
        let mut cur = func;
        for _ in 0..16 {
            let Some(value) = self.module.value(cur) else {
                break;
            };
            match value.def {
                ValueDef::Inst(iid) => match self.module.inst(iid).map(|i| i.op.clone()) {
                    Some(Op::Mov { src }) => {
                        cur = src;
                        continue;
                    }
                    Some(Op::DefineFunc { body, captures, .. }) => {
                        self.push_closure_node_steps(body, &captures, steps);
                        return;
                    }
                    _ => break,
                },
                _ => break,
            }
        }
        steps.push(RecStep::BuildFallback {
            op: "AllocClosure",
            note: "func operand is not a DefineFunc def-chain",
            count: 1,
        });
        steps.push(RecStep::Val(func));
    }

    /// Push deferred closure steps onto `steps`.
    fn push_closure_node_steps(
        &self,
        body: FuncId,
        captures: &[(Sym, ValueId)],
        steps: &mut Vec<RecStep>,
    ) {
        let name = self
            .module
            .func(body)
            .map(|f| sym_str(self.module, f.name))
            .unwrap_or_else(|| format!("<fn#{}>", body.index()));
        let kind = effective_kind(self.module, body);
        let cap_names: Vec<String> = captures
            .iter()
            .map(|(s, _)| sym_str(self.module, *s))
            .collect();
        steps.push(RecStep::BuildClosure {
            body,
            name,
            kind,
            cap_names,
        });
        for (_, v) in captures.iter().rev() {
            steps.push(RecStep::Val(*v));
        }
    }

    /// Push deferred class steps onto `steps` (or directly onto `vals` when no heritage).
    #[allow(
        clippy::too_many_arguments,
        reason = "class recovery step helper threads ctor, heritage, member buffer, and workstacks"
    )]
    fn push_class_node_steps(
        &self,
        ctor: FuncId,
        heritage: Option<ValueId>,
        members: ConstId,
        member_attrs: Vec<abcd_ir::op::MemberAttrs>,
        sendable: bool,
        steps: &mut Vec<RecStep>,
        vals: &mut Vec<Expr>,
    ) {
        let name = self
            .module
            .func(ctor)
            .map(|f| sym_str(self.module, f.name))
            .unwrap_or_else(|| format!("<fn#{}>", ctor.index()));
        let suppress = heritage.is_some_and(|h| provably_hole(self.module, h));
        match heritage {
            Some(h) if !suppress => {
                steps.push(RecStep::BuildClassWithHeritage {
                    ctor,
                    name,
                    members,
                    member_attrs,
                    sendable,
                });
                steps.push(RecStep::Val(h));
            }
            _ => vals.push(Expr::Class {
                ctor,
                name,
                heritage: None,
                members,
                member_attrs,
                sendable,
            }),
        }
    }

    /// Resolve a `gettemplateobject` literal operand to its
    /// `(raw, cooked)` template-string lists (G4, resolved by d-P10).
    ///
    /// Vendor grounding:
    /// - es2panda `compiler/base/literals.cpp`
    ///   `Literals::GetTemplateObject` builds `rawArr` (each quasi's
    ///   `element->Raw()`) and `cookedArr` (`element->Cooked()`), then
    ///   `templateArg = [rawArr, cookedArr]` — raw at index 0, cooked at
    ///   index 1 — via `createemptyarray` + `callruntime.definefieldbyvalue`.
    /// - The runtime `ecmascript/template_string.cpp`
    ///   `TemplateString::GetTemplateObject` reads `templateLiteral[0]`
    ///   as the raw strings and `[1]` as the cooked strings.
    ///
    /// Two IR shapes carry the pair: a const-pool array constant, or
    /// the imperative `AllocArray` + integer-keyed own-store build
    /// sequence (the form es2abc actually emits).
    fn template_strings_of(&self, literal: ValueId) -> (Option<Vec<Lit>>, Option<Vec<Lit>>) {
        let v = chase_mov(self.module, literal);
        // Const-pool form: the whole literal array is one constant.
        if let Some(cid) = const_id_of(self.module, v) {
            return match lit_of(self.module, cid).and_then(Lit::into_array) {
                Some(items) => {
                    // Vendor pair layout [raw, cooked]: both elements are
                    // themselves arrays. Anything else keeps the pre-d-P10
                    // interpretation (the flat list is the cooked list).
                    if items.len() == 2
                        && let (Lit::Array(raw), Lit::Array(cooked)) = (&items[0], &items[1])
                    {
                        return (Some(raw.clone()), Some(cooked.clone()));
                    }
                    (None, Some(items))
                }
                None => (None, None),
            };
        }
        // Imperative form: slots 0 (raw) and 1 (cooked) of the literal
        // array are own-stored element arrays. Lenient about the pair
        // array's other uses (it is read at the `gettemplateobject`
        // point regardless); strict about each element array.
        let mut slots: [Option<ValueId>; 2] = [None, None];
        for &user in self.chains.users_of(v) {
            let Some(inst) = self.module.inst(user) else {
                continue;
            };
            let (object, index, value) = match &inst.op {
                Op::StoreOwnPropDyn {
                    object, key, value, ..
                }
                | Op::StorePropDyn { object, key, value } => {
                    let Some(i) = self.const_index_of(*key) else {
                        continue;
                    };
                    (*object, i, *value)
                }
                Op::StoreOwnPropIdx {
                    object,
                    index,
                    value,
                    ..
                }
                | Op::StorePropIdx {
                    object,
                    index,
                    value,
                } => {
                    let Some(i) = self.const_index_of(*index) else {
                        continue;
                    };
                    (*object, i, *value)
                }
                _ => continue,
            };
            if chase_mov(self.module, object) == v && (index as usize) < 2 {
                slots[index as usize] = Some(value);
            }
        }
        let raw = slots[0].and_then(|a| self.string_elems_of(a));
        let cooked = slots[1].and_then(|a| self.string_elems_of(a));
        (raw, cooked)
    }

    /// Resolve an array value to its element literals — a const-pool
    /// array, or an `AllocArray` whose every use is accounted for by the
    /// es2panda template build: integer-keyed own/prop stores into it,
    /// `Mov` passthroughs, or appearing as a stored VALUE (the literal
    /// pair array's slot store). Any other use → unresolved (honest
    /// bail, the cooked-only fallback emits).
    fn string_elems_of(&self, arr: ValueId) -> Option<Vec<Lit>> {
        let arr = chase_mov(self.module, arr);
        if let Some(cid) = const_id_of(self.module, arr) {
            return lit_of(self.module, cid)?.into_array();
        }
        // The array must be a fresh allocation we can fully account for.
        let is_alloc = matches!(
            self.module.value(arr)?.def,
            ValueDef::Inst(iid)
                if matches!(
                    self.module.inst(iid).map(|i| &i.op),
                    Some(Op::AllocArray { .. })
                )
        );
        if !is_alloc {
            return None;
        }
        let mut elems: BTreeMap<u32, Lit> = BTreeMap::new();
        for &user in self.chains.users_of(arr) {
            let inst = self.module.inst(user)?;
            match &inst.op {
                Op::StoreOwnPropDyn {
                    object, key, value, ..
                }
                | Op::StorePropDyn { object, key, value } => {
                    if chase_mov(self.module, *object) == arr {
                        let i = self.const_index_of(*key)?;
                        let lit = self.lit_value_of(*value)?;
                        elems.insert(i, lit);
                    }
                    // else: arr is the stored value (the pair-array slot
                    // store) — accounted for, nothing to record.
                }
                Op::StoreOwnPropIdx {
                    object,
                    index,
                    value,
                    ..
                }
                | Op::StorePropIdx {
                    object,
                    index,
                    value,
                } => {
                    if chase_mov(self.module, *object) == arr {
                        let i = self.const_index_of(*index)?;
                        let lit = self.lit_value_of(*value)?;
                        elems.insert(i, lit);
                    }
                }
                Op::Mov { .. } => {}
                _ => return None,
            }
        }
        // Contiguity: elements are exactly indices 0..n.
        let n = elems.len() as u32;
        let mut out = Vec::with_capacity(elems.len());
        for i in 0..n {
            out.push(elems.get(&i)?.clone());
        }
        Some(out)
    }

    /// Resolve a value to a constant integer index (`ldai` →
    /// `Const::Number`), through `Mov`s.
    fn const_index_of(&self, v: ValueId) -> Option<u32> {
        let cid = const_id_of(self.module, chase_mov(self.module, v))?;
        match lit_of(self.module, cid)? {
            Lit::Number(bits) => {
                let x = f64::from_bits(bits);
                if x.fract() == 0.0 && x >= 0.0 && x <= u32::MAX as f64 {
                    Some(x as u32)
                } else {
                    None
                }
            }
            Lit::Int64(x) => u32::try_from(x).ok(),
            Lit::UInt64(x) => u32::try_from(x).ok(),
            _ => None,
        }
    }

    /// Resolve a value to a constant literal, through `Mov`s.
    fn lit_value_of(&self, v: ValueId) -> Option<Lit> {
        let cid = const_id_of(self.module, chase_mov(self.module, v))?;
        lit_of(self.module, cid)
    }
}

enum RecStep {
    Val(ValueId),
    Inst(InstId, Op),
    PopInline(InstId),
    BuildBinary(abcd_ir::op::BinOp),
    BuildUnary(abcd_ir::op::UnOp),
    BuildCompare(CmpOp),
    BuildPropName {
        name: String,
        dot_legal: bool,
    },
    BuildPropDynConstKey(Box<Expr>),
    BuildPropIndex,
    BuildPropDyn,
    BuildDeletePropDyn,
    BuildTestPropNamed(Box<Expr>),
    BuildIterResultObj,
    BuildIter {
        op: IterOp,
        status: NodeStatus,
    },
    BuildDynamicImport,
    BuildCall {
        has_this: bool,
        arg_count: usize,
        kind: CallKind,
        super_callee: bool,
    },
    BuildClosure {
        body: FuncId,
        name: String,
        kind: FunctionKind,
        cap_names: Vec<String>,
    },
    BuildClassWithHeritage {
        ctor: FuncId,
        name: String,
        members: ConstId,
        member_attrs: Vec<abcd_ir::op::MemberAttrs>,
        sendable: bool,
    },
    BuildPrivate {
        name: String,
        test: bool,
    },
    BuildCreateGenerator,
    BuildYield,
    BuildGenDriver(bool),
    BuildAwait(bool),
    BuildAsyncDriver(bool),
    BuildAsyncGenResolve,
    BuildSuperDyn,
    BuildArraySpread,
    BuildRestObject(usize),
    BuildFallback {
        op: &'static str,
        note: &'static str,
        count: usize,
    },
}

/// Chase `Mov` passthroughs to the underlying definition (bounded).
pub(super) fn chase_mov(module: &Module, mut v: ValueId) -> ValueId {
    for _ in 0..16 {
        let Some(value) = module.value(v) else {
            break;
        };
        match value.def {
            ValueDef::Inst(iid) => match module.inst(iid) {
                Some(inst) => match &inst.op {
                    Op::Mov { src } => {
                        v = *src;
                        continue;
                    }
                    _ => break,
                },
                None => break,
            },
            _ => break,
        }
    }
    v
}

/// Resolve a value to the constant it loads, if any.
pub(super) fn const_id_of(module: &Module, v: ValueId) -> Option<ConstId> {
    match module.value(v)?.def {
        ValueDef::Const(cid) => Some(cid),
        ValueDef::Inst(iid) => match &module.inst(iid)?.op {
            Op::LoadConst(cid) => Some(*cid),
            _ => None,
        },
        _ => None,
    }
}
