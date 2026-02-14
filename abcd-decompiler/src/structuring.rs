use std::collections::{HashMap, HashSet};

use abcd_ir::cfg::{BlockId, CFG};
use abcd_ir::expr::{BinOp, Expr, UnOp};
use abcd_ir::instruction::{Instruction, TryBlockInfo};
use abcd_ir::stmt::Stmt;

use crate::expr_recovery::{self, BlockRecovery, StringResolver};

/// Decompile a method's instructions into structured JavaScript statements.
pub fn structure_method(
    instructions: &[Instruction],
    cfg: &CFG,
    try_blocks: &[TryBlockInfo],
    resolver: &dyn StringResolver,
    method_off: u32,
    num_vregs: u32,
    num_args: u32,
) -> Vec<Stmt> {
    if cfg.blocks.is_empty() {
        return vec![];
    }

    let loop_headers = find_loop_headers(cfg);

    let mut ctx = StructCtx {
        cfg,
        instructions,
        recoveries: (0..cfg.blocks.len()).map(|_| None).collect(),
        try_blocks,
        loop_headers,
        visited: vec![false; cfg.blocks.len()],
        resolver,
        method_off,
        num_vregs,
        num_args,
    };

    // Recover entry block with no predecessor state
    ctx.ensure_recovered(cfg.entry, None, &HashMap::new());

    let mut result = Vec::new();
    emit_block_range(&mut ctx, &mut result, cfg.entry, None);
    result
}

struct StructCtx<'a> {
    cfg: &'a CFG,
    instructions: &'a [Instruction],
    recoveries: Vec<Option<BlockRecovery>>,
    try_blocks: &'a [TryBlockInfo],
    loop_headers: HashSet<BlockId>,
    visited: Vec<bool>,
    resolver: &'a dyn StringResolver,
    method_off: u32,
    num_vregs: u32,
    num_args: u32,
}

impl<'a> StructCtx<'a> {
    /// Ensure a block is recovered, optionally with predecessor state.
    fn ensure_recovered(
        &mut self,
        block_id: BlockId,
        pred_acc: Option<&Expr>,
        pred_regs: &HashMap<u16, Expr>,
    ) {
        if self.recoveries[block_id].is_some() {
            return;
        }
        let block = &self.cfg.blocks[block_id];
        let block_insns = &self.instructions[block.first_insn..block.last_insn];
        let recovery = if let Some(acc) = pred_acc {
            expr_recovery::recover_block_with_state(
                block_insns,
                self.resolver,
                self.method_off,
                self.num_vregs,
                self.num_args,
                acc.clone(),
                pred_regs.clone(),
            )
        } else {
            expr_recovery::recover_block(
                block_insns,
                self.resolver,
                self.method_off,
                self.num_vregs,
                self.num_args,
            )
        };
        self.recoveries[block_id] = Some(recovery);
    }

    /// Propagate state from current block to a successor and ensure it's recovered.
    fn propagate_and_recover(&mut self, from: BlockId, to: BlockId) {
        if self.recoveries[to].is_some() {
            return;
        }
        if let Some(ref pred) = self.recoveries[from] {
            let acc = pred.final_acc.clone();
            let regs = pred.final_regs.clone();
            self.ensure_recovered(to, Some(&acc), &regs);
        } else {
            self.ensure_recovered(to, None, &HashMap::new());
        }
    }

    fn get_recovery(&self, block_id: BlockId) -> &BlockRecovery {
        self.recoveries[block_id]
            .as_ref()
            .expect("block should be recovered before access")
    }
}

/// Find blocks that are targets of back edges (loop headers).
fn find_loop_headers(cfg: &CFG) -> HashSet<BlockId> {
    let mut headers = HashSet::new();
    for block in &cfg.blocks {
        for &succ in &block.succs {
            if succ <= block.id {
                headers.insert(succ);
            }
        }
    }
    headers
}

/// Find the try block that starts at or contains the given block offset.
fn find_try_block_for(try_blocks: &[TryBlockInfo], block_start: u32) -> Option<&TryBlockInfo> {
    try_blocks.iter().find(|tb| tb.start_pc == block_start)
}

fn emit_block_range(
    ctx: &mut StructCtx,
    result: &mut Vec<Stmt>,
    start: BlockId,
    stop_before: Option<BlockId>,
) {
    let mut current = start;

    loop {
        if current >= ctx.cfg.blocks.len() || ctx.visited[current] {
            break;
        }
        if let Some(stop) = stop_before {
            if current == stop {
                break;
            }
        }

        let block = &ctx.cfg.blocks[current];

        // Check if this block starts a try region
        if let Some(tb) = find_try_block_for(ctx.try_blocks, block.start) {
            let try_end = tb.start_pc + tb.length;
            let catch_blocks: Vec<_> = tb.catch_blocks.clone();

            let mut try_body = Vec::new();
            emit_try_body(ctx, &mut try_body, current, try_end);

            let mut catch_body = Vec::new();
            let mut catch_binding = None;
            for cb in &catch_blocks {
                if let Some(catch_block_id) = ctx.cfg.block_at_offset(cb.handler_pc) {
                    if !ctx.visited[catch_block_id] {
                        if cb.type_idx == 0 {
                            catch_binding = Some("$err".to_string());
                        }
                        ctx.ensure_recovered(catch_block_id, None, &HashMap::new());
                        emit_block_range(ctx, &mut catch_body, catch_block_id, None);
                    }
                }
            }

            result.push(Stmt::TryCatch {
                try_body,
                catch_binding,
                catch_body,
                finally_body: vec![],
            });

            if let Some(next) = find_next_unvisited(ctx, current) {
                current = next;
                continue;
            }
            break;
        }

        // Check if this is a loop header
        if ctx.loop_headers.contains(&current) && !ctx.visited[current] {
            emit_loop(ctx, result, current);
            if let Some(next) = find_next_unvisited(ctx, current) {
                current = next;
                continue;
            }
            break;
        }

        // Ensure this block is recovered
        ctx.ensure_recovered(current, None, &HashMap::new());
        ctx.visited[current] = true;

        result.extend(ctx.get_recovery(current).stmts.clone());

        if block.first_insn >= block.last_insn {
            break;
        }

        let last_insn = &ctx.instructions[block.last_insn - 1];
        let mn = last_insn.opcode.mnemonic();

        match block.succs.len() {
            0 => break,
            1 => {
                let next = block.succs[0];
                if next <= current && ctx.visited[next] {
                    result.push(Stmt::Continue);
                    break;
                }
                // Propagate state to successor
                ctx.propagate_and_recover(current, next);
                current = next;
            }
            2 => {
                let fall_through = block.succs[0];
                let jump_target = block.succs[1];

                let acc_expr = ctx.get_recovery(current).final_acc.clone();
                let cond = make_condition(mn, acc_expr);

                if jump_target <= current && ctx.visited[jump_target] {
                    result.push(Stmt::If {
                        cond,
                        then_body: vec![Stmt::Break],
                        else_body: vec![],
                    });
                    ctx.propagate_and_recover(current, fall_through);
                    current = fall_through;
                    continue;
                }

                if jump_target > current {
                    // Propagate state before combining conditions
                    ctx.propagate_and_recover(current, fall_through);
                    let (combined_cond, actual_then_start) =
                        try_combine_conditions(ctx, fall_through, jump_target, cond.clone(), mn);

                    let then_start_block = &ctx.cfg.blocks[actual_then_start];
                    let ft_ends_at_target = then_start_block.succs.len() == 1
                        && then_start_block.succs[0] == jump_target
                        && !ctx.visited[actual_then_start];

                    if ft_ends_at_target {
                        // Propagate state to actual then start
                        ctx.propagate_and_recover(current, actual_then_start);
                        let mut then_body = Vec::new();
                        emit_block_range(ctx, &mut then_body, actual_then_start, Some(jump_target));
                        result.push(Stmt::If {
                            cond: combined_cond,
                            then_body,
                            else_body: vec![],
                        });
                        // Propagate state to jump target
                        ctx.propagate_and_recover(current, jump_target);
                        current = jump_target;
                    } else {
                        ctx.propagate_and_recover(current, actual_then_start);
                        let mut then_body = Vec::new();
                        emit_block_range(ctx, &mut then_body, actual_then_start, Some(jump_target));

                        if !ctx.visited[jump_target] {
                            ctx.propagate_and_recover(current, jump_target);
                            let mut else_body = Vec::new();
                            emit_block_range(ctx, &mut else_body, jump_target, stop_before);
                            result.push(Stmt::If {
                                cond: combined_cond,
                                then_body,
                                else_body,
                            });
                        } else {
                            result.push(Stmt::If {
                                cond: combined_cond,
                                then_body,
                                else_body: vec![],
                            });
                        }
                        break;
                    }
                } else {
                    result.push(Stmt::Comment(format!("back jump to block {jump_target}")));
                    ctx.propagate_and_recover(current, fall_through);
                    current = fall_through;
                }
            }
            _ => {
                let next = block.succs[0];
                ctx.propagate_and_recover(current, next);
                current = next;
            }
        }
    }
}

/// Emit a loop structure starting at the given header block.
fn emit_loop(ctx: &mut StructCtx, result: &mut Vec<Stmt>, header: BlockId) {
    let block = &ctx.cfg.blocks[header];

    ctx.ensure_recovered(header, None, &HashMap::new());

    if block.succs.len() == 2 {
        let fall_through = block.succs[0];
        let jump_target = block.succs[1];

        ctx.visited[header] = true;

        let last_insn = &ctx.instructions[block.last_insn - 1];
        let mn = last_insn.opcode.mnemonic();
        let acc_expr = ctx.get_recovery(header).final_acc.clone();

        result.extend(ctx.get_recovery(header).stmts.clone());

        if jump_target > header && fall_through <= jump_target {
            let cond = make_condition(mn, acc_expr);
            ctx.propagate_and_recover(header, fall_through);
            let mut body = Vec::new();
            emit_block_range(ctx, &mut body, fall_through, Some(jump_target));
            result.push(Stmt::While { cond, body });
            if !ctx.visited[jump_target] {
                ctx.propagate_and_recover(header, jump_target);
                emit_block_range(ctx, result, jump_target, None);
            }
        } else {
            let cond = negate_expr(make_condition(mn, acc_expr));
            ctx.propagate_and_recover(header, jump_target);
            let mut body = Vec::new();
            emit_block_range(ctx, &mut body, jump_target, Some(header));
            result.push(Stmt::While { cond, body });
            if !ctx.visited[fall_through] {
                ctx.propagate_and_recover(header, fall_through);
                emit_block_range(ctx, result, fall_through, None);
            }
        }
    } else {
        ctx.visited[header] = true;
        result.extend(ctx.get_recovery(header).stmts.clone());

        let mut body = Vec::new();
        if block.succs.len() == 1 && !ctx.visited[block.succs[0]] {
            ctx.propagate_and_recover(header, block.succs[0]);
            emit_block_range(ctx, &mut body, block.succs[0], Some(header));
        }
        result.push(Stmt::While {
            cond: Expr::BoolLit(true),
            body,
        });
    }
}

/// Emit blocks within a try body region (from start until try_end offset).
fn emit_try_body(ctx: &mut StructCtx, result: &mut Vec<Stmt>, start: BlockId, try_end: u32) {
    let mut current = start;
    loop {
        if current >= ctx.cfg.blocks.len() || ctx.visited[current] {
            break;
        }
        let block = &ctx.cfg.blocks[current];
        if block.start >= try_end {
            break;
        }

        ctx.ensure_recovered(current, None, &HashMap::new());
        ctx.visited[current] = true;
        result.extend(ctx.get_recovery(current).stmts.clone());

        if block.first_insn >= block.last_insn {
            break;
        }

        let last_insn = &ctx.instructions[block.last_insn - 1];
        let mn = last_insn.opcode.mnemonic();

        match block.succs.len() {
            0 => break,
            1 => {
                let next = block.succs[0];
                if ctx.cfg.blocks[next].start >= try_end {
                    break;
                }
                ctx.propagate_and_recover(current, next);
                current = next;
            }
            2 => {
                let fall_through = block.succs[0];
                let jump_target = block.succs[1];
                let acc_expr = ctx.get_recovery(current).final_acc.clone();
                let cond = make_condition(mn, acc_expr);

                let mut then_body = Vec::new();
                if !ctx.visited[fall_through] && ctx.cfg.blocks[fall_through].start < try_end {
                    ctx.propagate_and_recover(current, fall_through);
                    emit_try_body(ctx, &mut then_body, fall_through, try_end);
                }

                if !ctx.visited[jump_target] && ctx.cfg.blocks[jump_target].start < try_end {
                    ctx.propagate_and_recover(current, jump_target);
                    let mut else_body = Vec::new();
                    emit_try_body(ctx, &mut else_body, jump_target, try_end);
                    result.push(Stmt::If {
                        cond,
                        then_body,
                        else_body,
                    });
                } else {
                    result.push(Stmt::If {
                        cond,
                        then_body,
                        else_body: vec![],
                    });
                }
                break;
            }
            _ => {
                let next = block.succs[0];
                ctx.propagate_and_recover(current, next);
                current = next;
            }
        }
    }
}

/// Try to combine short-circuit && and || conditions.
/// Returns (combined_condition, actual_then_start) where actual_then_start
/// is the block ID where the then-body should start (after consuming condition chains).
fn try_combine_conditions(
    ctx: &mut StructCtx,
    fall_through: BlockId,
    jump_target: BlockId,
    cond: Expr,
    _mn: &str,
) -> (Expr, BlockId) {
    if fall_through >= ctx.cfg.blocks.len() || ctx.visited[fall_through] {
        return (cond, fall_through);
    }

    let ft_block = &ctx.cfg.blocks[fall_through];
    if ft_block.succs.len() != 2 {
        return (cond, fall_through);
    }

    ctx.ensure_recovered(fall_through, None, &HashMap::new());

    if !ctx.get_recovery(fall_through).stmts.is_empty() {
        return (cond, fall_through);
    }

    let ft_jump = ft_block.succs[1];
    let ft_fall = ft_block.succs[0];

    // && pattern: both blocks jump to the same target on false
    if ft_jump == jump_target {
        let ft_last = &ctx.instructions[ft_block.last_insn - 1];
        let ft_mn = ft_last.opcode.mnemonic();
        let ft_acc = ctx.get_recovery(fall_through).final_acc.clone();
        let cond2 = make_condition(ft_mn, ft_acc);

        ctx.visited[fall_through] = true;

        let combined = Expr::BinaryOp {
            op: BinOp::And,
            lhs: Box::new(cond),
            rhs: Box::new(cond2),
        };

        // Propagate state to next fall-through for recursive combination
        ctx.propagate_and_recover(fall_through, ft_fall);
        return try_combine_conditions(ctx, ft_fall, jump_target, combined, ft_mn);
    }

    // || pattern: fall-through of B goes to same target as A's jump
    if ft_fall == jump_target {
        let ft_last = &ctx.instructions[ft_block.last_insn - 1];
        let ft_mn = ft_last.opcode.mnemonic();
        let ft_acc = ctx.get_recovery(fall_through).final_acc.clone();
        let cond2 = make_condition(ft_mn, ft_acc);

        ctx.visited[fall_through] = true;

        let combined = Expr::BinaryOp {
            op: BinOp::Or,
            lhs: Box::new(cond),
            rhs: Box::new(cond2),
        };

        // Propagate state to next jump target for recursive combination
        ctx.propagate_and_recover(fall_through, ft_jump);
        return try_combine_conditions(ctx, ft_jump, jump_target, combined, ft_mn);
    }

    (cond, fall_through)
}

fn find_next_unvisited(ctx: &StructCtx, after: BlockId) -> Option<BlockId> {
    for i in (after + 1)..ctx.cfg.blocks.len() {
        if !ctx.visited[i] && !ctx.cfg.blocks[i].is_catch_handler {
            return Some(i);
        }
    }
    None
}

/// Build the condition expression for a conditional branch.
fn make_condition(mnemonic: &str, acc: Expr) -> Expr {
    match mnemonic {
        "jeqz" | "wide.jeqz" => acc,
        "jnez" | "wide.jnez" => negate_expr(acc),
        _ => acc,
    }
}

fn negate_expr(expr: Expr) -> Expr {
    match expr {
        Expr::UnaryOp {
            op: UnOp::Not,
            expr: inner,
        } => *inner,
        Expr::BinaryOp {
            op: BinOp::StrictEq,
            lhs,
            rhs,
        } => Expr::BinaryOp {
            op: BinOp::StrictNotEq,
            lhs,
            rhs,
        },
        Expr::BinaryOp {
            op: BinOp::StrictNotEq,
            lhs,
            rhs,
        } => Expr::BinaryOp {
            op: BinOp::StrictEq,
            lhs,
            rhs,
        },
        Expr::BinaryOp {
            op: BinOp::Eq,
            lhs,
            rhs,
        } => Expr::BinaryOp {
            op: BinOp::NotEq,
            lhs,
            rhs,
        },
        Expr::BinaryOp {
            op: BinOp::NotEq,
            lhs,
            rhs,
        } => Expr::BinaryOp {
            op: BinOp::Eq,
            lhs,
            rhs,
        },
        Expr::BinaryOp {
            op: BinOp::Lt,
            lhs,
            rhs,
        } => Expr::BinaryOp {
            op: BinOp::Ge,
            lhs,
            rhs,
        },
        Expr::BinaryOp {
            op: BinOp::Ge,
            lhs,
            rhs,
        } => Expr::BinaryOp {
            op: BinOp::Lt,
            lhs,
            rhs,
        },
        Expr::BinaryOp {
            op: BinOp::Gt,
            lhs,
            rhs,
        } => Expr::BinaryOp {
            op: BinOp::Le,
            lhs,
            rhs,
        },
        Expr::BinaryOp {
            op: BinOp::Le,
            lhs,
            rhs,
        } => Expr::BinaryOp {
            op: BinOp::Gt,
            lhs,
            rhs,
        },
        Expr::BoolLit(b) => Expr::BoolLit(!b),
        other => Expr::UnaryOp {
            op: UnOp::Not,
            expr: Box::new(other),
        },
    }
}
