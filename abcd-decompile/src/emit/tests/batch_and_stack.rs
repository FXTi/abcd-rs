//! Multi-batch streaming, orphan-lexenv prefiltering, Round-3 ops, and 256 KiB stack tests.

use super::*;

#[test]
fn orphan_lexenv_prefilter_matches_naive_full_module_scan() {
    use abcd_ir::function::{Catch, DebugData, LocalName, LocalScope, TryRegion};
    use abcd_ir::op::ModuleVarKind;

    let mut m = mk_module();

    // 1. Plain functions without lexvars (majority path skipped by prefilter).
    for k in 0..40 {
        let f = add_fn(&mut m, &format!("plain_{k}"));
        let b = entry_of(&m, f);
        let c = m.consts.push(Const::number(k as f64));
        let v = emit_val(&mut m, b, Op::LoadConst(c));
        push_inst(&mut m, b, Op::Return { value: Some(v) });
    }

    // 2. Function with unnamed `NewLexEnv` + `PutLexVar` / `GetLexVar` (`v0_0`, `v1_2`).
    let f_lex = add_fn(&mut m, "with_lex");
    {
        let b = entry_of(&m, f_lex);
        let _env = emit_val(
            &mut m,
            b,
            Op::NewLexEnv {
                num_vars: 2,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let c = m.consts.push(Const::number(1.0));
        let v = emit_val(&mut m, b, Op::LoadConst(c));
        push_inst(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 1,
                value: v,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let rd = emit_val(
            &mut m,
            b,
            Op::GetLexVar {
                level: 3,
                slot: 2,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(rd) });
    }

    // 3. Function reading a global whose identifier happens to match `v<d>_<d>`.
    let f_glob = add_fn(&mut m, "with_fallback_global");
    {
        let b = entry_of(&m, f_glob);
        let gsym = m.sym.intern("v4_7");
        let g = emit_val(
            &mut m,
            b,
            Op::TryGetGlobal {
                name: gsym,
                default: None,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(g) });
    }

    // 4. Function whose debug param_names and catch local_names match `v<d>_<d>`.
    let f_dbg = add_fn(&mut m, "with_fallback_debug");
    {
        let _this = add_param(&mut m, f_dbg);
        let p = add_param(&mut m, f_dbg);
        let b0 = entry_of(&m, f_dbg);
        let bh = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(f_dbg).unwrap().blocks.push(bh);
        m.block_mut(bh)
            .unwrap()
            .preds
            .push(abcd_ir::function::Edge {
                from: b0,
                kind: abcd_ir::function::EdgeKind::Exceptional,
            });
        let exc = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::ExceptionParam(bh),
            ty: Ty::Any,
        });
        m.func_mut(f_dbg).unwrap().try_regions.push(TryRegion {
            protected: vec![b0],
            catches: vec![Catch {
                handler: bh,
                exception: exc,
                type_class: None,
            }],
        });
        let call_res = emit_val(
            &mut m,
            b0,
            Op::Call {
                callee: p,
                this: None,
                args: vec![],
                kind: CallKind::Direct,
            },
        );
        push_inst(
            &mut m,
            b0,
            Op::Return {
                value: Some(call_res),
            },
        );
        let handler_ret = push_inst(&mut m, bh, Op::Return { value: Some(exc) });

        let psym = m.sym.intern("v5_6");
        let lsym = m.sym.intern("v7_8");
        m.func_mut(f_dbg).unwrap().debug = Some(DebugData {
            param_names: vec![psym],
            local_names: vec![LocalName {
                name: lsym,
                ty: None,
                scope: Some(LocalScope {
                    start: handler_ret,
                    end: handler_ret,
                }),
            }],
            ..DebugData::default()
        });
    }

    // 5. Module slot resolved via TDZ guard to `v9_10`, read in a separate function.
    let f_mod_tdz = add_fn(&mut m, "mod_tdz");
    {
        let b = entry_of(&m, f_mod_tdz);
        let mv = emit_val(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::Local,
            },
        );
        let msym = m.sym.intern("v9_10");
        push_inst(
            &mut m,
            b,
            Op::ThrowUndefinedIfHoleWithName {
                name: msym,
                value: mv,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(mv) });
    }
    let f_mod_reader = add_fn(&mut m, "mod_reader");
    {
        let b = entry_of(&m, f_mod_reader);
        let mv = emit_val(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::Local,
            },
        );
        let mv2 = emit_val(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::Local,
            },
        );
        let sum = emit_val(
            &mut m,
            b,
            Op::BinaryOp {
                op: BinOp::Add,
                left: mv2,
                right: mv,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(sum) });
    }

    // 5b. Named `NewLexEnvWithName` + `GetLexVar`/`PutLexVar` MUST be skipped by
    //     `func_may_have_orphan_lexenv` when no fallback `v<d>_<d>` slot exists.
    let f_named_parent = add_fn(&mut m, "named_parent");
    let f_named_child = add_fn(&mut m, "named_child");
    {
        let b_p = entry_of(&m, f_named_parent);
        let s_x = m.sym.intern("namedSlot");
        let cs_x = m.consts.intern(Const::String(s_x));
        let arr = m.consts.push_array(vec![cs_x]);
        let _ = emit_val(
            &mut m,
            b_p,
            Op::NewLexEnvWithName {
                num_vars: 1,
                scope_names: arr,
            },
        );
        let c = m.consts.push(Const::number(42.0));
        let v = emit_val(&mut m, b_p, Op::LoadConst(c));
        push_inst(
            &mut m,
            b_p,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: v,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let df = emit_val(
            &mut m,
            b_p,
            Op::DefineFunc {
                body: f_named_child,
                captures: vec![],
                length: 0,
            },
        );
        push_inst(&mut m, b_p, Op::Return { value: Some(df) });

        let b_c = entry_of(&m, f_named_child);
        let rd = emit_val(
            &mut m,
            b_c,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        push_inst(&mut m, b_c, Op::Return { value: Some(rd) });
    }

    let index = DecompileIndex::build(&m);
    assert!(!func_may_have_orphan_lexenv(
        &m,
        f_named_parent,
        &index,
        false
    ));
    assert!(!func_may_have_orphan_lexenv(
        &m,
        f_named_child,
        &index,
        false
    ));
    assert!(func_may_have_orphan_lexenv(&m, f_lex, &index, false));
    let fast = collect_module_orphan_lexenv_names(&m, &index);
    let mut naive = BTreeSet::new();
    for i in 0..m.functions.len() {
        let rf = recover_func_with_index(&m, FuncId::new(i as u32), &index);
        naive.extend(orphan_lexenv_names_in_func(&rf));
    }
    assert_eq!(fast, naive);
    for expected in ["v0_1", "v3_2", "v4_7", "v5_6", "v7_8", "v9_10"] {
        assert!(fast.contains(expected), "missing {expected} in {fast:?}");
    }
}

#[test]
fn decompile_module_to_writer_multi_batch_and_shared_inline_closures_match() {
    let mut m = mk_module();

    // Shared inline closure referenced BOTH twice inside one function (tail-dup
    // simulation) AND across multiple 256-function batches.
    let shared_inline = add_fn(&mut m, "shared_cb");
    {
        let _this = add_param(&mut m, shared_inline);
        let x = add_param(&mut m, shared_inline);
        let b = entry_of(&m, shared_inline);
        push_inst(&mut m, b, Op::Return { value: Some(x) });
    }

    // Span >2 full bounded batches AND attach 25 inline closures to several roots so
    // `next_bounded_top_batch` exercises adaptive transitive batch capping (`<= 512`).
    let total_top = MAX_BATCH_PREPARED_FUNCS + 80;
    for k in 0..total_top {
        let name = if k == total_top - 1 {
            "func_main_0".to_string()
        } else {
            format!("top_fn_{k}")
        };
        let f = add_fn(&mut m, &name);
        let _this = add_param(&mut m, f);
        let b = entry_of(&m, f);
        if k < 30 {
            let mut acc_v = None;
            for j in 0..25 {
                let child = add_fn(&mut m, &format!("inline_{k}_{j}"));
                let _cthis = add_param(&mut m, child);
                let cb = entry_of(&m, child);
                let cc = m.consts.push(Const::number((k * 100 + j) as f64));
                let cv = emit_val(&mut m, cb, Op::LoadConst(cc));
                push_inst(&mut m, cb, Op::Return { value: Some(cv) });
                let df = emit_val(
                    &mut m,
                    b,
                    Op::DefineFunc {
                        body: child,
                        captures: vec![],
                        length: 0,
                    },
                );
                let cl = emit_val(&mut m, b, Op::AllocClosure { func: df });
                acc_v = Some(match acc_v {
                    None => cl,
                    Some(prev) => emit_val(
                        &mut m,
                        b,
                        Op::BinaryOp {
                            op: BinOp::Add,
                            left: cl,
                            right: prev,
                        },
                    ),
                });
            }
            push_inst(&mut m, b, Op::Return { value: acc_v });
            continue;
        }
        if k % 100 == 0 {
            // Emit `shared_inline` twice inside the same function AND across batches.
            let df1 = emit_val(
                &mut m,
                b,
                Op::DefineFunc {
                    body: shared_inline,
                    captures: vec![],
                    length: 1,
                },
            );
            let cl1 = emit_val(&mut m, b, Op::AllocClosure { func: df1 });
            let df2 = emit_val(
                &mut m,
                b,
                Op::DefineFunc {
                    body: shared_inline,
                    captures: vec![],
                    length: 1,
                },
            );
            let cl2 = emit_val(&mut m, b, Op::AllocClosure { func: df2 });
            let pair = emit_val(
                &mut m,
                b,
                Op::BinaryOp {
                    op: BinOp::Add,
                    left: cl2,
                    right: cl1,
                },
            );
            push_inst(&mut m, b, Op::Return { value: Some(pair) });
        } else {
            let c = m.consts.push(Const::number(k as f64));
            let v = emit_val(&mut m, b, Op::LoadConst(c));
            push_inst(&mut m, b, Op::Return { value: Some(v) });
        }
    }

    for opts in [
        EmitOptions::default(),
        EmitOptions {
            ts: true,
            call_entry: true,
            ..EmitOptions::default()
        },
    ] {
        let buffered = decompile_module(&m, &opts);
        let mut raw_out = Vec::new();
        let writer_stats =
            decompile_module_to_writer(&m, &opts, &mut raw_out).expect("stream to Vec");
        let streamed_text = String::from_utf8(raw_out).expect("UTF-8");
        assert_eq!(streamed_text, buffered.text);
        assert_eq!(writer_stats, buffered.stats);
        assert_eq!(writer_stats.functions, total_top);
    }

    // Verify I/O write error propagates cleanly without panicking.
    struct FailAfter {
        rem: usize,
    }
    impl Write for FailAfter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            if self.rem == 0 {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::BrokenPipe,
                    "simulated sink failure",
                ));
            }
            let n = buf.len().min(self.rem);
            self.rem -= n;
            Ok(n)
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    let mut failing = FailAfter { rem: 128 };
    let err = decompile_module_to_writer(&m, &EmitOptions::default(), &mut failing)
        .expect_err("must surface BrokenPipe");
    assert_eq!(err.kind(), std::io::ErrorKind::BrokenPipe);
}

#[test]
fn emit_walkers_survive_deep_nesting_and_cycles_on_256k_stack() {
    // Build 5,000-deep trees (a recursive debug-build walker uses >1 MiB of call
    // stack at depth 5,000 and overflows a 256 KiB stack immediately).
    let mut deep_expr = Expr::Ident("v12_34".to_string());
    for _ in 0..5_000 {
        deep_expr = Expr::Unary {
            op: UnOp::LogicalNot,
            operand: Box::new(deep_expr),
        };
    }
    let rf = RecoveredFunc {
        func: FuncId::new(0),
        name: "deep".to_string(),
        kind: FunctionKind::Function,
        params: Vec::new(),
        hidden_params: 0,
        blocks: vec![crate::recover::BlockStmts {
            block: BlockId::new(0),
            preds: Vec::new(),
            stmts: vec![Stmt::Expr(deep_expr)],
        }],
        histogram: BTreeMap::new(),
    };

    let mut deep_nodes = vec![SNode::Stmts(vec![
        Leaf::Raw(Stmt::ScopePush { names: vec![None] }),
        Leaf::Raw(Stmt::LexStore {
            level: 0,
            slot: 0,
            own: true,
            name: "inner_lex".to_string(),
            value: Expr::Temp {
                value: ValueId::new(0),
                name: "esc_tmp".to_string(),
            },
        }),
    ])];
    for step in 0..4_000 {
        deep_nodes = if step % 2 == 0 {
            vec![SNode::If {
                cond: id("c"),
                then: deep_nodes,
                otherwise: Vec::new(),
            }]
        } else {
            vec![SNode::DoWhile {
                label: None,
                body: deep_nodes,
                cond: id("c"),
            }]
        };
    }
    deep_nodes.insert(
        0,
        SNode::If {
            cond: id("c0"),
            then: vec![SNode::Stmts(vec![Leaf::Raw(Stmt::Declare {
                name: "esc_tmp".to_string(),
                mutable: false,
                value: num(1.0),
                value_id: ValueId::new(0),
            })])],
            otherwise: Vec::new(),
        },
    );

    // Flat 5,000-function DefineFunc chain + cycle (`f_4999 -> f_0`) and a
    // 5,000-deep ConstPool ArrayLiteral chain.
    let mut m = mk_module();
    let mut deep_const_id = m.consts.push(Const::method_ref(FuncId::new(7)));
    for _ in 0..5_000 {
        deep_const_id = m.consts.push_array(vec![deep_const_id]);
    }
    let chain_len = 5_000usize;
    let chain: Vec<FuncId> = (0..chain_len)
        .map(|i| add_fn(&mut m, &format!("f_{i}")))
        .collect();
    for i in 0..chain_len {
        let b = entry_of(&m, chain[i]);
        let next = chain[(i + 1) % chain_len];
        let _ = emit_val(
            &mut m,
            b,
            Op::DefineFunc {
                body: next,
                captures: vec![],
                length: 0,
            },
        );
        push_inst(&mut m, b, Op::Return { value: None });
    }

    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name("emit-256k-stack".to_string())
            .stack_size(256 * 1024)
            .spawn_scoped(s, || {
                let orphans = orphan_lexenv_names_in_func(&rf);
                assert_eq!(orphans, BTreeSet::from(["v12_34".to_string()]));

                let mut mrefs = BTreeSet::new();
                collect_method_refs(&m, deep_const_id, &mut mrefs);
                assert_eq!(mrefs, BTreeSet::from([FuncId::new(7)]));

                assert_eq!(lex_decls(&deep_nodes, &[]), vec!["inner_lex".to_string()]);
                assert_eq!(
                    escaped_temps(&deep_nodes),
                    BTreeSet::from(["esc_tmp".to_string()])
                );

                let batch = collect_batch_funcs(&m, &[chain[0]]);
                assert_eq!(batch.len(), chain_len);
                drop((rf, deep_nodes));
            })
            .expect("spawn 256k scoped thread");
        handle.join().expect("256k thread must not stack-overflow");
    });
}

#[test]
fn round3_jump_nez_and_jump_eqz_conditions_emit_clean_if_and_while() {
    use abcd_ir::function::{Edge, EdgeKind};

    let mut m = mk_module();
    let f = add_fn(&mut m, "func_main_0");
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);

    let b0 = entry_of(&m, f);
    let b_then = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(b_then);
    let b_else = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(b_else);
    let b_hdr = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(b_hdr);
    let b_body = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(b_body);
    let b_exit = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(b_exit);

    // `if (JumpNez(p1))` -> `if (p1)`; inside else `if (JumpEqz(p2))` -> `if (!p2)`.
    let c_nez = emit_val(
        &mut m,
        b0,
        Op::UnaryOp {
            op: UnOp::JumpNez,
            operand: p1,
        },
    );
    push_inst(
        &mut m,
        b0,
        Op::CondBranch {
            cond: c_nez,
            true_dest: b_then,
            false_dest: b_else,
        },
    );
    push_inst(&mut m, b_then, Op::Return { value: Some(p1) });

    let c_eqz = emit_val(
        &mut m,
        b_else,
        Op::UnaryOp {
            op: UnOp::JumpEqz,
            operand: p2,
        },
    );
    push_inst(
        &mut m,
        b_else,
        Op::CondBranch {
            cond: c_eqz,
            true_dest: b_hdr,
            false_dest: b_exit,
        },
    );

    let w_cond = emit_val(
        &mut m,
        b_hdr,
        Op::UnaryOp {
            op: UnOp::JumpNez,
            operand: p2,
        },
    );
    push_inst(
        &mut m,
        b_hdr,
        Op::CondBranch {
            cond: w_cond,
            true_dest: b_body,
            false_dest: b_exit,
        },
    );
    push_inst(&mut m, b_body, Op::Branch { dest: b_hdr });
    push_inst(&mut m, b_exit, Op::Return { value: Some(p2) });

    for (from, to) in [
        (b0, b_then),
        (b0, b_else),
        (b_else, b_hdr),
        (b_else, b_exit),
        (b_hdr, b_body),
        (b_hdr, b_exit),
        (b_body, b_hdr),
    ] {
        m.block_mut(to).unwrap().preds.push(Edge {
            from,
            kind: EdgeKind::Normal,
        });
    }
    m.classes[0].methods.push(f);

    let out = decompile_module(&m, &EmitOptions::default());
    assert!(out.stats.fallback_comments.is_empty(), "{}", out.text);
    assert!(
        out.text.contains("if (p1) {"),
        "JumpNez -> if (p1):\n{}",
        out.text
    );
    assert!(
        out.text.contains("if (!p2) {"),
        "JumpEqz -> if (!p2):\n{}",
        out.text
    );
    assert!(
        out.text.contains("while (p2) {"),
        "JumpNez while condition:\n{}",
        out.text
    );
}

#[test]
fn round3_call_kinds_topropertykey_symbol_concurrent_and_patch_lex() {
    let mut m = mk_module();
    let super_arrow = add_fn(&mut m, "arr");
    m.func_mut(super_arrow).unwrap().kind = FunctionKind::Arrow;
    {
        let _this = add_param(&mut m, super_arrow);
        let a0 = add_param(&mut m, super_arrow);
        let b = entry_of(&m, super_arrow);
        let sup = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: a0,
                this: None,
                args: vec![a0],
                kind: CallKind::SuperArrow,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(sup) });
    }
    assert!(fn_uses_super(&m, super_arrow));

    let f = add_fn(&mut m, "func_main_0");
    m.classes[0].methods.push(f);
    let this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let b = entry_of(&m, f);

    let new_sp = emit_val(
        &mut m,
        b,
        Op::Call {
            callee: p1,
            this: None,
            args: vec![p2],
            kind: CallKind::NewSpread,
        },
    );
    let cls_init = emit_val(
        &mut m,
        b,
        Op::Call {
            callee: p1,
            this: Some(this),
            args: vec![],
            kind: CallKind::ClassInit,
        },
    );
    let sym_v = emit_val(&mut m, b, Op::LoadSymbol);
    let tpk_dyn = emit_val(
        &mut m,
        b,
        Op::UnaryOp {
            op: UnOp::ToPropertyKey,
            operand: sym_v,
        },
    );
    // Rest-destructure key wrapped in `UnOp::ToPropertyKey` over `"a"`:
    let a_sym = m.sym.intern("a");
    let a_cid = m.consts.push(Const::String(a_sym));
    let a_str = emit_val(&mut m, b, Op::LoadConst(a_cid));
    let a_key = emit_val(
        &mut m,
        b,
        Op::UnaryOp {
            op: UnOp::ToPropertyKey,
            operand: a_str,
        },
    );
    let rest = emit_val(
        &mut m,
        b,
        Op::CreateObjectWithExcludedKeys {
            obj: p1,
            keys: vec![a_key],
        },
    );
    let a_prop = emit_val(
        &mut m,
        b,
        Op::LoadProp {
            object: p1,
            name: a_sym,
        },
    );
    push_inst(&mut m, b, Op::NotifyConcurrentResult { value: new_sp });
    let _env = emit_val(
        &mut m,
        b,
        Op::NewLexEnv {
            num_vars: 3,
            kind: abcd_ir::LexEnvKind::Sendable,
        },
    );
    push_inst(
        &mut m,
        b,
        Op::PutLexVar {
            level: 0,
            slot: 2,
            value: cls_init,
            kind: abcd_ir::LexEnvKind::Sendable,
        },
    );
    push_inst(
        &mut m,
        b,
        Op::PutLexVar {
            level: 0,
            slot: 2,
            value: tpk_dyn,
            kind: abcd_ir::LexEnvKind::Patch,
        },
    );
    let rd_patch = emit_val(
        &mut m,
        b,
        Op::GetLexVar {
            level: 0,
            slot: 2,
            kind: abcd_ir::LexEnvKind::Patch,
        },
    );
    let df = emit_val(
        &mut m,
        b,
        Op::DefineFunc {
            body: super_arrow,
            captures: vec![],
            length: 1,
        },
    );
    let cl = emit_val(&mut m, b, Op::AllocClosure { func: df });
    let sum0 = emit_val(
        &mut m,
        b,
        Op::BinaryOp {
            op: BinOp::Add,
            left: rest,
            right: a_prop,
        },
    );
    let sum1 = emit_val(
        &mut m,
        b,
        Op::BinaryOp {
            op: BinOp::Add,
            left: sum0,
            right: rd_patch,
        },
    );
    let sum2 = emit_val(
        &mut m,
        b,
        Op::BinaryOp {
            op: BinOp::Add,
            left: sum1,
            right: cl,
        },
    );
    push_inst(&mut m, b, Op::Return { value: Some(sum2) });

    let out = decompile_module(&m, &EmitOptions::default());
    assert!(out.stats.fallback_comments.is_empty(), "{}", out.text);
    assert!(out.text.contains("let v999999_2;"), "{}", out.text);
    assert!(out.text.contains("new p1(...p2)"), "{}", out.text);
    assert!(out.text.contains("p1.call(this)"), "{}", out.text);
    assert!(out.text.contains("super(p1)"), "{}", out.text);
    assert!(
        out.text.contains("Reflect.ownKeys({ [Symbol]: 0 })[0]"),
        "{}",
        out.text
    );
    assert!(out.text.contains("const {a, ..."), "{}", out.text);
    assert!(out.text.contains("NotifyConcurrentResult"), "{}", out.text);
}

#[test]
fn round3_async_generator_ops_full_fold() {
    use abcd_ir::function::{Catch, Edge, EdgeKind, TryRegion};

    let mut m = mk_module();
    let f = add_fn(&mut m, "func_main_0");
    m.func_mut(f).unwrap().kind = FunctionKind::AsyncGenerator;
    m.func_mut(f).unwrap().modifiers = abcd_ir::Modifiers::STATIC;
    m.classes[0].methods.push(f);
    let func_param = add_param(&mut m, f);
    let _new_target = add_param(&mut m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);

    let mk_blk = |m: &mut Module| {
        let id = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(f).unwrap().blocks.push(id);
        id
    };
    let b_entry = entry_of(&m, f);
    let b_try = mk_blk(&mut m);
    let b_throw1 = mk_blk(&mut m);
    let b_yield = mk_blk(&mut m);
    let b_ret_arm = mk_blk(&mut m);
    let b_ret_throw = mk_blk(&mut m);
    let b_ret_done = mk_blk(&mut m);
    let b_chk_throw = mk_blk(&mut m);
    let b_throw_ry = mk_blk(&mut m);
    let b_next = mk_blk(&mut m);
    let b_catch = mk_blk(&mut m);

    let ld_num = |m: &mut Module, b: BlockId, x: f64| {
        let c = m.consts.push(Const::number(x));
        emit_val(m, b, Op::LoadConst(c))
    };
    let ld_bool = |m: &mut Module, b: BlockId, v: bool| {
        let c = m.consts.push(Const::Bool(v));
        emit_val(m, b, Op::LoadConst(c))
    };

    // Entry: CreateAsyncGenerator + SetGeneratorState + SuspendGenerator(undefined) + dead drivers.
    let genobj = emit_val(
        &mut m,
        b_entry,
        Op::CreateAsyncGenerator { func: func_param },
    );
    push_inst(&mut m, b_entry, Op::SetGeneratorState { genobj, state: 0 });
    let undef_cid = m.consts.push(Const::Undefined);
    let undef = emit_val(&mut m, b_entry, Op::LoadConst(undef_cid));
    let _ = emit_val(
        &mut m,
        b_entry,
        Op::SuspendGenerator {
            genobj,
            value: undef,
        },
    );
    let _ = emit_val(&mut m, b_entry, Op::ResumeGenerator { genobj });
    let _ = emit_val(&mut m, b_entry, Op::GetResumeMode { genobj });
    push_inst(&mut m, b_entry, Op::Branch { dest: b_try });

    // Pre-yield await + JumpEqz mode==1 dispatch.
    let aw1 = emit_val(
        &mut m,
        b_try,
        Op::AwaitUncaught {
            funcobj: genobj,
            value: p1,
        },
    );
    let _ = emit_val(&mut m, b_try, Op::SuspendGenerator { genobj, value: aw1 });
    let r1 = emit_val(&mut m, b_try, Op::ResumeGenerator { genobj });
    let m1 = emit_val(&mut m, b_try, Op::GetResumeMode { genobj });
    let one1 = ld_num(&mut m, b_try, 1.0);
    let cmp1 = emit_val(
        &mut m,
        b_try,
        Op::Compare {
            op: CmpOp::Eq,
            left: m1,
            right: one1,
        },
    );
    let cond1 = emit_val(
        &mut m,
        b_try,
        Op::UnaryOp {
            op: UnOp::JumpEqz,
            operand: cmp1,
        },
    );
    push_inst(
        &mut m,
        b_try,
        Op::CondBranch {
            cond: cond1,
            true_dest: b_yield,
            false_dest: b_throw1,
        },
    );
    push_inst(&mut m, b_throw1, Op::Throw { value: r1 });

    // Yield point: SetGeneratorState + AsyncGeneratorResolve(genobj, r1, false) + resumption + 3-way.
    push_inst(&mut m, b_yield, Op::SetGeneratorState { genobj, state: 1 });
    let f_bool = ld_bool(&mut m, b_yield, false);
    let _ = emit_val(
        &mut m,
        b_yield,
        Op::AsyncGeneratorResolve {
            genobj,
            value: r1,
            done: f_bool,
        },
    );
    let ry = emit_val(&mut m, b_yield, Op::ResumeGenerator { genobj });
    let my = emit_val(&mut m, b_yield, Op::GetResumeMode { genobj });
    let zero = ld_num(&mut m, b_yield, 0.0);
    let cmp_ret = emit_val(
        &mut m,
        b_yield,
        Op::Compare {
            op: CmpOp::Eq,
            left: my,
            right: zero,
        },
    );
    let cond_ret = emit_val(
        &mut m,
        b_yield,
        Op::UnaryOp {
            op: UnOp::JumpNez,
            operand: cmp_ret,
        },
    );
    push_inst(
        &mut m,
        b_yield,
        Op::CondBranch {
            cond: cond_ret,
            true_dest: b_ret_arm,
            false_dest: b_chk_throw,
        },
    );

    // RETURN(0) arm.
    let aw_r = emit_val(
        &mut m,
        b_ret_arm,
        Op::AwaitUncaught {
            funcobj: genobj,
            value: ry,
        },
    );
    let _ = emit_val(
        &mut m,
        b_ret_arm,
        Op::SuspendGenerator {
            genobj,
            value: aw_r,
        },
    );
    let r_ret = emit_val(&mut m, b_ret_arm, Op::ResumeGenerator { genobj });
    let m_ret = emit_val(&mut m, b_ret_arm, Op::GetResumeMode { genobj });
    let one_r = ld_num(&mut m, b_ret_arm, 1.0);
    let cmp_rt = emit_val(
        &mut m,
        b_ret_arm,
        Op::Compare {
            op: CmpOp::Eq,
            left: m_ret,
            right: one_r,
        },
    );
    let cond_rt = emit_val(
        &mut m,
        b_ret_arm,
        Op::UnaryOp {
            op: UnOp::JumpNez,
            operand: cmp_rt,
        },
    );
    push_inst(
        &mut m,
        b_ret_arm,
        Op::CondBranch {
            cond: cond_rt,
            true_dest: b_ret_throw,
            false_dest: b_ret_done,
        },
    );
    push_inst(&mut m, b_ret_throw, Op::Throw { value: r_ret });
    let t_bool_r = ld_bool(&mut m, b_ret_done, true);
    let res_r = emit_val(
        &mut m,
        b_ret_done,
        Op::AsyncGeneratorResolve {
            genobj,
            value: r_ret,
            done: t_bool_r,
        },
    );
    push_inst(&mut m, b_ret_done, Op::Return { value: Some(res_r) });

    // THROW(1) vs NEXT(2).
    let one2 = ld_num(&mut m, b_chk_throw, 1.0);
    let cmp_th = emit_val(
        &mut m,
        b_chk_throw,
        Op::Compare {
            op: CmpOp::Eq,
            left: my,
            right: one2,
        },
    );
    let cond_th = emit_val(
        &mut m,
        b_chk_throw,
        Op::UnaryOp {
            op: UnOp::JumpNez,
            operand: cmp_th,
        },
    );
    push_inst(
        &mut m,
        b_chk_throw,
        Op::CondBranch {
            cond: cond_th,
            true_dest: b_throw_ry,
            false_dest: b_next,
        },
    );
    push_inst(&mut m, b_throw_ry, Op::Throw { value: ry });

    push_inst(&mut m, b_next, Op::SetGeneratorState { genobj, state: 4 });
    let t_bool = ld_bool(&mut m, b_next, true);
    let fin = emit_val(
        &mut m,
        b_next,
        Op::AsyncGeneratorResolve {
            genobj,
            value: ry,
            done: t_bool,
        },
    );
    push_inst(&mut m, b_next, Op::Return { value: Some(fin) });

    // Catch-all: AsyncGeneratorReject + return.
    let exc = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::ExceptionParam(b_catch),
        ty: Ty::Any,
    });
    let rej = emit_val(
        &mut m,
        b_catch,
        Op::AsyncGeneratorReject { genobj, value: exc },
    );
    push_inst(&mut m, b_catch, Op::Return { value: Some(rej) });

    for (from, to) in [
        (b_entry, b_try),
        (b_try, b_yield),
        (b_try, b_throw1),
        (b_yield, b_ret_arm),
        (b_yield, b_chk_throw),
        (b_ret_arm, b_ret_throw),
        (b_ret_arm, b_ret_done),
        (b_chk_throw, b_throw_ry),
        (b_chk_throw, b_next),
    ] {
        m.block_mut(to).unwrap().preds.push(Edge {
            from,
            kind: EdgeKind::Normal,
        });
    }
    let protected = vec![
        b_try,
        b_throw1,
        b_yield,
        b_ret_arm,
        b_ret_throw,
        b_chk_throw,
        b_throw_ry,
    ];
    for &p in &protected {
        m.block_mut(b_catch).unwrap().preds.push(Edge {
            from: p,
            kind: EdgeKind::Exceptional,
        });
    }
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected,
        catches: vec![Catch {
            handler: b_catch,
            exception: exc,
            type_class: None,
        }],
    });

    let out = decompile_module(&m, &EmitOptions::default());
    assert!(out.stats.fallback_comments.is_empty(), "{}", out.text);
    assert!(
        out.text.contains("async function* func_main_0(p3) {"),
        "{}",
        out.text
    );
    assert!(out.text.contains("yield p3"), "{}", out.text);
    assert!(!out.text.contains("AsyncGeneratorResolve"), "{}", out.text);
    assert!(!out.text.contains("AsyncGeneratorReject"), "{}", out.text);
    assert!(
        out.text.contains("elided SetGeneratorState"),
        "{}",
        out.text
    );
}

// ── Issue #84 Part 1a: Instruction-weight batching & 256 KiB stack tests ──

#[test]
fn batch_inst_weight_deduplicates_shared_inline_closures_and_rolls_back_cleanly() {
    let mut m = mk_module();

    // Shared inline closure: 1 block with 12 instructions (weight = 12).
    let shared_cb = add_fn(&mut m, "shared_cb");
    {
        let _this = add_param(&mut m, shared_cb);
        let mut cur = add_param(&mut m, shared_cb);
        let b = entry_of(&m, shared_cb);
        for k in 0..11 {
            let c = m.consts.push(Const::number((k + 1) as f64));
            let v = emit_val(&mut m, b, Op::LoadConst(c));
            cur = emit_val(
                &mut m,
                b,
                Op::BinaryOp {
                    op: BinOp::Add,
                    left: cur,
                    right: v,
                },
            );
        }
        push_inst(&mut m, b, Op::Return { value: Some(cur) });
    }
    // 11 * 2 + 1 = 23 instructions in `shared_cb`.
    assert_eq!(func_inst_weight(&m, shared_cb), 23);

    // Multi-block function with an empty block (`max(1)` per block).
    let multi_blk = add_fn(&mut m, "multi_blk");
    {
        let b0 = entry_of(&m, multi_blk);
        let b1 = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(multi_blk).unwrap().blocks.push(b1);
        push_inst(&mut m, b0, Op::Branch { dest: b1 });
        // b1 intentionally left with 0 insts -> counts as weight 1!
    }
    assert_eq!(func_inst_weight(&m, multi_blk), 2);
    assert_eq!(func_inst_weight(&m, FuncId::new(9999)), 0);

    // `root_a` (weight 3) references `shared_cb` (weight 23) -> transitive weight 26.
    let root_a = add_fn(&mut m, "root_a");
    {
        let _this = add_param(&mut m, root_a);
        let b = entry_of(&m, root_a);
        let df = emit_val(
            &mut m,
            b,
            Op::DefineFunc {
                body: shared_cb,
                captures: vec![],
                length: 1,
            },
        );
        let cl = emit_val(&mut m, b, Op::AllocClosure { func: df });
        push_inst(&mut m, b, Op::Return { value: Some(cl) });
    }
    assert_eq!(func_inst_weight(&m, root_a), 3);

    // `root_b` (weight 4) ALSO references `shared_cb` via an `AllocObject` shape `MethodRef`.
    // Deduplicated incremental weight when `shared_cb` is already admitted = 4 (NOT 4 + 23 = 27!).
    let root_b = add_fn(&mut m, "root_b");
    {
        let _this = add_param(&mut m, root_b);
        let b = entry_of(&m, root_b);
        let ksym = m.sym.intern("cb");
        let ck = m.consts.intern(Const::String(ksym));
        let cm = m.consts.intern(Const::method_ref(shared_cb));
        let shape = m.consts.push_object(vec![ck], vec![cm]);
        let obj = emit_val(&mut m, b, Op::AllocObject { shape });
        let c1 = m.consts.push(Const::number(1.0));
        let v1 = emit_val(&mut m, b, Op::LoadConst(c1));
        let sum = emit_val(
            &mut m,
            b,
            Op::BinaryOp {
                op: BinOp::Add,
                left: obj,
                right: v1,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(sum) });
    }
    assert_eq!(func_inst_weight(&m, root_b), 4);

    // `root_c` (weight 3) defines a class whose method `extra_m` has weight 10 -> +14 incremental.
    let ctor_c = add_ret_fn(&mut m, "CtorC");
    let extra_m = add_fn(&mut m, "extra_m");
    {
        let _this = add_param(&mut m, extra_m);
        let b = entry_of(&m, extra_m);
        let mut last = None;
        for k in 0..9 {
            let c = m.consts.push(Const::number(k as f64));
            last = Some(emit_val(&mut m, b, Op::LoadConst(c)));
        }
        push_inst(&mut m, b, Op::Return { value: last });
    }
    assert_eq!(func_inst_weight(&m, extra_m), 10);
    let root_c = add_fn(&mut m, "root_c");
    {
        let _this = add_param(&mut m, root_c);
        let b = entry_of(&m, root_c);
        let msym = m.sym.intern("run");
        let cm_k = m.consts.intern(Const::String(msym));
        let cm_f = m.consts.intern(Const::method_ref(extra_m));
        let members = m.consts.push_array(vec![cm_k, cm_f]);
        let cls = emit_val(
            &mut m,
            b,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: ctor_c,
                heritage: None,
                members,
                member_attrs: vec![],
                count: 1,
            })),
        );
        push_inst(&mut m, b, Op::Return { value: Some(cls) });
    }

    let weights = precompute_func_inst_weights(&m);
    assert_eq!(weights.len(), m.functions.len());

    let limits = BatchLimits {
        max_insts: 32,
        max_funcs: 10,
    };
    let mut visited = BTreeSet::new();
    let mut batch_weight = 0usize;

    assert!(try_extend_batch_funcs(
        &m,
        &weights,
        &[root_a],
        &mut visited,
        &mut batch_weight,
        Some(limits),
    ));
    assert_eq!(visited, BTreeSet::from([shared_cb, root_a]));
    assert_eq!(batch_weight, 26);

    // `root_b` shares `shared_cb`, so total weight becomes 26 + 4 = 30 <= 32!
    assert!(try_extend_batch_funcs(
        &m,
        &weights,
        &[root_b],
        &mut visited,
        &mut batch_weight,
        Some(limits),
    ));
    assert_eq!(visited, BTreeSet::from([shared_cb, root_a, root_b]));
    assert_eq!(batch_weight, 30);

    // `root_c` needs +13 weight (30 + 13 = 43 > 32): must roll back cleanly!
    assert!(!try_extend_batch_funcs(
        &m,
        &weights,
        &[root_c],
        &mut visited,
        &mut batch_weight,
        Some(limits),
    ));
    assert_eq!(visited, BTreeSet::from([shared_cb, root_a, root_b]));
    assert_eq!(batch_weight, 30);

    // Secondary `max_funcs` cap rollback check:
    let tight_func_limits = BatchLimits {
        max_insts: 10_000,
        max_funcs: 3,
    };
    assert!(!try_extend_batch_funcs(
        &m,
        &weights,
        &[root_c],
        &mut visited,
        &mut batch_weight,
        Some(tight_func_limits),
    ));
    assert_eq!(visited, BTreeSet::from([shared_cb, root_a, root_b]));
    assert_eq!(batch_weight, 30);

    // Oversized singleton forward progress: `root_a` + `shared_cb` has weight 26 > max_insts=10,
    // yet `next_bounded_top_batch` admits `take == 1` and stops before `root_b`.
    let (take, fids) = next_bounded_top_batch(
        &m,
        &weights,
        &[root_a, root_b, root_c],
        BatchLimits {
            max_insts: 10,
            max_funcs: 1,
        },
    );
    assert_eq!(take, 1);
    assert_eq!(fids, vec![shared_cb, root_a]);
}

#[test]
fn decompile_module_with_limits_matches_byte_for_byte_across_budgets() {
    use abcd_ir::op::{LexEnvKind, ModuleVarKind};

    let mut m = mk_module();
    let req_ext = m.sym.intern("./dep");
    let s_imp = m.sym.intern("depFn");
    let s_exp = m.sym.intern("exportedVal");
    m.module_requests.push(abcd_ir::module::ModuleRequest {
        specifier: req_ext,
        lazy: false,
    });
    m.imports.push(ImportDecl::Regular {
        local_name: s_imp,
        import_name: s_imp,
        module_request: req_ext,
    });
    m.exports.push(ExportDecl::Local {
        local_name: s_exp,
        export_name: s_exp,
    });

    // Shared inline closure referenced across multiple roots AND twice inside one root.
    let shared_fn = add_fn(&mut m, "shared_helper");
    {
        let _this = add_param(&mut m, shared_fn);
        let p = add_param(&mut m, shared_fn);
        let b = entry_of(&m, shared_fn);
        let lex = emit_val(
            &mut m,
            b,
            Op::GetLexVar {
                level: 2,
                slot: 1,
                kind: LexEnvKind::Plain,
            },
        );
        let sum = emit_val(
            &mut m,
            b,
            Op::BinaryOp {
                op: BinOp::Add,
                left: p,
                right: lex,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(sum) });
    }

    // Class with constructor, private field, and method.
    let cls_ctor = add_fn(&mut m, "Widget");
    m.func_mut(cls_ctor).unwrap().kind = FunctionKind::Constructor;
    {
        let _fn_obj = add_param(&mut m, cls_ctor);
        let _nt = add_param(&mut m, cls_ctor);
        let this = add_param(&mut m, cls_ctor);
        let b = entry_of(&m, cls_ctor);
        let c = m.consts.push(Const::number(7.0));
        let v = emit_val(&mut m, b, Op::LoadConst(c));
        push_inst(
            &mut m,
            b,
            Op::DefinePrivate {
                level: 0,
                slot: 0,
                obj: this,
                value: v,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(this) });
    }
    let cls_meth = add_fn(&mut m, "compute");
    {
        let _fn_obj = add_param(&mut m, cls_meth);
        let _nt = add_param(&mut m, cls_meth);
        let this = add_param(&mut m, cls_meth);
        let b = entry_of(&m, cls_meth);
        let pv = emit_val(
            &mut m,
            b,
            Op::LoadPrivate {
                level: 0,
                slot: 0,
                obj: this,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(pv) });
    }

    // Top-level 1: defines class + uses `shared_fn` twice.
    let top_1 = add_fn(&mut m, "build_widget");
    {
        let _this = add_param(&mut m, top_1);
        let b = entry_of(&m, top_1);
        let s_secret = m.sym.intern("secret");
        let cs_secret = m.consts.intern(Const::String(s_secret));
        let pnames = m.consts.push_array(vec![cs_secret]);
        push_inst(
            &mut m,
            b,
            Op::CreatePrivateNames {
                count: 1,
                names: pnames,
            },
        );
        let s_comp = m.sym.intern("compute");
        let cs_comp = m.consts.intern(Const::String(s_comp));
        let cm_comp = m.consts.intern(Const::method_ref(cls_meth));
        let members = m.consts.push_array(vec![cs_comp, cm_comp]);
        let cls_v = emit_val(
            &mut m,
            b,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: cls_ctor,
                heritage: None,
                members,
                member_attrs: vec![],
                count: 1,
            })),
        );
        let df1 = emit_val(
            &mut m,
            b,
            Op::DefineFunc {
                body: shared_fn,
                captures: vec![],
                length: 1,
            },
        );
        let cl1 = emit_val(&mut m, b, Op::AllocClosure { func: df1 });
        let df2 = emit_val(
            &mut m,
            b,
            Op::DefineFunc {
                body: shared_fn,
                captures: vec![],
                length: 1,
            },
        );
        let cl2 = emit_val(&mut m, b, Op::AllocClosure { func: df2 });
        let acc = emit_val(
            &mut m,
            b,
            Op::BinaryOp {
                op: BinOp::Add,
                left: cls_v,
                right: cl1,
            },
        );
        let res = emit_val(
            &mut m,
            b,
            Op::BinaryOp {
                op: BinOp::Add,
                left: acc,
                right: cl2,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(res) });
    }

    // Top-level 2: oversized single function (> 90 instructions, exceeding max_insts = 32).
    let giant_fn = add_fn(&mut m, "oversized_compute");
    {
        let _this = add_param(&mut m, giant_fn);
        let mut acc = add_param(&mut m, giant_fn);
        let b = entry_of(&m, giant_fn);
        for k in 0..45 {
            let c = m.consts.push(Const::number((k + 1) as f64));
            let v = emit_val(&mut m, b, Op::LoadConst(c));
            acc = emit_val(
                &mut m,
                b,
                Op::BinaryOp {
                    op: if k % 2 == 0 { BinOp::Add } else { BinOp::Sub },
                    left: acc,
                    right: v,
                },
            );
        }
        let df = emit_val(
            &mut m,
            b,
            Op::DefineFunc {
                body: shared_fn,
                captures: vec![],
                length: 1,
            },
        );
        let cl = emit_val(&mut m, b, Op::AllocClosure { func: df });
        let res = emit_val(
            &mut m,
            b,
            Op::BinaryOp {
                op: BinOp::Add,
                left: acc,
                right: cl,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(res) });
    }
    assert!(func_inst_weight(&m, giant_fn) > 90);

    // Top-level 3..7: several small functions + `func_main_0` touching module & global slots.
    for idx in 0..4 {
        let f = add_fn(&mut m, &format!("small_top_{idx}"));
        let _this = add_param(&mut m, f);
        let b = entry_of(&m, f);
        let ext = emit_val(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let c = m.consts.push(Const::number(idx as f64));
        let v = emit_val(&mut m, b, Op::LoadConst(c));
        let call = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: ext,
                this: None,
                args: vec![v],
                kind: CallKind::Dynamic,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(call) });
    }

    let f_main = add_fn(&mut m, "func_main_0");
    {
        let _this = add_param(&mut m, f_main);
        let b = entry_of(&m, f_main);
        let df = emit_val(
            &mut m,
            b,
            Op::DefineFunc {
                body: shared_fn,
                captures: vec![],
                length: 1,
            },
        );
        let cl = emit_val(&mut m, b, Op::AllocClosure { func: df });
        push_inst(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: cl,
            },
        );
        let gsym = m.sym.intern("globalCounter");
        push_inst(
            &mut m,
            b,
            Op::StoreGlobal {
                name: gsym,
                value: cl,
            },
        );
        push_inst(&mut m, b, Op::Return { value: None });
    }

    for f in [top_1, giant_fn, f_main] {
        m.classes[0].methods.push(f);
    }

    let budgets = [
        BatchLimits {
            max_insts: 1,
            max_funcs: 1,
        },
        BatchLimits {
            max_insts: 32,
            max_funcs: 2,
        },
        BatchLimits {
            max_insts: 64,
            max_funcs: 4,
        },
        BatchLimits::default(),
    ];

    for opts in [
        EmitOptions::default(),
        EmitOptions {
            ts: true,
            call_entry: true,
            ..EmitOptions::default()
        },
        EmitOptions {
            arkui: true,
            ..EmitOptions::default()
        },
    ] {
        let baseline = decompile_module(&m, &opts);
        for lim in budgets {
            let got = decompile_module_with_limits(&m, &opts, lim);
            assert_eq!(got.text, baseline.text, "text mismatch at {lim:?}");
            assert_eq!(got.stats, baseline.stats, "stats mismatch at {lim:?}");
        }
    }
}

#[test]
fn decompile_module_to_writer_and_split_survive_256k_worker_stacks() {
    use abcd_ir::function::{Catch, Edge, EdgeKind, TryRegion};
    use abcd_ir::module::{EsModule, ModuleRequest};
    use abcd_ir::op::ModuleVarKind;

    let mut m = Module::new();

    // Record 0: Deep CFG diamonds + loop + try/catch + 1,000-deep expression + large function.
    let r0_sym = m.sym.intern("Lcom.demo/app/ets/DeepCore;");
    let r0_cid = ClassId::new(0);
    m.classes.push(ClassData::new(r0_sym, r0_sym));
    let req_ui = m.sym.intern("@bundle:com.demo/app/ets/pages/UiPage");
    let s_page = m.sym.intern("UiPage");
    let s_run = m.sym.intern("runDeep");
    m.classes[0].es_module = Some(EsModule {
        module_requests: vec![ModuleRequest {
            specifier: req_ui,
            lazy: false,
        }],
        imports: vec![ImportDecl::Regular {
            local_name: s_page,
            import_name: s_page,
            module_request: req_ui,
        }],
        exports: vec![ExportDecl::Local {
            local_name: s_run,
            export_name: s_run,
        }],
    });

    let add_cls_fn = |m: &mut Module, cid: ClassId, name: &str, kind: FunctionKind| -> FuncId {
        let sym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(cid, sym, kind);
        fd.modifiers |= abcd_ir::Modifiers::STATIC;
        m.functions.push(fd);
        m.classes[cid.index()].methods.push(fid);
        let b = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(fid).unwrap().blocks.push(b);
        for _ in 0..3 {
            add_param(m, fid);
        }
        fid
    };

    // 1. Deeply nested CFG (`350` nested `if` diamonds inside a `try`/`catch`).
    let f_deep_cfg = add_cls_fn(&mut m, r0_cid, "deep_cfg", FunctionKind::Function);
    {
        let p = add_param(&mut m, f_deep_cfg);
        const DEPTH: usize = 350;
        let mut heads = Vec::with_capacity(DEPTH);
        heads.push(entry_of(&m, f_deep_cfg));
        for _ in 1..DEPTH {
            let bid = BlockId::new(m.blocks.len() as u32);
            m.blocks.push(Block::default());
            m.func_mut(f_deep_cfg).unwrap().blocks.push(bid);
            heads.push(bid);
        }
        let leaf = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(f_deep_cfg).unwrap().blocks.push(leaf);
        let mut merges = Vec::with_capacity(DEPTH);
        for _ in 0..DEPTH {
            let bid = BlockId::new(m.blocks.len() as u32);
            m.blocks.push(Block::default());
            m.func_mut(f_deep_cfg).unwrap().blocks.push(bid);
            merges.push(bid);
        }
        let catch_b = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(f_deep_cfg).unwrap().blocks.push(catch_b);
        let exit_b = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(f_deep_cfg).unwrap().blocks.push(exit_b);

        for i in 0..DEPTH - 1 {
            push_inst(
                &mut m,
                heads[i],
                Op::CondBranch {
                    cond: p,
                    true_dest: heads[i + 1],
                    false_dest: merges[i],
                },
            );
            m.block_mut(heads[i + 1]).unwrap().preds.push(Edge {
                from: heads[i],
                kind: EdgeKind::Normal,
            });
            m.block_mut(merges[i]).unwrap().preds.push(Edge {
                from: heads[i],
                kind: EdgeKind::Normal,
            });
        }
        push_inst(
            &mut m,
            heads[DEPTH - 1],
            Op::CondBranch {
                cond: p,
                true_dest: leaf,
                false_dest: merges[DEPTH - 1],
            },
        );
        m.block_mut(leaf).unwrap().preds.push(Edge {
            from: heads[DEPTH - 1],
            kind: EdgeKind::Normal,
        });
        m.block_mut(merges[DEPTH - 1]).unwrap().preds.push(Edge {
            from: heads[DEPTH - 1],
            kind: EdgeKind::Normal,
        });

        let leaf_call = emit_val(
            &mut m,
            leaf,
            Op::Call {
                callee: p,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let _ = leaf_call;
        push_inst(
            &mut m,
            leaf,
            Op::Branch {
                dest: merges[DEPTH - 1],
            },
        );
        m.block_mut(merges[DEPTH - 1]).unwrap().preds.push(Edge {
            from: leaf,
            kind: EdgeKind::Normal,
        });

        for i in (1..DEPTH).rev() {
            push_inst(
                &mut m,
                merges[i],
                Op::Branch {
                    dest: merges[i - 1],
                },
            );
            m.block_mut(merges[i - 1]).unwrap().preds.push(Edge {
                from: merges[i],
                kind: EdgeKind::Normal,
            });
        }
        push_inst(&mut m, merges[0], Op::Branch { dest: exit_b });
        m.block_mut(exit_b).unwrap().preds.push(Edge {
            from: merges[0],
            kind: EdgeKind::Normal,
        });
        push_inst(&mut m, exit_b, Op::Return { value: Some(p) });

        let exc = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::ExceptionParam(catch_b),
            ty: Ty::Any,
        });
        push_inst(&mut m, catch_b, Op::Return { value: Some(exc) });
        m.block_mut(catch_b).unwrap().preds.push(Edge {
            from: leaf,
            kind: EdgeKind::Exceptional,
        });
        m.func_mut(f_deep_cfg).unwrap().try_regions.push(TryRegion {
            protected: vec![leaf],
            catches: vec![Catch {
                handler: catch_b,
                exception: exc,
                type_class: None,
            }],
        });
    }

    // 2. Deeply nested single-use expression tree (`1,000` levels) + large instruction count.
    let f_deep_expr = add_cls_fn(
        &mut m,
        r0_cid,
        "deep_expr_and_large",
        FunctionKind::Function,
    );
    {
        let mut cur = add_param(&mut m, f_deep_expr);
        let b = entry_of(&m, f_deep_expr);
        for i in 0..1_000 {
            if i % 2 == 0 {
                cur = emit_val(
                    &mut m,
                    b,
                    Op::UnaryOp {
                        op: UnOp::LogicalNot,
                        operand: cur,
                    },
                );
            } else {
                let c = m.consts.push(Const::number((i % 7) as f64));
                let rhs = emit_val(&mut m, b, Op::LoadConst(c));
                // Per N36 (`BinaryOp` emits `right + left` in JS), place `cur` in `right`
                // and `rhs` in `left` so `cur` evaluates before `rhs` without eviction
                // and Stage A materializes a true 1,000-deep `Expr` tree!
                cur = emit_val(
                    &mut m,
                    b,
                    Op::BinaryOp {
                        op: BinOp::Add,
                        left: rhs,
                        right: cur,
                    },
                );
            }
        }
        let ext = emit_val(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let res = emit_val(
            &mut m,
            b,
            Op::BinaryOp {
                op: BinOp::Add,
                left: ext,
                right: cur,
            },
        );
        push_inst(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: res,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(res) });
    }

    // Record 1: ArkUI `ViewPU` component record to exercise `arkui.rs` + `split.rs` on 256 KiB stack.
    let r1_sym = m.sym.intern("Lcom.demo/app/ets/pages/UiPage;");
    let r1_cid = ClassId::new(1);
    m.classes.push(ClassData::new(r1_sym, r1_sym));
    m.classes[1].es_module = Some(EsModule {
        module_requests: vec![],
        imports: vec![],
        exports: vec![ExportDecl::Local {
            local_name: s_page,
            export_name: s_page,
        }],
    });
    let ui_ctor = add_cls_fn(&mut m, r1_cid, "UiPage", FunctionKind::Constructor);
    {
        let this = m.func(ui_ctor).unwrap().params[2];
        let b = entry_of(&m, ui_ctor);
        let obs_sym = m.sym.intern("ObservedPropertySimplePU");
        let obs_cls = emit_val(
            &mut m,
            b,
            Op::TryGetGlobal {
                name: obs_sym,
                default: None,
            },
        );
        let zero_c = m.consts.push(Const::number(0.0));
        let zero = emit_val(&mut m, b, Op::LoadConst(zero_c));
        let n_sym = m.sym.intern("n");
        let n_c = m.consts.push(Const::String(n_sym));
        let n_str = emit_val(&mut m, b, Op::LoadConst(n_c));
        let obs = emit_val(
            &mut m,
            b,
            Op::Call {
                callee: obs_cls,
                this: None,
                args: vec![zero, this, n_str],
                kind: CallKind::New,
            },
        );
        let k_n = m.sym.intern("__n");
        push_inst(
            &mut m,
            b,
            Op::StoreProp {
                object: this,
                name: k_n,
                value: obs,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(this) });
    }
    let ui_render = add_cls_fn(&mut m, r1_cid, "initialRender", FunctionKind::Function);
    {
        let b = entry_of(&m, ui_render);
        push_inst(&mut m, b, Op::Return { value: None });
    }
    let ui_main = add_cls_fn(&mut m, r1_cid, "func_main_0", FunctionKind::Function);
    {
        let b = entry_of(&m, ui_main);
        let vpu_sym = m.sym.intern("ViewPU");
        let vpu = emit_val(
            &mut m,
            b,
            Op::TryGetGlobal {
                name: vpu_sym,
                default: None,
            },
        );
        let ir_sym = m.sym.intern("initialRender");
        let cs_ir = m.consts.intern(Const::String(ir_sym));
        let cm_ir = m.consts.intern(Const::method_ref(ui_render));
        let members = m.consts.push_array(vec![cs_ir, cm_ir]);
        let cls_v = emit_val(
            &mut m,
            b,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: ui_ctor,
                heritage: Some(vpu),
                members,
                member_attrs: vec![],
                count: 1,
            })),
        );
        push_inst(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: cls_v,
            },
        );
        push_inst(&mut m, b, Op::Return { value: None });
    }

    let js_opts = EmitOptions::default();
    let ark_opts = EmitOptions {
        arkui: true,
        ..EmitOptions::default()
    };
    let expected_single_js = decompile_module(&m, &js_opts);
    let expected_single_ark = decompile_module(&m, &ark_opts);
    let expected_split_js = crate::split::decompile_module_split(&m, &js_opts);
    let expected_split_ark = crate::split::decompile_module_split(&m, &ark_opts);

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(2)
        .stack_size(256 * 1024)
        .build()
        .expect("build 256 KiB Rayon worker pool");

    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name("decompile-full-256k".to_string())
            .stack_size(256 * 1024)
            .spawn_scoped(s, || {
                pool.install(|| {
                    for (opts, exp_single, exp_split) in [
                        (&js_opts, &expected_single_js, &expected_split_js),
                        (&ark_opts, &expected_single_ark, &expected_split_ark),
                    ] {
                        let mut buf = Vec::new();
                        let stats = decompile_module_to_writer(&m, opts, &mut buf)
                            .expect("stream on 256 KiB stack");
                        let text = String::from_utf8(buf).expect("UTF-8");
                        assert_eq!(text, exp_single.text);
                        assert_eq!(stats, exp_single.stats);

                        let split = crate::split::decompile_module_split(&m, opts);
                        assert_eq!(split.files, exp_split.files);
                        assert_eq!(split.stats, exp_split.stats);
                    }
                });
            })
            .expect("spawn 256 KiB caller thread");
        handle
            .join()
            .expect("256 KiB caller + Rayon worker threads must not stack-overflow");
    });
}
