//! c-COV A11 (handler-phi half): the N21 pinned-store emission keyed by a
//! frame-initial const (isel.rs:613-618) and the handler-phi store
//! collector's self-reference / co-located skips (regalloc.rs:1172,
//! 1178-1182).
//!
//! A phi in a catch handler means "the handler sees the variable as of the
//! dynamic exception point"; the VM dispatches directly to the handler's
//! flat offset, so no copy code may run on the edge — regalloc pins
//! write-through stores instead, and isel emits them at the pred's block
//! start, or right after the source's definition when the source is
//! defined in the pred (including the entry block's seed materialization,
//! which is the definition site of a frame-initial const).

mod common;

use abcd_ir::{Catch, Const, Edge, EdgeKind, FunctionKind, Module, Op, TryRegion};
use abcd_isa::Bytecode;
use abcd_lower::fusion::{self, Suppression};
use abcd_lower::lower_function;
use abcd_lower::regalloc::{self, RegSlot};

use common::{Halt, Machine, V2Builder};

/// (isel.rs:613-618) A handler phi whose incoming value is an entry-seed
/// CONST with the ENTRY block as pred: the pinned store runs right after
/// the seed's materialization (its definition site), not at block start.
///
/// ```text
/// entry:  (seed 7 materializes; pinned Mov writes the phi result's home)
///         jmp exit
/// exit:   return 99                       // normal path
/// handler: phi [(entry --exceptional--> seed7)]; return phi
/// ```
#[test]
fn handler_phi_pinned_store_after_an_entry_seed_const() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, exit, handler, seed, phi);
    {
        let mut b = V2Builder::new(&mut module, func);
        entry = b.entry();
        exit = b.create_block();
        handler = b.create_block();
        b.add_predecessor(exit, entry);
        b.add_exceptional_predecessor(handler, entry);
        let exception = b.create_exception_param(handler);
        seed = b.create_const_value(Const::number(7.0));

        b.emit_void(Op::Branch { dest: exit });

        b.set_insert_block(exit);
        let c99 = b.konst(Const::number(99.0));
        let x = b.emit_val(Op::LoadConst(c99));
        b.emit_void(Op::Return { value: Some(x) });

        b.set_insert_block(handler);
        phi = b.emit_val(Op::Phi {
            entries: vec![(
                Edge {
                    from: entry,
                    kind: EdgeKind::Exceptional,
                },
                seed,
            )],
        });
        b.emit_void(Op::Return { value: Some(phi) });

        b.module.functions[func.index()]
            .try_regions
            .push(TryRegion {
                protected: vec![entry],
                catches: vec![Catch {
                    handler,
                    exception,
                    type_idx: None,
                }],
            });
    }

    // Regalloc side: exactly one pinned store, keyed (entry, seed, phi).
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let alloc = regalloc::allocate(&module, func, &suppression).expect("allocation must succeed");
    assert_eq!(
        alloc.handler_phi_stores,
        vec![(entry, seed, phi)],
        "the seed-sourced handler phi pins a store at the entry pred"
    );

    let result = lower_function(&module, func).expect("the handler-phi shape must lower");

    // The entry block's stream: the seed's load+home, then the pinned Mov.
    let RegSlot::Reg(seed_home) = alloc.allocation[&seed];
    let RegSlot::Reg(phi_home) = alloc.allocation[&phi];
    assert_ne!(seed_home, phi_home, "the N21 forbid edges keep them apart");
    let entry_codes = &result.bytecodes[..];
    let ldai7 = entry_codes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Ldai(imm) if imm.0 == 7))
        .expect("the seed materializes in the entry block");
    let pinned = entry_codes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Mov(d, s) if d.0 == phi_home && s.0 == seed_home))
        .expect("the pinned store Mov(phi_home, seed_home) is emitted");
    assert!(
        pinned > ldai7,
        "the pinned store runs right AFTER the seed materialization: {entry_codes:?}"
    );

    // Behavioral: the normal path returns 99, and a dispatch entering the
    // handler AFTER the entry ran observes the pinned seed value.
    let mut machine = Machine::new();
    let halt = machine.run(&result.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(99),
        "normal path (bytecodes: {:?})",
        result.bytecodes
    );
    let handler_pc = result.try_blocks[0].catches[0].handler as usize;
    let halt = machine.run_at(&result.bytecodes, handler_pc);
    assert_eq!(
        halt,
        Halt::Return(7),
        "the handler reads the phi result home written by the entry's \
         pinned store (bytecodes: {:?})",
        result.bytecodes
    );
}

/// (regalloc.rs:1172) A handler phi whose incoming value IS its own result
/// (a loop phi in a try/catch) needs no pinned store — the slot already
/// holds the value by construction.
#[test]
fn handler_phi_self_reference_pins_no_store() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, handler, phi_iid, phi);
    {
        let mut b = V2Builder::new(&mut module, func);
        entry = b.entry();
        handler = b.create_block();
        b.add_exceptional_predecessor(handler, entry);
        let exception = b.create_exception_param(handler);

        b.emit_void(Op::Return { value: None });

        b.set_insert_block(handler);
        // Emit the phi with an empty entry list, then close the
        // self-reference (the result id only exists after emission).
        let (iid, val) = b.emit(Op::Phi {
            entries: Vec::new(),
        });
        phi_iid = iid;
        phi = val.expect("Phi has a result");
        b.emit_void(Op::Return { value: Some(phi) });

        b.module.insts[phi_iid.index()].op = Op::Phi {
            entries: vec![(
                Edge {
                    from: entry,
                    kind: EdgeKind::Exceptional,
                },
                phi,
            )],
        };
        b.module.functions[func.index()]
            .try_regions
            .push(TryRegion {
                protected: vec![entry],
                catches: vec![Catch {
                    handler,
                    exception,
                    type_idx: None,
                }],
            });
    }

    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let alloc = regalloc::allocate(&module, func, &suppression).expect("allocation must succeed");
    assert!(
        alloc.handler_phi_stores.is_empty(),
        "a self-referential handler phi pins no store: {:?}",
        alloc.handler_phi_stores
    );
    lower_function(&module, func).expect("the self-referential handler phi must lower");
}

/// (regalloc.rs:1178-1182) A handler phi whose incoming value is colored to
/// the SAME slot as the result — and does not interfere with it — pins no
/// store either (already co-located).
///
/// Co-location is reachable only with a pred that liveness never saw (a
/// dangling pred block): for any LIVE pred the N21 safety edges make the
/// pair interfere, and greedy coloring separates them.
#[test]
fn handler_phi_co_located_with_its_source_pins_no_store() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (src, phi);
    {
        let mut b = V2Builder::new(&mut module, func);
        let entry = b.entry();
        let handler = b.create_block();
        b.add_exceptional_predecessor(handler, entry);
        let exception = b.create_exception_param(handler);

        let c5 = b.konst(Const::number(5.0));
        src = b.emit_val(Op::LoadConst(c5));
        b.emit_void(Op::Return { value: None });

        b.set_insert_block(handler);
        phi = b.emit_val(Op::Phi {
            entries: vec![(
                Edge {
                    // No such block: liveness/N21 never add safety edges
                    // for this pred, so coloring may co-locate src and phi.
                    from: abcd_ir::BlockId::new(999),
                    kind: EdgeKind::Exceptional,
                },
                src,
            )],
        });
        b.emit_void(Op::Return { value: Some(phi) });

        b.module.functions[func.index()]
            .try_regions
            .push(TryRegion {
                protected: vec![entry],
                catches: vec![Catch {
                    handler,
                    exception,
                    type_idx: None,
                }],
            });
    }

    let alloc = regalloc::allocate(&module, func, &Suppression::default())
        .expect("allocation must succeed");
    assert_eq!(
        alloc.allocation[&src], alloc.allocation[&phi],
        "without interference the greedy coloring co-locates the pair"
    );
    assert!(
        alloc.handler_phi_stores.is_empty(),
        "an already co-located pair pins no store: {:?}",
        alloc.handler_phi_stores
    );
    lower_function(&module, func).expect("the co-located handler phi must lower");
}

/// (isel.rs:616-618, the `s == d` edge) A pinned store whose source and
/// destination are co-located emits NO `mov` — hand-crafted allocation:
/// regalloc's own forbid edges never produce this pairing, but isel skips
/// the redundant store for hand-built inputs.
#[test]
fn pinned_store_skipped_when_source_and_dest_are_co_located() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, exit, handler, seed, phi, exit_val);
    {
        let mut b = V2Builder::new(&mut module, func);
        entry = b.entry();
        exit = b.create_block();
        handler = b.create_block();
        b.add_predecessor(exit, entry);
        b.add_exceptional_predecessor(handler, entry);
        let exception = b.create_exception_param(handler);
        seed = b.create_const_value(Const::number(7.0));

        b.emit_void(Op::Branch { dest: exit });

        b.set_insert_block(exit);
        let c99 = b.konst(Const::number(99.0));
        exit_val = b.emit_val(Op::LoadConst(c99));
        b.emit_void(Op::Return {
            value: Some(exit_val),
        });

        b.set_insert_block(handler);
        phi = b.emit_val(Op::Phi {
            entries: vec![(
                Edge {
                    from: entry,
                    kind: EdgeKind::Exceptional,
                },
                seed,
            )],
        });
        b.emit_void(Op::Return { value: Some(phi) });

        b.module.functions[func.index()]
            .try_regions
            .push(TryRegion {
                protected: vec![entry],
                catches: vec![Catch {
                    handler,
                    exception,
                    type_idx: None,
                }],
            });
    }

    // Hand-crafted allocation: seed and phi share Reg(0), and the pinned
    // store list still carries the pair (inconsistent input — the pinned
    // store must then be skipped, not emitted as a self-mov).
    let alloc = regalloc::RegAlloc {
        allocation: [
            (seed, RegSlot::Reg(0)),
            (phi, RegSlot::Reg(0)),
            (exit_val, RegSlot::Reg(1)),
        ]
        .into_iter()
        .collect(),
        phi_copies: Default::default(),
        handler_phi_stores: vec![(entry, seed, phi)],
        num_regs: 2,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    };
    let rpo = regalloc::compute_rpo(&module, func);
    let selected = abcd_lower::isel::select(&module, func, &alloc, &rpo, &Suppression::default())
        .expect("co-located pinned store must select");
    let entry_codes = &selected.block_codes[0].1;
    assert!(
        entry_codes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldai(imm) if imm.0 == 7)),
        "the seed still materializes: {entry_codes:?}"
    );
    assert!(
        !entry_codes.iter().any(|bc| matches!(bc, Bytecode::Mov(..))),
        "a co-located pinned store emits no self-mov: {entry_codes:?}"
    );

    // Behavioral: the handler observes the seed through the shared slot.
    let laid_out = abcd_lower::layout::layout(&module, func, &selected, &alloc, &rpo)
        .expect("layout must succeed");
    let mut machine = Machine::new();
    let halt = machine.run(&laid_out.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(99),
        "normal path: {:?}",
        laid_out.bytecodes
    );
    let handler_pc = laid_out.try_blocks[0].catches[0].handler as usize;
    let halt = machine.run_at(&laid_out.bytecodes, handler_pc);
    assert_eq!(
        halt,
        Halt::Return(7),
        "the handler reads the shared slot (bytecodes: {:?})",
        laid_out.bytecodes
    );
}
