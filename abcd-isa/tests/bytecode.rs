use abcd_isa::*;

// --- is_jump ---

#[test]
fn is_jump_positive() {
    assert!(insn::Jmp::new(Label(0)).is_jump());
    assert!(insn::Jeqz::new(Label(0)).is_jump());
    assert!(insn::Jnez::new(Label(0)).is_jump());
    assert!(insn::Jeq::new(Reg(0), Label(0)).is_jump());
}

#[test]
fn is_jump_negative() {
    assert!(!insn::Ldundefined::new().is_jump());
    assert!(!insn::Return::new().is_jump());
    assert!(!insn::Ldai::new(Imm(0)).is_jump());
}

// --- is_terminator ---

#[test]
fn is_terminator_positive() {
    assert!(insn::Return::new().is_terminator());
    assert!(insn::Returnundefined::new().is_terminator());
    assert!(insn::Throw::new().is_terminator());
    // Unconditional jump also ends a basic block.
    assert!(insn::Jmp::new(Label(0)).is_terminator());
}

#[test]
fn is_terminator_negative() {
    assert!(!insn::Ldundefined::new().is_terminator());
    assert!(!insn::Ldai::new(Imm(0)).is_terminator());
}

// --- is_return_or_throw ---

#[test]
fn is_return_or_throw() {
    assert!(insn::Return::new().is_return_or_throw());
    assert!(insn::Throw::new().is_return_or_throw());
    assert!(!insn::Ldundefined::new().is_return_or_throw());
}

// --- is_suspend ---

#[test]
fn is_suspend() {
    // The SUSPEND flag exists in the ISA schema but is never assigned to any
    // instruction (see has_flag_suspend_not_assigned). Consequently is_suspend()
    // returns false for all instructions, including suspendgenerator.
    assert!(!insn::Suspendgenerator::new(Reg(0)).is_suspend());
    assert!(!insn::Ldundefined::new().is_suspend());
    assert!(!insn::Return::new().is_suspend());
}

// --- is_range ---

#[test]
fn is_range() {
    assert!(insn::Callthisrange::new(Imm(0), Imm(0), Reg(0)).is_range());
    assert!(!insn::Callarg0::new(Imm(0)).is_range());
}

// --- can_throw ---

#[test]
fn can_throw() {
    // Throw instruction can throw; simple loads cannot.
    assert!(insn::Throw::new().can_throw());
    assert!(!insn::Ldundefined::new().can_throw());
}

#[test]
fn can_throw_extended() {
    // LdaStr has exception [x_oom], so it can throw.
    assert!(insn::LdaStr::new(EntityId(0)).can_throw());
    // Simple loads and arithmetic cannot throw in this ISA.
    assert!(!insn::Ldnull::new().can_throw());
    assert!(!insn::Ldtrue::new().can_throw());
    assert!(!insn::Add2::new(Imm(0), Reg(0)).can_throw());
}

// --- has_flag ---

#[test]
fn has_flag_jump() {
    assert!(insn::Jmp::new(Label(0)).has_flag(BytecodeFlag::JUMP));
}

#[test]
fn has_flag_return() {
    assert!(insn::Return::new().has_flag(BytecodeFlag::RETURN));
}

#[test]
fn has_flag_negative() {
    assert!(!insn::Ldundefined::new().has_flag(BytecodeFlag::RETURN));
    assert!(!insn::Ldundefined::new().has_flag(BytecodeFlag::JUMP));
}

// --- mnemonic ---

#[test]
fn mnemonic_values() {
    assert_eq!(insn::Ldundefined::new().mnemonic(), "ldundefined");
    assert_eq!(insn::Jmp::new(Label(0)).mnemonic(), "jmp");
    assert_eq!(insn::Return::new().mnemonic(), "return");
    assert_eq!(insn::Throw::new().mnemonic(), "throw");
    assert_eq!(
        insn::CallruntimeNotifyconcurrentresult::new().mnemonic(),
        "callruntime.notifyconcurrentresult"
    );
}

// --- Display / Debug ---

#[test]
fn display_no_operands() {
    assert_eq!(format!("{}", insn::Ldundefined::new()), "ldundefined");
}

#[test]
fn display_with_operands() {
    let s = format!("{}", insn::Add2::new(Imm(5), Reg(3)));
    assert_eq!(s, "add2 5 v3");
}

#[test]
fn debug_format() {
    let s = format!("{:?}", insn::Ldundefined::new());
    assert_eq!(s, "Bytecode(ldundefined)");
}

// --- jump_label_arg_index ---

#[test]
fn jump_label_arg_index_jmp() {
    assert_eq!(insn::Jmp::new(Label(0)).jump_label_arg_index(), Some(0));
}

#[test]
fn jump_label_arg_index_jeq() {
    assert_eq!(
        insn::Jeq::new(Reg(0), Label(0)).jump_label_arg_index(),
        Some(1)
    );
}

#[test]
fn jump_label_arg_index_non_jump() {
    assert_eq!(insn::Ldundefined::new().jump_label_arg_index(), None);
}

// --- emit_args ---

#[test]
fn emit_args_no_operands() {
    let (_, _, num_args) = insn::Ldundefined::new().emit_args();
    assert_eq!(num_args, 0);
}

#[test]
fn emit_args_with_operands() {
    let (_, args, num_args) = insn::Mov::new(Reg(1), Reg(2)).emit_args();
    assert_eq!(num_args, 2);
    assert_eq!(args[0], 1); // Reg(1)
    assert_eq!(args[1], 2); // Reg(2)
}

// --- is_throw_ex ---

#[test]
fn is_throw_ex_throw() {
    assert!(insn::Throw::new().is_throw_ex(ExceptionType::X_THROW));
    assert!(!insn::Throw::new().is_throw_ex(ExceptionType::X_NULL));
}

#[test]
fn is_throw_ex_throw_variants_inherit_x_none() {
    // ISA design: throw.* prefixed instructions (throw.notexists, etc.) inherit
    // the group-level exception list [x_none]. Only the base `throw` instruction
    // has an instruction-level x_throw override. This is intentional because
    // throw.* instructions raise specific JS errors unconditionally (they don't
    // "throw" in the exception-flag sense used for optimization).
    let all = ExceptionType::all();
    assert!(!insn::ThrowNotexists::new().is_throw_ex(all));
    assert!(!insn::ThrowConstassignment::new(Reg(0)).is_throw_ex(all));
    assert!(!insn::ThrowIfnotobject::new(Reg(0)).is_throw_ex(all));
}

#[test]
fn is_throw_ex_negative() {
    let all = ExceptionType::all();
    assert!(!insn::Ldundefined::new().is_throw_ex(all));
    assert!(!insn::Return::new().is_throw_ex(all));
    assert!(!insn::Jmp::new(Label(0)).is_throw_ex(all));
}

#[test]
fn is_throw_ex_lda_str_oom() {
    // lda.str group has exceptions: [x_oom] — the only non-throw, non-none exception.
    assert!(insn::LdaStr::new(EntityId(0)).is_throw_ex(ExceptionType::X_OOM));
    assert!(!insn::LdaStr::new(EntityId(0)).is_throw_ex(ExceptionType::X_NULL));
}

// --- has_flag extended ---

#[test]
fn has_flag_call_not_assigned() {
    // Regression: the CALL flag exists in the ISA schema but is never assigned
    // to any instruction. If the ISA definition changes to assign it, this test
    // should be updated to reflect the new assignment rather than removed.
    assert!(!insn::Callarg0::new(Imm(0)).has_flag(BytecodeFlag::CALL));
    assert!(!insn::Callthis0::new(Imm(0), Reg(0)).has_flag(BytecodeFlag::CALL));
}

#[test]
fn has_flag_suspend_not_assigned() {
    // Regression: same as CALL — SUSPEND flag exists but is never assigned.
    // This also explains why is_suspend() returns false for all instructions.
    assert!(!insn::Suspendgenerator::new(Reg(0)).has_flag(BytecodeFlag::SUSPEND));
}

#[test]
fn has_flag_string_id() {
    assert!(insn::LdaStr::new(EntityId(0)).has_flag(BytecodeFlag::STRING_ID));
    assert!(insn::Ldobjbyname::new(Imm(0), EntityId(0)).has_flag(BytecodeFlag::STRING_ID));
    assert!(insn::Tryldglobalbyname::new(Imm(0), EntityId(0)).has_flag(BytecodeFlag::STRING_ID));
}

#[test]
fn has_flag_method_id() {
    assert!(insn::Definefunc::new(Imm(0), EntityId(0), Imm(0)).has_flag(BytecodeFlag::METHOD_ID));
    assert!(insn::Definemethod::new(Imm(0), EntityId(0), Imm(0)).has_flag(BytecodeFlag::METHOD_ID));
}

#[test]
fn has_flag_literalarray_id() {
    assert!(
        insn::Createarraywithbuffer::new(Imm(0), EntityId(0))
            .has_flag(BytecodeFlag::LITERALARRAY_ID)
    );
    assert!(
        insn::Createobjectwithbuffer::new(Imm(0), EntityId(0))
            .has_flag(BytecodeFlag::LITERALARRAY_ID)
    );
}

#[test]
fn has_flag_conditional() {
    assert!(insn::Jeqz::new(Label(0)).has_flag(BytecodeFlag::CONDITIONAL));
    assert!(insn::Jnez::new(Label(0)).has_flag(BytecodeFlag::CONDITIONAL));
    assert!(insn::Jeq::new(Reg(0), Label(0)).has_flag(BytecodeFlag::CONDITIONAL));
    assert!(insn::Jne::new(Reg(0), Label(0)).has_flag(BytecodeFlag::CONDITIONAL));
    assert!(!insn::Jmp::new(Label(0)).has_flag(BytecodeFlag::CONDITIONAL));
}

#[test]
fn is_range_extended() {
    assert!(insn::Callthisrange::new(Imm(0), Imm(1), Reg(0)).is_range());
    assert!(insn::Newobjrange::new(Imm(0), Imm(1), Reg(0)).is_range());
    assert!(insn::WideCallrange::new(Imm(1), Reg(0)).is_range());
    assert!(!insn::Callarg0::new(Imm(0)).is_range());
}

// --- set_label ---

#[test]
fn set_label_updates_jump_target() {
    let mut jmp = insn::Jmp::new(Label(0));
    jmp.set_label(Label(42));
    let (_, args, num_args) = jmp.emit_args();
    assert_eq!(num_args, 1);
    assert_eq!(args[0], 42, "set_label should update the jump target");
}

#[test]
fn set_label_noop_on_non_jump() {
    let mut ld = insn::Ldundefined::new();
    ld.set_label(Label(99)); // should be a no-op
    let (_, _, num_args) = ld.emit_args();
    assert_eq!(num_args, 0, "set_label on non-jump should be a no-op");
}
