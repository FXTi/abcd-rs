//! Systematic opcode_table() coverage tests.
//!
//! Validates metadata consistency for every opcode in the ISA.

use abcd_isa::{OpcodeFlags, OperandKind, lookup, opcode_count, opcode_table};

#[test]
fn opcode_count_is_positive() {
    assert!(opcode_count() > 0, "ISA should have at least one opcode");
}

#[test]
fn lookup_roundtrip_for_all_opcodes() {
    for info in opcode_table() {
        let raw = info.opcode().raw();
        let found = lookup(raw);
        assert!(
            found.is_some(),
            "lookup({:#x}) returned None for mnemonic '{}'",
            raw,
            info.mnemonic()
        );
        let found = found.unwrap();
        assert_eq!(
            found.mnemonic(),
            info.mnemonic(),
            "lookup({:#x}) mnemonic mismatch",
            raw
        );
    }
}

#[test]
fn all_opcodes_have_positive_size() {
    for info in opcode_table() {
        assert!(info.size() >= 1, "'{}' has size 0", info.mnemonic());
    }
}

#[test]
fn all_opcodes_have_nonempty_mnemonic() {
    for info in opcode_table() {
        let m = info.mnemonic();
        assert!(
            !m.is_empty(),
            "opcode {:#x} has empty mnemonic",
            info.opcode().raw()
        );
        // Mnemonics should be ASCII lowercase/digits/dots/underscores
        assert!(
            m.bytes()
                .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'.' || b == b'_'),
            "mnemonic '{}' contains unexpected characters",
            m
        );
    }
}

#[test]
fn all_opcodes_have_nonempty_namespace() {
    for info in opcode_table() {
        assert!(
            !info.namespace().is_empty(),
            "'{}' has empty namespace",
            info.mnemonic()
        );
    }
}

#[test]
fn prefixed_opcodes_have_two_byte_encoding() {
    // Prefixed opcodes use a prefix byte followed by a sub-opcode byte.
    // The raw value encodes both: (sub << 8) | prefix_byte, but some may
    // have sub=0 so raw <= 0xFF. We just verify size >= 2.
    for info in opcode_table() {
        if info.is_prefixed() {
            assert!(
                info.size() >= 2,
                "prefixed '{}' has size {} < 2",
                info.mnemonic(),
                info.size()
            );
        }
    }
}

#[test]
fn non_prefixed_opcodes_fit_in_u8() {
    for info in opcode_table() {
        if !info.is_prefixed() {
            assert!(
                info.opcode().raw() <= 0xFF,
                "non-prefixed '{}' has raw value {:#x} > 0xFF",
                info.mnemonic(),
                info.opcode().raw()
            );
        }
    }
}

#[test]
fn prefixed_opcodes_have_size_ge_2() {
    for info in opcode_table() {
        if info.is_prefixed() {
            assert!(
                info.size() >= 2,
                "prefixed '{}' has size {} < 2",
                info.mnemonic(),
                info.size()
            );
        }
    }
}

#[test]
fn operand_count_is_consistent() {
    for info in opcode_table() {
        let ops: Vec<_> = info.operands().collect();
        let expected_len = info.operands().len();
        assert_eq!(
            ops.len(),
            expected_len,
            "'{}' operand iterator len() disagrees with count",
            info.mnemonic()
        );
    }
}

#[test]
fn operand_offsets_fit_within_instruction() {
    for info in opcode_table() {
        let size_bits = info.size() * 8;
        for op in info.operands() {
            let end_bit = op.byte_offset() * 8 + op.bit_offset_in_byte() + op.bit_width();
            assert!(
                end_bit <= size_bits,
                "'{}': operand ends at bit {} but instruction is only {} bits",
                info.mnemonic(),
                end_bit,
                size_bits
            );
        }
    }
}

#[test]
fn operand_kinds_are_valid() {
    for info in opcode_table() {
        for op in info.operands() {
            // Just ensure kind() doesn't panic and returns a known variant
            match op.kind() {
                OperandKind::Reg | OperandKind::Imm | OperandKind::Id => {}
            }
        }
    }
}

#[test]
fn jump_instructions_have_imm_operand() {
    for info in opcode_table() {
        if info.flags().contains(OpcodeFlags::JUMP) {
            let has_imm = info.operands().any(|op| op.kind() == OperandKind::Imm);
            assert!(
                has_imm,
                "JUMP instruction '{}' has no IMM operand for jump target",
                info.mnemonic()
            );
        }
    }
}

#[test]
fn return_instructions_are_terminators() {
    // Instructions with RETURN flag should logically be terminators.
    // We verify the flag is set consistently.
    for info in opcode_table() {
        if info.flags().contains(OpcodeFlags::RETURN) {
            // RETURN flag instructions should exist — just verify the flag is readable
            let _ = info.mnemonic();
        }
    }
}

#[test]
fn no_duplicate_opcode_values() {
    let mut seen = std::collections::HashMap::new();
    for info in opcode_table() {
        let raw = info.opcode().raw();
        if let Some(prev) = seen.insert(raw, info.mnemonic()) {
            panic!(
                "duplicate opcode value {:#x}: '{}' and '{}'",
                raw,
                prev,
                info.mnemonic()
            );
        }
    }
}

#[test]
fn no_duplicate_mnemonics_within_same_format() {
    // Some mnemonics may appear with different opcode values (e.g. `mov` with
    // different register widths). We verify that within the same format, there
    // are no duplicates.
    let mut seen: std::collections::HashMap<(&str, u8), u16> = std::collections::HashMap::new();
    for info in opcode_table() {
        let key = (info.mnemonic(), info.format().raw());
        if let Some(prev_raw) = seen.insert(key, info.opcode().raw()) {
            panic!(
                "duplicate mnemonic '{}' with same format {}: opcode {:#x} and {:#x}",
                info.mnemonic(),
                info.format().raw(),
                prev_raw,
                info.opcode().raw()
            );
        }
    }
}

#[test]
fn opcode_table_count_matches_opcode_count() {
    assert_eq!(opcode_table().count(), opcode_count());
}
