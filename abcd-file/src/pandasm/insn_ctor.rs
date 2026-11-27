//! Mnemonic → [`Bytecode`] construction table for the pandasm parser.
//!
//! Pre-generated from `isa.yaml` via `abcd-isa/templates/insn_ctor.rs.erb` and
//! verified by `python3 scripts/vendor-gen.py verify`.

use abcd_isa::insn;
use abcd_isa::{Bytecode, EntityId, Imm, Label, Reg};

use super::parse::RawOperand;
use super::parse::RawOperand::{E, I, L, R};

include!("generated/insn_ctor.rs");

#[cfg(test)]
mod tests {
    //! Unit coverage for the construction table: every `MNEMONICS` entry
    //! constructs from its canonical operand vector, wrong shapes return
    //! `None`, unknown mnemonics return `None`, and corpus-absent arms
    //! round-trip through `abcd_isa::{encode, decode}`.
    use super::*;
    use abcd_isa::Operand;

    fn canonical_ops(mnemonic: &str) -> Vec<RawOperand> {
        dummy(mnemonic)
            .unwrap_or_else(|| panic!("{mnemonic} must have a dummy arm"))
            .operands()
            .iter()
            .map(|op| match *op {
                Operand::Reg(_) => R(1),
                Operand::Imm(_) => I(1),
                Operand::Entity(_, _) => E(1),
                Operand::Label(_) => L(0),
            })
            .collect()
    }

    fn canonical_operands(mnemonic: &str) -> Vec<Operand> {
        dummy(mnemonic)
            .unwrap()
            .operands()
            .iter()
            .map(|op| match *op {
                Operand::Reg(_) => Operand::Reg(1),
                Operand::Imm(_) => Operand::Imm(1),
                Operand::Entity(kind, _) => Operand::Entity(kind, 1),
                Operand::Label(_) => Operand::Label(0),
            })
            .collect()
    }

    #[test]
    fn mnemonics_table_is_sorted_and_unique() {
        let mut sorted = MNEMONICS.to_vec();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted, MNEMONICS, "MNEMONICS must be sorted and unique");
    }

    #[test]
    fn dummy_covers_every_mnemonic() {
        for &mnemonic in MNEMONICS {
            assert!(dummy(mnemonic).is_some(), "dummy({mnemonic})");
        }
        assert!(dummy("bogus").is_none());
        assert!(dummy("").is_none());
        assert!(dummy("Ldai").is_none());
    }

    #[test]
    fn construct_every_mnemonic_mainline_and_roundtrip() {
        for &mnemonic in MNEMONICS {
            let ops = canonical_ops(mnemonic);
            let bc = construct(mnemonic, &ops)
                .unwrap_or_else(|| panic!("construct({mnemonic}, canonical ops)"));
            assert_eq!(bc.mnemonic(), mnemonic, "constructed variant");
            assert_eq!(
                bc.operands(),
                canonical_operands(mnemonic),
                "constructed operands for {mnemonic}"
            );
            let (bytes, _) =
                abcd_isa::encode(&[bc]).unwrap_or_else(|e| panic!("{mnemonic} must encode: {e}"));
            let decoded =
                abcd_isa::decode(&bytes).unwrap_or_else(|e| panic!("{mnemonic} must decode: {e}"));
            assert_eq!(decoded.len(), 1, "{mnemonic} decodes to one insn");
            assert_eq!(decoded[0].0.mnemonic(), mnemonic);
            assert_eq!(decoded[0].0.operands(), bc.operands());
        }
    }

    #[test]
    fn construct_rejects_wrong_operand_shapes() {
        for &mnemonic in MNEMONICS {
            let ops = canonical_ops(mnemonic);
            if ops.is_empty() {
                assert!(
                    construct(mnemonic, &[I(0)]).is_none(),
                    "{mnemonic} with an operand"
                );
            } else {
                assert!(
                    construct(mnemonic, &ops[..ops.len() - 1]).is_none(),
                    "{mnemonic} short"
                );
                let mut wrong = ops.clone();
                wrong[0] = match wrong[0] {
                    R(_) => I(0),
                    I(_) | E(_) | L(_) => R(0),
                };
                assert!(
                    construct(mnemonic, &wrong).is_none(),
                    "{mnemonic} wrong first kind"
                );
            }
        }
    }

    #[test]
    fn construct_unknown_mnemonic_is_none() {
        assert!(construct("bogus", &[]).is_none());
        assert!(construct("bogus", &[R(1), I(1), E(1), L(0)]).is_none());
        assert!(construct("LDai", &[I(1)]).is_none());
    }
}
