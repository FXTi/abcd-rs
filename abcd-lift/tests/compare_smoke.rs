//! Comparator smoke tests: the canonical comparison must (1) agree on
//! a real corpus fixture, and (2) BITE when the v0.2 module is
//! perturbed — a vacuous comparator is worse than none.

use abcd_file::decode;

mod common;
use common::compare;

fn arithmetic_fixture() -> abcd_file::File {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../exports/corpus/9.0.0.0/local/arithmetic/baseline/input.abc");
    decode(&std::fs::read(path).expect("corpus fixture")).expect("decode")
}

#[test]
#[ignore = "requires exported GHCR corpus"]
fn comparator_agrees_on_arithmetic() {
    let file = arithmetic_fixture();
    let v1 = abcd_ir::lift::lift_file(&file).expect("v0.1 lift");
    let v2 = abcd_lift::lift_file(&file).expect("v0.2 lift");
    let report = compare::compare_modules(&file, &v1, &v2);
    assert!(
        report.is_parity(),
        "expected parity, got: {:?}",
        report.mismatches
    );
    assert!(report.tokens_compared > 0);
}

#[test]
#[ignore = "requires exported GHCR corpus"]
fn comparator_bites_on_perturbation() {
    let file = arithmetic_fixture();
    let v1 = abcd_ir::lift::lift_file(&file).expect("v0.1 lift");
    let mut v2 = abcd_lift::lift_file(&file).expect("v0.2 lift");

    // Perturb: flip the first BinaryOp's operator.
    let flipped = v2.insts.iter_mut().find_map(|inst| {
        if let abcd_ir2::Op::BinaryOp { op, .. } = &mut inst.op {
            *op = match *op {
                abcd_ir2::BinOp::Add => abcd_ir2::BinOp::Sub,
                _ => abcd_ir2::BinOp::Add,
            };
            Some(true)
        } else {
            None
        }
    });
    assert_eq!(flipped, Some(true), "fixture must contain a BinaryOp");

    let report = compare::compare_modules(&file, &v1, &v2);
    assert_eq!(
        report.mismatches.len(),
        1,
        "exactly one function must mismatch: {:?}",
        report.mismatches
    );
    let m = &report.mismatches[0];
    assert!(m.v1.contains("BinaryOp"), "context: {}", m.v1);
    assert!(m.v2.contains("BinaryOp"), "context: {}", m.v2);
}
