//! Systematic Emitter roundtrip tests.
//!
//! For every Emitter method, emit an instruction with default operands,
//! build the bytecode, decode it, and verify the mnemonic matches.

include!(concat!(env!("OUT_DIR"), "/roundtrip_tests.rs"));

#[test]
fn all_emitter_mnemonics_roundtrip() {
    let mut passed = 0;
    let mut failed = Vec::new();

    for info in abcd_isa::opcode_table() {
        let mnemonic = info.mnemonic();
        match roundtrip_one(mnemonic) {
            Some(decoded) if decoded != mnemonic => {
                failed.push(format!(
                    "  {}: emitted but decoded as '{}'",
                    mnemonic, decoded
                ));
            }
            Some(_) => passed += 1,
            None => {} // no emitter method for this mnemonic, skip
        }
    }

    if !failed.is_empty() {
        panic!(
            "{} emitter mnemonics failed roundtrip:\n{}",
            failed.len(),
            failed.join("\n")
        );
    }

    // Sanity: we should have tested a substantial number
    assert!(
        passed > 100,
        "expected >100 emitter roundtrips, got {}",
        passed
    );
    eprintln!("roundtrip OK: {} emitter mnemonics", passed);
}
