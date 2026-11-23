#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if data.len() > 256 * 1024 {
        return;
    }
    // Raw instruction decoders (modern + legacy 0.0.0.2) must never panic or UB
    // on arbitrary byte slices.
    let _ = abcd_isa::decode(data);
    let _ = abcd_isa::decode_legacy(data);

    // Full `.abc` container decode; when valid, exercisepandasm emission and
    // SSA lifting + structural verification.
    if let Ok(file) = abcd_file::decode(data) {
        let _ = abcd_file::pandasm::emit_file(&file, "fuzz.abc");
        if let Ok(module) = abcd_lift::lift_file(&file) {
            let _ = abcd_ir::verify_module(&module);
        }
    }
});
