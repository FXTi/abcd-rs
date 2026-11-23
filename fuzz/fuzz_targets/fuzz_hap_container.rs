#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // Cap input size at 512 KiB so fuzzer throughput stays high and hostile
    // ZIP bombs / decompression budgets exercise bounded rejection cleanly.
    if data.len() > 512 * 1024 {
        return;
    }
    if let Ok(modules) = abcd_hap::abc_modules(data) {
        for m in &modules {
            let _ = abcd_file::decode(m.data.as_slice());
        }
    }
});
