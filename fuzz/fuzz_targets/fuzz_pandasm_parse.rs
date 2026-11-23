#![no_main]

use abcd_isa::Version;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if data.len() > 64 * 1024 {
        return;
    }
    // Exercise both the <=12.x header-literal-table and 13+/24 index-collection
    // parser paths on arbitrary `.pa` byte streams.
    for ver in [Version::new(12, 0, 6, 0), Version::new(24, 0, 0, 0)] {
        if let Ok(file) = abcd_file::pandasm::parse_file_with_version(data, ver) {
            let _ = abcd_file::pandasm::emit_file(&file, "fuzz.abc");
        }
    }
});
