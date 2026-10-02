//! Archaeology probe (manual, `#[ignore]`): dump per-method raw bytecode
//! from ancient (0.0.0.2-format) .abc files and report every byte the
//! v24-pinned ISA decoder rejects.
//!
//! Usage:
//!
//! ```text
//! ANCIENT_PROBE_DIR=/tmp/ancient-probe \
//!   cargo test -p abcd-file --test ancient_opcode_probe -- --ignored --nocapture
//! ```
//!
//! The probe walks classes/methods through the sys layer (which accepts the
//! 0.0.0.2 header — decode only dies inside the bytecode stage), dumps each
//! method's raw instruction stream to `<dir>/dump/<file>__<method_off>.bin`,
//! and prints the first undecodable byte per method.

use std::collections::BTreeMap;
use std::ffi::c_void;
use std::path::PathBuf;

use abcd_file_sys as sys;

unsafe extern "C" fn push_off(offset: u32, ctx: *mut c_void) {
    let vec = unsafe { &mut *(ctx as *mut Vec<u32>) };
    vec.push(offset);
}

/// Open an abc file and return `(version, [(method_off, code_bytes)])`.
fn dump_methods(data: &[u8]) -> ([u8; 4], Vec<(u32, Vec<u8>)>) {
    let f = unsafe { sys::abc_file_open(data.as_ptr(), data.len()) };
    assert!(!f.is_null(), "abc_file_open failed");
    let mut version = [0u8; 4];
    unsafe { sys::abc_file_version(f, version.as_mut_ptr()) };

    let mut out = Vec::new();
    let num_classes = unsafe { sys::abc_file_num_classes(f) };
    for i in 0..num_classes {
        let class_off = unsafe { sys::abc_file_class_offset(f, i) };
        if class_off == u32::MAX {
            continue;
        }
        if unsafe { sys::abc_file_is_external(f, class_off) } != 0 {
            continue;
        }
        let cr = unsafe { sys::abc_class_open(f, class_off) };
        if cr.is_null() {
            continue;
        }
        let mut moffs: Vec<u32> = Vec::new();
        unsafe {
            sys::abc_class_enumerate_methods(
                cr,
                Some(push_off),
                &mut moffs as *mut Vec<u32> as *mut c_void,
            )
        };
        for m in moffs {
            let mr = unsafe { sys::abc_method_open(f, m) };
            if mr.is_null() {
                continue;
            }
            let code_off = unsafe { sys::abc_method_code_off(mr) };
            unsafe { sys::abc_method_close(mr) };
            if code_off == u32::MAX {
                continue;
            }
            let code = unsafe { sys::abc_code_open(f, code_off) };
            if code.is_null() {
                continue;
            }
            let ptr = unsafe { sys::abc_code_instructions(code) };
            let len = unsafe { sys::abc_code_code_size(code) } as usize;
            let bytes = if ptr.is_null() {
                Vec::new()
            } else {
                unsafe { std::slice::from_raw_parts(ptr, len) }.to_vec()
            };
            unsafe { sys::abc_code_close(code) };
            out.push((m, bytes));
        }
        unsafe { sys::abc_class_close(cr) };
    }
    unsafe { sys::abc_file_close(f) };
    (version, out)
}

#[test]
#[ignore = "archaeology probe: needs ANCIENT_PROBE_DIR with extracted .abc files"]
fn ancient_opcode_probe() {
    let dir = PathBuf::from(
        std::env::var("ANCIENT_PROBE_DIR").unwrap_or_else(|_| "/tmp/ancient-probe".to_string()),
    );
    let dump_dir = dir.join("dump");
    std::fs::create_dir_all(&dump_dir).unwrap();

    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "abc"))
        .collect();
    entries.sort();

    // opcode byte (and second byte for prefixed) -> count of methods hitting it
    let mut first_byte_hits: BTreeMap<(u8, u8), u32> = BTreeMap::new();

    for path in entries {
        let data = std::fs::read(&path).unwrap();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let (version, methods) = dump_methods(&data);
        println!("== {name} version {}.{:.2?}", version[0], &version[1..]);
        let mut decode_fail = 0usize;
        for (moff, code) in &methods {
            let dump = dump_dir.join(format!("{name}__{moff:#x}.bin"));
            std::fs::write(&dump, code).unwrap();
            match abcd_isa::decode(code) {
                Ok(_) => {}
                Err(abcd_isa::DecodeError::InvalidOpcode(off)) => {
                    decode_fail += 1;
                    let b0 = code[off];
                    let b1 = code.get(off + 1).copied().unwrap_or(0);
                    *first_byte_hits.entry((b0, b1)).or_insert(0) += 1;
                    let ctx: Vec<String> = code[off.saturating_sub(4)..(off + 8).min(code.len())]
                        .iter()
                        .map(|b| format!("{b:02x}"))
                        .collect();
                    println!(
                        "  method {moff:#x}: invalid opcode {b0:#04x} at offset {off} (ctx: {})",
                        ctx.join(" ")
                    );
                }
                Err(e) => {
                    decode_fail += 1;
                    println!("  method {moff:#x}: other decode error: {e}");
                }
            }
        }
        println!(
            "  {} methods, {decode_fail} failing bytecode decode",
            methods.len()
        );
    }

    println!("\n== first-failing byte histogram (byte0, byte1) -> method count ==");
    for ((b0, b1), n) in &first_byte_hits {
        println!("  {b0:#04x} {b1:#04x}: {n}");
    }
}

/// Post-fix red->green check: every extracted 0.0.0.2 module must now decode.
#[test]
#[ignore = "archaeology probe: needs ANCIENT_PROBE_DIR with extracted .abc files"]
fn ancient_files_decode_green() {
    let dir = PathBuf::from(
        std::env::var("ANCIENT_PROBE_DIR").unwrap_or_else(|_| "/tmp/ancient-probe".to_string()),
    );
    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "abc"))
        .collect();
    entries.sort();

    let mut failures = Vec::new();
    let mut ok = 0usize;
    for path in entries {
        let data = std::fs::read(&path).unwrap();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        match abcd_file::decode(&data) {
            Ok(f) => {
                ok += 1;
                let methods: usize = f.classes.values().map(|c| c.methods.len()).sum();
                println!("OK  {name}: {} classes, {methods} methods", f.classes.len());
            }
            Err(e) => {
                failures.push(format!("{name}: {e}"));
                println!("ERR {name}: {e}");
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} legacy files failed to decode:\n{}",
        failures.len(),
        failures.join("\n")
    );
    println!("green: {ok} legacy .abc files decoded");
}
