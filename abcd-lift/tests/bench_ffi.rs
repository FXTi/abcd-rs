//! V-I7 local instrumentation: measure ISA-classification FFI overhead on the
//! lift hot path (design/bridge-vendor-isolation.md §B row 5).
//!
//! Lift's CFG construction calls `Bytecode::is_jump` / `is_terminator` per
//! instruction (abcd-lift/src/cfg.rs), and each call currently crosses FFI
//! into the vendor C++ bridge (`isa_is_jump_opcode` and family,
//! abcd-isa-sys/bridge/isa_bridge.cpp). The proposed alternative is a Rust
//! `OnceLock` snapshot table (one FFI sweep at first use, pure memory reads
//! afterwards). This bench measures both sides; it does not change anything.
//!
//! `#[ignore]`d local instrumentation — never runs in CI (same treatment as
//! the textual_oracle harnesses). Run release on dabai:
//!
//! ```text
//! KEEP=1 scripts/remote-test.sh test -p abcd-lift --release \
//!     --test bench_ffi -- --ignored --nocapture
//! ```
//!
//! Env knobs (forwarded to dabai by remote-test.sh): `ABCD_BENCH_PASSES`
//! (e2e passes, default 3), `ABCD_BENCH_STRIDE` (take every Nth fixture,
//! default 1 = full corpus), `ABCD_BENCH_REPS` (micro repetitions,
//! default 5).

use std::hint::black_box;
use std::os::raw::c_int;
use std::path::PathBuf;
use std::time::{Duration, Instant};

// The symbol is produced by the abcd-isa-sys C bridge and linked into this
// test binary through abcd-lift's normal dependency chain; declaring it
// here directly keeps this instrumentation file self-contained (no extra
// dev-dependency on abcd-isa-sys).
unsafe extern "C" {
    fn isa_is_jump_opcode(opcode: u16) -> c_int;
}

// ============================================================================
// Vendor opcode space (extracted from
// abcd-isa-sys/arkcompiler_runtime_core/isa/isa.yaml)
// ============================================================================

/// All 332 valid vendor opcodes. Prefixed opcodes encode as
/// `(second_byte << 8) | prefix_byte` (isapi.rb `opcode_idx`).
const VALID_OPCODES: [u16; 332] = [
    0x0000, 0x0001, 0x0002, 0x0003, 0x0004, 0x0005, 0x0006, 0x0007, 0x0008, 0x0009, 0x000a, 0x000b,
    0x000c, 0x000d, 0x000e, 0x000f, 0x0010, 0x0011, 0x0012, 0x0013, 0x0014, 0x0015, 0x0016, 0x0017,
    0x0018, 0x0019, 0x001a, 0x001b, 0x001c, 0x001d, 0x001e, 0x001f, 0x0020, 0x0021, 0x0022, 0x0023,
    0x0024, 0x0025, 0x0026, 0x0027, 0x0028, 0x0029, 0x002a, 0x002b, 0x002c, 0x002d, 0x002e, 0x002f,
    0x0030, 0x0031, 0x0032, 0x0033, 0x0034, 0x0035, 0x0036, 0x0037, 0x0038, 0x0039, 0x003a, 0x003b,
    0x003c, 0x003d, 0x003e, 0x003f, 0x0040, 0x0041, 0x0042, 0x0043, 0x0044, 0x0045, 0x0046, 0x0047,
    0x0048, 0x0049, 0x004a, 0x004b, 0x004c, 0x004d, 0x004e, 0x004f, 0x0050, 0x0051, 0x0052, 0x0053,
    0x0054, 0x0055, 0x0056, 0x0057, 0x0058, 0x0059, 0x005a, 0x005b, 0x005c, 0x005d, 0x005e, 0x005f,
    0x0060, 0x0061, 0x0062, 0x0063, 0x0064, 0x0065, 0x0066, 0x0067, 0x0068, 0x0069, 0x006a, 0x006b,
    0x006c, 0x006d, 0x006e, 0x006f, 0x0070, 0x0071, 0x0072, 0x0073, 0x0074, 0x0075, 0x0076, 0x0077,
    0x0078, 0x0079, 0x007a, 0x007b, 0x007c, 0x007d, 0x007e, 0x007f, 0x0080, 0x0081, 0x0082, 0x0083,
    0x0084, 0x0085, 0x0086, 0x0087, 0x0088, 0x0089, 0x008a, 0x008b, 0x008c, 0x008d, 0x008e, 0x008f,
    0x0090, 0x0091, 0x0092, 0x0093, 0x0094, 0x0095, 0x0096, 0x0097, 0x0098, 0x0099, 0x009a, 0x009b,
    0x009c, 0x009d, 0x009e, 0x009f, 0x00a0, 0x00a1, 0x00a2, 0x00a3, 0x00a4, 0x00a5, 0x00a6, 0x00a7,
    0x00a8, 0x00a9, 0x00aa, 0x00ab, 0x00ac, 0x00ad, 0x00ae, 0x00af, 0x00b0, 0x00b1, 0x00b2, 0x00b3,
    0x00b4, 0x00b5, 0x00b6, 0x00b7, 0x00b8, 0x00b9, 0x00ba, 0x00bb, 0x00bc, 0x00bd, 0x00be, 0x00bf,
    0x00c0, 0x00c1, 0x00c2, 0x00c3, 0x00c4, 0x00c5, 0x00c6, 0x00c7, 0x00c8, 0x00c9, 0x00ca, 0x00cb,
    0x00cc, 0x00cd, 0x00ce, 0x00cf, 0x00d0, 0x00d1, 0x00d2, 0x00d3, 0x00d4, 0x00d5, 0x00d6, 0x00d7,
    0x00d8, 0x00d9, 0x00da, 0x00db, 0x00dc, 0x00dd, 0x00de, 0x00df, 0x00e0, 0x00e1, 0x00fb, 0x00fc,
    0x00fd, 0x00fe, 0x01fb, 0x01fc, 0x01fd, 0x01fe, 0x02fb, 0x02fc, 0x02fd, 0x02fe, 0x03fb, 0x03fc,
    0x03fd, 0x03fe, 0x04fb, 0x04fc, 0x04fd, 0x04fe, 0x05fb, 0x05fc, 0x05fd, 0x05fe, 0x06fb, 0x06fc,
    0x06fd, 0x06fe, 0x07fb, 0x07fc, 0x07fd, 0x07fe, 0x08fb, 0x08fc, 0x08fd, 0x08fe, 0x09fb, 0x09fc,
    0x09fd, 0x09fe, 0x0afb, 0x0afc, 0x0afd, 0x0bfb, 0x0bfc, 0x0bfd, 0x0cfb, 0x0cfc, 0x0cfd, 0x0dfb,
    0x0dfc, 0x0dfd, 0x0efb, 0x0efc, 0x0efd, 0x0ffb, 0x0ffc, 0x0ffd, 0x10fb, 0x10fc, 0x10fd, 0x11fb,
    0x11fc, 0x11fd, 0x12fb, 0x12fc, 0x12fd, 0x13fb, 0x13fc, 0x13fd, 0x14fb, 0x14fc, 0x14fd, 0x15fb,
    0x15fc, 0x16fb, 0x16fc, 0x17fb, 0x17fc, 0x18fb, 0x18fc, 0x19fb, 0x19fc, 0x1afb, 0x1afc, 0x1bfb,
    0x1bfc, 0x1cfc, 0x1dfc, 0x1efc, 0x1ffc, 0x20fc, 0x21fc, 0x22fc, 0x23fc, 0x24fc, 0x25fc, 0x26fc,
    0x27fc, 0x28fc, 0x29fc, 0x2afc, 0x2bfc, 0x2cfc, 0x2dfc, 0x2efc,
];

/// Compressed table index: primary opcodes 0x00..=0xFA map 1:1; prefix
/// pages (0xFB..=0xFE; 0xFF is not a valid prefix but must not panic during
/// the full u16 sweep) map to 0xFB + page*256 + second byte.
/// Max index is 0xFB + 4*256 + 0xFF = 1530; the vendor ISA's valid entries
/// only reach 1028.
#[inline(always)]
fn table_idx(op: u16) -> usize {
    let lo = (op & 0xFF) as usize;
    if lo < 0xFB {
        lo
    } else {
        0xFB + (lo - 0xFB) * 256 + (op >> 8) as usize
    }
}

/// Reference table-read implementation (what the OnceLock prototype does
/// after its one-time FFI sweep).
fn build_jump_table() -> [u8; 1536] {
    let mut t = [0u8; 1536];
    for op in 0u32..=0xFFFF {
        let op = op as u16;
        // Skip impossible encodings: a nonzero second byte only exists
        // behind a prefix byte (0xFB..=0xFF) in the low half; sweeping them
        // would alias the primary-opcode slots.
        if op > 0xFF && (op & 0xFF) < 0xFB {
            continue;
        }
        t[table_idx(op)] = unsafe { isa_is_jump_opcode(op) } as u8;
    }
    t
}

// ============================================================================
// Micro benchmark: per-call FFI vs per-call table read
// ============================================================================

const MICRO_ITERS: usize = 20_000_000;

fn reps() -> usize {
    env_usize("ABCD_BENCH_REPS", 5)
}

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

/// Time `MICRO_ITERS` iterations of `body(op)` rotating over VALID_OPCODES.
fn time_opcode_loop(body: impl Fn(u16) -> u64) -> Vec<Duration> {
    let mut out = Vec::new();
    for _ in 0..reps() {
        let mut acc = 0u64;
        let mut i = 0usize;
        let t = Instant::now();
        for _ in 0..MICRO_ITERS {
            let op = VALID_OPCODES[i];
            i += 1;
            if i == VALID_OPCODES.len() {
                i = 0;
            }
            acc += body(black_box(op));
        }
        out.push(t.elapsed());
        black_box(acc);
    }
    out
}

/// Time the same loop over real decoded bytecodes (the actual hot-path
/// call shape: `representative_opcode()` match + classification).
fn time_bytecode_loop(bcs: &[abcd_isa::Bytecode]) -> Vec<Duration> {
    let mut out = Vec::new();
    for _ in 0..reps() {
        let mut acc = 0u64;
        let mut i = 0usize;
        let t = Instant::now();
        for _ in 0..MICRO_ITERS {
            let bc = bcs[i];
            i += 1;
            if i == bcs.len() {
                i = 0;
            }
            acc += black_box(bc).is_jump() as u64;
        }
        out.push(t.elapsed());
        black_box(acc);
    }
    out
}

fn ns_per_call(ds: &[Duration]) -> Vec<f64> {
    ds.iter()
        .map(|d| d.as_secs_f64() * 1e9 / MICRO_ITERS as f64)
        .collect()
}

/// Collect a pool of real decoded bytecodes from the first corpus fixtures.
fn bytecode_pool(paths: &[PathBuf], want: usize) -> Vec<abcd_isa::Bytecode> {
    let mut pool = Vec::new();
    for p in paths {
        let data = std::fs::read(p).expect("read fixture");
        let file = abcd_file::decode(&data).expect("decode fixture");
        for class in file.classes.values() {
            for m in &class.methods {
                if let Some(body) = &m.body {
                    pool.extend_from_slice(&body.bytecodes);
                    if pool.len() >= want {
                        return pool;
                    }
                }
            }
        }
    }
    pool
}

#[test]
#[ignore = "local instrumentation (V-I7); release-only micro benchmark"]
fn bench_micro_ffi_vs_table() {
    let table = build_jump_table();
    // Sanity: table agrees with FFI on every opcode.
    for &op in &VALID_OPCODES {
        let ffi = unsafe { isa_is_jump_opcode(op) } as u8;
        assert_eq!(ffi, table[table_idx(op)], "table mismatch at {op:#x}");
    }

    // Warm up the bridge path (first-call lazy init, icache).
    for &op in &VALID_OPCODES {
        black_box(unsafe { isa_is_jump_opcode(op) });
    }

    let baseline = ns_per_call(&time_opcode_loop(|op| (op & 1) as u64));
    let ffi = ns_per_call(&time_opcode_loop(|op| unsafe {
        isa_is_jump_opcode(op) as u64
    }));
    let tbl = ns_per_call(&time_opcode_loop(|op| table[table_idx(op)] as u64));

    let paths = corpus_paths();
    let pool = bytecode_pool(&paths, 200_000);
    println!(
        "[bench] micro real-bytecode pool: {} instructions",
        pool.len()
    );
    let bc_loop = ns_per_call(&time_bytecode_loop(&pool));

    println!(
        "[bench] micro iters per rep: {MICRO_ITERS}, reps: {}",
        reps()
    );
    println!(
        "[bench] micro baseline loop-only ns/call: {baseline:.3?} (median {:.3})",
        median(baseline.clone())
    );
    println!(
        "[bench] micro FFI isa_is_jump_opcode ns/call: {ffi:.3?} (median {:.3})",
        median(ffi.clone())
    );
    println!(
        "[bench] micro table-read ns/call: {tbl:.3?} (median {:.3})",
        median(tbl.clone())
    );
    println!(
        "[bench] micro Bytecode::is_jump (match + classify) ns/call: {bc_loop:.3?} (median {:.3})",
        median(bc_loop.clone())
    );
    println!(
        "[bench] micro net FFI ~= {:.3} ns/call, net table ~= {:.3} ns/call",
        median(ffi) - median(baseline.clone()),
        median(tbl) - median(baseline),
    );
}

// ============================================================================
// End-to-end: lift the corpus under release, N passes, median
// ============================================================================

fn corpus_paths() -> Vec<PathBuf> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../exports/corpus");
    let mut out = Vec::new();
    let mut stack = vec![root];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(dir).expect("corpus dir") {
            let p = entry.expect("dir entry").path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|e| e == "abc") {
                out.push(p);
            }
        }
    }
    out.sort();
    out
}

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

#[test]
#[ignore = "local instrumentation (V-I7); release-only e2e benchmark"]
fn bench_e2e_lift_corpus() {
    let all = corpus_paths();
    let stride = env_usize("ABCD_BENCH_STRIDE", 1).max(1);
    let passes = env_usize("ABCD_BENCH_PASSES", 3).max(1);
    let paths: Vec<_> = all.iter().step_by(stride).collect();
    println!(
        "[bench] e2e fixtures: {} of {} (stride {stride}), passes: {passes}",
        paths.len(),
        all.len()
    );

    let mut lift_passes = Vec::new();
    let mut decode_passes = Vec::new();
    let mut total_insns = 0u64;
    let mut decode_fail = 0u64;
    let mut lift_fail = 0u64;

    for pass in 0..passes {
        let mut lift_total = Duration::ZERO;
        let mut decode_total = Duration::ZERO;
        let mut insns = 0u64;
        for (n, p) in paths.iter().enumerate() {
            let data = std::fs::read(p).expect("read fixture");
            let t0 = Instant::now();
            let file = match abcd_file::decode(&data) {
                Ok(f) => f,
                Err(_) => {
                    decode_fail += 1;
                    continue;
                }
            };
            decode_total += t0.elapsed();
            for class in file.classes.values() {
                for m in &class.methods {
                    if let Some(body) = &m.body {
                        insns += body.bytecodes.len() as u64;
                    }
                }
            }
            let t1 = Instant::now();
            let module = match abcd_lift::lift_file(&file) {
                Ok(m) => m,
                Err(_) => {
                    lift_fail += 1;
                    continue;
                }
            };
            lift_total += t1.elapsed();
            black_box(module.functions.len());
            drop(module);
            if n % 500 == 499 {
                println!(
                    "[bench] pass {pass}: {n}/{} fixtures, lift so far {:?}",
                    paths.len(),
                    lift_total
                );
            }
        }
        total_insns = insns;
        lift_passes.push(lift_total);
        decode_passes.push(decode_total);
        println!(
            "[bench] pass {pass}: lift {:?}, decode {:?}, instructions {insns}",
            lift_total, decode_total
        );
    }

    let lifts: Vec<f64> = lift_passes.iter().map(|d| d.as_secs_f64() * 1e3).collect();
    let decodes: Vec<f64> = decode_passes
        .iter()
        .map(|d| d.as_secs_f64() * 1e3)
        .collect();
    println!("[bench] e2e lift totals ms: {lifts:.1?}");
    println!("[bench] e2e lift median: {:.1} ms", median(lifts.clone()));
    println!(
        "[bench] e2e lift spread: min {:.1}, max {:.1}",
        lifts.iter().cloned().fold(f64::INFINITY, f64::min),
        lifts.iter().cloned().fold(f64::NEG_INFINITY, f64::max),
    );
    println!("[bench] e2e decode totals ms: {decodes:.1?}");
    println!("[bench] e2e instructions lifted (last pass): {total_insns}");
    println!("[bench] e2e decode_fail={decode_fail} lift_fail={lift_fail}");
}
