//! Allocator comparison harness (musl/allocator track, MEMORY.md
//! 2026-10-02 — the maintainer's bench-first ruling: measure before any
//! glibc→musl / allocator switch).
//!
//! The global allocator is a compile-time-only choice, so this target
//! selects it by cargo feature (each test target is its own crate, so a
//! `#[global_allocator]` here is legal — but a target may declare only
//! ONE, hence the at-most-one-feature compile_error below):
//!
//! ```text
//! # dabai (Linux/glibc): system vs mimalloc vs jemalloc, release, 3 passes
//! KEEP=1 scripts/remote-test.sh test -p abcd-rs --release --test bench-alloc -- --ignored --nocapture
//! KEEP=1 scripts/remote-test.sh test -p abcd-rs --release --test bench-alloc --features alloc-mimalloc -- --ignored --nocapture
//! KEEP=1 scripts/remote-test.sh test -p abcd-rs --release --test bench-alloc --features alloc-jemalloc -- --ignored --nocapture
//! ```
//!
//! Run each of the two tests in a SEPARATE process invocation so the
//! reported peak RSS is attributable to that workload alone (ru_maxrss /
//! VmHWM is a process-lifetime maximum):
//!
//! ```text
//! cargo test -p abcd-rs --release --test bench-alloc -- --ignored --nocapture bench_lift_corpus
//! cargo test -p abcd-rs --release --test bench-alloc -- --ignored --nocapture bench_decompile_subset
//! ```
//!
//! Skip-by-absence: with no exported corpus (`exports/corpus`), each test
//! prints a skip line and returns green. The tests are `#[ignore]`d and
//! never run in CI (same treatment as tests/lift-decompile).
//!
//! Env knobs: `ABCD_BENCH_PASSES` (timed passes per workload, default 3),
//! `ABCD_BENCH_TOP_PER_VERSION` (decompile-subset fixtures per corpus
//! version, largest by file size, default 5), `ABCD_CORPUS_ROOT` (corpus
//! override, same as the other corpus gates).

use std::hint::black_box;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

#[cfg(all(feature = "alloc-mimalloc", feature = "alloc-jemalloc"))]
compile_error!("bench-alloc: enable at most one of alloc-mimalloc / alloc-jemalloc");

#[cfg(feature = "alloc-mimalloc")]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[cfg(feature = "alloc-jemalloc")]
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

/// The allocator label that goes into every report line.
fn allocator_name() -> &'static str {
    #[cfg(feature = "alloc-mimalloc")]
    return "mimalloc";
    #[cfg(feature = "alloc-jemalloc")]
    return "jemalloc";
    #[cfg(all(not(feature = "alloc-mimalloc"), not(feature = "alloc-jemalloc")))]
    return "system";
}

// ============================================================================
// Peak RSS (process-lifetime maximum resident set)
// ============================================================================

/// Peak RSS in bytes, or None on platforms without a probe here.
/// Linux: VmHWM from /proc/self/status. macOS: ru_maxrss (bytes) via
/// getrusage. Windows: unprobed (the GH experiment lane reports its own).
fn peak_rss_bytes() -> Option<u64> {
    #[cfg(target_os = "linux")]
    {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        for line in status.lines() {
            if let Some(rest) = line.strip_prefix("VmHWM:") {
                let kb: u64 = rest.trim().strip_suffix("kB")?.trim().parse().ok()?;
                return Some(kb * 1024);
            }
        }
        None
    }
    #[cfg(target_os = "macos")]
    {
        // struct rusage without a libc dep: two 16-byte timevals, then
        // ru_maxrss is the first long (word index 4) of the tail. The
        // buffer is oversized; getrusage writes what it knows.
        #[repr(C)]
        struct RusageBuf {
            words: [i64; 20],
        }
        extern "C" {
            fn getrusage(who: i32, usage: *mut RusageBuf) -> i32;
        }
        const RUSAGE_SELF: i32 = 0;
        let mut buf = RusageBuf { words: [0; 20] };
        let rc = unsafe { getrusage(RUSAGE_SELF, &mut buf) };
        (rc == 0).then(|| buf.words[4] as u64)
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        None
    }
}

// ============================================================================
// Corpus loading (same recursive walk as abcd-lift/tests/bench_ffi.rs)
// ============================================================================

fn corpus_root() -> PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus"))
}

/// Every `.abc` fixture under the corpus root, sorted for determinism.
/// None (skip-by-absence) when the corpus export is not there.
fn corpus_paths() -> Option<Vec<PathBuf>> {
    let root = corpus_root();
    if !root.is_dir() {
        return None;
    }
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
    if out.is_empty() {
        return None;
    }
    out.sort();
    Some(out)
}

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

// ============================================================================
// Reporting
// ============================================================================

struct StageTimes {
    decode: Duration,
    lift: Duration,
    decompile: Duration,
}

impl StageTimes {
    fn wall(&self) -> Duration {
        self.decode + self.lift + self.decompile
    }
}

/// Print the fixed-format per-pass lines plus the median/spread/RSS
/// summary line the report tables are built from.
fn report(workload: &str, fixtures: usize, passes: &[StageTimes]) {
    let walls_ms: Vec<f64> = passes
        .iter()
        .map(|p| p.wall().as_secs_f64() * 1e3)
        .collect();
    let med = median(walls_ms.clone());
    let min = walls_ms.iter().cloned().fold(f64::INFINITY, f64::min);
    let max = walls_ms.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
    let spread_pct = if med > 0.0 {
        (max - min) / med * 100.0
    } else {
        0.0
    };
    let rss_mib = peak_rss_bytes().map(|b| b as f64 / (1024.0 * 1024.0));

    println!("[bench] === workload: {workload} ===");
    println!("[bench] allocator: {}", allocator_name());
    println!("[bench] fixtures: {fixtures}, passes: {}", passes.len());
    for (i, p) in passes.iter().enumerate() {
        println!(
            "[bench] pass {i}: decode {:.1} ms, lift {:.1} ms, decompile {:.1} ms, wall {:.1} ms",
            p.decode.as_secs_f64() * 1e3,
            p.lift.as_secs_f64() * 1e3,
            p.decompile.as_secs_f64() * 1e3,
            p.wall().as_secs_f64() * 1e3,
        );
    }
    println!(
        "[bench] wall median {:.1} ms | min {:.1} | max {:.1} | spread {:.2}%",
        med, min, max, spread_pct
    );
    match rss_mib {
        Some(mib) => {
            println!("[bench] peak RSS: {mib:.1} MiB (process-lifetime max, end of workload)")
        }
        None => println!("[bench] peak RSS: unprobed on this platform"),
    }
    println!(
        "[bench] SUMMARY workload={workload} allocator={} wall_median_ms={med:.1} wall_min_ms={min:.1} wall_max_ms={max:.1} peak_rss_mib={}",
        allocator_name(),
        rss_mib
            .map(|m| format!("{m:.1}"))
            .unwrap_or_else(|| "n/a".into()),
    );
}

// ============================================================================
// Workload 1: lift the full corpus sweep
// ============================================================================

#[test]
#[ignore = "local instrumentation (allocator track); release-only benchmark"]
fn bench_lift_corpus() {
    let Some(paths) = corpus_paths() else {
        eprintln!("bench-alloc: no corpus at exports/corpus, skipping (corpus not exported)");
        return;
    };
    let passes = env_usize("ABCD_BENCH_PASSES", 3).max(1);
    println!(
        "[bench] lift sweep: {} fixtures, {passes} passes",
        paths.len()
    );

    let mut results = Vec::new();
    for pass in 0..passes {
        let mut t = StageTimes {
            decode: Duration::ZERO,
            lift: Duration::ZERO,
            decompile: Duration::ZERO,
        };
        let mut insns = 0u64;
        let mut decode_fail = 0u64;
        let mut lift_fail = 0u64;
        for p in &paths {
            let data = std::fs::read(p).expect("read fixture");
            let t0 = Instant::now();
            let file = match abcd_file::decode(&data) {
                Ok(f) => f,
                Err(_) => {
                    decode_fail += 1;
                    continue;
                }
            };
            t.decode += t0.elapsed();
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
            t.lift += t1.elapsed();
            black_box(module.functions.len());
            drop(module);
        }
        if pass == 0 {
            println!(
                "[bench] instructions lifted per pass: {insns} (decode_fail={decode_fail} lift_fail={lift_fail})"
            );
        }
        results.push(t);
    }
    report("lift", paths.len(), &results);
}

// ============================================================================
// Workload 2: decompile a representative subset (largest per version)
// ============================================================================

/// The subset: the `top_per_version` LARGEST fixtures of each corpus
/// version directory (first relative path component), sorted.
fn decompile_subset(paths: &[PathBuf], top_per_version: usize) -> Vec<PathBuf> {
    let root = corpus_root();
    let mut by_version: std::collections::BTreeMap<String, Vec<(u64, PathBuf)>> =
        std::collections::BTreeMap::new();
    for p in paths {
        let rel = p.strip_prefix(&root).unwrap_or(p);
        let version = rel
            .components()
            .next()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .unwrap_or_default();
        let size = std::fs::metadata(p).map(|m| m.len()).unwrap_or(0);
        by_version
            .entry(version)
            .or_default()
            .push((size, p.clone()));
    }
    let mut out = Vec::new();
    for (_version, mut group) in by_version {
        group.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
        group.truncate(top_per_version);
        out.extend(group.into_iter().map(|(_, p)| p));
    }
    out.sort();
    out
}

#[test]
#[ignore = "local instrumentation (allocator track); release-only benchmark"]
fn bench_decompile_subset() {
    let Some(paths) = corpus_paths() else {
        eprintln!("bench-alloc: no corpus at exports/corpus, skipping (corpus not exported)");
        return;
    };
    let passes = env_usize("ABCD_BENCH_PASSES", 3).max(1);
    let top = env_usize("ABCD_BENCH_TOP_PER_VERSION", 5).max(1);
    let subset = decompile_subset(&paths, top);
    println!(
        "[bench] decompile subset: {} fixtures (top {top} by size per version, of {}), {passes} passes",
        subset.len(),
        paths.len()
    );

    let mut results = Vec::new();
    for pass in 0..passes {
        let mut t = StageTimes {
            decode: Duration::ZERO,
            lift: Duration::ZERO,
            decompile: Duration::ZERO,
        };
        let mut functions = 0u64;
        let mut out_bytes = 0u64;
        for p in &subset {
            let data = std::fs::read(p).expect("read fixture");
            let t0 = Instant::now();
            let file = abcd_file::decode(&data).expect("decode fixture");
            t.decode += t0.elapsed();
            let t1 = Instant::now();
            let module = abcd_lift::lift_file(&file).expect("lift fixture");
            t.lift += t1.elapsed();
            let t2 = Instant::now();
            let out = abcd_decompile::emit::decompile_module(
                &module,
                &abcd_decompile::emit::EmitOptions::default(),
            );
            t.decompile += t2.elapsed();
            black_box(&out.text);
            if pass == 0 {
                functions += out.stats.function_bodies as u64;
                out_bytes += out.text.len() as u64;
            }
        }
        if pass == 0 {
            println!("[bench] decompiled: {functions} function bodies, {out_bytes} output bytes");
        }
        results.push(t);
    }
    report("decompile", subset.len(), &results);
}
