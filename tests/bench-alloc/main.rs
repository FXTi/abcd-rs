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
//! # dabai (Linux/glibc): system vs mimalloc, release, 3 passes
//! KEEP=1 scripts/remote-test.sh test -p abcd-rs --release --test bench-alloc -- --ignored --nocapture
//! KEEP=1 scripts/remote-test.sh test -p abcd-rs --release --test bench-alloc --features alloc-mimalloc -- --ignored --nocapture
//!
//! # dabai (Linux/musl, round-2): same three variants in an Alpine container
//! # (rsync the tree to dabai:/home/zjx/abcdtest/musl-bench first). The
//! # derived image is `docker build` from rust:alpine plus
//! # `apk add build-base ruby clang16-libclang cmake make`.
//! # -crt-static is REQUIRED: musl defaults to fully static linking and the
//! # abcd-file-sys build script then cannot dlopen libclang (bindgen).
//! docker run --rm -v <tree>:/w -w /w abcd-musl-bench sh -c '
//!   export CARGO_HOME=/w/.cargo-home-musl CARGO_TARGET_DIR=/w/target-musl
//!   export RUSTFLAGS="-C target-feature=-crt-static"
//!   cargo test -p abcd-rs --release --test bench-alloc [--features alloc-*] -- --ignored --nocapture
//! '
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
//!
//! Memory reporting is two-axis (round-2 ruling): the process-lifetime
//! PEAK RSS (VmHWM / ru_maxrss) plus a STEADY-STATE sample — a monitor
//! thread reads the live RSS every 50 ms for the duration of the workload
//! and the report prints the median/p95 of that sample sequence
//! (`rss_median_mib` / `rss_p95_mib` in the SUMMARY line). Linux samples
//! VmRSS from /proc/self/status; macOS samples resident_size via mach
//! task_info (hand-written externs, no libc dep); Windows is unprobed
//! (n/a — the GH experiment lane reports its own).

use std::collections::HashMap;
use std::hint::black_box;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

// (jemalloc was dropped after the mimalloc-everywhere ruling — the harness
// keeps a system-vs-mimalloc A/B only.)

#[cfg(feature = "alloc-mimalloc")]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// The allocator label that goes into every report line.
fn allocator_name() -> &'static str {
    #[cfg(feature = "alloc-mimalloc")]
    return "mimalloc";
    #[cfg(not(feature = "alloc-mimalloc"))]
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
// Steady-state RSS (monitor thread sampling the live RSS every 50 ms)
// ============================================================================

/// The monitor's sampling cadence.
const RSS_SAMPLE_INTERVAL: Duration = Duration::from_millis(50);

/// Live RSS in bytes, or None on platforms without a probe here.
/// Linux: VmRSS from /proc/self/status (process-wide value). macOS:
/// resident_size from mach task_info (MACH_TASK_BASIC_INFO), hand-written
/// externs so no libc dev-dep is needed. Windows: unprobed.
fn current_rss_bytes() -> Option<u64> {
    #[cfg(target_os = "linux")]
    {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        for line in status.lines() {
            if let Some(rest) = line.strip_prefix("VmRSS:") {
                let kb: u64 = rest.trim().strip_suffix("kB")?.trim().parse().ok()?;
                return Some(kb * 1024);
            }
        }
        None
    }
    #[cfg(target_os = "macos")]
    {
        // MACH_TASK_BASIC_INFO (flavor 20). Layout: three mach_vm_size_t
        // (u64: virtual_size, resident_size, resident_size_max), two
        // time_value_t (i32 pairs), policy (i32), suspend_count (i32) —
        // 48 bytes = 12 integer_t, hence the count 12 below.
        #[repr(C)]
        struct MachTaskBasicInfo {
            virtual_size: u64,
            resident_size: u64,
            resident_size_max: u64,
            user_time: [i32; 2],
            system_time: [i32; 2],
            policy: i32,
            suspend_count: i32,
        }
        extern "C" {
            fn mach_task_self() -> u32;
            fn task_info(
                task: u32,
                flavor: i32,
                info: *mut MachTaskBasicInfo,
                count: *mut u32,
            ) -> i32;
        }
        const MACH_TASK_BASIC_INFO: i32 = 20;
        let mut info = MachTaskBasicInfo {
            virtual_size: 0,
            resident_size: 0,
            resident_size_max: 0,
            user_time: [0; 2],
            system_time: [0; 2],
            policy: 0,
            suspend_count: 0,
        };
        let mut count: u32 = 12;
        let rc = unsafe {
            task_info(
                mach_task_self(),
                MACH_TASK_BASIC_INFO,
                &mut info,
                &mut count,
            )
        };
        (rc == 0).then_some(info.resident_size)
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        None
    }
}

/// Background RSS sampler: a thread that records `current_rss_bytes()`
/// every `RSS_SAMPLE_INTERVAL` until stopped. `finish()` joins the thread
/// and returns the sample sequence (empty on unprobed platforms).
struct RssMonitor {
    stop: Arc<AtomicBool>,
    handle: Option<std::thread::JoinHandle<Option<Vec<u64>>>>,
}

impl RssMonitor {
    fn start() -> Self {
        let stop = Arc::new(AtomicBool::new(false));
        let stop_thread = stop.clone();
        let handle = std::thread::spawn(move || -> Option<Vec<u64>> {
            // Bail out immediately when the platform has no probe, so the
            // monitor costs nothing there.
            current_rss_bytes()?;
            let mut samples = Vec::new();
            while !stop_thread.load(Ordering::Relaxed) {
                if let Some(bytes) = current_rss_bytes() {
                    samples.push(bytes);
                }
                std::thread::sleep(RSS_SAMPLE_INTERVAL);
            }
            Some(samples)
        });
        Self {
            stop,
            handle: Some(handle),
        }
    }

    /// Stop sampling; the collected RSS samples in bytes (empty when the
    /// platform is unprobed).
    fn finish(mut self) -> Vec<u64> {
        self.stop.store(true, Ordering::Relaxed);
        match self.handle.take() {
            Some(h) => h.join().ok().flatten().unwrap_or_default(),
            None => Vec::new(),
        }
    }
}

/// Nearest-rank percentile of a sample sequence (bytes), `p` in (0, 1].
/// Sorts a copy, so the caller's sequence is untouched.
fn percentile_bytes(samples: &[u64], p: f64) -> Option<u64> {
    if samples.is_empty() {
        return None;
    }
    let mut sorted = samples.to_vec();
    sorted.sort_unstable();
    let idx = ((sorted.len() as f64 * p).ceil() as usize).max(1) - 1;
    Some(sorted[idx.min(sorted.len() - 1)])
}

fn mib(bytes: u64) -> f64 {
    bytes as f64 / (1024.0 * 1024.0)
}

fn fmt_mib(value: Option<u64>) -> String {
    value
        .map(|b| format!("{:.1}", mib(b)))
        .unwrap_or_else(|| "n/a".into())
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
/// summary line the report tables are built from. `steady_rss` is the
/// monitor thread's RSS sample sequence (bytes) gathered over the whole
/// workload; its median/p95 are the steady-state memory figures.
fn report(workload: &str, fixtures: usize, passes: &[StageTimes], steady_rss: &[u64]) {
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
    let rss_mib = peak_rss_bytes().map(mib);
    let rss_median = percentile_bytes(steady_rss, 0.5);
    let rss_p95 = percentile_bytes(steady_rss, 0.95);

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
    if steady_rss.is_empty() {
        println!("[bench] steady RSS: unprobed on this platform (no samples)");
    } else {
        println!(
            "[bench] steady RSS: median {} MiB | p95 {} MiB ({} samples @ {} ms)",
            fmt_mib(rss_median),
            fmt_mib(rss_p95),
            steady_rss.len(),
            RSS_SAMPLE_INTERVAL.as_millis(),
        );
    }
    println!(
        "[bench] SUMMARY workload={workload} allocator={} wall_median_ms={med:.1} wall_min_ms={min:.1} wall_max_ms={max:.1} peak_rss_mib={} rss_median_mib={} rss_p95_mib={}",
        allocator_name(),
        rss_mib
            .map(|m| format!("{m:.1}"))
            .unwrap_or_else(|| "n/a".into()),
        fmt_mib(rss_median),
        fmt_mib(rss_p95),
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

    let monitor = RssMonitor::start();
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
    let steady = monitor.finish();
    report("lift", paths.len(), &results, &steady);
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

    let monitor = RssMonitor::start();
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
    let steady = monitor.finish();
    report("decompile", subset.len(), &results, &steady);
}

/// Corpus-free synthetic workload for hosts that cannot export the corpus
/// (Windows CI runners — the corpus image is linux/amd64 and their docker
/// is Windows-containers only). Mimics our allocation profile: heavy churn
/// of small Strings / Vecs / HashMap entries (interner-like), deterministic
/// xorshift so every variant does identical work. RSS sampling still applies
/// (returns empty on Windows — speed-only there).
#[test]
#[ignore = "local/CI-probe instrument; run explicitly"]
fn bench_synthetic() {
    let passes = env_usize("ABCD_BENCH_PASSES", 3).max(1);
    let scale = env_usize("ABCD_BENCH_SCALE", 1_000_000).max(1);
    let monitor = RssMonitor::start();
    let mut results = Vec::new();
    for _pass in 0..passes {
        let t0 = Instant::now();
        let mut rng: u64 = 0x9E3779B97F4A7C15;
        let mut next = move || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };
        let mut keep: HashMap<String, Vec<u64>> = HashMap::new();
        let mut churn: Vec<String> = Vec::new();
        for i in 0..scale {
            let key = format!("sym_{}", next() % 10_000);
            let vals: Vec<u64> = (0..(next() % 16 + 1)).map(|_| next()).collect();
            keep.insert(key, vals);
            churn.push(format!("payload_{}_{}", i, next()));
            if churn.len() > 512 {
                // Churn: drop the oldest quarter, mimicking phase turnover.
                churn.drain(..128);
                let keys: Vec<String> = keep.keys().take(64).cloned().collect();
                for k in keys {
                    keep.remove(&k);
                }
            }
            black_box(&churn);
            black_box(&keep);
        }
        let wall = t0.elapsed();
        results.push(StageTimes {
            decode: Duration::ZERO,
            lift: Duration::ZERO,
            decompile: wall,
        });
    }
    let steady = monitor.finish();
    report("synthetic", scale, &results, &steady);
}
