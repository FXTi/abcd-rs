//! Pandasm whole-file text emitter, byte-identical to upstream `ark_disasm`.
//!
//! Renders a decoded [`File`] as the complete `.pa` text that the vendored
//! disassembler produces (`disassembler/disassembler.cpp`, default CLI flags:
//! no `--verbose`, no `--quiet`/`--skip-string-literals`). The output is raw
//! bytes, not `String`: upstream prints string contents unescaped, so valid
//! output is not necessarily UTF-8 (the local/strings corpus fixtures are
//! not).
//!
//! Replicated upstream quirks (all verified against
//! `arkcompiler/arkcompiler_runtime_core-master/disassembler/disassembler.cpp`
//! and the corpus reference files):
//!
//! - Records/functions/literal tables live in `std::map`s keyed by STRINGS:
//!   emission order is byte-wise lexicographic on the record name / function
//!   signature / `"{index} 0x{offset}"` literal key (so `"10 0x…"` sorts
//!   before `"2 0x…"`).
//! - Duplicate record names / function signatures: first insertion wins, but
//!   a duplicate-signature method still runs instruction processing (its
//!   string operands land in the STRING section) before being dropped.
//! - Integer immediates print as `0x` + lowercase hex of the value
//!   reinterpreted as UNSIGNED 64-bit (C++ iostream hex of a signed
//!   negative); float immediates print `std::scientific` precision 6.
//! - Literal-array `f64` values and `f64` field/annotation values print with
//!   the iostream default (`%g`, 6 significant digits).
//! - Jump/try/catch labels share one table keyed by instruction index
//!   (first name wins); try/catch labels are allocated BEFORE jump labels,
//!   so `jump_label_N` numbering starts at the try/catch label count.
//! - A try region ending exactly at the end of the code produces a label
//!   bound past the last instruction, printed as a bare `:` line (upstream
//!   `AddLabels` `LabelIns("")` quirk).
//! - 13.x/24.x literal-array indexes are assigned in `std::unordered_set`
//!   iteration order (libstdc++); `sim` reproduces that container's
//!   insert/rehash/erase semantics bit-exactly.
//!
//! The emitter never panics on any [`File`] model: unresolvable entities
//! render as deterministic `!invalid:…` placeholders. (Corpus-driven tests
//! panic on mismatch by design — that is the gate's job, not the emitter's.)
//!
//! The inverse direction — whole-file pandasm text back to a [`File`]
//! model, the `abcd asm` foundation — lives in `parse` ([`parse_file`]).

#![forbid(unsafe_code)]

mod insn_ctor;
mod parse;

pub use parse::{DEFAULT_VERSION, ParseError, parse_file, parse_file_with_version};

use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::{self, Write as _};

use abcd_isa::{Bytecode, BytecodeFlags, EntityKind, Operand};

use crate::model::{
    Annotation, AnnotationValue, Class, EntityRef, FieldValue, File, LiteralArrayIdx, Method,
    MethodBody, MethodIdx, ModuleData, ModuleRecord,
};
use crate::types::{HasAccessFlags, SourceLang, Type};
use crate::{LiteralValue, StringId, Version};

/// Last file version whose header carries the literal-array index table
/// (vendored `LAST_CONTAINS_LITERAL_IN_HEADER_VERSION`, file.h:546).
const LAST_HEADER_LITERAL_VERSION: Version = Version::new(12, 0, 6, 0);

/// Stream the complete pandasm text of `file` to `out`, byte-identical to
/// upstream `ark_disasm <path> out.pa`. `source_name` is the input file's
/// basename (upstream `GetFileNameByPath`), printed in the `# source binary:`
/// header.
pub fn emit_file_to_writer<W: io::Write>(
    file: &File,
    source_name: &str,
    out: &mut W,
) -> io::Result<()> {
    Emitter::new(file).emit_to_writer(source_name, out)
}

/// Emit the complete pandasm text of `file`, byte-identical to upstream
/// `ark_disasm <path> out.pa`. `source_name` is the input file's basename
/// (upstream `GetFileNameByPath`), printed in the `# source binary:` header.
pub fn emit_file(file: &File, source_name: &str) -> Vec<u8> {
    let mut out = Vec::new();
    let _ = emit_file_to_writer(file, source_name, &mut out);
    out
}

// ---------------------------------------------------------------------------
// String bytes (MUTF-8 re-encode, matching upstream's raw print)
// ---------------------------------------------------------------------------

/// The raw bytes upstream prints for a pooled string: exact MUTF-8 wire
/// bytes (borrowed verbatim for lone-surrogate entries, encoded on demand for
/// valid Unicode entries including BMP PUA `U+E000..=U+F8FF`, #30).
fn string_bytes(file: &File, sid: StringId) -> Vec<u8> {
    match file.strings.to_mutf8_bytes(sid) {
        Some(bytes) => bytes.into_owned(),
        None => b"!invalid:string".to_vec(),
    }
}

/// MUTF-8 encode (embedded NUL as C0 80, astral chars as surrogate pairs,
/// all BMP characters including PUA `U+E000..=U+F8FF` preserved verbatim).
pub fn mutf8_bytes(s: &str) -> Vec<u8> {
    crate::string_pool::mutf8_encode(s)
}

// ---------------------------------------------------------------------------
// C++ iostream float formatting
// ---------------------------------------------------------------------------

/// `std::scientific` (precision 6) double print: `%.6e` with a signed,
/// at-least-two-digit exponent (`1.000000e-01`, `4.294967e+09`).
pub fn format_scientific6(v: f64) -> String {
    if v.is_nan() {
        return if v.is_sign_negative() { "-nan" } else { "nan" }.to_owned();
    }
    if v.is_infinite() {
        return if v.is_sign_negative() { "-inf" } else { "inf" }.to_owned();
    }
    let s = format!("{v:.6e}");
    let (mantissa, exp_str) = s.split_once('e').unwrap_or((&s, "0"));
    let exp: i32 = exp_str.parse().unwrap_or(0);
    format!(
        "{mantissa}e{}{:02}",
        if exp < 0 { '-' } else { '+' },
        exp.abs()
    )
}

/// C `printf("%g")` / iostream-default double formatting, precision 6:
/// `%e` when the post-rounding exponent is outside [-4, 6), else `%f`;
/// trailing zeros stripped. The `%e` branch keeps Rust's exponent rendering
/// (`e+09` — C's minimum-two-digit exponent matches after zero-padding).
pub fn format_g6(v: f64) -> String {
    const P: i32 = 6;
    if v.is_nan() {
        return if v.is_sign_negative() { "-nan" } else { "nan" }.to_owned();
    }
    if v.is_infinite() {
        return if v.is_sign_negative() { "-inf" } else { "inf" }.to_owned();
    }
    if v == 0.0 {
        return if v.is_sign_negative() {
            "-0".to_owned()
        } else {
            "0".to_owned()
        };
    }
    // X = the %e-form exponent AFTER rounding to P significant digits —
    // Rust's `{:.5e}` performs exactly that rounding.
    let (e, x) = format_scientific_exp(v, (P - 1) as usize);
    let mut s = if (-4..P).contains(&x) {
        let prec = (P - 1 - x).max(0) as usize;
        format!("{v:.prec$}")
    } else {
        e
    };
    // Strip trailing zeros (and a trailing point) from the mantissa. %g
    // drops the FRACTION's trailing zeros only: when the formatted output
    // has no '.', every digit is an integer digit and must be kept (the
    // prec == 0 case — |v| in [100000, 1000000) — renders "100000", not
    // "1"). The %e mantissa always carries a '.' (prec = P - 1 >= 1), so
    // the guard is needed on the fraction-less branch only.
    match s.find('e') {
        Some(epos) => {
            let mantissa = s[..epos].trim_end_matches('0').trim_end_matches('.');
            s = format!("{}{}", mantissa, &s[epos..]);
        }
        None => {
            if s.contains('.') {
                s = s.trim_end_matches('0').trim_end_matches('.').to_owned();
            }
        }
    }
    s
}

/// Exact lossless `f32` rendering for `array_f32` literal items (Ryū shortest
/// decimal for finite values, `-0.0` for negative zero, `inf`/`-inf`, and
/// `bits:0x...` for NaN bit patterns).
fn write_exact_f32(v: f32, out: &mut Vec<u8>) {
    if v.is_nan() {
        let _ = write!(out, "bits:0x{:08x}", v.to_bits());
    } else if v.is_infinite() {
        out.extend_from_slice(if v.is_sign_negative() {
            b"-inf"
        } else {
            b"inf"
        });
    } else if v == 0.0 && v.is_sign_negative() {
        out.extend_from_slice(b"-0.0");
    } else {
        let _ = write!(out, "{v}");
    }
}

/// Exact lossless `f64` rendering for `array_f64` literal items.
fn write_exact_f64(v: f64, out: &mut Vec<u8>) {
    if v.is_nan() {
        let _ = write!(out, "bits:0x{:016x}", v.to_bits());
    } else if v.is_infinite() {
        out.extend_from_slice(if v.is_sign_negative() {
            b"-inf"
        } else {
            b"inf"
        });
    } else if v == 0.0 && v.is_sign_negative() {
        out.extend_from_slice(b"-0.0");
    } else {
        let _ = write!(out, "{v}");
    }
}

/// `{:.5e}`-style scientific text with the C two-digit signed exponent and
/// its parsed base-10 exponent.
fn format_scientific_exp(v: f64, prec: usize) -> (String, i32) {
    let s = format!("{v:.prec$e}");
    let (mantissa, exp_str) = s.split_once('e').unwrap_or((&s, "0"));
    let exp: i32 = exp_str.parse().unwrap_or(0);
    let text = format!(
        "{mantissa}e{}{:02}",
        if exp < 0 { '-' } else { '+' },
        exp.abs()
    );
    (text, exp)
}

// ---------------------------------------------------------------------------
// Name rendering (upstream mangling/type helpers)
// ---------------------------------------------------------------------------

/// `pandasm::Type::FromDescriptor` + component + `GetPandasmName` for a class
/// descriptor: strip array brackets and the `L…;` wrapper, map primitive
/// letters, then replace `/` with `.`.
fn record_pandasm_name(descriptor: &[u8]) -> Vec<u8> {
    let mut d = descriptor;
    let mut rank = 0usize;
    while d.first() == Some(&b'[') {
        rank += 1;
        d = &d[1..];
    }
    let component: Vec<u8> = if d.first() == Some(&b'L') {
        // Ref type: drop the leading 'L' and the trailing byte (';').
        let inner = &d[1..];
        if inner.len() > 1 {
            inner[..inner.len() - 1].to_vec()
        } else {
            inner.to_vec()
        }
    } else {
        match d {
            b"Z" => b"u1".to_vec(),
            b"B" => b"i8".to_vec(),
            b"H" => b"u8".to_vec(),
            b"S" => b"i16".to_vec(),
            b"C" => b"u16".to_vec(),
            b"I" => b"i32".to_vec(),
            b"U" => b"u32".to_vec(),
            b"F" => b"f32".to_vec(),
            b"D" => b"f64".to_vec(),
            b"J" => b"i64".to_vec(),
            b"Q" => b"u64".to_vec(),
            b"V" => b"void".to_vec(),
            b"A" => b"any".to_vec(),
            other => other.to_vec(),
        }
    };
    let mut name = component;
    for _ in 0..rank {
        name.extend_from_slice(b"[]");
    }
    for b in &mut name {
        if *b == b'/' {
            *b = b'.';
        }
    }
    name
}

/// Upstream `IsSystemType`: array descriptors and `_GLOBAL`.
fn is_system_type(record_name: &[u8]) -> bool {
    record_name.contains(&b'[') || record_name == b"_GLOBAL"
}

fn language_str(lang: SourceLang) -> &'static str {
    match lang {
        SourceLang::EcmaScript => "ECMAScript",
        SourceLang::JavaScript => "JavaScript",
        SourceLang::TypeScript => "TypeScript",
        SourceLang::ArkTs => "ArkTS",
        SourceLang::PandaAssembly => "PandaAssembly",
    }
}

/// `GetFileNameByPath`: basename at the last '/'.
fn file_name_by_path(name: &[u8]) -> &[u8] {
    match name.iter().rposition(|&b| b == b'/') {
        Some(pos) => &name[pos + 1..],
        None => name,
    }
}

// ---------------------------------------------------------------------------
// libstdc++ unordered_set<uint32_t> simulation (13.x/24.x literal indexes)
// ---------------------------------------------------------------------------

mod sim {
    //! libstdc++ `std::unordered_set<uint32_t>` (identity hash, prime rehash
    //! policy, max_load_factor 1.0) iteration order, reproduced bit-exactly.
    //! Upstream's 13.x/24.x literal-array index assignment iterates this
    //! container (`CollectUtil::CollectLiteralArray` → `GetLiteralArrays`).
    //!
    //! Container model (libstdc++ `_Hashtable`): one global singly-linked
    //! node list (`head` = `_M_before_begin._M_nxt`); `buckets[b]` holds the
    //! BEFORE-node of bucket b's first node (`BeforeBegin` when that node is
    //! the list head, `Null` when the bucket is empty). Same-bucket nodes are
    //! contiguous in the list.

    /// Exact 32-bit prefix of GCC libstdc++ `__prime_list`
    /// (`libstdc++-v3/src/shared/hashtable-aux.cc`), matching
    /// `std::__detail::_Prime_rehash_policy::_M_next_bkt` across the full
    /// `u32` offset space.
    pub(super) const PRIMES: &[u32] = &[
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97, 103, 109, 113, 127, 137, 139, 149, 157, 167, 179, 193, 199, 211, 227, 241, 257, 277,
        293, 313, 337, 359, 383, 409, 439, 467, 503, 541, 577, 619, 661, 709, 761, 823, 887, 953,
        1031, 1109, 1193, 1289, 1381, 1493, 1613, 1741, 1879, 2029, 2179, 2357, 2549, 2753, 2971,
        3209, 3469, 3739, 4027, 4349, 4703, 5087, 5503, 5953, 6427, 6949, 7517, 8123, 8783, 9497,
        10273, 11113, 12011, 12983, 14033, 15173, 16411, 17749, 19183, 20753, 22447, 24281, 26267,
        28411, 30727, 33223, 35933, 38873, 42043, 45481, 49201, 53201, 57557, 62233, 67307, 72817,
        78779, 85229, 92203, 99733, 107897, 116731, 126271, 136607, 147793, 159871, 172933, 187091,
        202409, 218971, 236897, 256279, 277261, 299951, 324503, 351061, 379787, 410857, 444487,
        480881, 520241, 562841, 608903, 658753, 712697, 771049, 834181, 902483, 976369, 1056323,
        1142821, 1236397, 1337629, 1447153, 1565659, 1693859, 1832561, 1982627, 2144977, 2320627,
        2510653, 2716249, 2938679, 3179303, 3439651, 3721303, 4026031, 4355707, 4712381, 5098259,
        5515729, 5967347, 6456007, 6984629, 7556579, 8175383, 8844859, 9569143, 10352717, 11200489,
        12117689, 13109983, 14183539, 15345007, 16601593, 17961079, 19431899, 21023161, 22744717,
        24607243, 26622317, 28802401, 31160981, 33712729, 36473443, 39460231, 42691603, 46187573,
        49969847, 54061849, 58488943, 63278561, 68460391, 74066549, 80131819, 86693767, 93793069,
        101473717, 109783337, 118773397, 128499677, 139022417, 150406843, 162723577, 176048909,
        190465427, 206062531, 222936881, 241193053, 260944219, 282312799, 305431229, 330442829,
        357502601, 386778277, 418451333, 452718089, 489790921, 529899637, 573292817, 620239453,
        671030513, 725980837, 785430967, 849749479, 919334987, 994618837, 1076067617, 1164186217,
        1259520799, 1362662261, 1474249943, 1594975441, 1725587117, 1866894511, 2019773507,
        2185171673, 2364114217, 2557710269, 2767159799, 2993761039, 3238918481, 3504151727,
        3791104843, 4101556399, 4294967291,
    ];

    fn next_bkt(n: usize) -> usize {
        let idx = PRIMES.partition_point(|&p| (p as usize) < n);
        PRIMES.get(idx).map_or(n, |&p| p as usize)
    }

    /// Bucket-slot value: the before-node of the bucket's first node.
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Slot {
        Null,
        BeforeBegin,
        Node(usize),
    }

    pub struct U32Set {
        /// Node arena: `(value, next)`; erased nodes stay (links die).
        nodes: Vec<(u32, Option<usize>)>,
        head: Option<usize>,
        buckets: Vec<Slot>,
        size: usize,
        next_resize: usize,
    }

    impl Default for U32Set {
        fn default() -> Self {
            Self::new()
        }
    }

    impl U32Set {
        pub fn new() -> Self {
            U32Set {
                nodes: Vec::new(),
                head: None,
                buckets: vec![Slot::Null],
                size: 0,
                next_resize: 0,
            }
        }

        fn bucket_of(&self, v: u32) -> usize {
            v as usize % self.buckets.len()
        }

        /// The node following a before-node slot.
        fn slot_next(&self, slot: Slot) -> Option<usize> {
            match slot {
                Slot::Null => None,
                Slot::BeforeBegin => self.head,
                Slot::Node(n) => self.nodes[n].1,
            }
        }

        fn link_after(&mut self, slot: Slot, node: Option<usize>) {
            match slot {
                Slot::BeforeBegin => self.head = node,
                Slot::Node(n) => self.nodes[n].1 = node,
                Slot::Null => unreachable!("link after null slot"),
            }
        }

        /// `_M_insert_bucket_begin` (new node, bucket index `bkt`).
        fn insert_bucket_begin(&mut self, bkt: usize, node: usize) {
            match self.buckets[bkt] {
                Slot::Null => {
                    // Empty bucket: splice at the front of the list; the
                    // former head's bucket re-points its before-node.
                    let old_head = self.head;
                    self.nodes[node].1 = old_head;
                    self.head = Some(node);
                    if let Some(h) = old_head {
                        let hb = self.bucket_of(self.nodes[h].0);
                        self.buckets[hb] = Slot::Node(node);
                    }
                    self.buckets[bkt] = Slot::BeforeBegin;
                }
                before => {
                    let next = self.slot_next(before);
                    self.nodes[node].1 = next;
                    self.link_after(before, Some(node));
                }
            }
        }

        /// `_M_rehash_aux` (unique keys): walk the old list; each node goes
        /// to the front of its new bucket, new buckets to the list front.
        fn rehash(&mut self, new_count: usize) {
            let mut new_buckets = vec![Slot::Null; new_count];
            let mut p = self.head;
            self.head = None;
            let mut bbegin_bkt = 0usize;
            while let Some(node) = p {
                let next = self.nodes[node].1;
                let bkt = self.nodes[node].0 as usize % new_count;
                if new_buckets[bkt] == Slot::Null {
                    self.nodes[node].1 = self.head;
                    self.head = Some(node);
                    new_buckets[bkt] = Slot::BeforeBegin;
                    if let Some(old_head) = self.nodes[node].1 {
                        let _ = old_head;
                        new_buckets[bbegin_bkt] = Slot::Node(node);
                    }
                    bbegin_bkt = bkt;
                } else {
                    let before = new_buckets[bkt];
                    let after = self.slot_next(before);
                    self.nodes[node].1 = after;
                    self.link_after(before, Some(node));
                }
                p = next;
            }
            self.buckets = new_buckets;
        }

        /// `_Prime_rehash_policy::_M_need_rehash` (load factor 1.0, growth
        /// factor 2, initial minimum 11).
        fn maybe_rehash(&mut self, n_ins: usize) {
            if self.size + n_ins <= self.next_resize {
                return;
            }
            let min_bkts = (self.size + n_ins).max(if self.next_resize == 0 { 11 } else { 0 });
            if min_bkts >= self.buckets.len() {
                let new_count = next_bkt((min_bkts + 1).max(self.buckets.len() * 2));
                self.next_resize = new_count;
                self.rehash(new_count);
            } else {
                self.next_resize = self.buckets.len();
            }
        }

        pub fn insert(&mut self, v: u32) {
            if self.contains(v) {
                return;
            }
            self.maybe_rehash(1);
            let bkt = self.bucket_of(v);
            let node = self.nodes.len();
            self.nodes.push((v, None));
            self.insert_bucket_begin(bkt, node);
            self.size += 1;
        }

        pub fn contains(&self, v: u32) -> bool {
            let bkt = self.bucket_of(v);
            let before = self.buckets[bkt];
            if before == Slot::Null {
                return false;
            }
            let mut n = self.slot_next(before);
            while let Some(node) = n {
                if self.nodes[node].0 == v {
                    return true;
                }
                let next = self.nodes[node].1;
                match next {
                    Some(m) if self.bucket_of(self.nodes[m].0) == bkt => n = Some(m),
                    _ => break,
                }
            }
            false
        }

        /// `_M_erase` by value (used by `ProcessNestLiteralArray`).
        pub fn erase(&mut self, v: u32) {
            let bkt = self.bucket_of(v);
            let before = self.buckets[bkt];
            if before == Slot::Null {
                return;
            }
            let mut prev = before;
            let mut n = self.slot_next(before);
            while let Some(node) = n {
                if self.nodes[node].0 == v {
                    let next = self.nodes[node].1;
                    self.link_after(prev, next);
                    if let Some(m) = next {
                        let mb = self.bucket_of(self.nodes[m].0);
                        if mb != bkt {
                            // The next node opens another bucket; its
                            // before-node becomes prev.
                            self.buckets[mb] = prev;
                        }
                    }
                    let first_of_bucket = self.buckets[bkt] == prev;
                    let bucket_empty = match next {
                        None => true,
                        Some(m) => self.bucket_of(self.nodes[m].0) != bkt,
                    };
                    if first_of_bucket && bucket_empty {
                        self.buckets[bkt] = Slot::Null;
                    }
                    self.size -= 1;
                    return;
                }
                prev = Slot::Node(node);
                let next = self.nodes[node].1;
                match next {
                    Some(m) if self.bucket_of(self.nodes[m].0) == bkt => n = Some(m),
                    _ => break,
                }
            }
        }

        /// Iteration order: the global singly-linked list from the head.
        pub fn iter(&self) -> Vec<u32> {
            let mut out = Vec::with_capacity(self.size);
            let mut n = self.head;
            while let Some(node) = n {
                out.push(self.nodes[node].0);
                n = self.nodes[node].1;
            }
            out
        }

        pub fn first(&self) -> Option<u32> {
            self.head.map(|h| self.nodes[h].0)
        }

        #[cfg(test)]
        pub(super) fn bucket_count(&self) -> usize {
            self.buckets.len()
        }
    }
}

// ---------------------------------------------------------------------------
// Internal program model (what upstream's pandasm::Program carries)
// ---------------------------------------------------------------------------

/// One catch block line (`.catchall …` / `.catch <record>, …`).
struct CatchLine {
    /// Empty = `.catchall`.
    exception_record: Vec<u8>,
    try_begin: String,
    try_end: String,
    catch_begin: String,
    /// Empty = omitted (zero-length handler).
    catch_end: String,
}

struct FnHeader {
    /// Full (class-prefixed, ctor-renamed) name, raw bytes.
    name: Vec<u8>,
    params: Vec<Vec<u8>>,
    /// Return type name; empty for code-less methods (upstream default
    /// `Type()` prints as the empty string).
    return_type: &'static str,
    language: SourceLang,
    is_static: bool,
    is_external: bool,
    is_ctor: bool,
    is_cctor: bool,
}

impl FnHeader {
    /// `GetFunctionSignatureFromName`: `name:(type,type,…)`.
    fn signature(&self) -> Vec<u8> {
        let mut sig = self.name.clone();
        sig.extend_from_slice(b":(");
        for (i, p) in self.params.iter().enumerate() {
            if i > 0 {
                sig.push(b',');
            }
            sig.extend_from_slice(p);
        }
        sig.extend_from_slice(b")");
        sig
    }
}

struct PaRecord {
    name: Vec<u8>,
    language: SourceLang,
    is_external: bool,
    /// Fully rendered field lines (without the leading tab).
    fields: Vec<Vec<u8>>,
}

type LiteralTables<'f> = (BTreeMap<Vec<u8>, u32>, BTreeMap<Vec<u8>, &'f ModuleData>);

struct Emitter<'f> {
    file: &'f File,
    /// STRING section: offset → raw bytes (upstream `string_offset_to_name_`,
    /// a map sorted by offset).
    strings: BTreeMap<u32, Vec<u8>>,
    /// Deterministic synthetic offsets assigned to offsetless `EntityRef::String`s.
    synth_string_offsets: HashMap<StringId, u32>,
    next_synth_string_off: u32,
    /// `_ESModuleRecord`-style u32 field values (module blob offsets).
    module_literals: HashSet<u32>,
    /// Dense `(owner_desc, class, method)` table indexed by [`MethodIdx`].
    methods: Vec<(StringId, &'f Class, &'f Method)>,
    /// Dense `LiteralArrayIdx → effective u32 offset` (`source_offset` when
    /// present, otherwise a deterministic synthetic offset).
    literal_offsets: Vec<u32>,
    /// Pre-indexed `offset → LiteralArrayIdx` (first match in table order).
    literal_by_offset: HashMap<u32, usize>,
    /// Pre-indexed `md.source_offset → &ModuleData` (first match in
    /// class/field iteration order).
    module_data_by_offset: HashMap<u32, &'f ModuleData>,
}

impl<'f> Emitter<'f> {
    fn new(file: &'f File) -> Self {
        let methods = file.method_table();
        let mut module_data_by_offset = HashMap::new();
        for class in file.classes.values() {
            for field in &class.fields {
                if let Some(FieldValue::ModuleData(md)) = &field.initial_value {
                    module_data_by_offset.entry(md.source_offset).or_insert(md);
                }
            }
        }
        let mut literal_offsets = Vec::with_capacity(file.literal_arrays.len());
        let mut literal_by_offset = HashMap::with_capacity(file.literal_arrays.len());
        for (idx, la) in file.literal_arrays.iter().enumerate() {
            let off = la.source_offset.unwrap_or(0x2000_0000 + (idx as u32) * 4);
            literal_offsets.push(off);
            literal_by_offset.entry(off).or_insert(idx);
        }
        Emitter {
            file,
            strings: BTreeMap::new(),
            synth_string_offsets: HashMap::new(),
            next_synth_string_off: 0x1000_0000,
            module_literals: HashSet::new(),
            methods,
            literal_offsets,
            literal_by_offset,
            module_data_by_offset,
        }
    }

    fn str_bytes(&self, sid: StringId) -> Vec<u8> {
        string_bytes(self.file, sid)
    }

    /// Pandasm record name for a class descriptor StringId.
    fn class_name(&self, desc: StringId) -> Vec<u8> {
        record_pandasm_name(&self.str_bytes(desc))
    }

    /// Upstream `GetFullMethodName`: class prefix unless the class is a
    /// system type.
    fn full_method_name(&self, owner_desc: StringId, name_sid: StringId) -> Vec<u8> {
        let name = self.str_bytes(name_sid);
        let class = self.class_name(owner_desc);
        if is_system_type(&class) {
            name
        } else {
            let mut full = class;
            full.push(b'.');
            full.extend_from_slice(&name);
            full
        }
    }

    /// Signature text for a method reference (`GetMethodSignature`): full
    /// name + `:(` + param types + `)`.
    fn method_signature_by_idx(&self, idx: MethodIdx) -> Vec<u8> {
        if let Some(&(desc, class, m)) = self.methods.get(idx.index()) {
            return self.build_fn_header(desc, class, m).signature();
        }
        format!("!invalid:method:{:#x}:()", idx.0).into_bytes()
    }

    // -- function construction (upstream GetMethod/AddMethodToTables) -------

    /// Build header metadata and signature components for one method without
    /// rendering its body.
    fn build_fn_header(&self, owner_desc: StringId, class: &Class, method: &Method) -> FnHeader {
        let raw_name = self.str_bytes(method.name);
        let is_static = method.is_static();
        let is_ctor = raw_name == b".ctor";
        let is_cctor = raw_name == b".cctor";
        let mut name = self.full_method_name(owner_desc, method.name);
        let mut params = Vec::new();
        // GetMetaData: non-static methods gain a leading `this` parameter.
        if !is_static {
            params.push(self.class_name(class.descriptor));
        }
        if is_ctor {
            replace_once(&mut name, b".ctor", b"_ctor_");
        } else if is_cctor {
            replace_once(&mut name, b".cctor", b"_cctor_");
        }
        let return_type = if let Some(body) = &method.body {
            for _ in 0..body.num_args {
                params.push(b"any".to_vec());
            }
            "any"
        } else {
            ""
        };
        FnHeader {
            name,
            params,
            return_type,
            language: if method.is_external {
                SourceLang::EcmaScript // upstream DEFUALT_SOURCE_LANG
            } else {
                method.source_lang
            },
            is_static,
            is_external: method.is_external,
            is_ctor,
            is_cctor,
        }
    }

    fn register_string_ref(&mut self, sid: StringId, source_offset: Option<u32>) -> u32 {
        let off = match source_offset {
            Some(off) => off,
            None => *self.synth_string_offsets.entry(sid).or_insert_with(|| {
                let assigned = self.next_synth_string_off;
                self.next_synth_string_off = self.next_synth_string_off.wrapping_add(4);
                assigned
            }),
        };
        if !self.strings.contains_key(&off) {
            let bytes = self.str_bytes(sid);
            self.strings.insert(off, bytes);
        }
        off
    }

    fn register_body_strings(&mut self, body: &MethodBody) {
        let bcs = body.bytecodes();
        for bc in bcs.iter() {
            let (ops, len) = bc.entity_operands_inline();
            for &(kind, id) in &ops[..len] {
                if kind == EntityKind::StringId
                    && let Some(&EntityRef::String {
                        id: sid,
                        source_offset,
                    }) = body.entities.get(&(kind, id.0))
                {
                    self.register_string_ref(sid, source_offset);
                }
            }
        }
    }

    /// Method annotations (upstream `GetMethodAnnotations` — the
    /// compile-time `ANNOTATION` tag list), rendered as header blocks.
    fn collect_annotations(&self, method: &Method) -> Vec<(Vec<u8>, Vec<Vec<u8>>)> {
        let mut annotations = Vec::new();
        for ann in &method.annotations.compile_time {
            self.render_annotation(&mut annotations, ann);
        }
        annotations
    }

    fn render_annotation(&self, annotations: &mut Vec<(Vec<u8>, Vec<Vec<u8>>)>, ann: &Annotation) {
        let mut name = self.str_bytes(ann.class_descriptor);
        name.pop(); // strip the trailing ';' of the descriptor
        if name.is_empty() {
            return;
        }
        let idx = match annotations.iter().position(|(n, _)| *n == name) {
            Some(i) => i,
            None => {
                annotations.push((name, Vec::new()));
                annotations.len() - 1
            }
        };
        for elem in &ann.elements {
            let elem_name = self.str_bytes(elem.name);
            if elem_name.is_empty() {
                continue;
            }
            let line = match &elem.value {
                AnnotationValue::U32(v) => {
                    let mut l = b"\tu32 ".to_vec();
                    l.extend_from_slice(&elem_name);
                    let _ = write!(l, " {{ 0x{v:x} }}");
                    l
                }
                AnnotationValue::F64(v) => {
                    let mut l = b"\tf64 ".to_vec();
                    l.extend_from_slice(&elem_name);
                    let _ = write!(l, " {{ {} }}", format_g6(*v));
                    l
                }
                AnnotationValue::Bool(v) => {
                    let mut l = b"\tu1 ".to_vec();
                    l.extend_from_slice(&elem_name);
                    let _ = write!(l, " {{ {} }}", *v as u8);
                    l
                }
                AnnotationValue::String(sid) => {
                    let mut l = b"\tpanda.String ".to_vec();
                    l.extend_from_slice(&elem_name);
                    l.extend_from_slice(b" { \"");
                    l.extend_from_slice(&self.str_bytes(*sid));
                    l.extend_from_slice(b"\" }");
                    l
                }
                // Upstream handles only U1/U32/F64/STRING/LITERALARRAY
                // method-annotation element tags (anything else hits its
                // UNREACHABLE); skip the rest deterministically.
                _ => continue,
            };
            annotations[idx].1.push(line);
        }
    }

    // -- instructions (upstream GetInstructions) ----------------------------

    fn build_body_into(
        &mut self,
        body: &MethodBody,
        insn_buf: &mut Vec<u8>,
        insn_ranges: &mut Vec<(usize, usize)>,
    ) -> (BTreeMap<u32, String>, bool, Vec<CatchLine>) {
        let bcs = body.bytecodes();
        let count = bcs.len() as u32;
        // Label table: instruction index → name. Try/catch labels allocate
        // first (upstream GetExceptions runs before the instruction walk).
        let mut labels: BTreeMap<u32, String> = BTreeMap::new();

        let mut catches: Vec<CatchLine> = Vec::new();
        'tries: for (try_idx, tb) in body.try_blocks.iter().enumerate() {
            let begin = tb.start;
            let Some(end) = tb.start.checked_add(tb.len) else {
                break 'tries;
            };
            // Upstream range checks; failure aborts try-block enumeration.
            if begin >= count || end > count {
                break 'tries;
            }
            let try_begin = alloc_label(&mut labels, begin, format!("try_begin_label_{try_idx}"));
            let try_end = alloc_label(&mut labels, end, format!("try_end_label_{try_idx}"));
            for (catch_idx, cb) in tb.catches.iter().enumerate() {
                let exception_record = match cb.type_class {
                    None => Vec::new(),
                    Some(sid) => match self.file.strings.to_mutf8_bytes(sid) {
                        Some(bytes) => record_pandasm_name(&bytes),
                        None => format!("!invalid:catch:{}", sid.index()).into_bytes(),
                    },
                };
                let hbegin = cb.handler;
                let Some(hend) = cb.handler.checked_add(cb.len) else {
                    break 'tries;
                };
                if hbegin >= count || hend > count {
                    break 'tries;
                }
                let catch_begin = alloc_label(
                    &mut labels,
                    hbegin,
                    format!("handler_begin_label_{try_idx}_{catch_idx}"),
                );
                let catch_end = if cb.len != 0 {
                    alloc_label(
                        &mut labels,
                        hend,
                        format!("handler_end_label_{try_idx}_{catch_idx}"),
                    )
                } else {
                    String::new()
                };
                catches.push(CatchLine {
                    exception_record,
                    try_begin: try_begin.clone(),
                    try_end: try_end.clone(),
                    catch_begin,
                    catch_end,
                });
            }
        }

        // Instruction walk: jump labels allocate as `jump_label_{table len}`.
        // Labels attach AFTER the full walk (upstream AddLabels): a label
        // allocated by a later jump still prints on its target line.
        insn_buf.clear();
        insn_ranges.clear();
        insn_ranges.reserve(bcs.len());
        for bc in bcs.iter() {
            let start = insn_buf.len();
            self.render_instruction_into(bc, body, &mut labels, insn_buf);
            insn_ranges.push((start, insn_buf.len()));
        }
        let trailing_empty_label = labels.contains_key(&count);
        (labels, trailing_empty_label, catches)
    }

    fn render_instruction_into(
        &mut self,
        bc: &Bytecode,
        body: &MethodBody,
        labels: &mut BTreeMap<u32, String>,
        out: &mut Vec<u8>,
    ) {
        let (operands, len) = bc.operands_inline();
        // Upstream call-arg trimming (CALL-flagged pandasm opcodes) is
        // not needed here: BytecodeFlags::CALL exists in the ISA schema
        // but is never assigned to any instruction (regression test
        // abcd-isa/tests/bytecode.rs has_flag_call_not_assigned), so the
        // trim_call_args/method_proto machinery was deleted as dead.
        let float = bc.has_flag(BytecodeFlags::FLOAT);
        out.extend_from_slice(bc.mnemonic().as_bytes());
        for (i, op) in operands[..len].iter().enumerate() {
            out.extend_from_slice(if i == 0 { b" " } else { b", " });
            self.render_operand(bc, float, op, body, labels, out);
        }
    }

    fn render_operand(
        &mut self,
        bc: &Bytecode,
        float: bool,
        op: &Operand,
        body: &MethodBody,
        labels: &mut BTreeMap<u32, String>,
        out: &mut Vec<u8>,
    ) {
        let _ = bc;
        match *op {
            Operand::Reg(r) => {
                if r as u32 >= body.num_vregs {
                    let _ = write!(out, "a{}", r as u32 - body.num_vregs);
                } else {
                    let _ = write!(out, "v{r}");
                }
            }
            Operand::Imm(i) => {
                if float {
                    // fldai: the immediate carries the f64 value bits.
                    out.extend_from_slice(format_scientific6(f64::from_bits(i as u64)).as_bytes());
                } else {
                    let _ = write!(out, "0x{:x}", i as u64);
                }
            }
            Operand::Label(l) => {
                let count = body.insn_count() as u32;
                if l < count {
                    let next_idx = labels.len();
                    let name = labels
                        .entry(l)
                        .or_insert_with(|| format!("jump_label_{next_idx}"));
                    out.extend_from_slice(name.as_bytes());
                } else {
                    // Upstream: an out-of-bounds jump keeps the raw decimal
                    // offset text (the error path never replaces the id).
                    let _ = write!(out, "{l}");
                }
            }
            Operand::Entity(kind, id) => self.render_entity(kind, id, body, out),
        }
    }

    fn render_entity(&mut self, kind: EntityKind, id: u32, body: &MethodBody, out: &mut Vec<u8>) {
        let eref = body.entities.get(&(kind, id)).copied();
        match (kind, eref) {
            (
                EntityKind::StringId,
                Some(EntityRef::String {
                    id: sid,
                    source_offset,
                }),
            ) => {
                let off = self.register_string_ref(sid, source_offset);
                out.push(b'"');
                if let Some(bytes) = self.strings.get(&off) {
                    out.extend_from_slice(bytes);
                }
                out.push(b'"');
            }
            (EntityKind::MethodId, Some(EntityRef::Method(midx))) => {
                let sig = self.method_signature_by_idx(midx);
                out.extend_from_slice(&sig);
            }
            (EntityKind::MethodId, Some(EntityRef::ExternalMethod { name, .. })) => {
                out.extend_from_slice(&self.str_bytes(name));
                out.extend_from_slice(b":()");
            }
            (EntityKind::LiteralarrayId, Some(EntityRef::LiteralArray(la_idx))) => {
                match self.file.literal_arrays.get(la_idx.index()) {
                    Some(array) => self.serialize_literal_array_into(&array.values, out),
                    None => out.extend_from_slice(b"!invalid:literalarray"),
                }
            }
            _ => {
                let _ = write!(out, "!invalid:entity:{kind:?}:{id}");
            }
        }
    }

    /// `SerializeLiteralArray`: `{ <count> [ <tag:value, … ]}`; empty arrays
    /// render as the empty string (the section line keeps its trailing
    /// space). Upstream drops TAGVALUE-tagged items (`FillLiteralData`'s
    /// early return); our `Integer8` is that tag.
    fn serialize_literal_array_into(&self, values: &[LiteralValue], out: &mut Vec<u8>) {
        // Integer8 is filtered out here (the upstream TAGVALUE drop), so
        // serialize_literal_item has no Integer8 arm — one would be dead.
        let count = values
            .iter()
            .filter(|v| !matches!(v, LiteralValue::Integer8(_)))
            .count();
        if count == 0 {
            return;
        }
        let _ = write!(out, "{{ {count} [ ");
        for v in values
            .iter()
            .filter(|v| !matches!(v, LiteralValue::Integer8(_)))
        {
            self.serialize_literal_item(v, out);
            out.extend_from_slice(b", ");
        }
        out.extend_from_slice(b"]}");
    }

    fn serialize_literal_item(&self, v: &LiteralValue, out: &mut Vec<u8>) {
        match v {
            LiteralValue::Bool(b) => {
                let _ = write!(out, "u1:{}", *b as u8);
            }
            LiteralValue::Integer(v) => {
                let _ = write!(out, "i32:{}", *v as i32);
            }
            LiteralValue::Float(v) => {
                let _ = write!(out, "f32:{}", format_g6(f64::from(*v)));
            }
            LiteralValue::Double(v) => {
                let _ = write!(out, "f64:{}", format_g6(*v));
            }
            LiteralValue::String(sid) => {
                out.extend_from_slice(b"string:\"");
                out.extend_from_slice(&self.str_bytes(*sid));
                out.push(b'"');
            }
            LiteralValue::EtsImplements(sid) => {
                out.extend_from_slice(b"ets_implements:\"");
                out.extend_from_slice(&self.str_bytes(*sid));
                out.push(b'"');
            }
            LiteralValue::Method(idx) => self.method_name_item(b"method", *idx, out),
            LiteralValue::GeneratorMethod(idx) => {
                self.method_name_item(b"generator_method", *idx, out)
            }
            LiteralValue::Getter(idx) => self.method_name_item(b"getter", *idx, out),
            LiteralValue::Setter(idx) => self.method_name_item(b"setter", *idx, out),
            LiteralValue::AsyncGeneratorMethod(idx) => {
                // No upstream rendering (UNREACHABLE); deterministic fallback.
                self.method_name_item(b"async_generator_method", *idx, out)
            }
            LiteralValue::Accessor(v) => {
                let _ = write!(out, "accessor:{}", i16::from(*v as i8));
            }
            LiteralValue::MethodAffiliate(v) => {
                let _ = write!(out, "method_affiliate:{v}");
            }
            LiteralValue::NullValue(v) => {
                let _ = write!(out, "null_value:{}", i16::from(*v as i8));
            }
            LiteralValue::LiteralArray(idx) => {
                // Decode rewrites the payload to a table index when the
                // target decoded; upstream prints the raw source offset.
                let offset = self.literal_offset_of(*idx);
                let _ = write!(out, "lit_offset:0x{offset:x}");
            }
            LiteralValue::LiteralBufferIndex(idx) => {
                let _ = write!(out, "lit_index:{}", idx.0 as i32);
            }
            LiteralValue::BuiltinTypeIndex(v) => {
                let _ = write!(out, "builtin_type:{}", i16::from(*v));
            }
            LiteralValue::ArrayU1(elems) => {
                out.extend_from_slice(b"array_u1:[");
                for (i, &x) in elems.iter().enumerate() {
                    if i > 0 {
                        out.extend_from_slice(b", ");
                    }
                    let _ = write!(out, "{}", u8::from(x));
                }
                out.push(b']');
            }
            LiteralValue::ArrayU8(elems) => {
                out.extend_from_slice(b"array_u8:[");
                for (i, &x) in elems.iter().enumerate() {
                    if i > 0 {
                        out.extend_from_slice(b", ");
                    }
                    let _ = write!(out, "{x}");
                }
                out.push(b']');
            }
            LiteralValue::ArrayI8(elems) => {
                out.extend_from_slice(b"array_i8:[");
                for (i, &x) in elems.iter().enumerate() {
                    if i > 0 {
                        out.extend_from_slice(b", ");
                    }
                    let _ = write!(out, "{x}");
                }
                out.push(b']');
            }
            LiteralValue::ArrayU16(elems) => {
                out.extend_from_slice(b"array_u16:[");
                for (i, &x) in elems.iter().enumerate() {
                    if i > 0 {
                        out.extend_from_slice(b", ");
                    }
                    let _ = write!(out, "{x}");
                }
                out.push(b']');
            }
            LiteralValue::ArrayI16(elems) => {
                out.extend_from_slice(b"array_i16:[");
                for (i, &x) in elems.iter().enumerate() {
                    if i > 0 {
                        out.extend_from_slice(b", ");
                    }
                    let _ = write!(out, "{x}");
                }
                out.push(b']');
            }
            LiteralValue::ArrayU32(elems) => {
                out.extend_from_slice(b"array_u32:[");
                for (i, &x) in elems.iter().enumerate() {
                    if i > 0 {
                        out.extend_from_slice(b", ");
                    }
                    let _ = write!(out, "{x}");
                }
                out.push(b']');
            }
            LiteralValue::ArrayI32(elems) => {
                out.extend_from_slice(b"array_i32:[");
                for (i, &x) in elems.iter().enumerate() {
                    if i > 0 {
                        out.extend_from_slice(b", ");
                    }
                    let _ = write!(out, "{x}");
                }
                out.push(b']');
            }
            LiteralValue::ArrayU64(elems) => {
                out.extend_from_slice(b"array_u64:[");
                for (i, &x) in elems.iter().enumerate() {
                    if i > 0 {
                        out.extend_from_slice(b", ");
                    }
                    let _ = write!(out, "{x}");
                }
                out.push(b']');
            }
            LiteralValue::ArrayI64(elems) => {
                out.extend_from_slice(b"array_i64:[");
                for (i, &x) in elems.iter().enumerate() {
                    if i > 0 {
                        out.extend_from_slice(b", ");
                    }
                    let _ = write!(out, "{x}");
                }
                out.push(b']');
            }
            LiteralValue::ArrayF32(elems) => {
                out.extend_from_slice(b"array_f32:[");
                for (i, &x) in elems.iter().enumerate() {
                    if i > 0 {
                        out.extend_from_slice(b", ");
                    }
                    write_exact_f32(x, out);
                }
                out.push(b']');
            }
            LiteralValue::ArrayF64(elems) => {
                out.extend_from_slice(b"array_f64:[");
                for (i, &x) in elems.iter().enumerate() {
                    if i > 0 {
                        out.extend_from_slice(b", ");
                    }
                    write_exact_f64(x, out);
                }
                out.push(b']');
            }
            LiteralValue::ArrayString(elems) => {
                out.extend_from_slice(b"array_string:[");
                for (i, &sid) in elems.iter().enumerate() {
                    if i > 0 {
                        out.extend_from_slice(b", ");
                    }
                    out.push(b'"');
                    out.extend_from_slice(&self.str_bytes(sid));
                    out.push(b'"');
                }
                out.push(b']');
            }
            LiteralValue::Integer8(_) => {
                // Filtered out by `serialize_literal_array_into`.
            }
        }
    }

    /// Reverse a decode-rewritten literal-array table index to its source
    /// file offset (or assigned synthetic offset).
    fn literal_offset_of(&self, idx: LiteralArrayIdx) -> u32 {
        self.literal_offsets
            .get(idx.index())
            .copied()
            .unwrap_or(idx.0)
    }

    fn method_name_item(&self, tag: &[u8], idx: MethodIdx, out: &mut Vec<u8>) {
        out.extend_from_slice(tag);
        out.push(b':');
        match self.methods.get(idx.index()) {
            Some(&(_, _, m)) => out.extend_from_slice(&self.str_bytes(m.name)),
            None => {
                let _ = write!(out, "!invalid:method:{:#x}", idx.0);
            }
        }
    }

    // -- literal table collection (upstream GetLiteralArrays) ---------------

    /// Field-scan side effects of `GetMetadataFieldValue` (module/phase
    /// offset classification), in class file order × field order.
    fn classify_field_offsets(&mut self) {
        for class in self.file.classes.values() {
            let record_name = self.class_name(class.descriptor);
            let is_scope_record = record_name == b"_ESScopeNamesRecord";
            for field in &class.fields {
                if field.field_type != Type::U32 {
                    continue;
                }
                let name = self.file.strings.resolve(field.name).unwrap_or("");
                let Some(offset) = self.field_u32_offset(field) else {
                    continue;
                };
                if name == crate::MODULE_REQUEST_PHASE_FIELD {
                    continue; // phase blobs: excluded from the listing
                }
                if name != crate::TYPE_SUMMARY_OFFSET_FIELD
                    && !is_scope_record
                    && name != crate::SCOPE_NAMES_FIELD
                {
                    self.module_literals.insert(offset);
                }
            }
        }
    }

    /// The LITERALS section tables: regular literal arrays and module
    /// arrays, both keyed by `"{index} 0x{offset}"` (sorted as strings —
    /// upstream `std::map<std::string, …>`).
    fn collect_literal_tables(&self) -> LiteralTables<'f> {
        let mut regular: BTreeMap<Vec<u8>, u32> = BTreeMap::new();
        let mut modules: BTreeMap<Vec<u8>, &'f ModuleData> = BTreeMap::new();
        let uses_header_table = match self.file.dialect() {
            Some(crate::Dialect::DynamicLegacy) => true,
            Some(crate::Dialect::DynamicModern) => self.file.version <= LAST_HEADER_LITERAL_VERSION,
            Some(crate::Dialect::Static) | None => false,
        };
        if uses_header_table {
            self.collect_header_literal_tables(&mut regular, &mut modules);
        } else {
            self.collect_simulated_literal_tables(&mut regular, &mut modules);
        }
        (regular, modules)
    }

    /// ≤12.0.6.0: the header literal-array index table, walked in header
    /// order (module blobs route to the module table; phase blobs occupy a
    /// header slot but are excluded from the listing — disassembler.cpp:372).
    /// Hand-built models carry no header table: fall back to the decoded
    /// table order with module blobs appended (documented best-effort).
    fn collect_header_literal_tables(
        &self,
        regular: &mut BTreeMap<Vec<u8>, u32>,
        modules: &mut BTreeMap<Vec<u8>, &'f ModuleData>,
    ) {
        if !self.file.literal_array_header_offsets.is_empty() {
            let phase_offsets: HashSet<u32> = self
                .file
                .classes
                .values()
                .flat_map(|c| c.fields.iter())
                .filter_map(|f| match &f.initial_value {
                    Some(FieldValue::ModuleRequestPhase(p)) => Some(p.source_offset),
                    _ => None,
                })
                .collect();
            for (index, offset) in self
                .file
                .literal_array_header_offsets
                .iter()
                .copied()
                .enumerate()
            {
                if phase_offsets.contains(&offset) {
                    continue;
                }
                let key = format!("{index} 0x{offset:x}").into_bytes();
                if let Some(md) = self.module_data_at(offset) {
                    modules.insert(key, md);
                } else {
                    regular.insert(key, offset);
                }
            }
            return;
        }
        self.collect_header_literal_tables_fallback(regular, modules);
    }

    /// Header-table reconstruction for hand-built models (no recorded
    /// header): decoded table order, then module blobs, then scope-names
    /// arrays.
    fn collect_header_literal_tables_fallback(
        &self,
        regular: &mut BTreeMap<Vec<u8>, u32>,
        modules: &mut BTreeMap<Vec<u8>, &'f ModuleData>,
    ) {
        let scope_indices: HashSet<usize> = self
            .file
            .classes
            .values()
            .flat_map(|c| {
                let c_is_scope = self.file.strings.resolve(c.descriptor)
                    == Some(crate::ES_SCOPE_NAMES_RECORD_DESCRIPTOR);
                c.fields.iter().filter_map(move |f| {
                    let is_scope_field = c_is_scope
                        || self.file.strings.resolve(f.name) == Some(crate::SCOPE_NAMES_FIELD);
                    match (&f.initial_value, is_scope_field) {
                        (Some(FieldValue::LiteralArrayRef { index, .. }), true) => {
                            Some(index.index())
                        }
                        _ => None,
                    }
                })
            })
            .collect();
        let mut index: u32 = 0;
        for (arr_idx, &offset) in self.literal_offsets.iter().enumerate() {
            if !scope_indices.contains(&arr_idx) {
                regular.insert(format!("{index} 0x{offset:x}").into_bytes(), offset);
                index += 1;
            }
        }
        // Module blobs in field order (class file order × field order).
        for class in self.file.classes.values() {
            for field in &class.fields {
                if let Some(FieldValue::ModuleData(md)) = &field.initial_value {
                    modules.insert(format!("{index} 0x{:x}", md.source_offset).into_bytes(), md);
                    index += 1;
                }
            }
        }
        // Scope-names arrays (tagged literal arrays, header order).
        for (arr_idx, &offset) in self.literal_offsets.iter().enumerate() {
            if scope_indices.contains(&arr_idx) {
                regular.insert(format!("{index} 0x{offset:x}").into_bytes(), offset);
                index += 1;
            }
        }
    }

    /// 13.x/24.x: `CollectUtil::CollectLiteralArray` — collect offsets
    /// referenced by instruction literal-array operands (class/method/
    /// instruction order) plus transitively nested arrays, then assign
    /// indexes in libstdc++ `unordered_set` iteration order.
    fn collect_simulated_literal_tables(
        &self,
        regular: &mut BTreeMap<Vec<u8>, u32>,
        modules: &mut BTreeMap<Vec<u8>, &'f ModuleData>,
    ) {
        let mut processed = sim::U32Set::new();
        let mut nest = sim::U32Set::new();
        for class in self.file.classes.values() {
            if class.is_external {
                continue;
            }
            let class_raw = self.str_bytes(class.name);
            let class_matches =
                class_raw == b"_ESModuleRecord;" || class_raw == b"_ESScopeNamesRecord";
            for field in &class.fields {
                let name = self.file.strings.resolve(field.name).unwrap_or("");
                if !(class_matches
                    || name == crate::SCOPE_NAMES_FIELD
                    || name == crate::MODULE_RECORD_IDX_FIELD)
                {
                    continue;
                }
                if let Some(offset) = self.field_u32_offset(field) {
                    processed.insert(offset);
                }
            }
            for method in &class.methods {
                let Some(body) = &method.body else { continue };
                let bcs = body.bytecodes();
                for bc in bcs.iter() {
                    let (ops, len) = bc.entity_operands_inline();
                    for &(kind, id) in &ops[..len] {
                        if kind != EntityKind::LiteralarrayId {
                            continue;
                        }
                        if let Some(&EntityRef::LiteralArray(la_idx)) =
                            body.entities.get(&(kind, id.0))
                        {
                            nest.insert(self.literal_offset_of(la_idx));
                        }
                    }
                }
            }
        }
        while let Some(offset) = nest.first() {
            processed.insert(offset);
            if let Some(array) = self
                .literal_by_offset
                .get(&offset)
                .and_then(|&idx| self.file.literal_arrays.get(idx))
            {
                for v in &array.values {
                    if let LiteralValue::LiteralArray(target) = v {
                        let target = self.literal_offset_of(*target);
                        if !processed.contains(target) && !nest.contains(target) {
                            nest.insert(target);
                        }
                    }
                }
            }
            nest.erase(offset);
        }
        for (index, offset) in processed.iter().into_iter().enumerate() {
            let key = format!("{index} 0x{offset:x}").into_bytes();
            if self.module_literals.contains(&offset)
                && let Some(md) = self.module_data_at(offset)
            {
                modules.insert(key, md);
                continue;
            }
            regular.insert(key, offset);
        }
    }

    fn module_data_at(&self, offset: u32) -> Option<&'f ModuleData> {
        self.module_data_by_offset.get(&offset).copied()
    }

    // -- emission -----------------------------------------------------------

    fn emit_to_writer<W: io::Write>(mut self, source_name: &str, out: &mut W) -> io::Result<()> {
        write!(out, "# source binary: {source_name}\n\n")?;
        out.write_all(b"# ====================\n# LITERALS\n\n")?;

        self.classify_field_offsets();

        let mut records: BTreeMap<Vec<u8>, PaRecord> = BTreeMap::new();
        let mut functions: BTreeMap<Vec<u8>, (StringId, &'f Class, &'f Method)> = BTreeMap::new();
        self.index_records_and_functions(&mut records, &mut functions);

        let mut scratch = Vec::new();
        let (regular, modules) = self.collect_literal_tables();
        for (key, offset) in &regular {
            scratch.clear();
            scratch.extend_from_slice(key);
            scratch.push(b' ');
            if let Some(array) = self
                .literal_by_offset
                .get(offset)
                .and_then(|&idx| self.file.literal_arrays.get(idx))
            {
                self.serialize_literal_array_into(&array.values, &mut scratch);
            }
            scratch.push(b'\n');
            out.write_all(&scratch)?;
        }
        for (key, md) in &modules {
            scratch.clear();
            scratch.extend_from_slice(key);
            scratch.push(b' ');
            self.serialize_module_array(md, &mut scratch);
            scratch.push(b'\n');
            out.write_all(&scratch)?;
        }
        drop(regular);
        drop(modules);
        out.write_all(b"\n")?;

        out.write_all(b"# ====================\n# RECORDS\n\n")?;
        for record in records.values() {
            scratch.clear();
            self.emit_record(record, &mut scratch);
            if !scratch.is_empty() {
                out.write_all(&scratch)?;
            }
        }
        drop(records);

        out.write_all(b"# ====================\n# METHODS\n\n")?;
        let mut insn_buf = Vec::new();
        let mut insn_ranges = Vec::new();
        for &(desc, class, method) in functions.values() {
            scratch.clear();
            self.render_method(
                desc,
                class,
                method,
                &mut insn_buf,
                &mut insn_ranges,
                &mut scratch,
            );
            out.write_all(&scratch)?;
        }
        drop(functions);
        drop(insn_buf);
        drop(insn_ranges);

        out.write_all(b"# ====================\n# STRING\n\n")?;
        for (offset, bytes) in &self.strings {
            scratch.clear();
            let _ = write!(scratch, "[offset:0x{offset:x}, name_value:");
            scratch.extend_from_slice(bytes);
            scratch.extend_from_slice(b"]\n");
            out.write_all(&scratch)?;
        }
        Ok(())
    }

    fn index_records_and_functions(
        &mut self,
        records: &mut BTreeMap<Vec<u8>, PaRecord>,
        functions: &mut BTreeMap<Vec<u8>, (StringId, &'f Class, &'f Method)>,
    ) {
        for (&desc, class) in &self.file.classes {
            let record_name = self.class_name(desc);
            // GetRecord processes methods even for duplicate record names;
            // only the record TABLE insert is first-wins.
            if !class.is_external {
                for method in &class.methods {
                    if let Some(body) = &method.body {
                        self.register_body_strings(body);
                    }
                    let sig = self.build_fn_header(desc, class, method).signature();
                    functions.entry(sig).or_insert((desc, class, method));
                }
            }
            if !records.contains_key(&record_name) {
                let is_external = class.is_external;
                let language = if is_external {
                    SourceLang::EcmaScript
                } else {
                    class.source_lang
                };
                let fields = if is_external {
                    Vec::new()
                } else {
                    self.render_fields(class)
                };
                records.insert(
                    record_name.clone(),
                    PaRecord {
                        name: record_name,
                        language,
                        is_external,
                        fields,
                    },
                );
            }
        }
    }

    fn render_fields(&self, class: &Class) -> Vec<Vec<u8>> {
        let mut out = Vec::new();
        for field in &class.fields {
            let mut line = Vec::new();
            line.extend_from_slice(type_pandasm_name(self.file, &field.field_type).as_bytes());
            line.push(b' ');
            let name = self.str_bytes(field.name);
            line.extend_from_slice(file_name_by_path(&name));
            if field.initial_value.is_some() {
                self.render_field_value(field, &mut line);
            }
            out.push(line);
        }
        out
    }

    /// `GetMetadataFieldValue` + `SerializeFieldValue` (the value never
    /// prints for the other field types upstream handles).
    fn render_field_value(&self, field: &crate::model::Field, line: &mut Vec<u8>) {
        match field.field_type {
            Type::U32 => {
                if let Some(v) = self.field_u32_offset(field) {
                    let _ = write!(line, " = 0x{v:x}");
                }
            }
            Type::U8 => {
                if let Some(FieldValue::I32(v)) = &field.initial_value {
                    let _ = write!(line, " = 0x{:x}", u32::from(*v as u8));
                }
            }
            Type::F64 => {
                if let Some(FieldValue::F64(v)) = &field.initial_value {
                    let _ = write!(line, " = {}", format_g6(*v));
                }
            }
            Type::Bool => {
                if let Some(FieldValue::I32(v)) = &field.initial_value {
                    let _ = write!(line, " = {}", i32::from(*v != 0));
                }
            }
            _ => {}
        }
    }

    /// `SerializeModuleLiteralArray` over the decoded module data.
    fn serialize_module_array(&self, md: &ModuleData, out: &mut Vec<u8>) {
        let _ = writeln!(out, "{{ {} [", md.records.len());
        out.extend_from_slice(b"\tMODULE_REQUEST_ARRAY: {\n");
        for (i, req) in md.requests.iter().enumerate() {
            let _ = write!(out, "\t\t{i} : ");
            out.extend_from_slice(&self.str_bytes(*req));
            out.extend_from_slice(b",\n");
        }
        out.extend_from_slice(b"\t};\n");
        for rec in &md.records {
            out.extend_from_slice(b"\tModuleTag: ");
            match rec {
                ModuleRecord::RegularImport {
                    local_name,
                    import_name,
                    module_request_idx,
                } => {
                    out.extend_from_slice(b"REGULAR_IMPORT, local_name: ");
                    out.extend_from_slice(&self.str_bytes(*local_name));
                    out.extend_from_slice(b", import_name: ");
                    out.extend_from_slice(&self.str_bytes(*import_name));
                    self.module_request(md, *module_request_idx, out);
                }
                ModuleRecord::NamespaceImport {
                    local_name,
                    module_request_idx,
                } => {
                    out.extend_from_slice(b"NAMESPACE_IMPORT, local_name: ");
                    out.extend_from_slice(&self.str_bytes(*local_name));
                    self.module_request(md, *module_request_idx, out);
                }
                ModuleRecord::LocalExport {
                    local_name,
                    export_name,
                } => {
                    out.extend_from_slice(b"LOCAL_EXPORT, local_name: ");
                    out.extend_from_slice(&self.str_bytes(*local_name));
                    out.extend_from_slice(b", export_name: ");
                    out.extend_from_slice(&self.str_bytes(*export_name));
                }
                ModuleRecord::IndirectExport {
                    export_name,
                    import_name,
                    module_request_idx,
                } => {
                    out.extend_from_slice(b"INDIRECT_EXPORT, export_name: ");
                    out.extend_from_slice(&self.str_bytes(*export_name));
                    out.extend_from_slice(b", import_name: ");
                    out.extend_from_slice(&self.str_bytes(*import_name));
                    self.module_request(md, *module_request_idx, out);
                }
                ModuleRecord::StarExport { module_request_idx } => {
                    out.extend_from_slice(b"STAR_EXPORT");
                    self.module_request(md, *module_request_idx, out);
                }
            }
            out.extend_from_slice(b";\n");
        }
        out.extend_from_slice(b"]}");
    }

    fn module_request(&self, md: &ModuleData, idx: u32, out: &mut Vec<u8>) {
        out.extend_from_slice(b", module_request: ");
        match md.requests.get(idx as usize) {
            Some(sid) => out.extend_from_slice(&self.str_bytes(*sid)),
            None => {
                let _ = write!(out, "!invalid:module_request:{idx}");
            }
        }
    }

    fn emit_record(&self, record: &PaRecord, out: &mut Vec<u8>) {
        if is_system_type(&record.name) {
            return;
        }
        let _ = writeln!(out, ".language {}", language_str(record.language));
        out.extend_from_slice(b".record ");
        out.extend_from_slice(&record.name);
        if record.is_external {
            out.extend_from_slice(b" <external>");
            out.extend_from_slice(b"\n\n");
            return;
        }
        out.extend_from_slice(b" {\n");
        for field in &record.fields {
            out.push(b'\t');
            out.extend_from_slice(field);
            out.push(b'\n');
        }
        out.extend_from_slice(b"}\n\n");
    }

    fn render_method(
        &mut self,
        owner_desc: StringId,
        class: &Class,
        method: &Method,
        insn_buf: &mut Vec<u8>,
        insn_ranges: &mut Vec<(usize, usize)>,
        out: &mut Vec<u8>,
    ) {
        let annotations = self.collect_annotations(method);
        for (name, elements) in &annotations {
            out.extend_from_slice(name);
            out.extend_from_slice(b":\n");
            if !elements.is_empty() {
                for (i, elem) in elements.iter().enumerate() {
                    out.extend_from_slice(elem);
                    if i + 1 < elements.len() {
                        out.push(b'\n');
                    }
                }
                out.push(b'\n');
            }
        }
        let hdr = self.build_fn_header(owner_desc, class, method);
        let _ = writeln!(out, ".language {}", language_str(hdr.language));
        let _ = write!(out, ".function {} ", hdr.return_type);
        out.extend_from_slice(&hdr.name);
        out.push(b'(');
        for (i, p) in hdr.params.iter().enumerate() {
            if i > 0 {
                out.extend_from_slice(b", ");
            }
            out.extend_from_slice(p);
            let _ = write!(out, " a{i}");
        }
        out.push(b')');
        // Bool attributes: the corpus carries only `static`; upstream's
        // unordered_set order for multi-attribute sets is pinned by no
        // corpus fixture, so insertion order is used.
        let mut attrs: Vec<&str> = Vec::new();
        if hdr.is_static {
            attrs.push("static");
        }
        if hdr.is_external {
            attrs.push("external");
        }
        if hdr.is_ctor {
            attrs.push("ctor");
        }
        if hdr.is_cctor {
            attrs.push("cctor");
        }
        if !attrs.is_empty() {
            out.extend_from_slice(b" <");
            out.extend_from_slice(attrs.join(", ").as_bytes());
            out.push(b'>');
        }
        out.extend_from_slice(b" {\n");
        if let Some(body) = &method.body {
            let (labels, trailing_empty_label, catches) =
                self.build_body_into(body, insn_buf, insn_ranges);
            for (i, &(start, end)) in insn_ranges.iter().enumerate() {
                if let Some(label) = labels.get(&(i as u32)) {
                    out.extend_from_slice(label.as_bytes());
                    out.extend_from_slice(b":\n");
                }
                out.push(b'\t');
                out.extend_from_slice(&insn_buf[start..end]);
                out.push(b'\n');
            }
            if trailing_empty_label {
                out.extend_from_slice(b":\n");
            }
            if !catches.is_empty() {
                out.push(b'\n');
                for catch in &catches {
                    if catch.exception_record.is_empty() {
                        out.extend_from_slice(b".catchall ");
                    } else {
                        out.extend_from_slice(b".catch ");
                        out.extend_from_slice(&catch.exception_record);
                        out.extend_from_slice(b", ");
                    }
                    let _ = write!(
                        out,
                        "{}, {}, {}",
                        catch.try_begin, catch.try_end, catch.catch_begin
                    );
                    if !catch.catch_end.is_empty() {
                        let _ = write!(out, ", {}", catch.catch_end);
                    }
                    out.push(b'\n');
                }
            }
        }
        out.extend_from_slice(b"}\n\n");
    }
    /// The u32 wire value of a field's initial value, abstracting over the
    /// structural module/scope/phase models.
    fn field_u32_offset(&self, field: &crate::model::Field) -> Option<u32> {
        match &field.initial_value {
            Some(FieldValue::I32(v)) => u32::try_from(*v).ok(),
            Some(FieldValue::ModuleData(md)) => Some(md.source_offset),
            Some(FieldValue::LiteralArrayRef {
                index,
                source_offset,
            }) => Some(
                source_offset
                    .or_else(|| self.literal_offsets.get(index.index()).copied())
                    .unwrap_or(index.0),
            ),
            Some(FieldValue::ModuleRequestPhase(p)) => Some(p.source_offset),
            Some(FieldValue::JsonFileContent { source_offset, .. }) => Some(*source_offset),
            _ => None,
        }
    }
}

/// First-name-wins label allocation (upstream `LabelTable` insert).
fn alloc_label(labels: &mut BTreeMap<u32, String>, idx: u32, name: String) -> String {
    labels.entry(idx).or_insert(name).clone()
}

/// `FieldTypeToPandasmType`: primitive tag names, `any` for tagged, and the
/// pandasm record name for references.
fn type_pandasm_name(file: &File, ty: &Type) -> String {
    match ty {
        Type::Void => "void".to_owned(),
        Type::Bool => "u1".to_owned(),
        Type::I8 => "i8".to_owned(),
        Type::U8 => "u8".to_owned(),
        Type::I16 => "i16".to_owned(),
        Type::U16 => "u16".to_owned(),
        Type::I32 => "i32".to_owned(),
        Type::U32 => "u32".to_owned(),
        Type::I64 => "i64".to_owned(),
        Type::U64 => "u64".to_owned(),
        Type::F32 => "f32".to_owned(),
        Type::F64 => "f64".to_owned(),
        Type::Tagged => "any".to_owned(),
        Type::Reference(sid) => {
            String::from_utf8_lossy(&record_pandasm_name(&string_bytes(file, *sid))).into_owned()
        }
    }
}

/// `std::string::replace(find(needle), …)` — replace the first occurrence.
fn replace_once(haystack: &mut Vec<u8>, needle: &[u8], with: &[u8]) {
    if !needle.is_empty()
        && let Some(pos) = haystack.windows(needle.len()).position(|w| w == needle)
    {
        haystack.splice(pos..pos + needle.len(), with.iter().copied());
    }
}

#[cfg(test)]
mod emit_tests;
