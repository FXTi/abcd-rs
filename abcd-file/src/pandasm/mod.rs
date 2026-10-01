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
//!   iteration order (libstdc++); [`sim`] reproduces that container's
//!   insert/rehash/erase semantics bit-exactly.
//!
//! The emitter never panics on any [`File`] model: unresolvable entities
//! render as deterministic `!invalid:…` placeholders. (Corpus-driven tests
//! panic on mismatch by design — that is the gate's job, not the emitter's.)
//!
//! The inverse direction — whole-file pandasm text back to a [`File`]
//! model, the `abcd asm` foundation — lives in [`parse`].

mod insn_ctor;
mod parse;

pub use parse::{DEFAULT_VERSION, ParseError, parse_file, parse_file_with_version};

use std::collections::BTreeMap;
use std::io::Write as _;

use abcd_isa::{Bytecode, BytecodeFlags, EntityKind, Operand};

use crate::model::{
    Annotation, AnnotationValue, Class, FieldValue, File, Method, MethodBody, ModuleData,
    ModuleRecord,
};
use crate::types::{HasAccessFlags, SourceLang, Type};
use crate::{LiteralValue, StringId, Version};

/// Last file version whose header carries the literal-array index table
/// (vendored `LAST_CONTAINS_LITERAL_IN_HEADER_VERSION`, file.h:546).
const LAST_HEADER_LITERAL_VERSION: Version = Version::new(12, 0, 6, 0);

/// Emit the complete pandasm text of `file`, byte-identical to upstream
/// `ark_disasm <path> out.pa`. `source_name` is the input file's basename
/// (upstream `GetFileNameByPath`), printed in the `# source binary:` header.
pub fn emit_file(file: &File, source_name: &str) -> Vec<u8> {
    Emitter::new(file).emit(source_name)
}

// ---------------------------------------------------------------------------
// String bytes (MUTF-8 re-encode, matching upstream's raw print)
// ---------------------------------------------------------------------------

/// The raw bytes upstream prints for a pooled string: the captured original
/// MUTF-8 for the registered lossy class (lone surrogates), else the MUTF-8
/// re-encode of the pool identity (embedded NUL as `C0 80`, astral chars as
/// surrogate pairs).
fn string_bytes(file: &File, sid: StringId) -> Vec<u8> {
    let Some(identity) = file.strings.resolve(sid) else {
        return b"!invalid:string".to_vec();
    };
    if let Some(raw) = file.string_raw_bytes.get(identity) {
        return raw.to_vec();
    }
    mutf8_bytes(identity)
}

/// MUTF-8 encode (embedded NUL as C0 80, astral chars as surrogate pairs).
/// The N72 disambiguation suffix (U+E000 + hex) is our bookkeeping and is
/// never emitted.
pub fn mutf8_bytes(s: &str) -> Vec<u8> {
    let s = s.find('\u{E000}').map_or(s, |i| &s[..i]);
    let mut out = Vec::new();
    for c in s.chars() {
        let c = c as u32;
        if c == 0 {
            out.extend_from_slice(&[0xC0, 0x80]);
        } else if c >= 0x10000 {
            let c = c - 0x10000;
            for unit in [0xD800 + (c >> 10), 0xDC00 + (c & 0x3FF)] {
                out.extend_from_slice(&[
                    0xE0 | (unit >> 12) as u8,
                    0x80 | ((unit >> 6) & 0x3F) as u8,
                    0x80 | (unit & 0x3F) as u8,
                ]);
            }
        } else {
            let mut buf = [0u8; 4];
            out.extend_from_slice(char::from_u32(c).unwrap().encode_utf8(&mut buf).as_bytes());
        }
    }
    out
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
    let epos = s.find('e').expect("scientific format has an exponent");
    let exp: i32 = s[epos + 1..].parse().expect("scientific exponent");
    format!(
        "{}e{}{:02}",
        &s[..epos],
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
    let e = format_scientific_exp(v, (P - 1) as usize);
    let x: i32 = e[e.find('e').unwrap() + 1..]
        .parse()
        .expect("%e exponent parses");
    let mut s = if (-4..P).contains(&x) {
        let prec = (P - 1 - x).max(0) as usize;
        format!("{v:.prec$}")
    } else {
        e
    };
    // Strip trailing zeros (and a trailing point) from the mantissa.
    match s.find('e') {
        Some(epos) => {
            let mantissa = s[..epos].trim_end_matches('0').trim_end_matches('.');
            s = format!("{}{}", mantissa, &s[epos..]);
        }
        None => {
            s = s.trim_end_matches('0').trim_end_matches('.').to_owned();
        }
    }
    s
}

/// `{:.5e}`-style scientific text with the C two-digit signed exponent.
fn format_scientific_exp(v: f64, prec: usize) -> String {
    let s = format!("{v:.prec$e}");
    let epos = s.find('e').expect("scientific format has an exponent");
    let exp: i32 = s[epos + 1..].parse().expect("scientific exponent");
    format!(
        "{}e{}{:02}",
        &s[..epos],
        if exp < 0 { '-' } else { '+' },
        exp.abs()
    )
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

    /// First primes of libstdc++'s `__prime_list` (ample for any realistic
    /// literal-array count).
    const PRIMES: &[usize] = &[
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97, 103, 109, 113, 127, 137, 139, 149, 157, 167, 179, 193, 199, 211, 227, 241, 257, 277,
        293, 313, 337, 359, 383, 409, 439, 467, 503, 541, 577, 619, 661, 709, 761, 823, 887, 953,
        1031, 1109, 1193, 1289, 1381, 1483, 1601, 1709, 1831, 1973, 2129, 2309, 2491, 2689, 2903,
        3137, 3391, 3659, 3947, 4271, 4621, 4999, 5407, 5851, 6323, 6841, 7399, 7993, 8641, 9341,
        10099, 10939, 11831, 12821, 13877, 15013, 16231, 17551, 18973, 20507, 22171, 23957,
    ];

    fn next_bkt(n: usize) -> usize {
        match PRIMES.iter().position(|&p| p >= n) {
            Some(i) => PRIMES[i],
            None => n, // out of table: never reached at corpus scale
        }
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

struct PaFunction {
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
    /// `(annotation name, element lines)` in file order; elements of a
    /// repeated name merge into its first entry (upstream `find_if` quirk).
    annotations: Vec<(Vec<u8>, Vec<Vec<u8>>)>,
    /// Rendered body: `(label bound before this instruction?, text)`.
    insns: Vec<(Option<String>, Vec<u8>)>,
    /// Bare `:` line quirk: a label bound past the last instruction.
    trailing_empty_label: bool,
    catches: Vec<CatchLine>,
}

impl PaFunction {
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

struct Emitter<'f> {
    file: &'f File,
    /// STRING section: offset → raw bytes (upstream `string_offset_to_name_`,
    /// a map sorted by offset).
    strings: BTreeMap<u32, Vec<u8>>,
    /// `_ESModuleRecord`-style u32 field values (module blob offsets), in
    /// class file order × field order.
    module_literals: Vec<u32>,
}

impl<'f> Emitter<'f> {
    fn new(file: &'f File) -> Self {
        Emitter {
            file,
            strings: BTreeMap::new(),
            module_literals: Vec::new(),
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
    /// name + `:(` + param types + `)`. Falls back to the bare entity name
    /// with an empty parameter list when the method is not a decoded class
    /// method (external — no corpus coverage).
    fn method_signature_by_offset(&mut self, offset: u32) -> Vec<u8> {
        for (desc, class) in &self.file.classes {
            if let Some(m) = class.methods.iter().find(|m| m.offset == offset) {
                let fun = self.build_function(*desc, class, m, false);
                return fun.signature();
            }
        }
        let mut sig = match self.file.resolve_entity(offset) {
            Some(sid) => self.str_bytes(sid),
            None => format!("!invalid:method:{offset:#x}").into_bytes(),
        };
        sig.extend_from_slice(b":()");
        sig
    }

    // -- function construction (upstream GetMethod/AddMethodToTables) -------

    /// Build the pandasm function for one method. `process_body` controls
    /// whether instructions are rendered and strings registered (upstream
    /// runs this even for later-dropped duplicate signatures).
    fn build_function(
        &mut self,
        owner_desc: StringId,
        class: &Class,
        method: &Method,
        process_body: bool,
    ) -> PaFunction {
        let raw_name = self.str_bytes(method.name);
        let mut fun = PaFunction {
            name: self.full_method_name(owner_desc, method.name),
            params: Vec::new(),
            return_type: "",
            language: if method.is_external {
                SourceLang::EcmaScript // upstream DEFUALT_SOURCE_LANG
            } else {
                method.source_lang
            },
            is_static: method.is_static(),
            is_external: method.is_external,
            is_ctor: raw_name == b".ctor",
            is_cctor: raw_name == b".cctor",
            annotations: Vec::new(),
            insns: Vec::new(),
            trailing_empty_label: false,
            catches: Vec::new(),
        };
        // GetMetaData: non-static methods gain a leading `this` parameter.
        if !fun.is_static {
            fun.params.push(self.class_name(class.descriptor));
        }
        if fun.is_ctor {
            replace_once(&mut fun.name, b".ctor", b"_ctor_");
        } else if fun.is_cctor {
            replace_once(&mut fun.name, b".cctor", b"_cctor_");
        }
        if let Some(body) = &method.body {
            fun.return_type = "any";
            for _ in 0..body.num_args {
                fun.params.push(b"any".to_vec());
            }
            if process_body {
                self.build_body(&mut fun, body);
            }
        }
        fun
    }

    /// Method annotations (upstream `GetMethodAnnotations` — the
    /// compile-time `ANNOTATION` tag list), rendered as header blocks.
    fn build_annotations(&mut self, fun: &mut PaFunction, method: &Method) {
        for ann in &method.annotations.compile_time {
            self.render_annotation(fun, ann);
        }
    }

    fn render_annotation(&mut self, fun: &mut PaFunction, ann: &Annotation) {
        let mut name = self.str_bytes(ann.class_descriptor);
        name.pop(); // strip the trailing ';' of the descriptor
        if name.is_empty() {
            return;
        }
        let idx = match fun.annotations.iter().position(|(n, _)| *n == name) {
            Some(i) => i,
            None => {
                fun.annotations.push((name, Vec::new()));
                fun.annotations.len() - 1
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
            fun.annotations[idx].1.push(line);
        }
    }

    // -- instructions (upstream GetInstructions) ----------------------------

    fn build_body(&mut self, fun: &mut PaFunction, body: &MethodBody) {
        let count = body.bytecodes.len() as u32;
        // Label table: instruction index → name. Try/catch labels allocate
        // first (upstream GetExceptions runs before the instruction walk).
        let mut labels: BTreeMap<u32, String> = BTreeMap::new();

        let mut catches: Vec<CatchLine> = Vec::new();
        'tries: for (try_idx, tb) in body.try_blocks.iter().enumerate() {
            let begin = tb.start;
            let end = tb.start + tb.len;
            // Upstream range checks; failure aborts try-block enumeration.
            if begin >= count || end > count {
                break 'tries;
            }
            let try_begin = alloc_label(&mut labels, begin, format!("try_begin_label_{try_idx}"));
            let try_end = alloc_label(&mut labels, end, format!("try_end_label_{try_idx}"));
            for (catch_idx, cb) in tb.catches.iter().enumerate() {
                let exception_record = if cb.type_idx == u32::MAX {
                    Vec::new()
                } else {
                    match self.file.resolve_entity(cb.type_idx) {
                        Some(sid) => record_pandasm_name(&self.str_bytes(sid)),
                        None => format!("!invalid:catch:{:#x}", cb.type_idx).into_bytes(),
                    }
                };
                let hbegin = cb.handler;
                let hend = cb.handler + cb.len;
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
        fun.catches = catches;

        // Instruction walk: jump labels allocate as `jump_label_{table len}`.
        // Labels attach AFTER the full walk (upstream AddLabels): a label
        // allocated by a later jump still prints on its target line.
        let mut texts: Vec<Vec<u8>> = Vec::with_capacity(body.bytecodes.len());
        for bc in &body.bytecodes {
            texts.push(self.render_instruction(bc, body, &mut labels));
        }
        fun.trailing_empty_label = labels.contains_key(&count);
        fun.insns = texts
            .into_iter()
            .enumerate()
            .map(|(i, text)| (labels.get(&(i as u32)).cloned(), text))
            .collect();
    }

    fn render_instruction(
        &mut self,
        bc: &Bytecode,
        body: &MethodBody,
        labels: &mut BTreeMap<u32, String>,
    ) -> Vec<u8> {
        let mut operands = bc.operands();
        // Upstream call-arg trimming (CALL-flagged pandasm opcodes): pop
        // trailing registers beyond the callee proto's argument count.
        if bc.has_flag(BytecodeFlags::CALL) {
            self.trim_call_args(bc, body, &mut operands);
        }
        let float = bc.has_flag(BytecodeFlags::FLOAT);
        let mut out = bc.mnemonic().as_bytes().to_vec();
        for (i, op) in operands.iter().enumerate() {
            out.extend_from_slice(if i == 0 { b" " } else { b", " });
            self.render_operand(bc, float, op, body, labels, &mut out);
        }
        out
    }

    fn trim_call_args(&self, bc: &Bytecode, body: &MethodBody, operands: &mut Vec<Operand>) {
        let n_regs = operands
            .iter()
            .filter(|op| matches!(op, Operand::Reg(_)))
            .count();
        // Callee: the METHOD_ID operand if any, else the containing method
        // (indirect call — no proto known here, no trim).
        let callee_offset = bc
            .entity_operands()
            .into_iter()
            .find(|(kind, _)| *kind == EntityKind::MethodId)
            .and_then(|(kind, id)| body.entity_offsets.get(&(kind, id.0)).copied());
        let Some((num_args, is_static)) = callee_offset.and_then(|off| self.method_proto(off))
        else {
            return;
        };
        let overhead = if is_static {
            n_regs as i64 - num_args as i64
        } else {
            n_regs as i64 - num_args as i64 - 1
        };
        if overhead <= 0 {
            return;
        }
        // Drop the LAST `overhead` register operands.
        let n_regs_total = operands
            .iter()
            .filter(|op| matches!(op, Operand::Reg(_)))
            .count();
        let mut seen = 0usize;
        operands.retain(|op| {
            if matches!(op, Operand::Reg(_)) {
                seen += 1;
                seen <= n_regs_total - overhead as usize
            } else {
                true
            }
        });
    }

    /// (proto num_args, is_static) of the method at an item offset.
    fn method_proto(&self, offset: u32) -> Option<(u32, bool)> {
        for class in self.file.classes.values() {
            if let Some(m) = class.methods.iter().find(|m| m.offset == offset) {
                return Some((m.arg_types.len() as u32, m.is_static()));
            }
        }
        None
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
                let count = body.bytecodes.len() as u32;
                if l < count {
                    let next = format!("jump_label_{}", labels.len());
                    let name = labels.entry(l).or_insert(next);
                    let name = name.clone();
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
        let offset = body.entity_offsets.get(&(kind, id)).copied();
        match (kind, offset) {
            (EntityKind::StringId, Some(off)) => {
                let bytes = self
                    .file
                    .resolve_entity(off)
                    .map(|sid| self.str_bytes(sid))
                    .unwrap_or_else(|| b"!invalid:string".to_vec());
                self.strings.entry(off).or_insert_with(|| bytes.clone());
                out.push(b'"');
                out.extend_from_slice(&bytes);
                out.push(b'"');
            }
            (EntityKind::MethodId, Some(off)) => {
                let sig = self.method_signature_by_offset(off);
                out.extend_from_slice(&sig);
            }
            (EntityKind::LiteralarrayId, Some(off)) => {
                let text = self.literal_array_by_offset(off);
                out.extend_from_slice(&text);
            }
            _ => {
                let _ = write!(out, "!invalid:entity:{kind:?}:{id}");
            }
        }
    }

    /// The literal-array operand text (`{ N [ … ]}`) for a source offset.
    fn literal_array_by_offset(&self, offset: u32) -> Vec<u8> {
        match self
            .file
            .literal_array_offsets
            .get(&offset)
            .and_then(|idx| self.file.literal_arrays.get(*idx as usize))
        {
            Some(array) => self.serialize_literal_array(&array.values),
            None => b"!invalid:literalarray".to_vec(),
        }
    }

    /// `SerializeLiteralArray`: `{ <count> [ <tag:value, … ]}`; empty arrays
    /// render as the empty string (the section line keeps its trailing
    /// space). Upstream drops TAGVALUE-tagged items (`FillLiteralData`'s
    /// early return); our `Integer8` is that tag.
    fn serialize_literal_array(&self, values: &[LiteralValue]) -> Vec<u8> {
        let items: Vec<&LiteralValue> = values
            .iter()
            .filter(|v| !matches!(v, LiteralValue::Integer8(_)))
            .collect();
        if items.is_empty() {
            return Vec::new();
        }
        let mut out = b"{ ".to_vec();
        let _ = write!(out, "{} [ ", items.len());
        for v in items {
            self.serialize_literal_item(v, &mut out);
            out.extend_from_slice(b", ");
        }
        out.extend_from_slice(b"]}");
        out
    }

    fn serialize_literal_item(&self, v: &LiteralValue, out: &mut Vec<u8>) {
        match v {
            LiteralValue::Bool(b) => {
                let _ = write!(out, "u1:{}", *b as u8);
            }
            LiteralValue::Integer8(v) => {
                let _ = write!(out, "i8:{}", *v as i8);
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
            LiteralValue::Method(off) => self.method_name_item(b"method", *off, out),
            LiteralValue::GeneratorMethod(off) => {
                self.method_name_item(b"generator_method", *off, out)
            }
            LiteralValue::Getter(off) => self.method_name_item(b"getter", *off, out),
            LiteralValue::Setter(off) => self.method_name_item(b"setter", *off, out),
            LiteralValue::AsyncGeneratorMethod(off) => {
                // No upstream rendering (UNREACHABLE); deterministic fallback.
                self.method_name_item(b"async_generator_method", *off, out)
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
            // ARRAY_* payloads stay undecoded offsets in our model and never
            // occur in the corpus; render a deterministic placeholder.
            other => {
                let _ = write!(out, "!invalid:literal:{other:?}");
            }
        }
    }

    /// Reverse a decode-rewritten literal-array table index to its source
    /// file offset (identity when the target was never decoded).
    fn literal_offset_of(&self, idx: crate::LiteralArrayIdx) -> u32 {
        self.file
            .literal_array_offsets
            .iter()
            .find(|(_, i)| **i == idx.0)
            .map(|(o, _)| *o)
            .unwrap_or(idx.0)
    }

    fn method_name_item(&self, tag: &[u8], offset: u32, out: &mut Vec<u8>) {
        out.extend_from_slice(tag);
        out.push(b':');
        match self.file.resolve_entity(offset) {
            Some(sid) => out.extend_from_slice(&self.str_bytes(sid)),
            None => {
                let _ = write!(out, "!invalid:method:{offset:#x}");
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
                let Some(offset) = field_u32_offset(field) else {
                    continue;
                };
                if name == crate::MODULE_REQUEST_PHASE_FIELD {
                    continue; // phase blobs: excluded from the listing
                }
                if name != crate::TYPE_SUMMARY_OFFSET_FIELD
                    && !is_scope_record
                    && name != "scopeNames"
                {
                    self.module_literals.push(offset);
                }
            }
        }
    }

    /// The LITERALS section tables: regular literal arrays and module
    /// arrays, both keyed by `"{index} 0x{offset}"` (sorted as strings —
    /// upstream `std::map<std::string, …>`).
    fn collect_literal_tables(&self) -> (BTreeMap<Vec<u8>, u32>, BTreeMap<Vec<u8>, ModuleData>) {
        let mut regular: BTreeMap<Vec<u8>, u32> = BTreeMap::new();
        let mut modules: BTreeMap<Vec<u8>, ModuleData> = BTreeMap::new();
        if self.file.version <= LAST_HEADER_LITERAL_VERSION {
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
        modules: &mut BTreeMap<Vec<u8>, ModuleData>,
    ) {
        if !self.file.literal_array_header_offsets.is_empty() {
            let phase_offsets: std::collections::HashSet<u32> = self
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
        modules: &mut BTreeMap<Vec<u8>, ModuleData>,
    ) {
        let scope_offsets: std::collections::HashSet<u32> = self
            .file
            .classes
            .values()
            .flat_map(|c| c.fields.iter())
            .filter_map(|f| match &f.initial_value {
                Some(FieldValue::LiteralArrayRef(off)) => Some(*off),
                _ => None,
            })
            .collect();
        let mut decoded: Vec<(u32, u32)> = self
            .file
            .literal_array_offsets
            .iter()
            .map(|(o, i)| (*o, *i))
            .collect();
        decoded.sort_by_key(|(_, i)| *i);
        let mut index: u32 = 0;
        for (offset, _) in decoded.iter().filter(|(o, _)| !scope_offsets.contains(o)) {
            regular.insert(format!("{index} 0x{offset:x}").into_bytes(), *offset);
            index += 1;
        }
        // Module blobs in field order (class file order × field order).
        for class in self.file.classes.values() {
            for field in &class.fields {
                if let Some(FieldValue::ModuleData(md)) = &field.initial_value {
                    modules.insert(
                        format!("{index} 0x{:x}", md.source_offset).into_bytes(),
                        md.clone(),
                    );
                    index += 1;
                }
            }
        }
        // Scope-names arrays (tagged literal arrays, header order).
        for (offset, _) in decoded.iter().filter(|(o, _)| scope_offsets.contains(o)) {
            regular.insert(format!("{index} 0x{offset:x}").into_bytes(), *offset);
            index += 1;
        }
    }

    /// 13.x/24.x: `CollectUtil::CollectLiteralArray` — collect offsets
    /// referenced by instruction literal-array operands (class/method/
    /// instruction order) plus transitively nested arrays, then assign
    /// indexes in libstdc++ `unordered_set` iteration order.
    fn collect_simulated_literal_tables(
        &self,
        regular: &mut BTreeMap<Vec<u8>, u32>,
        modules: &mut BTreeMap<Vec<u8>, ModuleData>,
    ) {
        let mut processed = sim::U32Set::new();
        let mut nest = sim::U32Set::new();
        for class in self.file.classes.values() {
            if class.is_external {
                continue;
            }
            // Field-driven collection: upstream matches the RAW class name
            // against "_ESModuleRecord;"/"_ESScopeNamesRecord" (never true
            // for the "L…;"-shaped descriptors these records carry) and
            // field names "scopeNames"/"moduleRecordIdx".
            let class_raw = self.str_bytes(class.name);
            let class_matches =
                class_raw == b"_ESModuleRecord;" || class_raw == b"_ESScopeNamesRecord";
            for field in &class.fields {
                let name = self.file.strings.resolve(field.name).unwrap_or("");
                if !(class_matches || name == "scopeNames" || name == "moduleRecordIdx") {
                    continue;
                }
                if let Some(offset) = field_u32_offset(field) {
                    processed.insert(offset);
                }
            }
            for method in &class.methods {
                let Some(body) = &method.body else { continue };
                for bc in &body.bytecodes {
                    for (kind, id) in bc.entity_operands() {
                        if kind != EntityKind::LiteralarrayId {
                            continue;
                        }
                        if let Some(&off) = body.entity_offsets.get(&(kind, id.0)) {
                            nest.insert(off);
                        }
                    }
                }
            }
        }
        // ProcessNestLiteralArray: pop the iteration-first element, collect
        // its nested literal-array references, repeat.
        while let Some(offset) = nest.first() {
            processed.insert(offset);
            if let Some(array) = self
                .file
                .literal_array_offsets
                .get(&offset)
                .and_then(|idx| self.file.literal_arrays.get(*idx as usize))
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
            // Upstream routes by module_literals_ membership
            // (GetMetadataFieldValue's u32-field classification).
            if self.module_literals.contains(&offset) {
                if let Some(md) = self.module_data_at(offset) {
                    modules.insert(key, md);
                    continue;
                }
            }
            regular.insert(key, offset);
        }
    }

    fn module_data_at(&self, offset: u32) -> Option<ModuleData> {
        self.file
            .classes
            .values()
            .flat_map(|c| c.fields.iter())
            .find_map(|f| match &f.initial_value {
                Some(FieldValue::ModuleData(md)) if md.source_offset == offset => Some(md.clone()),
                _ => None,
            })
    }

    // -- emission -----------------------------------------------------------

    fn emit(mut self, source_name: &str) -> Vec<u8> {
        let mut out = Vec::new();
        let _ = write!(out, "# source binary: {source_name}\n\n");
        out.extend_from_slice(b"# ====================\n# LITERALS\n\n");

        self.classify_field_offsets();

        // GetRecords runs before GetLiteralArrays upstream and registers
        // strings during instruction processing; build the program first.
        let mut records: BTreeMap<Vec<u8>, PaRecord> = BTreeMap::new();
        let mut functions: BTreeMap<Vec<u8>, PaFunction> = BTreeMap::new();
        self.build_records_and_functions(&mut records, &mut functions);

        let (regular, modules) = self.collect_literal_tables();
        for (key, offset) in &regular {
            out.extend_from_slice(key);
            out.push(b' ');
            if let Some(array) = self
                .file
                .literal_array_offsets
                .get(offset)
                .and_then(|idx| self.file.literal_arrays.get(*idx as usize))
            {
                out.extend_from_slice(&self.serialize_literal_array(&array.values));
            }
            out.push(b'\n');
        }
        for (key, md) in &modules {
            out.extend_from_slice(key);
            out.push(b' ');
            self.serialize_module_array(md, &mut out);
            out.push(b'\n');
        }
        out.push(b'\n');

        out.extend_from_slice(b"# ====================\n# RECORDS\n\n");
        for record in records.values() {
            self.emit_record(record, &mut out);
        }

        out.extend_from_slice(b"# ====================\n# METHODS\n\n");
        for function in functions.values() {
            self.emit_function(function, &mut out);
        }

        out.extend_from_slice(b"# ====================\n# STRING\n\n");
        for (offset, bytes) in &self.strings {
            let _ = write!(out, "[offset:0x{offset:x}, name_value:");
            out.extend_from_slice(bytes);
            out.extend_from_slice(b"]\n");
        }
        out
    }

    fn build_records_and_functions(
        &mut self,
        records: &mut BTreeMap<Vec<u8>, PaRecord>,
        functions: &mut BTreeMap<Vec<u8>, PaFunction>,
    ) {
        for (desc, class) in &self.file.classes {
            let record_name = self.class_name(*desc);
            // GetRecord processes methods even for duplicate record names;
            // only the record TABLE insert is first-wins.
            if !class.is_external {
                for method in &class.methods {
                    let mut fun = self.build_function(*desc, class, method, true);
                    let sig = fun.signature();
                    if functions.contains_key(&sig) {
                        // Duplicate signature: strings already registered,
                        // the function itself is dropped (upstream emplace).
                        continue;
                    }
                    self.build_annotations(&mut fun, method);
                    functions.insert(sig, fun);
                }
            }
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
            records.entry(record_name.clone()).or_insert(PaRecord {
                name: record_name,
                language,
                is_external,
                fields,
            });
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
                if let Some(v) = field_u32_offset(field) {
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
        let _ = write!(out, "{{ {} [\n", md.records.len());
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

    fn emit_function(&self, fun: &PaFunction, out: &mut Vec<u8>) {
        for (name, elements) in &fun.annotations {
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
        let _ = writeln!(out, ".language {}", language_str(fun.language));
        let _ = write!(out, ".function {} ", fun.return_type);
        out.extend_from_slice(&fun.name);
        out.push(b'(');
        for (i, p) in fun.params.iter().enumerate() {
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
        if fun.is_static {
            attrs.push("static");
        }
        if fun.is_external {
            attrs.push("external");
        }
        if fun.is_ctor {
            attrs.push("ctor");
        }
        if fun.is_cctor {
            attrs.push("cctor");
        }
        if !attrs.is_empty() {
            out.extend_from_slice(b" <");
            out.extend_from_slice(attrs.join(", ").as_bytes());
            out.push(b'>');
        }
        out.extend_from_slice(b" {\n");
        for (label, insn) in &fun.insns {
            if let Some(label) = label {
                out.extend_from_slice(label.as_bytes());
                out.extend_from_slice(b":\n");
            }
            out.push(b'\t');
            out.extend_from_slice(insn);
            out.push(b'\n');
        }
        if fun.trailing_empty_label {
            out.extend_from_slice(b":\n");
        }
        if !fun.catches.is_empty() {
            out.push(b'\n');
            for catch in &fun.catches {
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
        out.extend_from_slice(b"}\n\n");
    }
}

/// First-name-wins label allocation (upstream `LabelTable` insert).
fn alloc_label(labels: &mut BTreeMap<u32, String>, idx: u32, name: String) -> String {
    labels.entry(idx).or_insert(name).clone()
}

/// The 13.x/24.x literal-table assignment for a model: the `(index,
/// offset)` pairs the emitter's collection would print, in index order.
/// Exposed to the parser (crate-internal): the method ORDER within a class
/// is invisible in pandasm text (functions print in signature-sorted
/// order), so the parser may sort methods to make this assignment reproduce
/// the parsed LITERALS keys. Pure query — no emission behavior change.
pub(crate) fn simulated_literal_assignment(file: &File) -> Vec<(u32, u32)> {
    if file.version <= LAST_HEADER_LITERAL_VERSION {
        return Vec::new();
    }
    let mut emitter = Emitter::new(file);
    emitter.classify_field_offsets();
    let (regular, modules) = emitter.collect_literal_tables();
    let mut out: Vec<(u32, u32)> = Vec::new();
    let read_key = |key: &[u8], out: &mut Vec<(u32, u32)>| {
        if let Some((index, offset, _)) = parse::parse_literal_key(key) {
            out.push((index, offset));
        }
    };
    for key in regular.keys() {
        read_key(key, &mut out);
    }
    for key in modules.keys() {
        read_key(key, &mut out);
    }
    out.sort_by_key(|(index, _)| *index);
    out
}

/// The u32 wire value of a field's initial value, abstracting over the
/// structural module/scope/phase models (which keep the source offset).
fn field_u32_offset(field: &crate::model::Field) -> Option<u32> {
    match &field.initial_value {
        Some(FieldValue::I32(v)) => u32::try_from(*v).ok(),
        Some(FieldValue::ModuleData(md)) => Some(md.source_offset),
        Some(FieldValue::LiteralArrayRef(off)) => Some(*off),
        Some(FieldValue::ModuleRequestPhase(p)) => Some(p.source_offset),
        // Upstream prints the offset (disassembler.cpp GetMetadataFieldValue
        // SetValue) and only EXCLUDES it from module-literal classification
        // — classify_field_offsets drops it by field name.
        Some(FieldValue::TypeSummaryOffset(off)) => Some(*off),
        _ => None,
    }
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
mod tests {
    //! The no-panic rule: the emitter must render ANY File model, including
    //! hand-built ones with dangling references (placeholders, never panic).
    use super::*;
    use crate::model::{MethodBody, ParamAnnotations};
    use crate::types::AccessFlags;
    use std::collections::{BTreeMap, HashMap};

    fn empty_file() -> File {
        File {
            version: Version::new(12, 0, 6, 0),
            checksum: 0,
            size: 0,
            file_type: crate::FileType::Dynamic,
            strings: crate::StringPool::default(),
            classes: BTreeMap::new(),
            literal_arrays: Vec::new(),
            literal_array_offsets: HashMap::new(),
            literal_array_header_offsets: Vec::new(),
            entity_map: HashMap::new(),
            string_raw_bytes: HashMap::new(),
        }
    }

    #[test]
    fn empty_file_emits_sections() {
        let out = emit_file(&empty_file(), "empty.abc");
        let text = String::from_utf8(out).expect("empty file output is UTF-8");
        assert!(
            text.starts_with("# source binary: empty.abc\n\n# ====================\n# LITERALS\n")
        );
        assert!(text.contains("# RECORDS\n"));
        assert!(text.contains("# METHODS\n"));
        assert!(text.ends_with("# STRING\n\n"));
    }

    #[test]
    fn dangling_references_render_placeholders() {
        let mut file = empty_file();
        let desc = file.strings.get_or_intern("L_GLOBAL;");
        let name = file.strings.get_or_intern("f");
        // A body whose entity references resolve to nothing.
        let mut body = MethodBody {
            num_vregs: 1,
            num_args: 0,
            bytecodes: Vec::new(),
            entity_offsets: HashMap::new(),
            try_blocks: Vec::new(),
            ic_size: None,
        };
        // Decode two real instructions via abcd-isa and add a dangling
        // entity offset by hand.
        let (bytes, _) = abcd_isa::encode(&[
            abcd_isa::insn::Ldai::new(abcd_isa::Imm(7)),
            abcd_isa::insn::Returnundefined::new(),
        ])
        .expect("encode smoke body");
        body.bytecodes = abcd_isa::decode(&bytes)
            .expect("decode smoke body")
            .into_iter()
            .map(|(bc, _)| bc)
            .collect();
        let method = Method {
            name,
            offset: 0x100,
            access_flags: AccessFlags::STATIC,
            function_kind: crate::types::FunctionKind::None,
            source_lang: SourceLang::EcmaScript,
            is_external: false,
            return_type: None,
            arg_types: Vec::new(),
            body: Some(body),
            annotations: crate::model::Annotations::default(),
            param_annotations: ParamAnnotations::default(),
            debug: None,
        };
        file.classes.insert(
            desc,
            Class {
                descriptor: desc,
                name: desc,
                access_flags: AccessFlags::empty(),
                source_lang: SourceLang::EcmaScript,
                source_file: None,
                is_external: false,
                super_class: None,
                interfaces: Vec::new(),
                methods: vec![method],
                fields: Vec::new(),
                annotations: crate::model::Annotations::default(),
            },
        );
        let out = emit_file(&file, "dangling.abc");
        let text = String::from_utf8_lossy(&out);
        assert!(text.contains(".function any f() <static> {"), "{text}");
        assert!(text.contains("\tldai 0x7\n"), "{text}");
    }
}
