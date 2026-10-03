//! Pandasm whole-file text parser: `.pa` bytes → [`File`] model.
//!
//! This is the inverse of the emitter in [`super`] and the foundation of
//! `abcd asm`. The input is raw bytes (valid pandasm is not necessarily
//! UTF-8 — string contents print unescaped), so all scanning is byte-level
//! and every failure is a structured [`ParseError`] carrying a 1-based line
//! number and context; the parser never panics on arbitrary input.
//!
//! # What the text carries (and what it cannot)
//!
//! The emitter prints layout offsets in three places — LITERALS entry keys
//! (`{index} 0x{offset}`), STRING entries (`[offset:0x{offset}, …]`), and
//! u32 field values (`= 0x{offset}`) — and the parser PRESERVES them in the
//! model (`literal_array_offsets` / `literal_array_header_offsets` /
//! `entity_offsets` / `entity_map`), so `parse_file` → `emit_file` is a
//! byte-exact round trip. A fresh `encode` re-lays the file out (the
//! vendored writer assigns offsets in its own order; the original string
//! order is not recoverable from the text), so the binary leg is validated
//! under layout-offset normalization by the corpus gate
//! (`tests/file-isa/pandasm_asm.rs`).
//!
//! # Disambiguation rules (from the upstream assembler)
//!
//! `assembler/assembly-parser.cpp` + `templates/opcode_parsing.h.erb`:
//! operand typing is OPCODE-DRIVEN — each mnemonic's operand list has fixed
//! kinds (register / immediate / float immediate / label / string / method
//! / literal array) taken from the vendored ISA, so a quoted token in
//! string position is a string, `name:(sig)` in method position is a method
//! reference, `{ … }` in literal position is a literal array. Register
//! counting follows upstream too (`ParseOperandVreg` /
//! `ParseResetFunctionLabelsAndParams`): `num_vregs = max(v-index) + 1`
//! and `a`-registers are shifted by that base after the body is parsed.
//!
//! Raw string contents (no escaping anywhere in the format) are delimited
//! with the file's own STRING section as the oracle set — the same trick
//! the dis-side comparison harness used with the decoded string pool,
//! except here the oracle comes from the text itself (upstream `ark_asm`
//! never sees the disassembler's sections; our emitter prints them, so the
//! round-trip parser exploits them).

use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::OnceLock;

use abcd_isa::{BytecodeFlags, EntityKind, Version};

use crate::file::RAW_ID_SENTINEL;
use crate::model::{
    Annotation, AnnotationElem, AnnotationValue, Annotations, CatchBlock, Class, Field, FieldValue,
    File, LiteralArray, Method, MethodBody, ModuleData, ModuleRecord, ModuleRequestPhase,
    ParamAnnotations, TryBlock,
};
use crate::types::{AccessFlags, FunctionKind, SourceLang, Type};
use crate::{LiteralArrayIdx, LiteralValue, StringId, StringPool};

use super::insn_ctor;

/// A structured parse failure: 1-based line number plus context.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    /// 1-based line number in the input (0 when not line-attributable).
    pub line: usize,
    /// Human-readable context (offending token, expectation, …).
    pub message: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "pandasm parse error at line {}: {}",
            self.line, self.message
        )
    }
}

impl std::error::Error for ParseError {}

/// One typed operand value on its way to a [`abcd_isa::Bytecode`]; the
/// generated constructor table in [`super::insn_ctor`] consumes these.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RawOperand {
    /// Virtual register (frame slot).
    R(u16),
    /// Plain immediate (float immediates carry the value bits).
    I(i64),
    /// Constant-pool entity reference (method-local raw index).
    E(u32),
    /// Jump target instruction index.
    L(u32),
}

/// The file version [`parse_file`] assumes when the caller does not say
/// otherwise (pandasm text carries no version). This matches upstream
/// `ark_asm`, which always writes the current format version.
pub const DEFAULT_VERSION: Version = Version::new(24, 0, 0, 0);

/// Last file version whose header carries the literal-array index table
/// (mirrors the emitter's constant).
const LAST_HEADER_LITERAL_VERSION: Version = Version::new(12, 0, 6, 0);

/// Parse pandasm text into a [`File`] model, assuming [`DEFAULT_VERSION`].
///
/// The text carries no file version; callers that know it (e.g. from the
/// input's provenance) should use [`parse_file_with_version`] — the version
/// selects the literal-table layout (≤12.0.6.0 header table vs 13.x/24.x
/// collector) and whether method protos carry types.
pub fn parse_file(text: &[u8]) -> Result<File, ParseError> {
    parse_file_with_version(text, DEFAULT_VERSION)
}

/// [`parse_file`] with an explicit target file version.
pub fn parse_file_with_version(text: &[u8], version: Version) -> Result<File, ParseError> {
    Parser::new(version).run(text)
}

// ---------------------------------------------------------------------------
// Byte-level helpers
// ---------------------------------------------------------------------------

fn trim_start(mut b: &[u8]) -> &[u8] {
    while let [first, rest @ ..] = b {
        if first.is_ascii_whitespace() {
            b = rest;
        } else {
            break;
        }
    }
    b
}

fn trim_end(mut b: &[u8]) -> &[u8] {
    while let [rest @ .., last] = b {
        if last.is_ascii_whitespace() {
            b = rest;
        } else {
            break;
        }
    }
    b
}

fn trim(b: &[u8]) -> &[u8] {
    trim_end(trim_start(b))
}

fn err<T>(line: usize, message: impl Into<String>) -> Result<T, ParseError> {
    Err(ParseError {
        line,
        message: message.into(),
    })
}

fn lossy(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

// ---------------------------------------------------------------------------
// MUTF-8 → String with the N72 lossy class
// ---------------------------------------------------------------------------

/// Strict MUTF-8 decode: `C0 80` → NUL, CESU-8 surrogate pairs combine into
/// astral characters. `None` on any malformed sequence, including LONE
/// surrogates — exactly the case the vendored MUTF-8→UTF-16 conversion
/// fails on (the decode-side lossy class, N72).
fn mutf8_decode(bytes: &[u8]) -> Option<String> {
    let mut out: Vec<u16> = Vec::new();
    let mut i = 0usize;
    while i < bytes.len() {
        let b = bytes[i];
        if b == 0 {
            return None; // MUTF-8 never carries a raw NUL
        } else if b < 0x80 {
            out.push(b as u16);
            i += 1;
        } else if b & 0xE0 == 0xC0 {
            let b2 = *bytes.get(i + 1)?;
            if b2 & 0xC0 != 0x80 {
                return None;
            }
            out.push((((b & 0x1F) as u16) << 6) | (b2 & 0x3F) as u16);
            i += 2;
        } else if b & 0xF0 == 0xE0 {
            let b2 = *bytes.get(i + 1)?;
            let b3 = *bytes.get(i + 2)?;
            if b2 & 0xC0 != 0x80 || b3 & 0xC0 != 0x80 {
                return None;
            }
            let cp = (((b & 0x0F) as u32) << 12) | (((b2 & 0x3F) as u32) << 6) | (b3 & 0x3F) as u32;
            if (0xD800..0xDC00).contains(&cp) {
                // High surrogate: try to pair with a following low one
                // (CESU-8 astral encoding, lossless).
                let (n2, n3, n4) = (*bytes.get(i + 3)?, *bytes.get(i + 4)?, *bytes.get(i + 5)?);
                if n2 & 0xF0 != 0xE0 || n3 & 0xC0 != 0x80 || n4 & 0xC0 != 0x80 {
                    return None; // lone high surrogate: the lossy class
                }
                let lo =
                    (((n2 & 0x0F) as u32) << 12) | (((n3 & 0x3F) as u32) << 6) | (n4 & 0x3F) as u32;
                if !(0xDC00..0xE000).contains(&lo) {
                    return None; // high surrogate followed by a non-low: lossy
                }
                out.push(cp as u16);
                out.push(lo as u16);
                i += 6;
                continue;
            } else if (0xDC00..0xE000).contains(&cp) {
                return None; // lone low surrogate: the lossy class
            }
            out.push(cp as u16);
            i += 3;
        } else if b & 0xF8 == 0xF0 {
            let b2 = *bytes.get(i + 1)?;
            let b3 = *bytes.get(i + 2)?;
            let b4 = *bytes.get(i + 3)?;
            if b2 & 0xC0 != 0x80 || b3 & 0xC0 != 0x80 || b4 & 0xC0 != 0x80 {
                return None;
            }
            let cp = (((b & 0x07) as u32) << 18)
                | (((b2 & 0x3F) as u32) << 12)
                | (((b3 & 0x3F) as u32) << 6)
                | (b4 & 0x3F) as u32;
            let ch = char::from_u32(cp)?;
            let mut buf = [0u16; 2];
            out.extend_from_slice(&*ch.encode_utf16(&mut buf));
            i += 4;
        } else {
            return None;
        }
    }
    String::from_utf16(&out).ok()
}

// ---------------------------------------------------------------------------
// The string oracle (raw contents may contain quotes/commas/newlines)
// ---------------------------------------------------------------------------

/// Candidate string contents used to delimit raw-printed strings. Seeded
/// from the STRING section (exhaustive for instruction string operands)
/// and extended with every literal-array string as it is parsed. `multi`
/// holds the quote/newline-bearing contents, sorted, for prefix probes.
#[derive(Default)]
struct Oracle {
    set: HashSet<Vec<u8>>,
    multi: Vec<Vec<u8>>,
}

impl Oracle {
    fn add(&mut self, content: &[u8]) {
        if !self.set.insert(content.to_vec()) {
            return;
        }
        if content.contains(&b'"') || content.contains(&b'\n') {
            let idx = self.multi.partition_point(|s| s.as_slice() < content);
            self.multi.insert(idx, content.to_vec());
        }
    }

    fn contains(&self, content: &[u8]) -> bool {
        self.set.contains(content)
    }

    /// Does any quote/newline-bearing oracle string start with `prefix`?
    fn has_string_prefix(&self, prefix: &[u8]) -> bool {
        let idx = self.multi.partition_point(|s| s.as_slice() < prefix);
        idx < self.multi.len() && self.multi[idx].starts_with(prefix)
    }
}

/// Split a pandasm operand list at top-level commas, respecting
/// `()`/`{}`/`[]` groups and oracle-delimited raw strings (ported from the
/// dis-side comparison harness). Returns the tokens, the total matched
/// string-content bytes (the longest-match signal for multi-line
/// disambiguation) and the offset of the last string's opening quote.
/// `None` = an opened string has no valid close yet (the caller appends the
/// next physical line).
fn split_operands(rest: &[u8], oracle: &Oracle) -> Option<(Vec<Vec<u8>>, usize, Option<usize>)> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut cur: Vec<u8> = Vec::new();
    let mut string_bytes = 0usize;
    let mut last_open = None;
    let mut depth = 0i32;
    let mut i = 0usize;
    while i < rest.len() {
        let b = rest[i];
        if b == b'"' {
            // Oracle close: latest `"` whose content is an oracle entry,
            // followed by a separator or the end of the text.
            let mut close = None;
            for j in (i + 1..rest.len()).rev() {
                if rest[j] != b'"' {
                    continue;
                }
                if !oracle.contains(&rest[i + 1..j]) {
                    continue;
                }
                let mut k = j + 1;
                while k < rest.len() && rest[k].is_ascii_whitespace() {
                    k += 1;
                }
                if k == rest.len() || matches!(rest[k], b',' | b']' | b'}') {
                    close = Some(j);
                    break;
                }
            }
            let close = match close {
                Some(c) => c,
                None => {
                    // Not an oracle string (or the lossy class, whose
                    // contents ARE in the oracle — this fallback covers
                    // hand-written text): next quote on the same physical
                    // line; a newline means the string spans lines — signal
                    // the caller to extend.
                    match rest[i + 1..].iter().position(|&b| b == b'"') {
                        Some(off) if !rest[i + 1..i + 1 + off].contains(&b'\n') => i + 1 + off,
                        _ => return None,
                    }
                }
            };
            cur.push(b'"');
            cur.extend_from_slice(&rest[i + 1..close]);
            cur.push(b'"');
            string_bytes += close - (i + 1);
            last_open = Some(i);
            i = close + 1;
            continue;
        }
        match b {
            b'{' | b'[' | b'(' => {
                depth += 1;
                cur.push(b);
            }
            b'}' | b']' | b')' => {
                depth -= 1;
                cur.push(b);
            }
            b',' if depth == 0 => {
                let token = trim(&cur);
                if !token.is_empty() {
                    out.push(token.to_vec());
                }
                cur.clear();
            }
            _ => cur.push(b),
        }
        i += 1;
    }
    let token = trim(&cur);
    if !token.is_empty() {
        out.push(token.to_vec());
    }
    Some((out, string_bytes, last_open))
}

// ---------------------------------------------------------------------------
// Instruction operand spec (runtime-discovered from the vendored ISA)
// ---------------------------------------------------------------------------

/// How one operand position of a mnemonic is typed (upstream
/// `opcode_parsing.h.erb`: opcode-driven operand kinds).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OpKind {
    Reg,
    Imm,
    /// Float immediate (the FLOAT flag): the text is a decimal rendering.
    ImmFloat,
    Label,
    Str,
    Method,
    LiteralArr,
}

struct InsnSpec {
    kinds: Vec<OpKind>,
}

/// The spec table, built once by constructing a zero-valued instance of
/// every mnemonic and reading the operand kinds / FLOAT flag back.
fn insn_specs() -> &'static HashMap<&'static str, InsnSpec> {
    static SPECS: OnceLock<HashMap<&'static str, InsnSpec>> = OnceLock::new();
    SPECS.get_or_init(|| {
        let mut map = HashMap::new();
        for &mnemonic in insn_ctor::MNEMONICS {
            let Some(bc) = insn_ctor::dummy(mnemonic) else {
                continue;
            };
            let float = bc.has_flag(BytecodeFlags::FLOAT);
            let kinds = bc
                .operands()
                .iter()
                .map(|op| match *op {
                    abcd_isa::Operand::Reg(_) => OpKind::Reg,
                    abcd_isa::Operand::Imm(_) => {
                        if float {
                            OpKind::ImmFloat
                        } else {
                            OpKind::Imm
                        }
                    }
                    abcd_isa::Operand::Label(_) => OpKind::Label,
                    abcd_isa::Operand::Entity(kind, _) => match kind {
                        EntityKind::StringId => OpKind::Str,
                        EntityKind::MethodId => OpKind::Method,
                        EntityKind::LiteralarrayId => OpKind::LiteralArr,
                    },
                })
                .collect();
            map.insert(mnemonic, InsnSpec { kinds });
        }
        map
    })
}

// ---------------------------------------------------------------------------
// Syntactic (unresolved) parse tree
// ---------------------------------------------------------------------------

/// A literal-array item as parsed; method references still carry the
/// printed NAME (resolved to entity offsets once the method table exists).
#[derive(Clone, Debug, PartialEq)]
enum PaItem {
    Bool(bool),
    Int(u32),
    Int8(u8),
    Float(f32),
    Double(f64),
    Str(Vec<u8>),
    EtsImplements(Vec<u8>),
    Method(Vec<u8>),
    GeneratorMethod(Vec<u8>),
    Getter(Vec<u8>),
    Setter(Vec<u8>),
    AsyncGeneratorMethod(Vec<u8>),
    Accessor(u8),
    MethodAffiliate(u16),
    NullValue(u8),
    LitOffset(u32),
    LitBufferIndex(u32),
    BuiltinType(u8),
}

/// One LITERALS section entry.
#[derive(Clone, Debug)]
enum PaLiteral {
    /// `{ N [ item, … ]}` (empty vec = the empty/all-TAGVALUE array, which
    /// prints as nothing after the key).
    Regular(Vec<PaItem>),
    /// A module-record blob's multi-line rendering.
    Module(PaModule),
}

#[derive(Clone, Debug, Default)]
struct PaModule {
    requests: Vec<Vec<u8>>,
    records: Vec<PaModuleRecord>,
}

#[derive(Clone, Debug)]
enum PaModuleRecord {
    RegularImport {
        local: Vec<u8>,
        import: Vec<u8>,
        request: Vec<u8>,
    },
    NamespaceImport {
        local: Vec<u8>,
        request: Vec<u8>,
    },
    LocalExport {
        local: Vec<u8>,
        export: Vec<u8>,
    },
    IndirectExport {
        export: Vec<u8>,
        import: Vec<u8>,
        request: Vec<u8>,
    },
    StarExport {
        request: Vec<u8>,
    },
}

#[derive(Clone, Debug)]
struct PaField {
    ty: Vec<u8>,
    name: Vec<u8>,
    /// The ` = …` value text (hex `0x…` or a float rendering).
    value: Option<Vec<u8>>,
    line: usize,
}

#[derive(Clone, Debug)]
struct PaRecord {
    name: Vec<u8>,
    lang: SourceLang,
    external: bool,
    fields: Vec<PaField>,
}

/// An annotation element as parsed; string values still carry raw bytes
/// (interned at build time).
#[derive(Clone, Debug)]
enum PaElemValue {
    U32(u32),
    Bool(bool),
    F64(f64),
    Str(Vec<u8>),
}

#[derive(Clone, Debug)]
struct PaAnnotation {
    /// Descriptor bytes WITH the trailing `;` restored.
    descriptor: Vec<u8>,
    elements: Vec<(Vec<u8>, PaElemValue)>,
}

/// One operand token, typed at finalization time via the mnemonic's spec.
#[derive(Clone, Debug)]
enum PaOp {
    /// `vN`.
    VReg(u16),
    /// `aN` — shifted by `num_vregs` once the body is fully parsed
    /// (upstream `ParseResetFunctionLabelsAndParams`).
    AReg(u16),
    Imm(i64),
    Float(f64),
    Str(Vec<u8>),
    /// Full `name:(sig)` bytes of a method reference.
    MethodSig(Vec<u8>),
    /// Raw `{ … }` text of an inline literal array (empty = the
    /// prints-as-nothing empty array).
    Literal(Vec<u8>),
    LabelRef(Vec<u8>),
}

#[derive(Clone, Debug)]
struct PaInsn {
    mnemonic: Vec<u8>,
    ops: Vec<PaOp>,
    line: usize,
}

#[derive(Clone, Debug)]
struct PaCatch {
    /// Empty = `.catchall`.
    record: Vec<u8>,
    try_begin: Vec<u8>,
    try_end: Vec<u8>,
    catch_begin: Vec<u8>,
    /// Empty = omitted (zero-length handler).
    catch_end: Vec<u8>,
    line: usize,
}

#[derive(Debug)]
struct PaFunction {
    annotations: Vec<PaAnnotation>,
    lang: SourceLang,
    /// Full (record-prefixed, ctor-mangled) name as printed.
    name: Vec<u8>,
    /// Parameter type tokens as printed (`any`, record names, …).
    params: Vec<Vec<u8>>,
    is_static: bool,
    is_external: bool,
    is_ctor: bool,
    is_cctor: bool,
    /// Whether the header carried a return type (body-bearing methods do).
    has_body: bool,
    insns: Vec<PaInsn>,
    /// Label name → instruction index (or one-past-the-end).
    labels: HashMap<Vec<u8>, u32>,
    /// A bare `:` line was seen: some label binds one past the end.
    trailing_empty_label: bool,
    catches: Vec<PaCatch>,
    line: usize,
}

// ---------------------------------------------------------------------------
// The parser
// ---------------------------------------------------------------------------

/// Base of the synthetic offset space for entities the text references by
/// name (methods, catch records). Real file offsets stay far below this in
/// practice, so synthetic and text-carried offsets never collide.
const SYNTHETIC_OFFSET_BASE: u32 = 0x4000_0000;

struct Parser {
    version: Version,
    oracle: Oracle,
    /// String pool with the N72 lossy-string side table.
    strings: StringPool,
    string_raw_bytes: HashMap<String, Box<[u8]>>,
    /// STRING section: content → offsets (file order = offset order).
    string_offsets: HashMap<Vec<u8>, Vec<u32>>,
    /// Regular literal entries in print order: (key index, key offset,
    /// items, raw value text).
    regular: Vec<(u32, u32, Vec<PaItem>, Vec<u8>)>,
    /// Raw value text → (key offsets, round-robin cursor). The text of an
    /// inline literal operand does not say WHICH of several same-content
    /// arrays it references (the disassembler prints content inline), so
    /// references are distributed round-robin — each original offset is
    /// referenced at least once (an unreferenced array would not be in the
    /// 13.x/24.x listing at all).
    lit_by_text: HashMap<Vec<u8>, (Vec<u32>, usize)>,
    /// Key offset → position in `regular`.
    lit_by_offset: HashMap<u32, usize>,
    /// Module blob offset → parsed module data.
    modules: HashMap<u32, PaModule>,
    /// Offsets named by `lit_offset:` items (nested references are exact —
    /// they pin WHICH same-content array a parent nests).
    nested_targets: HashSet<u32>,
    /// Every LITERALS key index → offset (module arrays included), for the
    /// ≤12 header-table reconstruction.
    key_index_to_offset: Vec<(u32, u32)>,
    records: Vec<PaRecord>,
    functions: Vec<PaFunction>,
}

impl Parser {
    fn new(version: Version) -> Self {
        Parser {
            version,
            oracle: Oracle::default(),
            strings: StringPool::default(),
            string_raw_bytes: HashMap::new(),
            string_offsets: HashMap::new(),
            regular: Vec::new(),
            lit_by_text: HashMap::new(),
            lit_by_offset: HashMap::new(),
            modules: HashMap::new(),
            nested_targets: HashSet::new(),
            key_index_to_offset: Vec::new(),
            records: Vec::new(),
            functions: Vec::new(),
        }
    }

    /// Intern raw MUTF-8 bytes, mirroring `file::intern_string` (the N72
    /// lossy class: lone-surrogate contents intern their lossy form and
    /// record the raw bytes; colliding raw forms get a sentinel identity).
    fn intern(&mut self, raw: &[u8]) -> Result<StringId, ParseError> {
        if let Some(text) = mutf8_decode(raw) {
            return Ok(self.strings.get_or_intern(&text));
        }
        let text = String::from_utf8_lossy(raw).into_owned();
        enum Case {
            Duplicate,
            First,
            Collision,
        }
        let case = match self.string_raw_bytes.get(&text) {
            Some(existing) if existing.as_ref() == raw => Case::Duplicate,
            Some(_) => Case::Collision,
            None => Case::First,
        };
        let identity = match case {
            Case::Duplicate => text,
            Case::First => {
                self.string_raw_bytes
                    .insert(text.clone(), raw.to_vec().into_boxed_slice());
                text
            }
            Case::Collision => {
                let mut disambiguated = text.clone();
                disambiguated.push(RAW_ID_SENTINEL);
                for b in raw {
                    disambiguated.push_str(&format!("{b:02x}"));
                }
                match self.string_raw_bytes.get(&disambiguated) {
                    Some(existing) => {
                        if existing.as_ref() != raw {
                            return err(
                                0,
                                "disambiguated lossy-string identity collision".to_owned(),
                            );
                        }
                    }
                    None => {
                        if self.strings.get(disambiguated.as_str()).is_some() {
                            return err(
                                0,
                                "genuine string collides with a lossy identity".to_owned(),
                            );
                        }
                        self.string_raw_bytes
                            .insert(disambiguated.clone(), raw.to_vec().into_boxed_slice());
                    }
                }
                disambiguated
            }
        };
        Ok(self.strings.get_or_intern(&identity))
    }

    // -- top level -----------------------------------------------------------

    fn run(mut self, text: &[u8]) -> Result<File, ParseError> {
        let sections = split_sections(text)?;
        // The STRING section is the disambiguation oracle: parse it first
        // even though it is last in the file.
        self.parse_string_section(sections.strings.0, sections.strings.1)?;
        self.parse_literals_section(sections.literals.0, sections.literals.1)?;
        self.parse_records_section(sections.records.0, sections.records.1)?;
        self.parse_methods_section(sections.methods.0, sections.methods.1)?;
        self.build()
    }

    // -- STRING section -------------------------------------------------------

    fn parse_string_section(&mut self, body: &[u8], base: usize) -> Result<(), ParseError> {
        // Entries start at line-initial `[offset:0x`; contents are raw and
        // may span lines, so an entry runs to the next entry's line start.
        let mut starts = Vec::new();
        let mut pos = 0usize;
        while pos < body.len() {
            if body[pos..].starts_with(b"[offset:0x") {
                starts.push(pos);
            }
            match body[pos..].iter().position(|&b| b == b'\n') {
                Some(nl) => pos += nl + 1,
                None => break,
            }
        }
        for (i, &start) in starts.iter().enumerate() {
            let end = starts.get(i + 1).copied().unwrap_or(body.len());
            let entry = trim_end(&body[start..end]);
            let line = base + body[..start].iter().filter(|&&b| b == b'\n').count();
            let Some(sep) = entry
                .windows(b", name_value:".len())
                .position(|w| w == b", name_value:")
            else {
                return err(line, "malformed STRING entry (missing `, name_value:`)");
            };
            let hex = &entry[b"[offset:0x".len()..sep];
            let Ok(offset) = u32::from_str_radix(std::str::from_utf8(hex).unwrap_or(""), 16) else {
                return err(line, "malformed STRING entry offset");
            };
            if entry.last() != Some(&b']') {
                return err(line, "malformed STRING entry (missing `]`)");
            }
            let content = &entry[sep + b", name_value:".len()..entry.len() - 1];
            self.oracle.add(content);
            self.string_offsets
                .entry(content.to_vec())
                .or_default()
                .push(offset);
        }
        Ok(())
    }

    // -- LITERALS section -----------------------------------------------------

    fn parse_literals_section(&mut self, body: &[u8], base: usize) -> Result<(), ParseError> {
        let lines: Vec<&[u8]> = body.split(|&b| b == b'\n').collect();
        let mut i = 0usize;
        while i < lines.len() {
            let line = lines[i];
            if trim(line).is_empty() {
                i += 1;
                continue;
            }
            let Some((index, offset, value_start)) = parse_literal_key(line) else {
                return err(base + i, "malformed LITERALS entry key");
            };
            // Accumulate the value across physical lines until the
            // oracle-aware scanner finds the closing `]}`.
            let mut acc = line[value_start..].to_vec();
            let mut j = i + 1;
            let value = loop {
                if value_is_complete(&acc, &self.oracle) {
                    break acc;
                }
                // Module arrays can run to hundreds of records; the only
                // bound needed is the section length itself.
                if j >= lines.len() {
                    return err(base + i, "unterminated LITERALS entry value");
                }
                acc.push(b'\n');
                acc.extend_from_slice(lines[j]);
                j += 1;
            };
            let value = trim_end(&value);
            let literal = if value.is_empty() {
                // The empty (or all-TAGVALUE) array prints as nothing.
                PaLiteral::Regular(Vec::new())
            } else if value.starts_with(b"{") {
                self.parse_literal_value(value, base + i)?
            } else {
                return err(base + i, "malformed LITERALS entry value");
            };
            self.key_index_to_offset.push((index, offset));
            match &literal {
                PaLiteral::Regular(items) => {
                    self.lit_by_text
                        .entry(value.to_vec())
                        .or_default()
                        .0
                        .push(offset);
                    self.lit_by_offset.insert(offset, self.regular.len());
                    self.regular
                        .push((index, offset, items.clone(), value.to_vec()));
                    // Newly-seen literal strings join the oracle for the
                    // rest of the section (and for instruction parsing);
                    // lit_offset targets pin their exact offsets.
                    let strings: Vec<Vec<u8>> = items
                        .iter()
                        .filter_map(|item| match item {
                            PaItem::Str(s) | PaItem::EtsImplements(s) => Some(s.clone()),
                            _ => None,
                        })
                        .collect();
                    for s in strings {
                        self.oracle.add(&s);
                    }
                    for item in items {
                        if let PaItem::LitOffset(off) = item {
                            self.nested_targets.insert(*off);
                        }
                    }
                }
                PaLiteral::Module(md) => {
                    self.modules.insert(offset, md.clone());
                }
            }
            i = j;
        }
        Ok(())
    }

    /// Parse one literal-array value text (`{ N [ item, … ]}` or the module
    /// block form). `value` is the complete (possibly multi-line) text.
    fn parse_literal_value(&self, value: &[u8], line: usize) -> Result<PaLiteral, ParseError> {
        // Module block: `{ N [\n\tMODULE_REQUEST_ARRAY: {` — the marker
        // only appears at a line start in the module rendering (a string
        // content would have to contain a newline followed by exactly this
        // text — vanishingly unlikely, and it would fail loudly below).
        if value
            .windows(25)
            .any(|w| w == b"\n\tMODULE_REQUEST_ARRAY: {")
        {
            return self.parse_module_value(value, line).map(PaLiteral::Module);
        }
        let Some(open) = value.iter().position(|&b| b == b'[') else {
            return err(line, "literal array missing `[`");
        };
        if !value.ends_with(b"]}") || open + 1 > value.len() - 2 {
            return err(line, "literal array missing `]}`");
        }
        let items_text = &value[open + 1..value.len() - 2];
        let (tokens, _, _) =
            split_operands(items_text, &self.oracle).ok_or_else(|| ParseError {
                line,
                message: "unterminated string in literal array".to_owned(),
            })?;
        let mut items = Vec::with_capacity(tokens.len());
        for token in tokens {
            items.push(self.parse_literal_item(&token, line)?);
        }
        Ok(PaLiteral::Regular(items))
    }

    /// Parse one tagged literal item (`tag:value`).
    fn parse_literal_item(&self, token: &[u8], line: usize) -> Result<PaItem, ParseError> {
        let Some(colon) = token.iter().position(|&b| b == b':') else {
            return err(0, "literal item missing `tag:`");
        };
        let tag = &token[..colon];
        let value = &token[colon + 1..];
        let quoted = |v: &[u8]| -> Result<Vec<u8>, ParseError> {
            if v.len() >= 2 && v[0] == b'"' && v[v.len() - 1] == b'"' {
                Ok(v[1..v.len() - 1].to_vec())
            } else {
                err(line, "literal string item is not quoted")
            }
        };
        let int = |v: &[u8]| -> Result<i64, ParseError> {
            let text = std::str::from_utf8(v).map_err(|_| ParseError {
                line,
                message: "literal integer is not ASCII".to_owned(),
            })?;
            text.parse::<i64>().map_err(|_| ParseError {
                line,
                message: format!("literal integer `{text}` does not parse"),
            })
        };
        let float = |v: &[u8]| -> Result<f64, ParseError> {
            let text = std::str::from_utf8(v).map_err(|_| ParseError {
                line,
                message: "literal float is not ASCII".to_owned(),
            })?;
            text.parse::<f64>().map_err(|_| ParseError {
                line,
                message: format!("literal float `{text}` does not parse"),
            })
        };
        Ok(match tag {
            b"u1" => PaItem::Bool(int(value)? != 0),
            b"i8" => PaItem::Int8(int(value)? as i8 as u8),
            b"i32" => PaItem::Int(int(value)? as u32),
            b"f32" => PaItem::Float(float(value)? as f32),
            b"f64" => PaItem::Double(float(value)?),
            b"string" => PaItem::Str(quoted(value)?),
            b"ets_implements" => PaItem::EtsImplements(quoted(value)?),
            b"method" => PaItem::Method(value.to_vec()),
            b"generator_method" => PaItem::GeneratorMethod(value.to_vec()),
            b"getter" => PaItem::Getter(value.to_vec()),
            b"setter" => PaItem::Setter(value.to_vec()),
            b"async_generator_method" => PaItem::AsyncGeneratorMethod(value.to_vec()),
            b"accessor" => PaItem::Accessor(int(value)? as i16 as u8),
            b"method_affiliate" => PaItem::MethodAffiliate(int(value)? as u16),
            b"null_value" => PaItem::NullValue(int(value)? as i16 as u8),
            b"lit_offset" => {
                let text = std::str::from_utf8(value).map_err(|_| ParseError {
                    line,
                    message: "lit_offset is not ASCII".to_owned(),
                })?;
                let hex = text.strip_prefix("0x").unwrap_or(text);
                let off = u32::from_str_radix(hex, 16).map_err(|_| ParseError {
                    line,
                    message: format!("lit_offset `{text}` does not parse"),
                })?;
                PaItem::LitOffset(off)
            }
            b"lit_index" => PaItem::LitBufferIndex(int(value)? as u32),
            b"builtin_type" => PaItem::BuiltinType(int(value)? as i16 as u8),
            other => {
                return err(
                    line,
                    format!("unknown literal tag `{}`", String::from_utf8_lossy(other)),
                );
            }
        })
    }

    /// Parse a module-array value block (`{ N [\n\tMODULE_REQUEST_ARRAY…`).
    fn parse_module_value(&self, value: &[u8], line: usize) -> Result<PaModule, ParseError> {
        let mut md = PaModule::default();
        let lines: Vec<&[u8]> = value.split(|&b| b == b'\n').collect();
        let mut i = 0usize;
        // Skip `{ N [`.
        while i < lines.len() && !lines[i].ends_with(b"[") {
            i += 1;
        }
        if i >= lines.len() {
            return err(line, "module array missing `[`");
        }
        i += 1;
        if i >= lines.len() || trim(lines[i]) != b"MODULE_REQUEST_ARRAY: {" {
            return err(line, "module array missing MODULE_REQUEST_ARRAY");
        }
        i += 1;
        while i < lines.len() && trim(lines[i]) != b"};" {
            let l = trim(lines[i]);
            // `{i} : {request},`
            let Some(colon) = l.iter().position(|&b| b == b':') else {
                return err(line, "malformed module request line");
            };
            let req = trim(&l[colon + 1..]);
            let req = req.strip_suffix(b",").unwrap_or(req);
            md.requests.push(req.to_vec());
            i += 1;
        }
        i += 1; // skip `};`
        while i < lines.len() {
            let l = trim(lines[i]);
            if l == b"]}" {
                break;
            }
            if l.is_empty() {
                i += 1;
                continue;
            }
            let Some(rest) = l.strip_prefix(b"ModuleTag: ") else {
                return err(line, "malformed module record line");
            };
            let Some(rest) = rest.strip_suffix(b";") else {
                return err(line, "module record line missing `;`");
            };
            md.records.push(parse_module_record(rest, line)?);
            i += 1;
        }
        Ok(md)
    }

    // -- RECORDS section ------------------------------------------------------

    fn parse_records_section(&mut self, body: &[u8], base: usize) -> Result<(), ParseError> {
        let lines: Vec<&[u8]> = body.split(|&b| b == b'\n').collect();
        let mut i = 0usize;
        let mut pending_lang = SourceLang::EcmaScript;
        while i < lines.len() {
            let line = lines[i];
            if trim(line).is_empty() {
                i += 1;
                continue;
            }
            if let Some(lang) = line.strip_prefix(b".language ") {
                pending_lang = parse_language(trim(lang)).ok_or_else(|| ParseError {
                    line: base + i,
                    message: format!("unknown language `{}`", String::from_utf8_lossy(lang)),
                })?;
                i += 1;
                continue;
            }
            let Some(rest) = line.strip_prefix(b".record ") else {
                return err(base + i, "expected `.record` or `.language`");
            };
            if let Some(name) = rest.strip_suffix(b" <external>") {
                self.records.push(PaRecord {
                    name: name.to_vec(),
                    lang: pending_lang,
                    external: true,
                    fields: Vec::new(),
                });
                i += 1;
                continue;
            }
            let Some(name) = rest.strip_suffix(b" {") else {
                return err(base + i, "malformed `.record` header");
            };
            let mut fields = Vec::new();
            i += 1;
            while i < lines.len() && lines[i] != b"}" {
                let fline = lines[i];
                if trim(fline).is_empty() {
                    i += 1;
                    continue;
                }
                let Some(fl) = fline.strip_prefix(b"\t") else {
                    return err(base + i, "record field line must be tab-indented");
                };
                fields.push(self.parse_field_line(fl, base + i)?);
                i += 1;
            }
            if i >= lines.len() {
                return err(base + i, "unterminated `.record` body");
            }
            i += 1; // skip `}`
            self.records.push(PaRecord {
                name: name.to_vec(),
                lang: pending_lang,
                external: false,
                fields,
            });
        }
        Ok(())
    }

    /// Parse one field line (`type name[ = value]`). The name prints raw
    /// (the emitter basename-strips paths); the value introducer is the
    /// LAST ` = `.
    fn parse_field_line(&self, line: &[u8], line_no: usize) -> Result<PaField, ParseError> {
        let Some(sp) = line.iter().position(|&b| b == b' ') else {
            return err(line_no, "malformed field line (no type/name split)");
        };
        let ty = line[..sp].to_vec();
        let rest = &line[sp + 1..];
        let (name, value) = match rest.windows(3).rposition(|w| w == b" = ") {
            Some(eq) => (
                trim_end(&rest[..eq]).to_vec(),
                Some(trim_start(&rest[eq + 3..]).to_vec()),
            ),
            None => (trim_end(rest).to_vec(), None),
        };
        Ok(PaField {
            ty,
            name,
            value,
            line: line_no,
        })
    }

    // -- METHODS section ------------------------------------------------------

    fn parse_methods_section(&mut self, body: &[u8], base: usize) -> Result<(), ParseError> {
        let lines: Vec<&[u8]> = body.split(|&b| b == b'\n').collect();
        let mut i = 0usize;
        while i < lines.len() {
            let line = match lines.get(i) {
                Some(l) => l,
                None => break,
            };
            if trim(line).is_empty() {
                i += 1;
                continue;
            }
            // Annotation blocks: `Name:` followed by tab-indented elements.
            let mut annotations = Vec::new();
            while i < lines.len()
                && !lines[i].starts_with(b".")
                && !lines[i].starts_with(b"\t")
                && !lines[i].starts_with(b" ")
                && lines[i].ends_with(b":")
            {
                let name = &lines[i][..lines[i].len() - 1];
                let mut descriptor = name.to_vec();
                descriptor.push(b';');
                i += 1;
                let mut elements = Vec::new();
                while i < lines.len() && lines[i].starts_with(b"\t") {
                    elements.push(self.parse_annotation_element(lines[i], base + i)?);
                    i += 1;
                }
                annotations.push(PaAnnotation {
                    descriptor,
                    elements,
                });
            }
            let Some(lang) = lines.get(i).and_then(|l| l.strip_prefix(b".language ")) else {
                return err(base + i, "expected `.language` before `.function`");
            };
            let lang = parse_language(trim(lang)).ok_or_else(|| ParseError {
                line: base + i,
                message: format!("unknown language `{}`", String::from_utf8_lossy(lang)),
            })?;
            i += 1;
            let Some(fline) = lines.get(i) else {
                return err(base + i, "unexpected end of METHODS section");
            };
            let mut fun = self.parse_function_header(fline, base + i)?;
            fun.annotations = annotations;
            fun.lang = lang;
            i += 1;
            // Body: instructions / labels / directives until `}`.
            loop {
                let Some(&line) = lines.get(i) else {
                    return err(fun.line, "unterminated `.function` body");
                };
                if line == b"}" {
                    i += 1;
                    break;
                }
                if trim(line).is_empty() {
                    i += 1;
                    continue;
                }
                if line[0] == b'\t' || line[0] == b' ' {
                    i = self.parse_instruction(&lines, i, &mut fun, base)?;
                    continue;
                }
                if line == b":" {
                    fun.trailing_empty_label = true;
                    i += 1;
                    continue;
                }
                if line.starts_with(b".catch") {
                    fun.catches.push(parse_catch_line(line, base + i)?);
                    i += 1;
                    continue;
                }
                if line.ends_with(b":") && !line.starts_with(b".") {
                    fun.labels
                        .insert(line[..line.len() - 1].to_vec(), fun.insns.len() as u32);
                    i += 1;
                    continue;
                }
                return err(base + i, "unexpected line in function body");
            }
            self.functions.push(fun);
        }
        Ok(())
    }

    /// `.function {ret} {name}({params})[ <attrs>] {` — the name may
    /// contain spaces (accessor mangling) and the return type may be EMPTY
    /// (code-less methods print a double space).
    fn parse_function_header(&self, line: &[u8], line_no: usize) -> Result<PaFunction, ParseError> {
        let Some(rest) = line.strip_prefix(b".function ") else {
            return err(line_no, "expected `.function`");
        };
        let (rest, has_body) = if let Some(r) = rest.strip_prefix(b" ") {
            (r, false)
        } else {
            (rest, true)
        };
        let Some(paren) = rest.iter().position(|&b| b == b'(') else {
            return err(line_no, "`.function` missing parameter list");
        };
        let head = &rest[..paren];
        let name: Vec<u8> = if has_body {
            // Drop the return-type token; the remainder is the name.
            match head.iter().position(|&b| b == b' ') {
                Some(sp) => head[sp + 1..].to_vec(),
                None => return err(line_no, "`.function` missing name"),
            }
        } else {
            trim_end(head).to_vec()
        };
        let Some(close) = rest.iter().rposition(|&b| b == b')') else {
            return err(line_no, "`.function` missing `)`");
        };
        if close <= paren {
            return err(line_no, "`.function` has `)` before `(`");
        }
        let params_text = &rest[paren + 1..close];
        let mut params = Vec::new();
        if !trim(params_text).is_empty() {
            for p in params_text.split(|&b| b == b',') {
                let p = trim(p);
                // `<type> a<i>` — the type is the first token.
                let Some(sp) = p.iter().position(|&b| b == b' ') else {
                    return err(line_no, "malformed parameter");
                };
                params.push(p[..sp].to_vec());
            }
        }
        let tail = trim(&rest[close + 1..]);
        let Some(tail) = tail.strip_suffix(b"{") else {
            return err(line_no, "`.function` missing `{`");
        };
        let tail = trim_end(tail);
        let mut fun = PaFunction {
            annotations: Vec::new(),
            lang: SourceLang::EcmaScript,
            name,
            params,
            is_static: false,
            is_external: false,
            is_ctor: false,
            is_cctor: false,
            has_body,
            insns: Vec::new(),
            labels: HashMap::new(),
            trailing_empty_label: false,
            catches: Vec::new(),
            line: line_no,
        };
        if !tail.is_empty() {
            let Some(attrs) = tail.strip_prefix(b"<").and_then(|t| t.strip_suffix(b">")) else {
                return err(line_no, "malformed `.function` attributes");
            };
            for attr in attrs.split(|&b| b == b',') {
                match trim(attr) {
                    b"static" => fun.is_static = true,
                    b"external" => fun.is_external = true,
                    b"ctor" => fun.is_ctor = true,
                    b"cctor" => fun.is_cctor = true,
                    other => {
                        return err(
                            line_no,
                            format!(
                                "unknown function attribute `{}`",
                                String::from_utf8_lossy(other)
                            ),
                        );
                    }
                }
            }
        }
        Ok(fun)
    }

    /// Parse one annotation element line (`\t{tag} {name} { {value} }`).
    fn parse_annotation_element(
        &self,
        line: &[u8],
        line_no: usize,
    ) -> Result<(Vec<u8>, PaElemValue), ParseError> {
        let l = trim(line);
        let Some(open) = l.iter().position(|&b| b == b'{') else {
            return err(line_no, "annotation element missing `{`");
        };
        if !l.ends_with(b"}") {
            return err(line_no, "annotation element missing `}`");
        }
        let head = trim_end(&l[..open]);
        let value = trim(&l[open + 1..l.len() - 1]);
        let Some(sp) = head.iter().position(|&b| b == b' ') else {
            return err(line_no, "annotation element missing name");
        };
        let tag = &head[..sp];
        let name = head[sp + 1..].to_vec();
        let parsed = match tag {
            b"u32" => {
                let text = std::str::from_utf8(value).unwrap_or("");
                let hex = text.strip_prefix("0x").unwrap_or(text);
                let v = u32::from_str_radix(hex, 16).map_err(|_| ParseError {
                    line: line_no,
                    message: format!("annotation u32 `{text}` does not parse"),
                })?;
                PaElemValue::U32(v)
            }
            b"u1" => PaElemValue::Bool(value == b"1"),
            b"f64" => {
                let text = std::str::from_utf8(value).unwrap_or("");
                let v = text.parse::<f64>().map_err(|_| ParseError {
                    line: line_no,
                    message: format!("annotation f64 `{text}` does not parse"),
                })?;
                PaElemValue::F64(v)
            }
            b"panda.String" => {
                if value.len() < 2 || value[0] != b'"' || value[value.len() - 1] != b'"' {
                    return err(line_no, "annotation string is not quoted");
                }
                PaElemValue::Str(value[1..value.len() - 1].to_vec())
            }
            other => {
                return err(
                    line_no,
                    format!(
                        "unknown annotation element tag `{}`",
                        String::from_utf8_lossy(other)
                    ),
                );
            }
        };
        Ok((name, parsed))
    }

    /// Parse one instruction starting at physical line `i`, with the
    /// bounded multi-line lookahead for raw strings that span lines.
    /// Returns the next unconsumed line index.
    fn parse_instruction(
        &mut self,
        lines: &[&[u8]],
        i: usize,
        fun: &mut PaFunction,
        base: usize,
    ) -> Result<usize, ParseError> {
        /// Multi-line string lookahead bound (physical lines).
        const MAX_MULTILINE: usize = 64;
        let mut acc = trim_start(lines[i]).to_vec();
        let mut best: Option<(usize, Vec<u8>, usize)> = None;
        let limit = (i + MAX_MULTILINE).min(lines.len());
        let mut j = i + 1;
        loop {
            match insn_ops_parse(&acc, &self.oracle) {
                Some((string_bytes, last_open)) => {
                    let better = match &best {
                        None => true,
                        Some((_, _, prev)) => string_bytes > *prev,
                    };
                    if better {
                        best = Some((j, acc.clone(), string_bytes));
                    }
                    let tail = last_open.map(|o| &acc[o + 1..]);
                    if j >= limit || !tail.is_some_and(|t| self.oracle.has_string_prefix(t)) {
                        break;
                    }
                }
                None => {
                    let open = acc.iter().rposition(|&b| b == b'"');
                    if j >= limit
                        || !open.is_some_and(|o| self.oracle.has_string_prefix(&acc[o + 1..]))
                    {
                        break;
                    }
                }
            }
            if j >= lines.len() {
                break;
            }
            acc.push(b'\n');
            acc.extend_from_slice(lines[j]);
            j += 1;
        }
        let Some((end, acc, _)) = best else {
            return err(base + i, "unterminated string in instruction");
        };
        let split = acc
            .iter()
            .position(|b| b.is_ascii_whitespace())
            .unwrap_or(acc.len());
        let mnemonic = acc[..split].to_vec();
        let (tokens, _, _) =
            split_operands(&acc[split..], &self.oracle).ok_or_else(|| ParseError {
                line: base + i,
                message: "lookahead-resolved instruction failed to re-split".to_owned(),
            })?;
        let mut ops = Vec::with_capacity(tokens.len());
        for token in &tokens {
            ops.push(parse_operand_token(token, base + i)?);
        }
        fun.insns.push(PaInsn {
            mnemonic,
            ops,
            line: base + i,
        });
        Ok(end)
    }

    // -- model construction ---------------------------------------------------

    fn build(mut self) -> Result<File, ParseError> {
        let mut b = BuildCtx::default();
        // Detach the section data so the interning loops below can take
        // `&mut self` while iterating.
        let records = std::mem::take(&mut self.records);
        let functions = std::mem::take(&mut self.functions);

        // Records → classes (fields resolved below; methods attached when
        // functions are built). Descriptors intern in BYTE-SORTED order —
        // the file's class-index order, which is also the decode-time
        // interning order; the 13.x/24.x literal-table index assignment
        // (emitter's unordered_set simulation) depends on the class
        // iteration order that interning order induces.
        //
        // `_GLOBAL` (a system record) is never printed; synthesize it up
        // front when any function's name matches no printed record prefix,
        // so it takes its sorted place among the descriptors.
        let needs_global = functions
            .iter()
            .any(|f| record_prefix_of(&f.name, &records).is_none());
        let mut descriptors: Vec<Vec<u8>> =
            records.iter().map(|r| record_descriptor(&r.name)).collect();
        if needs_global {
            descriptors.push(b"L_GLOBAL;".to_vec());
        }
        descriptors.sort();
        descriptors.dedup();
        for desc in &descriptors {
            let sid = self.intern(desc)?;
            if desc == b"L_GLOBAL;" {
                b.global_class = Some(sid);
            }
            b.class_by_descriptor.insert(desc.clone(), sid);
        }
        let mut record_classes: Vec<StringId> = Vec::new();
        for rec in &records {
            let desc = record_descriptor(&rec.name);
            let sid = b.class_by_descriptor[&desc];
            record_classes.push(sid);
            b.class_by_record_name.insert(rec.name.clone(), sid);
        }

        // Fields (classification mirrors decode_field_at: phase by name,
        // module/scope blobs by record descriptor).
        let mut class_fields: HashMap<StringId, Vec<Field>> = HashMap::new();
        for (rec, &desc_sid) in records.iter().zip(&record_classes) {
            let mut fields = Vec::new();
            for pf in &rec.fields {
                fields.push(self.build_field(rec, desc_sid, pf, &mut b)?);
            }
            class_fields.insert(desc_sid, fields);
        }

        // Method shells: owner record (longest name prefix), demangled
        // name, synthetic offset, signature registration.
        for fun in &functions {
            let (owner_name, bare) = split_owner(&fun.name, &b.class_by_record_name);
            let bare = demangle(bare, fun.is_ctor, fun.is_cctor);
            let owner_sid = match owner_name {
                Some(name) => b.class_by_record_name[name],
                // System-type owners are never printed; unprefixed
                // functions belong to the global record (synthesized above).
                None => match b.global_class {
                    Some(sid) => sid,
                    None => return err(fun.line, "function owner record missing".to_owned()),
                },
            };
            let name_sid = self.intern(&bare)?;
            let offset = b.next_synthetic_offset();
            let sig = function_signature(&fun.name, &fun.params);
            // First signature wins (the emitter dedups; the text holds each
            // signature at most once anyway).
            b.method_by_signature.entry(sig).or_insert(offset);
            b.method_by_name.entry(bare).or_insert(offset);
            b.entity_map.insert(offset, name_sid);
            b.method_shells.push(MethodShell {
                owner: owner_sid,
                name_sid,
                offset,
            });
        }

        // Rank-order same-content literal groups by the printed LITERALS
        // index (the 13.x/24.x index order approximates the original
        // first-appearance order), keeping lit_offset-pinned offsets last —
        // they are referenced exactly by their nesting parent.
        {
            let mut rank: HashMap<u32, u32> = HashMap::new();
            let mut sorted = self.key_index_to_offset.clone();
            sorted.sort_by_key(|(index, _)| *index);
            for (i, (_, off)) in sorted.iter().enumerate() {
                rank.insert(*off, i as u32);
            }
            let nested = std::mem::take(&mut self.nested_targets);
            for (offsets, _) in self.lit_by_text.values_mut() {
                offsets.sort_by_key(|off| {
                    (
                        nested.contains(off),
                        rank.get(off).copied().unwrap_or(u32::MAX),
                    )
                });
            }
            self.nested_targets = nested;
        }

        // Bodies.
        let mut methods_by_owner: HashMap<StringId, Vec<Method>> = HashMap::new();
        for (idx, fun) in functions.iter().enumerate() {
            let shell = MethodShell {
                owner: b.method_shells[idx].owner,
                name_sid: b.method_shells[idx].name_sid,
                offset: b.method_shells[idx].offset,
            };
            let method = self.build_method(fun, &shell, &mut b)?;
            methods_by_owner
                .entry(shell.owner)
                .or_default()
                .push(method);
        }

        // Literal arrays → model values (needs the method name table).
        // `regular` is detached; `lit_by_offset` indices refer to it.
        let regular = std::mem::take(&mut self.regular);
        let mut literal_arrays: Vec<LiteralArray> = Vec::new();
        let mut literal_array_offsets: HashMap<u32, u32> = HashMap::new();
        for (_, offset, items, _) in &regular {
            let values = self.resolve_literal_items(items, &b)?;
            literal_array_offsets.insert(*offset, literal_arrays.len() as u32);
            literal_arrays.push(LiteralArray { values });
        }

        // 13/24 scope-names arrays are not printed: synthesize an empty
        // array for every LiteralArrayRef target that has no key.
        let scope_targets: Vec<u32> = class_fields
            .values()
            .flat_map(|fields| fields.iter())
            .filter_map(|f| match f.initial_value {
                Some(FieldValue::LiteralArrayRef(off)) => Some(off),
                _ => None,
            })
            .collect();
        for off in scope_targets {
            if let std::collections::hash_map::Entry::Vacant(e) = literal_array_offsets.entry(off) {
                e.insert(literal_arrays.len() as u32);
                literal_arrays.push(LiteralArray { values: Vec::new() });
            }
        }

        // The ≤12 header literal table: key index → key offset, with gaps
        // (excluded phase-blob slots) filled from the parsed phase fields.
        let mut literal_array_header_offsets = Vec::new();
        if self.version <= LAST_HEADER_LITERAL_VERSION && !self.key_index_to_offset.is_empty() {
            let max_index = self
                .key_index_to_offset
                .iter()
                .map(|(i, _)| *i)
                .max()
                .unwrap_or(0);
            let mut table = vec![0u32; max_index as usize + 1];
            let mut known = vec![false; max_index as usize + 1];
            for (index, offset) in &self.key_index_to_offset {
                table[*index as usize] = *offset;
                known[*index as usize] = true;
            }
            // Gap fill: phase-blob offsets in field order.
            let phase_offsets: Vec<u32> = class_fields
                .values()
                .flat_map(|fields| fields.iter())
                .filter_map(|f| match &f.initial_value {
                    Some(FieldValue::ModuleRequestPhase(p)) => Some(p.source_offset),
                    _ => None,
                })
                .collect();
            let mut phase_iter = phase_offsets.iter();
            for slot in known.iter_mut().zip(table.iter_mut()) {
                if !*slot.0 {
                    *slot.1 = phase_iter.next().copied().unwrap_or(0);
                }
            }
            literal_array_header_offsets = table;
        }

        // Assemble classes in record order, then the global class (if it
        // was synthesized and is not already present).
        let mut classes: BTreeMap<StringId, Class> = BTreeMap::new();
        for (rec, &desc_sid) in records.iter().zip(&record_classes) {
            let class = Class {
                descriptor: desc_sid,
                name: desc_sid,
                access_flags: AccessFlags::empty(),
                source_lang: rec.lang,
                source_file: None,
                is_external: rec.external,
                super_class: None,
                interfaces: Vec::new(),
                methods: methods_by_owner.remove(&desc_sid).unwrap_or_default(),
                fields: class_fields.remove(&desc_sid).unwrap_or_default(),
                annotations: Annotations::default(),
            };
            classes.insert(desc_sid, class);
        }
        if let Some(global_sid) = b.global_class {
            classes.entry(global_sid).or_insert_with(|| Class {
                descriptor: global_sid,
                name: global_sid,
                access_flags: AccessFlags::empty(),
                source_lang: SourceLang::EcmaScript,
                source_file: None,
                is_external: false,
                super_class: None,
                interfaces: Vec::new(),
                methods: methods_by_owner.remove(&global_sid).unwrap_or_default(),
                fields: Vec::new(),
                annotations: Annotations::default(),
            });
        }

        let mut file = File {
            version: self.version,
            checksum: 0,
            size: 0,
            file_type: crate::FileType::Dynamic,
            strings: self.strings,
            classes,
            literal_arrays,
            literal_array_offsets,
            literal_array_header_offsets,
            entity_map: b.entity_map,
            string_raw_bytes: self.string_raw_bytes,
        };
        // 13.x/24.x: the LITERALS index assignment is a pure function of
        // the (textually invisible) per-class method order and of which
        // source offset each same-content literal operand referenced.
        // Recover both (see fix_literal_assignment).
        if self.version > LAST_HEADER_LITERAL_VERSION && !self.key_index_to_offset.is_empty() {
            let mut target: Vec<(u32, u32)> = self.key_index_to_offset.clone();
            target.sort_by_key(|(index, _)| *index);
            fix_literal_assignment(&mut file, &target);
        }
        Ok(file)
    }

    /// Build one field; the value classification mirrors `decode_field_at`
    /// (phase by field name, module/scope blobs by record descriptor).
    fn build_field(
        &mut self,
        _rec: &PaRecord,
        desc_sid: StringId,
        pf: &PaField,
        b: &mut BuildCtx,
    ) -> Result<Field, ParseError> {
        let field_type = parse_type(&mut |raw| self.intern(raw), &pf.ty)?;
        let name_sid = self.intern(&pf.name)?;
        let offset = b.next_synthetic_offset();
        b.entity_map.insert(offset, name_sid);
        let descriptor = self.strings.resolve(desc_sid).unwrap_or("").to_owned();
        let value_text = pf.value.as_deref();
        let initial_value = match value_text {
            None => None,
            Some(text) => {
                let name_str = lossy(&pf.name);
                if name_str == crate::TYPE_SUMMARY_OFFSET_FIELD {
                    // Mirrors encode's hard error (N8 revised): assembling a
                    // raw nested offset would dangle — the write side never
                    // emits it.
                    return err(
                        pf.line,
                        "typeSummaryOffset fields are not representable".to_owned(),
                    );
                }
                let u32_value = |_p: &Parser| -> Result<u32, ParseError> {
                    let text = std::str::from_utf8(text).map_err(|_| ParseError {
                        line: pf.line,
                        message: "field value is not ASCII".to_owned(),
                    })?;
                    let hex = text.strip_prefix("0x").unwrap_or(text);
                    u32::from_str_radix(hex, 16).map_err(|_| ParseError {
                        line: pf.line,
                        message: format!("field value `{text}` does not parse as hex"),
                    })
                };
                if name_str == crate::MODULE_REQUEST_PHASE_FIELD && field_type == Type::U32 {
                    let off = u32_value(self)?;
                    Some(FieldValue::ModuleRequestPhase(ModuleRequestPhase {
                        source_offset: off,
                        // The phase flags are never printed; one zero flag
                        // per module request of the file's first module
                        // blob (the flags are text-invisible either way).
                        flags: self
                            .modules
                            .values()
                            .next()
                            .map(|m| vec![0u8; m.requests.len()])
                            .unwrap_or_default(),
                    }))
                } else if descriptor == crate::ES_MODULE_RECORD_DESCRIPTOR
                    && field_type == Type::U32
                {
                    let off = u32_value(self)?;
                    let pa_module = self.modules.get(&off).cloned();
                    let md = match pa_module {
                        Some(ref pa) => self.build_module_data(off, pa)?,
                        None => {
                            // 13.x/24.x: the disassembler never prints the
                            // module blob for these records (the field-name
                            // driven collector misses it), so the content
                            // is unrecoverable — an empty blob keeps the
                            // model structurally valid for encode.
                            ModuleData {
                                source_offset: off,
                                requests: Vec::new(),
                                records: Vec::new(),
                            }
                        }
                    };
                    Some(FieldValue::ModuleData(md))
                } else if descriptor == crate::ES_SCOPE_NAMES_RECORD_DESCRIPTOR
                    && field_type == Type::U32
                {
                    Some(FieldValue::LiteralArrayRef(u32_value(self)?))
                } else {
                    match field_type {
                        Type::U32 | Type::U8 | Type::Bool => {
                            let v = u32_value(self)?;
                            Some(FieldValue::I32(v as i32))
                        }
                        Type::F64 => {
                            let text = std::str::from_utf8(text).map_err(|_| ParseError {
                                line: pf.line,
                                message: "field f64 value is not ASCII".to_owned(),
                            })?;
                            let v = text.parse::<f64>().map_err(|_| ParseError {
                                line: pf.line,
                                message: format!("field f64 `{text}` does not parse"),
                            })?;
                            Some(FieldValue::F64(v))
                        }
                        // The emitter only prints U32/U8/F64/Bool values.
                        _ => {
                            return err(
                                pf.line,
                                "field initial value on a type the emitter never prints".to_owned(),
                            );
                        }
                    }
                }
            }
        };
        Ok(Field {
            name: name_sid,
            offset,
            field_type,
            access_flags: AccessFlags::empty(),
            is_external: false,
            initial_value,
            annotations: Annotations::default(),
        })
    }

    /// PaModule → ModuleData with interned strings; `module_request:` names
    /// resolve to request indices (first match — identical names print
    /// identically either way).
    fn build_module_data(&mut self, offset: u32, pa: &PaModule) -> Result<ModuleData, ParseError> {
        let mut requests = Vec::with_capacity(pa.requests.len());
        for req in &pa.requests {
            requests.push(self.intern(req)?);
        }
        let request_idx = |name: &[u8]| -> Result<u32, ParseError> {
            pa.requests
                .iter()
                .position(|r| r == name)
                .map(|p| p as u32)
                .ok_or_else(|| ParseError {
                    line: 0,
                    message: format!(
                        "module_request `{}` not in the request array",
                        String::from_utf8_lossy(name)
                    ),
                })
        };
        let mut records = Vec::with_capacity(pa.records.len());
        for rec in &pa.records {
            let r = match rec {
                PaModuleRecord::RegularImport {
                    local,
                    import,
                    request,
                } => ModuleRecord::RegularImport {
                    local_name: self.intern(local)?,
                    import_name: self.intern(import)?,
                    module_request_idx: request_idx(request)?,
                },
                PaModuleRecord::NamespaceImport { local, request } => {
                    ModuleRecord::NamespaceImport {
                        local_name: self.intern(local)?,
                        module_request_idx: request_idx(request)?,
                    }
                }
                PaModuleRecord::LocalExport { local, export } => ModuleRecord::LocalExport {
                    local_name: self.intern(local)?,
                    export_name: self.intern(export)?,
                },
                PaModuleRecord::IndirectExport {
                    export,
                    import,
                    request,
                } => ModuleRecord::IndirectExport {
                    export_name: self.intern(export)?,
                    import_name: self.intern(import)?,
                    module_request_idx: request_idx(request)?,
                },
                PaModuleRecord::StarExport { request } => ModuleRecord::StarExport {
                    module_request_idx: request_idx(request)?,
                },
            };
            records.push(r);
        }
        Ok(ModuleData {
            source_offset: offset,
            requests,
            records,
        })
    }

    /// Resolve parsed literal items to model values (method names →
    /// synthetic method offsets, `lit_offset` → table indices).
    fn resolve_literal_items(
        &mut self,
        items: &[PaItem],
        b: &BuildCtx,
    ) -> Result<Vec<LiteralValue>, ParseError> {
        let mut out = Vec::with_capacity(items.len());
        for item in items {
            let v = match item {
                PaItem::Bool(v) => LiteralValue::Bool(*v),
                PaItem::Int(v) => LiteralValue::Integer(*v),
                PaItem::Int8(v) => LiteralValue::Integer8(*v),
                PaItem::Float(v) => LiteralValue::Float(*v),
                PaItem::Double(v) => LiteralValue::Double(*v),
                PaItem::Str(s) => LiteralValue::String(self.intern(s)?),
                PaItem::EtsImplements(s) => LiteralValue::EtsImplements(self.intern(s)?),
                PaItem::Method(name) => LiteralValue::Method(self.method_ref(name, b)?),
                PaItem::GeneratorMethod(name) => {
                    LiteralValue::GeneratorMethod(self.method_ref(name, b)?)
                }
                PaItem::Getter(name) => LiteralValue::Getter(self.method_ref(name, b)?),
                PaItem::Setter(name) => LiteralValue::Setter(self.method_ref(name, b)?),
                PaItem::AsyncGeneratorMethod(name) => {
                    LiteralValue::AsyncGeneratorMethod(self.method_ref(name, b)?)
                }
                PaItem::Accessor(v) => LiteralValue::Accessor(*v),
                PaItem::MethodAffiliate(v) => LiteralValue::MethodAffiliate(*v),
                PaItem::NullValue(v) => LiteralValue::NullValue(*v),
                PaItem::LitOffset(off) => {
                    // Decode rewrites the payload to a table index when the
                    // target decoded; mirror that here.
                    let idx = self
                        .lit_by_offset
                        .get(off)
                        .copied()
                        .ok_or_else(|| ParseError {
                            line: 0,
                            message: format!("lit_offset 0x{off:x} names no literal array"),
                        })?;
                    LiteralValue::LiteralArray(LiteralArrayIdx(idx as u32))
                }
                PaItem::LitBufferIndex(v) => LiteralValue::LiteralBufferIndex(LiteralArrayIdx(*v)),
                PaItem::BuiltinType(v) => LiteralValue::BuiltinTypeIndex(*v),
            };
            out.push(v);
        }
        Ok(out)
    }

    /// Method name (bare bytes) → the method's synthetic entity offset.
    fn method_ref(&mut self, name: &[u8], b: &BuildCtx) -> Result<u32, ParseError> {
        b.method_by_name
            .get(name)
            .copied()
            .ok_or_else(|| ParseError {
                line: 0,
                message: format!(
                    "literal method reference `{}` names no defined function",
                    String::from_utf8_lossy(name)
                ),
            })
    }

    /// Build one method (body finalization: registers, labels, entities,
    /// try blocks — then ISA construction).
    fn build_method(
        &mut self,
        fun: &PaFunction,
        shell: &MethodShell,
        b: &mut BuildCtx,
    ) -> Result<Method, ParseError> {
        // Access flags: the corpus prints `static` only; ctor/cctor carry
        // no extra model flags here (the name carries the semantics).
        let mut access_flags = AccessFlags::empty();
        if fun.is_static {
            access_flags |= AccessFlags::STATIC;
        }

        let num_args = fun.params.len().saturating_sub(usize::from(!fun.is_static)) as u32;

        let annotations = self.build_annotations(fun)?;

        let body = if fun.has_body && !fun.is_external {
            Some(self.build_body(fun, b)?)
        } else {
            if !fun.insns.is_empty() || !fun.catches.is_empty() {
                return err(
                    fun.line,
                    "code-less function (no return type) with a body".to_owned(),
                );
            }
            None
        };

        // Proto types: ≤12.0.6.0 protos carry no shorty (decode yields
        // None/[]); 13.x/24.x es2abc protos are all-`any` (Tagged).
        let (return_type, arg_types) = if self.version <= LAST_HEADER_LITERAL_VERSION {
            (None, Vec::new())
        } else if fun.has_body {
            (Some(Type::Tagged), vec![Type::Tagged; num_args as usize])
        } else {
            (None, Vec::new())
        };

        Ok(Method {
            name: shell.name_sid,
            offset: shell.offset,
            access_flags,
            function_kind: FunctionKind::None,
            source_lang: fun.lang,
            is_external: fun.is_external,
            return_type,
            arg_types,
            body,
            annotations,
            param_annotations: ParamAnnotations::default(),
            debug: None,
        })
    }

    fn build_annotations(&mut self, fun: &PaFunction) -> Result<Annotations, ParseError> {
        let mut compile_time = Vec::new();
        for pa in &fun.annotations {
            let descriptor = self.intern(&pa.descriptor)?;
            let mut elements = Vec::new();
            for (name, value) in &pa.elements {
                let name = self.intern(name)?;
                let value = match value {
                    PaElemValue::U32(v) => AnnotationValue::U32(*v),
                    PaElemValue::Bool(v) => AnnotationValue::Bool(*v),
                    PaElemValue::F64(v) => AnnotationValue::F64(*v),
                    PaElemValue::Str(raw) => AnnotationValue::String(self.intern(raw)?),
                };
                elements.push(AnnotationElem { name, value });
            }
            compile_time.push(Annotation {
                class_descriptor: descriptor,
                elements,
            });
        }
        Ok(Annotations {
            compile_time,
            ..Annotations::default()
        })
    }

    /// Finalize one function body: the upstream register rule
    /// (`num_vregs = max(v-index) + 1`, `a`-regs shifted by it), label
    /// resolution, entity registration, and ISA construction.
    fn build_body(&mut self, fun: &PaFunction, b: &mut BuildCtx) -> Result<MethodBody, ParseError> {
        let num_vregs = fun
            .insns
            .iter()
            .flat_map(|insn| insn.ops.iter())
            .filter_map(|op| match op {
                PaOp::VReg(v) => Some(*v as u32 + 1),
                _ => None,
            })
            .max()
            .unwrap_or(0);

        let insn_count = fun.insns.len() as u32;
        let mut entity_offsets: HashMap<(EntityKind, u32), u32> = HashMap::new();
        let mut next_raw: HashMap<EntityKind, u32> = HashMap::new();
        let mut bytecodes = Vec::with_capacity(fun.insns.len());

        for insn in &fun.insns {
            let mnemonic = std::str::from_utf8(&insn.mnemonic).map_err(|_| ParseError {
                line: insn.line,
                message: "instruction mnemonic is not ASCII".to_owned(),
            })?;
            let spec = insn_specs().get(mnemonic).ok_or_else(|| ParseError {
                line: insn.line,
                message: format!("unknown instruction `{mnemonic}`"),
            })?;
            // Align tokens to the spec. An empty literal-array operand
            // prints as NOTHING (the token was dropped by the splitter), so
            // a LiteralArr position with a non-literal/exhausted token gets
            // an implicit empty literal.
            let mut raw_ops: Vec<RawOperand> = Vec::with_capacity(spec.kinds.len());
            let mut ops_iter = insn.ops.iter().peekable();
            for (pos, kind) in spec.kinds.iter().enumerate() {
                let op = if *kind == OpKind::LiteralArr
                    && !matches!(ops_iter.peek(), Some(PaOp::Literal(_)))
                {
                    &PaOp::Literal(Vec::new())
                } else {
                    ops_iter.next().ok_or_else(|| ParseError {
                        line: insn.line,
                        message: format!("`{mnemonic}` expects more operands"),
                    })?
                };
                let raw = self.convert_operand(
                    insn.line,
                    fun,
                    mnemonic,
                    pos,
                    *kind,
                    op,
                    num_vregs,
                    insn_count,
                    &mut entity_offsets,
                    &mut next_raw,
                    b,
                )?;
                raw_ops.push(raw);
            }
            if ops_iter.next().is_some() {
                return err(
                    insn.line,
                    format!("`{mnemonic}` has more operands than the ISA allows"),
                );
            }
            let bc = insn_ctor::construct(mnemonic, &raw_ops).ok_or_else(|| ParseError {
                line: insn.line,
                message: format!("`{mnemonic}` operand kinds do not match the ISA"),
            })?;
            bytecodes.push(bc);
        }

        let try_blocks = self.build_try_blocks(fun, insn_count, b)?;

        Ok(MethodBody {
            num_vregs,
            num_args: fun.params.len().saturating_sub(usize::from(!fun.is_static)) as u32,
            bytecodes,
            entity_offsets,
            try_blocks,
            ic_size: None,
        })
    }

    /// Convert one syntactic operand to its typed form per the spec kind,
    /// registering entities as needed.
    #[allow(clippy::too_many_arguments)]
    fn convert_operand(
        &mut self,
        line: usize,
        fun: &PaFunction,
        mnemonic: &str,
        pos: usize,
        kind: OpKind,
        op: &PaOp,
        num_vregs: u32,
        insn_count: u32,
        entity_offsets: &mut HashMap<(EntityKind, u32), u32>,
        next_raw: &mut HashMap<EntityKind, u32>,
        b: &mut BuildCtx,
    ) -> Result<RawOperand, ParseError> {
        let mismatch = || ParseError {
            line,
            message: format!("`{mnemonic}` operand {pos} has the wrong kind for the ISA"),
        };
        match (kind, op) {
            (OpKind::Reg, PaOp::VReg(v)) => Ok(RawOperand::R(*v)),
            (OpKind::Reg, PaOp::AReg(a)) => {
                let reg = num_vregs + *a as u32;
                let reg = u16::try_from(reg).map_err(|_| ParseError {
                    line,
                    message: format!("`{mnemonic}` register {reg} out of range"),
                })?;
                Ok(RawOperand::R(reg))
            }
            (OpKind::Imm, PaOp::Imm(v)) => Ok(RawOperand::I(*v)),
            (OpKind::ImmFloat, PaOp::Float(v)) => Ok(RawOperand::I(v.to_bits() as i64)),
            (OpKind::ImmFloat, PaOp::Imm(v)) => Ok(RawOperand::I(*v)),
            (OpKind::Label, PaOp::LabelRef(name)) => {
                let idx = match fun.labels.get(name) {
                    Some(&idx) => idx,
                    None if fun.trailing_empty_label => insn_count,
                    None => {
                        return err(
                            line,
                            format!("undefined label `{}`", String::from_utf8_lossy(name)),
                        );
                    }
                };
                Ok(RawOperand::L(idx))
            }
            // The emitter's out-of-range jump quirk prints the raw index
            // in decimal.
            (OpKind::Label, PaOp::Imm(v)) => Ok(RawOperand::L(*v as u32)),
            (OpKind::Str, PaOp::Str(content)) => {
                let sid = self.intern(content)?;
                // The offset the STRING section printed for this content
                // (first listed), so re-emission reproduces the section.
                let offset = match self.string_offsets.get(content) {
                    Some(offsets) => offsets[0],
                    None => {
                        let off = b.next_synthetic_offset();
                        b.entity_map.insert(off, sid);
                        off
                    }
                };
                b.entity_map.insert(offset, sid);
                let raw = next_raw.entry(EntityKind::StringId).or_insert(0);
                let id = *raw;
                *raw += 1;
                entity_offsets.insert((EntityKind::StringId, id), offset);
                Ok(RawOperand::E(id))
            }
            (OpKind::Method, PaOp::MethodSig(sig)) => {
                let offset = b
                    .method_by_signature
                    .get(sig)
                    .copied()
                    .ok_or_else(|| ParseError {
                        line,
                        message: format!(
                            "method reference `{}` names no defined function",
                            String::from_utf8_lossy(sig)
                        ),
                    })?;
                let raw = next_raw.entry(EntityKind::MethodId).or_insert(0);
                let id = *raw;
                *raw += 1;
                entity_offsets.insert((EntityKind::MethodId, id), offset);
                Ok(RawOperand::E(id))
            }
            (OpKind::LiteralArr, PaOp::Literal(text)) => {
                let offset = match self.lit_by_text.get_mut(text) {
                    Some((offsets, cursor)) => {
                        // The list was rank-ordered at build time (target
                        // index order, nested-pinned offsets last): the
                        // walk's first-appearance order then matches the
                        // printed index order. Extra references cycle.
                        let off = offsets[*cursor % offsets.len()];
                        *cursor += 1;
                        off
                    }
                    None => {
                        // An inline literal the LITERALS section does not
                        // list: parse it and give it a synthetic offset so
                        // the model stays encodable (the re-emitted
                        // LITERALS section then diverges — loudly).
                        let items = if text.is_empty() {
                            Vec::new()
                        } else {
                            match self.parse_literal_value(text, line)? {
                                PaLiteral::Regular(items) => items,
                                PaLiteral::Module(_) => {
                                    return err(
                                        line,
                                        "module array as an instruction operand".to_owned(),
                                    );
                                }
                            }
                        };
                        let off = b.next_synthetic_offset();
                        self.lit_by_text
                            .entry(text.clone())
                            .or_default()
                            .0
                            .push(off);
                        self.lit_by_offset.insert(off, self.regular.len());
                        self.regular.push((0, off, items, text.clone()));
                        off
                    }
                };
                let raw = next_raw.entry(EntityKind::LiteralarrayId).or_insert(0);
                let id = *raw;
                *raw += 1;
                entity_offsets.insert((EntityKind::LiteralarrayId, id), offset);
                Ok(RawOperand::E(id))
            }
            _ => Err(mismatch()),
        }
    }

    /// Group the printed `.catch`/`.catchall` lines into try blocks (one
    /// block per (try-begin, try-end) pair, first-appearance order — the
    /// emitter's enumeration order).
    fn build_try_blocks(
        &mut self,
        fun: &PaFunction,
        insn_count: u32,
        b: &mut BuildCtx,
    ) -> Result<Vec<TryBlock>, ParseError> {
        let label_idx = |fun: &PaFunction, name: &[u8], line: usize| -> Result<u32, ParseError> {
            match fun.labels.get(name) {
                Some(&idx) => Ok(idx),
                None if fun.trailing_empty_label => Ok(insn_count),
                None => err(
                    line,
                    format!("undefined catch label `{}`", String::from_utf8_lossy(name)),
                ),
            }
        };
        let mut blocks: Vec<TryBlock> = Vec::new();
        let mut by_range: HashMap<(u32, u32), usize> = HashMap::new();
        for catch in &fun.catches {
            let begin = label_idx(fun, &catch.try_begin, catch.line)?;
            let end = label_idx(fun, &catch.try_end, catch.line)?;
            if end < begin || end > insn_count {
                return err(catch.line, "catch try range out of bounds".to_owned());
            }
            let handler = label_idx(fun, &catch.catch_begin, catch.line)?;
            let handler_end = if catch.catch_end.is_empty() {
                handler
            } else {
                label_idx(fun, &catch.catch_end, catch.line)?
            };
            if handler_end < handler || handler_end > insn_count {
                return err(catch.line, "catch handler range out of bounds".to_owned());
            }
            let type_idx = if catch.record.is_empty() {
                u32::MAX
            } else {
                let desc = record_descriptor(&catch.record);
                let sid = self.intern(&desc)?;
                let off = b.next_synthetic_offset();
                b.entity_map.insert(off, sid);
                off
            };
            let cb = CatchBlock {
                type_idx,
                handler,
                len: handler_end - handler,
            };
            let key = (begin, end);
            match by_range.get(&key) {
                Some(&idx) => blocks[idx].catches.push(cb),
                None => {
                    by_range.insert(key, blocks.len());
                    blocks.push(TryBlock {
                        start: begin,
                        len: end - begin,
                        catches: vec![cb],
                    });
                }
            }
        }
        Ok(blocks)
    }
}

// ---------------------------------------------------------------------------
// Build-time state
// ---------------------------------------------------------------------------

#[derive(Default)]
struct BuildCtx {
    /// Record name (pandasm form) → class descriptor id.
    class_by_record_name: HashMap<Vec<u8>, StringId>,
    /// Descriptor bytes → id (all classes, including synthesized _GLOBAL).
    class_by_descriptor: HashMap<Vec<u8>, StringId>,
    /// Synthesized `_GLOBAL` class descriptor (unprefixed functions).
    global_class: Option<StringId>,
    /// `name:(sig)` → synthetic method offset.
    method_by_signature: HashMap<Vec<u8>, u32>,
    /// Bare method name → synthetic method offset (literal method refs).
    method_by_name: HashMap<Vec<u8>, u32>,
    entity_map: HashMap<u32, StringId>,
    method_shells: Vec<MethodShell>,
    next_offset: u32,
}

impl BuildCtx {
    fn next_synthetic_offset(&mut self) -> u32 {
        self.next_offset = self
            .next_offset
            .checked_add(4)
            .unwrap_or(SYNTHETIC_OFFSET_BASE);
        if self.next_offset < SYNTHETIC_OFFSET_BASE {
            self.next_offset = SYNTHETIC_OFFSET_BASE;
        }
        self.next_offset
    }
}

struct MethodShell {
    owner: StringId,
    name_sid: StringId,
    offset: u32,
}

// ---------------------------------------------------------------------------
// Name / type helpers
// ---------------------------------------------------------------------------

/// Inverse of the emitter's `record_pandasm_name` for non-array record
/// names: dots become slashes inside an `L…;` wrapper.
fn record_descriptor(name: &[u8]) -> Vec<u8> {
    let mut desc = Vec::with_capacity(name.len() + 2);
    desc.push(b'L');
    for &b in name {
        desc.push(if b == b'.' { b'/' } else { b });
    }
    desc.push(b';');
    desc
}

/// Inverse of the emitter's `replace_once(".ctor", "_ctor_")` mangling.
fn demangle(name: &[u8], is_ctor: bool, is_cctor: bool) -> Vec<u8> {
    let mut out = name.to_vec();
    let (needle, with): (&[u8], &[u8]) = if is_ctor {
        (b"_ctor_", b".ctor")
    } else if is_cctor {
        (b"_cctor_", b".cctor")
    } else {
        return out;
    };
    if let Some(pos) = out.windows(needle.len()).position(|w| w == needle) {
        out.splice(pos..pos + needle.len(), with.iter().copied());
    }
    out
}

/// The longest printed record name that prefixes `name` + `.` (owner
/// resolution before the name→id map exists).
fn record_prefix_of<'a>(name: &[u8], records: &'a [PaRecord]) -> Option<&'a [u8]> {
    let mut best: Option<&[u8]> = None;
    for rec in records {
        let r = rec.name.as_slice();
        if name.len() > r.len()
            && name.starts_with(r)
            && name[r.len()] == b'.'
            && best.is_none_or(|b| r.len() > b.len())
        {
            best = Some(r);
        }
    }
    best
}

/// Split a full printed function name into (record name, bare method
/// name): the LONGEST known record name followed by `.`; `None` = global.
fn split_owner<'a, 'b>(
    name: &'a [u8],
    records: &'b HashMap<Vec<u8>, StringId>,
) -> (Option<&'b [u8]>, &'a [u8]) {
    let mut best: Option<&[u8]> = None;
    for rec in records.keys() {
        if name.len() > rec.len()
            && name.starts_with(rec)
            && name[rec.len()] == b'.'
            && best.is_none_or(|b| rec.len() > b.len())
        {
            best = Some(rec);
        }
    }
    match best {
        Some(rec) => (Some(rec), &name[rec.len() + 1..]),
        None => (None, name),
    }
}

/// `GetFunctionSignatureFromName`: `name:(type,type,…)`.
fn function_signature(name: &[u8], params: &[Vec<u8>]) -> Vec<u8> {
    let mut sig = name.to_vec();
    sig.extend_from_slice(b":(");
    for (i, p) in params.iter().enumerate() {
        if i > 0 {
            sig.push(b',');
        }
        sig.extend_from_slice(p);
    }
    sig.extend_from_slice(b")");
    sig
}

/// Parse a pandasm type name (field types, parameter types): the inverse
/// of the emitter's `type_pandasm_name` / `record_pandasm_name`.
fn parse_type(
    intern: &mut dyn FnMut(&[u8]) -> Result<StringId, ParseError>,
    name: &[u8],
) -> Result<Type, ParseError> {
    Ok(match name {
        b"void" => Type::Void,
        b"u1" => Type::Bool,
        b"i8" => Type::I8,
        b"u8" => Type::U8,
        b"i16" => Type::I16,
        b"u16" => Type::U16,
        b"i32" => Type::I32,
        b"u32" => Type::U32,
        b"i64" => Type::I64,
        b"u64" => Type::U64,
        b"f32" => Type::F32,
        b"f64" => Type::F64,
        b"any" => Type::Tagged,
        other => {
            // Reference type: `Foo.Bar[]` → `[[LFoo/Bar;`.
            let mut rank = 0usize;
            let mut base = other;
            while base.ends_with(b"[]") {
                rank += 1;
                base = &base[..base.len() - 2];
            }
            let mut desc = Vec::new();
            desc.resize(rank, b'[');
            let prim: Option<u8> = match base {
                b"u1" => Some(b'Z'),
                b"i8" => Some(b'B'),
                b"u8" => Some(b'H'),
                b"i16" => Some(b'S'),
                b"u16" => Some(b'C'),
                b"i32" => Some(b'I'),
                b"u32" => Some(b'U'),
                b"f32" => Some(b'F'),
                b"f64" => Some(b'D'),
                b"i64" => Some(b'J'),
                b"u64" => Some(b'Q'),
                b"void" => Some(b'V'),
                _ => None,
            };
            match prim {
                Some(p) => desc.push(p),
                None => {
                    desc.push(b'L');
                    for &b in base {
                        desc.push(if b == b'.' { b'/' } else { b });
                    }
                    desc.push(b';');
                }
            }
            Type::Reference(intern(&desc)?)
        }
    })
}

// ---------------------------------------------------------------------------
// Section parsing
// ---------------------------------------------------------------------------

/// The four banner-delimited sections, each with the 1-based line number
/// of its first body line (for error reporting).
struct Sections<'a> {
    literals: (&'a [u8], usize),
    records: (&'a [u8], usize),
    methods: (&'a [u8], usize),
    strings: (&'a [u8], usize),
}

/// 1-based line number of the line starting at byte offset `off`.
fn line_of(text: &[u8], off: usize) -> usize {
    1 + text[..off.min(text.len())]
        .iter()
        .filter(|&&b| b == b'\n')
        .count()
}

fn split_sections(text: &[u8]) -> Result<Sections<'_>, ParseError> {
    const BANNER: &[u8] = b"# ====================\n";
    let mut marks = Vec::new();
    let mut pos = 0usize;
    while pos + BANNER.len() <= text.len() {
        if &text[pos..pos + BANNER.len()] == BANNER {
            marks.push(pos);
            pos += BANNER.len();
        } else {
            pos += 1;
        }
    }
    if marks.len() != 4 {
        return err(
            0,
            "expected exactly four section banners (LITERALS/RECORDS/METHODS/STRING)",
        );
    }
    let mut bodies: Vec<(&[u8], usize)> = Vec::new();
    for (i, &m) in marks.iter().enumerate() {
        let name_start = m + BANNER.len();
        let Some(nl) = text[name_start..].iter().position(|&b| b == b'\n') else {
            return err(0, "truncated section name");
        };
        let mut body_start = name_start + nl + 1;
        // One blank line follows the section name.
        if text.get(body_start) == Some(&b'\n') {
            body_start += 1;
        }
        let end = marks.get(i + 1).copied().unwrap_or(text.len());
        bodies.push((&text[body_start..end], line_of(text, body_start)));
    }
    Ok(Sections {
        literals: bodies[0],
        records: bodies[1],
        methods: bodies[2],
        strings: bodies[3],
    })
}

/// Parse a LITERALS key line: `{index} 0x{offset} {value…}` →
/// (index, offset, value start offset in the line). Crate-visible: the
/// emitter's assignment-verification helper reuses it on its own keys.
pub(crate) fn parse_literal_key(line: &[u8]) -> Option<(u32, u32, usize)> {
    let sp = line.iter().position(|&b| b == b' ')?;
    if line[..sp].is_empty() || !line[..sp].iter().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let index: u32 = std::str::from_utf8(&line[..sp]).ok()?.parse().ok()?;
    let rest = &line[sp + 1..];
    let hex = rest.strip_prefix(b"0x")?;
    let hex_len = hex.iter().take_while(|b| b.is_ascii_hexdigit()).count();
    if hex_len == 0 {
        return None;
    }
    let offset = u32::from_str_radix(std::str::from_utf8(&hex[..hex_len]).ok()?, 16).ok()?;
    let value_start = sp + 1 + 2 + hex_len + 1;
    if value_start > line.len() {
        return None;
    }
    Some((index, offset, value_start))
}

/// Is the accumulated literal-array value text complete? Scans with the
/// oracle for raw strings; complete when the braces/brackets balance and
/// the text ends with `]}` (or when the value is empty).
fn value_is_complete(acc: &[u8], oracle: &Oracle) -> bool {
    if trim(acc).is_empty() {
        return true; // the empty array prints as nothing
    }
    let mut depth = 0i32;
    let mut i = 0usize;
    while i < acc.len() {
        let b = acc[i];
        if b == b'"' {
            // Oracle close, else the next quote in the accumulated text.
            let mut close = None;
            for j in (i + 1..acc.len()).rev() {
                if acc[j] != b'"' {
                    continue;
                }
                if !oracle.contains(&acc[i + 1..j]) {
                    continue;
                }
                close = Some(j);
                break;
            }
            let close = match close {
                Some(c) => c,
                None => match acc[i + 1..].iter().position(|&b| b == b'"') {
                    Some(off) => i + 1 + off,
                    None => return false,
                },
            };
            i = close + 1;
            continue;
        }
        match b {
            b'{' | b'[' => depth += 1,
            b'}' | b']' => depth -= 1,
            _ => {}
        }
        i += 1;
    }
    depth == 0 && acc.ends_with(b"]}")
}

/// Try to split the operand list of one accumulated instruction text;
/// `Some((matched_string_bytes, last_open_quote))` on success.
fn insn_ops_parse(text: &[u8], oracle: &Oracle) -> Option<(usize, Option<usize>)> {
    let split = text
        .iter()
        .position(|b| b.is_ascii_whitespace())
        .unwrap_or(text.len());
    split_operands(&text[split..], oracle)
        .map(|(_, n, last_open)| (n, last_open.map(|o| split + o)))
}

/// Parse a `vN`/`aN` register token body.
fn parse_reg_operand(
    digits: &str,
    text: &str,
    line: usize,
    ctor: fn(u16) -> PaOp,
) -> Result<PaOp, ParseError> {
    digits.parse::<u16>().map(ctor).map_err(|_| ParseError {
        line,
        message: format!("register `{text}` out of range"),
    })
}

/// Token → syntactic operand (untyped; the mnemonic's spec assigns kinds
/// at build time).
fn parse_operand_token(token: &[u8], line: usize) -> Result<PaOp, ParseError> {
    if token.len() >= 2 && token[0] == b'"' && token[token.len() - 1] == b'"' {
        return Ok(PaOp::Str(token[1..token.len() - 1].to_vec()));
    }
    if token.starts_with(b"{") {
        return Ok(PaOp::Literal(token.to_vec()));
    }
    if token.is_ascii() {
        let text = std::str::from_utf8(token).expect("ASCII checked");
        if let Some(rest) = text.strip_prefix('v')
            && !rest.is_empty()
            && rest.bytes().all(|b| b.is_ascii_digit())
        {
            return parse_reg_operand(rest, text, line, PaOp::VReg);
        }
        if let Some(rest) = text.strip_prefix('a')
            && !rest.is_empty()
            && rest.bytes().all(|b| b.is_ascii_digit())
        {
            return parse_reg_operand(rest, text, line, PaOp::AReg);
        }
        if let Some(digits) = text.strip_prefix("0x") {
            return u64::from_str_radix(digits, 16)
                .map(|v| PaOp::Imm(v as i64))
                .map_err(|_| ParseError {
                    line,
                    message: format!("hex immediate `{text}` does not parse"),
                });
        }
        if text.contains(":(") && text.ends_with(')') {
            return Ok(PaOp::MethodSig(token.to_vec()));
        }
        if (text.contains('.')
            || text.contains('e')
            || text.contains("inf")
            || text.contains("nan"))
            && let Ok(v) = text.parse::<f64>()
        {
            return Ok(PaOp::Float(v));
        }
        if let Ok(v) = text.parse::<i64>() {
            return Ok(PaOp::Imm(v));
        }
        return Ok(PaOp::LabelRef(token.to_vec()));
    }
    // Non-ASCII bare token: method names may carry arbitrary bytes.
    if token.windows(2).any(|w| w == b":(") && token.ends_with(b")") {
        return Ok(PaOp::MethodSig(token.to_vec()));
    }
    Ok(PaOp::LabelRef(token.to_vec()))
}

/// `.catchall l1, l2, l3[, l4]` / `.catch Rec, l1, l2, l3[, l4]`.
fn parse_catch_line(line: &[u8], line_no: usize) -> Result<PaCatch, ParseError> {
    let malformed = || ParseError {
        line: line_no,
        message: "malformed .catch directive".to_owned(),
    };
    let (record, rest) = if let Some(r) = line.strip_prefix(b".catchall ") {
        (Vec::new(), r)
    } else if let Some(r) = line.strip_prefix(b".catch ") {
        let Some(comma) = r.iter().position(|&b| b == b',') else {
            return Err(malformed());
        };
        (r[..comma].to_vec(), trim_start(&r[comma + 1..]))
    } else {
        return Err(malformed());
    };
    let parts: Vec<&[u8]> = rest.split(|&b| b == b',').map(trim).collect();
    if parts.len() != 3 && parts.len() != 4 {
        return Err(malformed());
    }
    Ok(PaCatch {
        record,
        try_begin: parts[0].to_vec(),
        try_end: parts[1].to_vec(),
        catch_begin: parts[2].to_vec(),
        catch_end: parts.get(3).map(|p| p.to_vec()).unwrap_or_default(),
        line: line_no,
    })
}

/// `ModuleTag: REGULAR_IMPORT, local_name: a, import_name: b, module_request: r`.
fn parse_module_record(text: &[u8], line: usize) -> Result<PaModuleRecord, ParseError> {
    let malformed = |what: &str| ParseError {
        line,
        message: format!("malformed module record ({what})"),
    };
    let Some(comma) = text.iter().position(|&b| b == b',') else {
        return Err(malformed("no tag"));
    };
    let tag = &text[..comma];
    let mut fields: HashMap<&[u8], &[u8]> = HashMap::new();
    for part in text[comma + 1..].split(|&b| b == b',') {
        let part = trim(part);
        let Some(colon) = part.iter().position(|&b| b == b':') else {
            return Err(malformed("field without colon"));
        };
        fields.insert(trim(&part[..colon]), trim(&part[colon + 1..]));
    }
    let get = |name: &[u8]| fields.get(name).map(|v| v.to_vec());
    let req = || get(b"module_request").ok_or_else(|| malformed("missing module_request"));
    Ok(match tag {
        b"REGULAR_IMPORT" => PaModuleRecord::RegularImport {
            local: get(b"local_name").ok_or_else(|| malformed("missing local_name"))?,
            import: get(b"import_name").ok_or_else(|| malformed("missing import_name"))?,
            request: req()?,
        },
        b"NAMESPACE_IMPORT" => PaModuleRecord::NamespaceImport {
            local: get(b"local_name").ok_or_else(|| malformed("missing local_name"))?,
            request: req()?,
        },
        b"LOCAL_EXPORT" => PaModuleRecord::LocalExport {
            local: get(b"local_name").ok_or_else(|| malformed("missing local_name"))?,
            export: get(b"export_name").ok_or_else(|| malformed("missing export_name"))?,
        },
        b"INDIRECT_EXPORT" => PaModuleRecord::IndirectExport {
            export: get(b"export_name").ok_or_else(|| malformed("missing export_name"))?,
            import: get(b"import_name").ok_or_else(|| malformed("missing import_name"))?,
            request: req()?,
        },
        b"STAR_EXPORT" => PaModuleRecord::StarExport { request: req()? },
        other => {
            return Err(ParseError {
                line,
                message: format!("unknown ModuleTag `{}`", String::from_utf8_lossy(other)),
            });
        }
    })
}

fn parse_language(text: &[u8]) -> Option<SourceLang> {
    Some(match text {
        b"ECMAScript" => SourceLang::EcmaScript,
        b"JavaScript" => SourceLang::JavaScript,
        b"TypeScript" => SourceLang::TypeScript,
        b"ArkTS" => SourceLang::ArkTs,
        b"PandaAssembly" => SourceLang::PandaAssembly,
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// 13.x/24.x literal-table index recovery
// ---------------------------------------------------------------------------
//
// The LITERALS key index of a 13.x/24.x array is its position in the
// emitter's libstdc++-unordered_set iteration over the collected offsets —
// a pure function of the insertion (first-appearance) order in the
// class/method/instruction walk. The pandasm text carries neither the
// method order within a class (functions print signature-sorted) nor the
// source offset an inline literal operand referenced (contents print
// inline). [`fix_literal_assignment`] recovers the assignment for the
// common case: same-content references were bound in printed index order at
// build time (the original first-appearance order usually coincides), and
// each class's methods are then sorted by the smallest printed index their
// instructions reference — method order is textually invisible (functions
// print signature-sorted), so permuting it costs nothing. Fixtures whose
// original order coincides with neither are ledgered by the corpus gate
// (scripts/pandasm-asm-divergences.json,
// `text:literal-index-order-underdetermined`).

fn fix_literal_assignment(file: &mut File, target: &[(u32, u32)]) {
    // No fast path: simulated_literal_assignment was deleted (its emitter
    // keys are bare `{index} 0x{offset}` while parse_literal_key requires
    // a trailing value byte, so it always returned [] and the compare
    // against a non-empty target was never true). The sort below always
    // runs — same behavior as before.
    // Method order within a class is invisible in the text (functions print
    // signature-sorted) but drives the 13.x/24.x collection order. Sort
    // each class's methods by the smallest printed index their literal
    // operands reference. (Bindings keep the build-time target-rank order.)
    let rank: HashMap<u32, u32> = target
        .iter()
        .enumerate()
        .map(|(i, (_, off))| (*off, i as u32))
        .collect();
    for class in file.classes.values_mut() {
        class
            .methods
            .sort_by_key(|m| method_min_literal_rank(m, &rank));
    }
}

/// The smallest `rank` among the literal arrays a method's instructions
/// reference (`u32::MAX` when it references none).
fn method_min_literal_rank(m: &Method, rank: &HashMap<u32, u32>) -> u32 {
    m.body
        .as_ref()
        .map(|body| {
            body.bytecodes
                .iter()
                .flat_map(|bc| bc.entity_operands())
                .filter(|(kind, _)| *kind == EntityKind::LiteralarrayId)
                .filter_map(|(kind, id)| {
                    body.entity_offsets
                        .get(&(kind, id.0))
                        .and_then(|off| rank.get(off))
                        .copied()
                })
                .min()
                .unwrap_or(u32::MAX)
        })
        .unwrap_or(u32::MAX)
}

#[cfg(test)]
mod tests {
    //! Parser smoke tests: round-trip, structured errors, and a
    //! deterministic fuzz round proving no panics on arbitrary input.
    use super::*;
    use crate::types::HasAccessFlags as _;

    /// A minimal but complete pandasm text (one static function).
    const MINIMAL: &[u8] = b"# source binary: t.abc\n\n# ====================\n# LITERALS\n\n\n# ====================\n# RECORDS\n\n# ====================\n# METHODS\n\n.language ECMAScript\n.function any f() <static> {\n\tldai 0x7\n\treturnundefined\n}\n\n# ====================\n# STRING\n\n";

    #[test]
    fn minimal_roundtrip_is_byte_exact() {
        let file = parse_file(MINIMAL).expect("minimal parses");
        let out = super::super::emit_file(&file, "t.abc");
        assert_eq!(out, MINIMAL, "parse->emit must be byte-exact");
        // And the model must assemble.
        crate::encode(&file).expect("minimal encodes");
    }

    #[test]
    fn string_operands_use_the_string_section_oracle() {
        let text: &[u8] = b"# source binary: t.abc\n\n# ====================\n# LITERALS\n\n\n# ====================\n# RECORDS\n\n# ====================\n# METHODS\n\n.language ECMAScript\n.function any f() <static> {\n\tlda.str \"a,b}\"\n\tthrow.undefinedifholewithname \"a,b}\"\n\treturnundefined\n}\n\n# ====================\n# STRING\n\n[offset:0x40, name_value:a,b}]\n";
        let file = parse_file(text).expect("quoted-comma string parses");
        let out = super::super::emit_file(&file, "t.abc");
        assert_eq!(out, text);
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn garbage_is_a_structured_error() {
        let err = parse_file(b"hello world").expect_err("garbage rejected");
        assert!(err.message.contains("section banners"), "{err}");
        // A truncated file: banners present, body cut mid-function.
        let truncated = &MINIMAL[..MINIMAL.len() - 30];
        let res = parse_file(truncated);
        assert!(res.is_err(), "truncated input must fail, not panic");
    }

    /// Deterministic fuzz round: random buffers, mutations, truncations,
    /// and duplicated lines of a valid document. The parser must never
    /// panic; errors are fine.
    #[test]
    fn fuzz_never_panics() {
        let mut state = 0x853c_49e6_748f_ea9bu64;
        let mut rng = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for round in 0..4000u32 {
            let input: Vec<u8> = match round % 4 {
                0 => {
                    // Random bytes.
                    let len = (rng() % 200) as usize;
                    (0..len).map(|_| rng() as u8).collect()
                }
                1 => {
                    // Point mutations of a valid document.
                    let mut v = MINIMAL.to_vec();
                    for _ in 0..(rng() % 8 + 1) {
                        let pos = (rng() as usize) % v.len();
                        v[pos] = rng() as u8;
                    }
                    v
                }
                2 => {
                    // Truncation at a random point.
                    let end = (rng() as usize) % (MINIMAL.len() + 1);
                    MINIMAL[..end].to_vec()
                }
                _ => {
                    // Splice a random slice of the document back into it.
                    let mut v = MINIMAL.to_vec();
                    let start = (rng() as usize) % MINIMAL.len();
                    let len = (rng() as usize) % (MINIMAL.len() - start);
                    let at = (rng() as usize) % v.len();
                    let piece: Vec<u8> = MINIMAL[start..start + len].to_vec();
                    v.splice(at..at, piece);
                    v
                }
            };
            // A panic fails the test outright; Err is fine.
            let _ = parse_file(&input);
        }
    }

    // ------------------------------------------------------------------
    // Coverage batches (the CI coverage job skips the asm corpus gates, so
    // the parser's coverage comes from these unit tests alone):
    //  * negative batch — one malformed document per structured error;
    //  * positive batch — handwritten-only constructs (external records,
    //    ctor/cctor, typed catches, code-less functions, non-corpus
    //    literal/annotation tags, handwritten tolerances);
    //  * mainline batch — small synthetic documents exercising the parse
    //    section/body builders the corpus gates used to cover.
    // ------------------------------------------------------------------

    /// Assemble a four-section pandasm document from section bodies.
    fn doc(literals: &[u8], records: &[u8], methods: &[u8], strings: &[u8]) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(b"# source binary: t.abc\n\n# ====================\n# LITERALS\n\n");
        v.extend_from_slice(literals);
        v.extend_from_slice(b"# ====================\n# RECORDS\n\n");
        v.extend_from_slice(records);
        v.extend_from_slice(b"# ====================\n# METHODS\n\n");
        v.extend_from_slice(methods);
        v.extend_from_slice(b"# ====================\n# STRING\n\n");
        v.extend_from_slice(strings);
        v
    }

    /// A methods section carrying one function with the given body lines.
    fn one_function(body: &[u8]) -> Vec<u8> {
        let mut m = b".language ECMAScript\n.function any f() <static> {\n".to_vec();
        m.extend_from_slice(body);
        m.extend_from_slice(b"}\n");
        m
    }

    fn parse_err(input: &[u8]) -> ParseError {
        parse_file(input).expect_err("document must be rejected")
    }

    // -- mutf8_decode: strict decoder, direct calls -----------------------

    #[test]
    fn mutf8_decode_valid_forms() {
        assert_eq!(mutf8_decode(b"abc").as_deref(), Some("abc"));
        assert_eq!(mutf8_decode(b"").as_deref(), Some(""));
        // 2-byte.
        assert_eq!(mutf8_decode(&[0xC3, 0xA9]).as_deref(), Some("\u{00e9}"));
        // 3-byte.
        assert_eq!(
            mutf8_decode(&[0xE2, 0x82, 0xAC]).as_deref(),
            Some("\u{20ac}")
        );
        // Embedded NUL (MUTF-8 C0 80).
        assert_eq!(
            mutf8_decode(&[b'a', 0xC0, 0x80, b'b']).as_deref(),
            Some("a\0b")
        );
        // CESU-8 surrogate pair (U+1F600).
        assert_eq!(
            mutf8_decode(&[0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80]).as_deref(),
            Some("\u{1F600}")
        );
        // Raw 4-byte UTF-8 (handwritten-only: the emitter prints CESU-8).
        assert_eq!(
            mutf8_decode(&[0xF0, 0x9F, 0x98, 0x80]).as_deref(),
            Some("\u{1F600}")
        );
        // Round-trip through the emitter's encoder.
        assert_eq!(
            mutf8_decode(&super::super::mutf8_bytes("a\0\u{1F600}\u{20ac}")).as_deref(),
            Some("a\0\u{1F600}\u{20ac}")
        );
    }

    #[test]
    fn mutf8_decode_rejects_malformed() {
        // Raw NUL is never valid MUTF-8.
        assert_eq!(mutf8_decode(b"a\0b"), None);
        // 2-byte: bad continuation, truncated.
        assert_eq!(mutf8_decode(&[0xC3, 0x28]), None);
        assert_eq!(mutf8_decode(&[0xC3]), None);
        // 3-byte: bad second/third continuation, truncated.
        assert_eq!(mutf8_decode(&[0xE2, 0x28, 0xAC]), None);
        assert_eq!(mutf8_decode(&[0xE2, 0x82, 0x28]), None);
        assert_eq!(mutf8_decode(&[0xE2, 0x82]), None);
        // Lone high surrogate (truncated pair), high surrogate followed by
        // a non-low 3-byte sequence, lone low surrogate.
        assert_eq!(mutf8_decode(&[0xED, 0xA0, 0xBD]), None);
        assert_eq!(mutf8_decode(&[0xED, 0xA0, 0xBD, 0xE1, 0x80, 0x80]), None);
        assert_eq!(mutf8_decode(&[0xED, 0xB0, 0x80]), None);
        // High surrogate followed by an ASCII byte (not a 3-byte lead), in
        // both short and full-lookahead forms.
        assert_eq!(mutf8_decode(&[0xED, 0xA0, 0xBD, b'a']), None);
        assert_eq!(mutf8_decode(&[0xED, 0xA0, 0xBD, b'a', 0x80, 0x80]), None);
        // 4-byte: bad continuation, truncated, out-of-range code point.
        assert_eq!(mutf8_decode(&[0xF0, 0x9F, 0x28, 0x80]), None);
        assert_eq!(mutf8_decode(&[0xF0, 0x9F]), None);
        assert_eq!(mutf8_decode(&[0xF4, 0x90, 0x80, 0x80]), None);
        // Invalid lead bytes.
        assert_eq!(mutf8_decode(&[0x80]), None);
        assert_eq!(mutf8_decode(&[0xFF]), None);
    }

    // -- parse_literal_key / parse_language: direct calls ------------------

    #[test]
    fn parse_literal_key_forms() {
        assert_eq!(parse_literal_key(b"0 0x10 { }"), Some((0, 0x10, 7)));
        assert_eq!(parse_literal_key(b"10 0x2a "), Some((10, 0x2a, 8)));
        assert_eq!(parse_literal_key(b""), None);
        assert_eq!(parse_literal_key(b"0"), None);
        assert_eq!(parse_literal_key(b"x 0x10"), None);
        assert_eq!(parse_literal_key(b" 0x10"), None);
        assert_eq!(parse_literal_key(b"0 zz"), None);
        assert_eq!(parse_literal_key(b"0 0x"), None);
        assert_eq!(parse_literal_key(b"0 0x10"), None);
        assert_eq!(parse_literal_key(b"99999999999 0x1 "), None);
    }

    #[test]
    fn parse_language_all_variants() {
        assert_eq!(parse_language(b"ECMAScript"), Some(SourceLang::EcmaScript));
        assert_eq!(parse_language(b"JavaScript"), Some(SourceLang::JavaScript));
        assert_eq!(parse_language(b"TypeScript"), Some(SourceLang::TypeScript));
        assert_eq!(parse_language(b"ArkTS"), Some(SourceLang::ArkTs));
        assert_eq!(
            parse_language(b"PandaAssembly"),
            Some(SourceLang::PandaAssembly)
        );
        assert_eq!(parse_language(b"Klingon"), None);
    }

    // -- Negative batch: one malformed document per structured error -------

    /// A module-array LITERALS entry whose record section is `record_line`.
    fn module_blob_doc(record_line: &[u8]) -> Vec<u8> {
        let mut lit = b"0 0x100 { 1 [\n\tMODULE_REQUEST_ARRAY: {\n\t\t0 : r,\n\t};\n".to_vec();
        lit.extend_from_slice(record_line);
        lit.extend_from_slice(b"\n]}\n");
        doc(&lit, b"", b"", b"")
    }

    #[test]
    fn malformed_documents_fail_with_structured_errors() {
        let cases: Vec<(Vec<u8>, String)> = vec![
            // Section splitting.
            (
                b"# ====================\n# LITERALS\n\n# ====================\n# RECORDS\n\n# ====================\n# METHODS\n\n# ====================\n".to_vec(),
                "truncated section name".to_owned(),
            ),
            // STRING section entries.
            (
                doc(b"", b"", b"", b"[offset:0x40]"),
                "malformed STRING entry (missing `, name_value:`)".to_owned(),
            ),
            (
                doc(b"", b"", b"", b"[offset:0xZZ, name_value:ab]"),
                "malformed STRING entry offset".to_owned(),
            ),
            (
                doc(b"", b"", b"", b"[offset:0x40, name_value:ab"),
                "malformed STRING entry (missing `]`)".to_owned(),
            ),
            // LITERALS section entries.
            (
                doc(b"foo bar\n", b"", b"", b""),
                "malformed LITERALS entry key".to_owned(),
            ),
            (
                doc(b"0 0x10 { 1 [ string:\"abc\n", b"", b"", b""),
                "unterminated LITERALS entry value".to_owned(),
            ),
            (
                // Brace-balanced and `]}`-terminated, but not `{`-started.
                doc(b"0 0x10 [{ ]}\n", b"", b"", b""),
                "malformed LITERALS entry value".to_owned(),
            ),
            // Literal array shape (reached via an inline literal operand:
            // the section path pre-checks completeness).
            (
                doc(b"", b"", &one_function(b"\tcreatearraywithbuffer 0x0, { 1 }\n"), b""),
                "literal array missing `[`".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tcreatearraywithbuffer 0x0, { 1 [ i32:1 }\n"), b""),
                "literal array missing `]}`".to_owned(),
            ),
            // A multi-line string not in the oracle: complete by the
            // section scanner's fallback, unsplittable per-line.
            (
                doc(b"0 0x10 { 1 [ string:\"ab\ncd\", ]}\n", b"", b"", b""),
                "unterminated string in literal array".to_owned(),
            ),
            // Literal items.
            (
                doc(b"0 0x10 { 1 [ hello, ]}\n", b"", b"", b""),
                "literal item missing `tag:`".to_owned(),
            ),
            (
                doc(b"0 0x10 { 1 [ string:abc, ]}\n", b"", b"", b""),
                "literal string item is not quoted".to_owned(),
            ),
            (
                doc(b"0 0x10 { 1 [ i32:\xff, ]}\n", b"", b"", b""),
                "literal integer is not ASCII".to_owned(),
            ),
            (
                doc(b"0 0x10 { 1 [ i32:zz, ]}\n", b"", b"", b""),
                "literal integer `zz` does not parse".to_owned(),
            ),
            (
                doc(b"0 0x10 { 1 [ f64:\xff, ]}\n", b"", b"", b""),
                "literal float is not ASCII".to_owned(),
            ),
            (
                doc(b"0 0x10 { 1 [ f64:zz, ]}\n", b"", b"", b""),
                "literal float `zz` does not parse".to_owned(),
            ),
            (
                doc(b"0 0x10 { 1 [ lit_offset:\xff, ]}\n", b"", b"", b""),
                "lit_offset is not ASCII".to_owned(),
            ),
            (
                doc(b"0 0x10 { 1 [ lit_offset:zz, ]}\n", b"", b"", b""),
                "lit_offset `zz` does not parse".to_owned(),
            ),
            (
                doc(b"0 0x10 { 1 [ what:1, ]}\n", b"", b"", b""),
                "unknown literal tag `what`".to_owned(),
            ),
            // Module-array values.
            (
                doc(b"0 0x99 { 5 [ junk\n\tMODULE_REQUEST_ARRAY: {\n\t};\n]}\n", b"", b"", b""),
                "module array missing `[`".to_owned(),
            ),
            (
                doc(
                    b"0 0x99 { 0 [\n\tjunk\n\tMODULE_REQUEST_ARRAY: {\n\t};\n]}\n",
                    b"",
                    b"",
                    b"",
                ),
                "module array missing MODULE_REQUEST_ARRAY".to_owned(),
            ),
            (
                doc(
                    b"0 0x99 { 0 [\n\tMODULE_REQUEST_ARRAY: {\n\t\tjunkline\n\t};\n]}\n",
                    b"",
                    b"",
                    b"",
                ),
                "malformed module request line".to_owned(),
            ),
            (
                doc(
                    b"0 0x99 { 0 [\n\tMODULE_REQUEST_ARRAY: {\n\t};\n\tjunk\n]}\n",
                    b"",
                    b"",
                    b"",
                ),
                "malformed module record line".to_owned(),
            ),
            (
                doc(
                    b"0 0x99 { 0 [\n\tMODULE_REQUEST_ARRAY: {\n\t};\n\tModuleTag: STAR_EXPORT, module_request: r\n]}\n",
                    b"",
                    b"",
                    b"",
                ),
                "module record line missing `;`".to_owned(),
            ),
            // Module records.
            (
                module_blob_doc(b"\tModuleTag: STAR_EXPORT;"),
                "malformed module record (no tag)".to_owned(),
            ),
            (
                module_blob_doc(b"\tModuleTag: STAR_EXPORT, module_request;"),
                "malformed module record (field without colon)".to_owned(),
            ),
            (
                module_blob_doc(b"\tModuleTag: STAR_EXPORT, other: x;"),
                "malformed module record (missing module_request)".to_owned(),
            ),
            (
                module_blob_doc(b"\tModuleTag: REGULAR_IMPORT, import_name: b, module_request: r;"),
                "malformed module record (missing local_name)".to_owned(),
            ),
            (
                module_blob_doc(b"\tModuleTag: FROB, module_request: r;"),
                "unknown ModuleTag `FROB`".to_owned(),
            ),
            // RECORDS section.
            (
                doc(b"", b".language Klingon\n", b"", b""),
                "unknown language `Klingon`".to_owned(),
            ),
            (
                doc(b"", b"garbage\n", b"", b""),
                "expected `.record` or `.language`".to_owned(),
            ),
            (
                doc(b"", b".record Foo\n", b"", b""),
                "malformed `.record` header".to_owned(),
            ),
            (
                doc(b"", b".record R {\n u32 x\n}\n", b"", b""),
                "record field line must be tab-indented".to_owned(),
            ),
            (
                doc(b"", b".record R {\n\tu32 x\n", b"", b""),
                "unterminated `.record` body".to_owned(),
            ),
            (
                doc(b"", b".record R {\n\tu32\n}\n", b"", b""),
                "malformed field line (no type/name split)".to_owned(),
            ),
            // METHODS section framing.
            (
                doc(b"", b"", b"garbage\n", b""),
                "expected `.language` before `.function`".to_owned(),
            ),
            (
                doc(b"", b"", b".language Klingon\n.function any f() <static> {\n}\n", b""),
                "unknown language `Klingon`".to_owned(),
            ),
            (
                // No trailing newline: the section ends with the directive.
                doc(b"", b"", b".language ECMAScript", b""),
                "unexpected end of METHODS section".to_owned(),
            ),
            (
                doc(b"", b"", b".language ECMAScript\ngarbage\n", b""),
                "expected `.function`".to_owned(),
            ),
            // Function headers.
            (
                doc(b"", b"", b".language ECMAScript\n.function any f <static> {\n}\n", b""),
                "`.function` missing parameter list".to_owned(),
            ),
            (
                doc(b"", b"", b".language ECMAScript\n.function any() <static> {\n}\n", b""),
                "`.function` missing name".to_owned(),
            ),
            (
                doc(b"", b"", b".language ECMAScript\n.function any f( <static> {\n}\n", b""),
                "`.function` missing `)`".to_owned(),
            ),
            (
                doc(b"", b"", b".language ECMAScript\n.function any f)a( <static> {\n}\n", b""),
                "`.function` has `)` before `(`".to_owned(),
            ),
            (
                doc(b"", b"", b".language ECMAScript\n.function any f(any) <static> {\n}\n", b""),
                "malformed parameter".to_owned(),
            ),
            (
                doc(b"", b"", b".language ECMAScript\n.function any f() <static>\n", b""),
                "`.function` missing `{`".to_owned(),
            ),
            (
                doc(b"", b"", b".language ECMAScript\n.function any f() static {\n}\n", b""),
                "malformed `.function` attributes".to_owned(),
            ),
            (
                doc(b"", b"", b".language ECMAScript\n.function any f() <bogus> {\n}\n", b""),
                "unknown function attribute `bogus`".to_owned(),
            ),
            (
                doc(b"", b"", b".language ECMAScript\n.function any f() <static> {\n", b""),
                "unterminated `.function` body".to_owned(),
            ),
            (
                doc(b"", b"", b".language ECMAScript\n.function any f() <static> {\ngarbage\n}\n", b""),
                "unexpected line in function body".to_owned(),
            ),
            // Annotation elements.
            (
                doc(b"", b"", b"LAnno:\n\tu32 x 5 }\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
                "annotation element missing `{`".to_owned(),
            ),
            (
                doc(b"", b"", b"LAnno:\n\tu32 x { 5\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
                "annotation element missing `}`".to_owned(),
            ),
            (
                doc(b"", b"", b"LAnno:\n\tu32 { 5 }\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
                "annotation element missing name".to_owned(),
            ),
            (
                doc(b"", b"", b"LAnno:\n\tu32 x { zz }\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
                "annotation u32 `zz` does not parse".to_owned(),
            ),
            (
                doc(b"", b"", b"LAnno:\n\tf64 x { zz }\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
                "annotation f64 `zz` does not parse".to_owned(),
            ),
            (
                doc(b"", b"", b"LAnno:\n\tpanda.String x { hi }\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
                "annotation string is not quoted".to_owned(),
            ),
            (
                doc(b"", b"", b"LAnno:\n\tq32 x { 1 }\n.language ECMAScript\n.function any f() <static> {\n}\n", b""),
                "unknown annotation element tag `q32`".to_owned(),
            ),
            // Instructions.
            (
                doc(b"", b"", &one_function(b"\tbogusinsn\n"), b""),
                "unknown instruction `bogusinsn`".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\t\xff\n"), b""),
                "instruction mnemonic is not ASCII".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tldai\n"), b""),
                "`ldai` expects more operands".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tldai 0x1, 0x2\n"), b""),
                "`ldai` has more operands than the ISA allows".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tldai v0\n"), b""),
                "`ldai` operand 0 has the wrong kind for the ISA".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tldai 0xZZ\n"), b""),
                "hex immediate `0xZZ` does not parse".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tmov v65536, v0\n"), b""),
                "register `v65536` out of range".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tmov v65535, a0\n"), b""),
                "`mov` register 65536 out of range".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tjmp nowhere\n"), b""),
                "undefined label `nowhere`".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tdefinefunc 0x0, missing:(), 0x0\n"), b""),
                "method reference `missing:()` names no defined function".to_owned(),
            ),
            // Unterminated multi-line instruction string: the lookahead
            // walks to the section end while an oracle prefix is pending.
            (
                doc(
                    b"",
                    b"",
                    b".language ECMAScript\n.function any f() <static> {\n\tlda.str \"abc\n",
                    b"[offset:0x40, name_value:abc\ndef]",
                ),
                "unterminated string in instruction".to_owned(),
            ),
            // An oracle-listed string whose close quote is NOT followed by
            // a separator: the close scan skips it and the token is not a
            // string at all.
            (
                doc(
                    b"",
                    b"",
                    &one_function(b"\tlda.str \"a\"x\n"),
                    b"[offset:0x40, name_value:a]",
                ),
                "`lda.str` operand 0 has the wrong kind for the ISA".to_owned(),
            ),
            // Whitespace between the closing quote and the separator.
            (
                doc(
                    b"",
                    b"",
                    &one_function(b"\tlda.str \"a\"  , v0\n"),
                    b"[offset:0x40, name_value:a]",
                ),
                "`lda.str` has more operands than the ISA allows".to_owned(),
            ),
            // Literal resolution.
            (
                doc(b"0 0x10 { 1 [ method:ghost, ]}\n", b"", b"", b""),
                "literal method reference `ghost` names no defined function".to_owned(),
            ),
            (
                doc(b"0 0x10 { 1 [ lit_offset:0x99, ]}\n", b"", b"", b""),
                "lit_offset 0x99 names no literal array".to_owned(),
            ),
            // Field values.
            (
                doc(b"", b".record R {\n\tu32 x = zz\n}\n", b"", b""),
                "field value `zz` does not parse as hex".to_owned(),
            ),
            (
                doc(b"", b".record R {\n\tu32 x = \xff\n}\n", b"", b""),
                "field value is not ASCII".to_owned(),
            ),
            (
                doc(b"", b".record R {\n\tf64 x = zz\n}\n", b"", b""),
                "field f64 `zz` does not parse".to_owned(),
            ),
            (
                doc(b"", b".record R {\n\tf64 x = \xff\n}\n", b"", b""),
                "field f64 value is not ASCII".to_owned(),
            ),
            // Code-less function carrying a body.
            (
                doc(
                    b"",
                    b"",
                    b".language ECMAScript\n.function  f() <external> {\n\tnop\n}\n",
                    b"",
                ),
                "code-less function (no return type) with a body".to_owned(),
            ),
            // Catch directives.
            (
                doc(b"", b"", &one_function(b"\tnop\n.catch NoComma\n"), b""),
                "malformed .catch directive".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tnop\n.catchfoo a, b, c\n"), b""),
                "malformed .catch directive".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tnop\n.catchall a, b\n"), b""),
                "malformed .catch directive".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tnop\nl1:\nl2:\n.catchall l1, l2, l3\n"), b""),
                "undefined catch label `l3`".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tnop\nl1:\n\tnop\nh:\nl2:\n.catchall l2, l1, h\n"), b""),
                "catch try range out of bounds".to_owned(),
            ),
            (
                doc(b"", b"", &one_function(b"\tnop\nh1:\nl1:\n\tnop\nh2:\nl2:\n.catchall l1, l2, h2, h1\n"), b""),
                "catch handler range out of bounds".to_owned(),
            ),
        ];
        for (input, expected) in cases {
            let err = parse_err(&input);
            assert_eq!(
                err.message,
                expected,
                "input: {}",
                String::from_utf8_lossy(&input)
            );
        }
    }

    #[test]
    fn module_request_must_be_in_the_request_array() {
        let input = doc(
            b"0 0x100 { 1 [\n\tMODULE_REQUEST_ARRAY: {\n\t\t0 : other,\n\t};\n\tModuleTag: STAR_EXPORT, module_request: missing;\n]}\n",
            b".record _ESModuleRecord {\n\tu32 moduleRecordIdx = 0x100\n}\n",
            b"",
            b"",
        );
        let err = parse_err(&input);
        assert_eq!(
            err.message,
            "module_request `missing` not in the request array"
        );
    }

    #[test]
    fn module_array_is_not_an_instruction_operand() {
        // The module marker inside a multi-line STRING operand fools the
        // value classifier into the module form, which the instruction
        // operand path rejects.
        let methods: &[u8] = b".language ECMAScript\n.function any f() <static> {\n\tcreatearraywithbuffer 0x0, { 1 [ string:\"z\n{ [\n\tMODULE_REQUEST_ARRAY: {\n\t};\n]}\n\"\n}\n";
        let input = doc(
            b"",
            b"",
            methods,
            b"[offset:0x40, name_value:z\n{ [\n\tMODULE_REQUEST_ARRAY: {\n\t};\n]}\n]",
        );
        let err = parse_err(&input);
        assert_eq!(err.message, "module array as an instruction operand");
    }

    // -- A9: the two deliberate hard errors (exact messages) ---------------

    #[test]
    fn unsupported_constructs_are_hard_errors() {
        let input = doc(
            b"",
            b".record R {\n\tu32 typeSummaryOffset = 0x40\n}\n",
            b"",
            b"",
        );
        let err = parse_err(&input);
        assert_eq!(
            err.message,
            "typeSummaryOffset fields are not representable"
        );

        let input = doc(b"", b".record R {\n\ti32 x = 0x1\n}\n", b"", b"");
        let err = parse_err(&input);
        assert_eq!(
            err.message,
            "field initial value on a type the emitter never prints"
        );
    }

    // -- Positive batch: handwritten-only constructs ------------------------

    #[test]
    fn record_owned_ctor_cctor_and_language_variants() {
        let input = doc(
            b"",
            b".language JavaScript\n.record RJs {\n}\n.language ArkTS\n.record R {\n}\n",
            b".language ECMAScript\n.function any R.f() <static> {\n\treturnundefined\n}\n.language JavaScript\n.function any R._ctor_() <ctor> {\n\treturnundefined\n}\n.language TypeScript\n.function any R._cctor_() <static, cctor> {\n\treturnundefined\n}\n.language ArkTS\n.function any RJs.g() <static> {\n\treturnundefined\n}\n",
            b"",
        );
        let file = parse_file(&input).expect("record-owned functions parse");
        let r = file.class_by_str("LR;").expect("record R");
        let names: Vec<&str> = r
            .methods
            .iter()
            .filter_map(|m| file.strings.resolve(m.name))
            .collect();
        assert!(names.contains(&"f"), "{names:?}");
        assert!(names.contains(&".ctor"), "ctor demangled: {names:?}");
        assert!(names.contains(&".cctor"), "cctor demangled: {names:?}");
        let ctor = r
            .methods
            .iter()
            .find(|m| file.strings.resolve(m.name) == Some(".ctor"))
            .unwrap();
        assert_eq!(ctor.source_lang, SourceLang::JavaScript);
        assert!(!ctor.is_static());
        let rjs = file.class_by_str("LRJs;").expect("record RJs");
        assert_eq!(rjs.source_lang, SourceLang::JavaScript);
        let g = &rjs.methods[0];
        assert_eq!(g.source_lang, SourceLang::ArkTs);
        // Emit side: non-system owner prefix, ctor/cctor renames, language
        // lines for the four non-default languages.
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        assert!(
            text.contains(".language JavaScript\n.record RJs {\n}\n"),
            "{text}"
        );
        assert!(text.contains(".language ArkTS\n.record R {\n}\n"), "{text}");
        assert!(text.contains(".function any R.f() <static> {"), "{text}");
        assert!(
            text.contains(".function any R._ctor_(R a0) <ctor> {"),
            "{text}"
        );
        assert!(
            text.contains(".function any R._cctor_() <static, cctor> {"),
            "{text}"
        );
        assert!(
            text.contains(".language ArkTS\n.function any RJs.g() <static> {"),
            "{text}"
        );
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn external_record_and_codeless_external_function() {
        // `.record … <external>` (corpus-absent) plus an `external` method
        // on a NORMAL record (the emitter prints only those: external
        // classes skip method processing entirely).
        let input = doc(
            b"",
            b".record Ext.Thing <external>\n.record R {\n}\n",
            b".language ECMAScript\n.function  R.decl() <static, external> {\n}\n",
            b"",
        );
        let file = parse_file(&input).expect("external record parses");
        let class = file.class_by_str("LExt/Thing;").expect("external class");
        assert!(class.is_external);
        assert!(class.fields.is_empty());
        let r = file.class_by_str("LR;").expect("record R");
        let m = &r.methods[0];
        assert!(m.is_external);
        assert!(m.is_static());
        assert!(m.body.is_none(), "code-less method has no body");
        // 24.x: code-less protos carry no types.
        assert_eq!(m.return_type, None);
        assert!(m.arg_types.is_empty());
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        assert!(text.contains(".record Ext.Thing <external>\n\n"), "{text}");
        assert!(
            text.contains(".language ECMAScript\n.function  R.decl() <static, external> {\n}\n"),
            "{text}"
        );
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn codeless_function_at_12x() {
        let input = doc(
            b"",
            b"",
            b".language ECMAScript\n.function  f() <static> {\n}\n",
            b"",
        );
        let file = parse_file_with_version(&input, Version::new(12, 0, 6, 0)).expect("12.x parses");
        let global = file.class_by_str("L_GLOBAL;").expect("global class");
        assert_eq!(global.methods.len(), 1);
        assert!(global.methods[0].body.is_none());
        assert_eq!(global.methods[0].return_type, None);
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        assert!(text.contains(".function  f() <static> {\n}\n"), "{text}");
    }

    #[test]
    fn field_types_values_and_references() {
        let input = doc(
            b"",
            b".record Types {\n\tvoid v0\n\tu1 b0\n\ti8 i8f\n\tu8 u8f\n\ti16 i16f\n\tu16 u16f\n\ti32 i32f\n\tu32 u32f\n\ti64 i64f\n\tu64 u64f\n\tf32 f32f\n\tf64 f64f\n\tany anyf\n\tFoo.Bar ref\n\ti32[] arri\n\tFoo.Bar[][] arrr\n\tu1[] pa1\n\ti8[] pa2\n\tu8[] pa3\n\ti16[] pa4\n\tu16[] pa5\n\tu32[] pa6\n\tf32[] pa7\n\tf64[] pa8\n\ti64[] pa9\n\tu64[] pa10\n\tvoid[] pa11\n\tu32 valued = 0x2a\n\tu8 small = 0xf\n\tu1 flag = 1\n\tf64 fval = 1.25\n\tu32 path/name = 0x0\n}\n",
            b"",
            b"",
        );
        let file = parse_file(&input).expect("field zoo parses");
        let class = file.class_by_str("LTypes;").expect("record Types");
        let by_name = |n: &str| {
            class
                .fields
                .iter()
                .find(|f| file.strings.resolve(f.name) == Some(n))
                .unwrap_or_else(|| panic!("field {n}"))
        };
        assert_eq!(by_name("v0").field_type, Type::Void);
        assert_eq!(by_name("b0").field_type, Type::Bool);
        assert_eq!(by_name("i8f").field_type, Type::I8);
        assert_eq!(by_name("u16f").field_type, Type::U16);
        assert_eq!(by_name("i64f").field_type, Type::I64);
        assert_eq!(by_name("anyf").field_type, Type::Tagged);
        // Field without a value: no initial_value.
        assert_eq!(by_name("i32f").initial_value, None);
        // Reference/array types intern the descriptor.
        match by_name("ref").field_type {
            Type::Reference(sid) => assert_eq!(file.strings.resolve(sid), Some("LFoo/Bar;")),
            other => panic!("ref type: {other:?}"),
        }
        match by_name("arrr").field_type {
            Type::Reference(sid) => assert_eq!(file.strings.resolve(sid), Some("[[LFoo/Bar;")),
            other => panic!("arrr type: {other:?}"),
        }
        match by_name("arri").field_type {
            Type::Reference(sid) => assert_eq!(file.strings.resolve(sid), Some("[I")),
            other => panic!("arri type: {other:?}"),
        }
        assert_eq!(by_name("valued").initial_value, Some(FieldValue::I32(0x2a)));
        assert_eq!(by_name("flag").initial_value, Some(FieldValue::I32(1)));
        assert_eq!(by_name("fval").initial_value, Some(FieldValue::F64(1.25)));
        // Emit side: type names (all type_pandasm_name arms), the f64 field
        // value via format_g6, basename-stripped field names.
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        for line in [
            "\tvoid v0\n",
            "\tu1 b0\n",
            "\ti8 i8f\n",
            "\tu8 u8f\n",
            "\ti16 i16f\n",
            "\tu16 u16f\n",
            "\ti32 i32f\n",
            "\tu32 u32f\n",
            "\ti64 i64f\n",
            "\tu64 u64f\n",
            "\tf32 f32f\n",
            "\tf64 f64f\n",
            "\tany anyf\n",
            "\tFoo.Bar ref\n",
            "\ti32[] arri\n",
            "\tFoo.Bar[][] arrr\n",
            "\tu1[] pa1\n",
            "\ti8[] pa2\n",
            "\tu8[] pa3\n",
            "\ti16[] pa4\n",
            "\tu16[] pa5\n",
            "\tu32[] pa6\n",
            "\tf32[] pa7\n",
            "\tf64[] pa8\n",
            "\ti64[] pa9\n",
            "\tu64[] pa10\n",
            "\tvoid[] pa11\n",
            "\tu32 valued = 0x2a\n",
            "\tu8 small = 0xf\n",
            "\tu1 flag = 1\n",
            "\tf64 fval = 1.25\n",
            "\tu32 name = 0x0\n",
        ] {
            assert!(text.contains(line), "missing {line:?} in {text}");
        }
        // (No encode: the vendored writer rejects `void`-typed fields.)
    }

    #[test]
    fn annotations_all_value_tags() {
        let input = doc(
            b"",
            b"",
            b"LMyAnno:\n\tu32 num { 0x2a }\n\tu1 flag { 1 }\n\tf64 score { 2.5 }\n\tpanda.String text { \"hello\" }\nLOther:\n\tu32 x { 0x1 }\nLMyAnno:\n\tu32 second { 0x2 }\n.language ECMAScript\n.function any f() <static> {\n\treturnundefined\n}\n",
            b"",
        );
        let file = parse_file(&input).expect("annotations parse");
        let global = file.class_by_str("L_GLOBAL;").unwrap();
        let m = &global.methods[0];
        let anns = &m.annotations.compile_time;
        assert_eq!(anns.len(), 3, "three annotation blocks (dup name kept)");
        let first = &anns[0];
        assert_eq!(
            file.strings.resolve(first.class_descriptor),
            Some("LMyAnno;")
        );
        let vals: Vec<&AnnotationValue> = first.elements.iter().map(|e| &e.value).collect();
        assert_eq!(
            vals,
            [
                &AnnotationValue::U32(0x2a),
                &AnnotationValue::Bool(true),
                &AnnotationValue::F64(2.5),
                &AnnotationValue::String(file.strings.get("hello").unwrap()),
            ]
        );
        // Emit side: same-name annotations merge into the first block, one
        // element per line.
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        assert!(
            text.contains(
                "LMyAnno:\n\tu32 num { 0x2a }\n\tu1 flag { 1 }\n\tf64 score { 2.5 }\n\tpanda.String text { \"hello\" }\n\tu32 second { 0x2 }\n"
            ),
            "{text}"
        );
        assert!(text.contains("LOther:\n\tu32 x { 0x1 }\n"), "{text}");
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn instruction_operand_kinds_mainline() {
        let input = doc(
            b"",
            b"",
            b".language ECMAScript\n.function any g(any a0) <static> {\n\treturnundefined\n}\n.language PandaAssembly\n.function any f(any a0, any a1) <static> {\n\tldai 0x7\n\tldai 7\n\tsta a0\n\tmov v0, a1\n\tfldai 1.5\n\tfldai 0x0\n\tfldai inf\n\tfldai -nan\n\tjmp l_end\nl_end:\n\tdefinefunc 0x0, g:(any), 0x0\n\tlda.str \"hello\"\n\treturnundefined\n}\n",
            b"",
        );
        let file = parse_file(&input).expect("operand kinds parse");
        let global = file.class_by_str("L_GLOBAL;").unwrap();
        let f = global
            .methods
            .iter()
            .find(|m| file.strings.resolve(m.name) == Some("f"))
            .unwrap();
        assert_eq!(f.source_lang, SourceLang::PandaAssembly);
        let body = f.body.as_ref().unwrap();
        assert_eq!(body.num_vregs, 1, "max v-index + 1");
        assert_eq!(body.num_args, 2);
        assert_eq!(body.bytecodes.len(), 12);
        // a-regs are shifted past the vregs.
        assert_eq!(
            body.bytecodes[2].operands(),
            [abcd_isa::Operand::Reg(1)],
            "sta a0"
        );
        assert_eq!(
            body.bytecodes[3].operands(),
            [abcd_isa::Operand::Reg(0), abcd_isa::Operand::Reg(2)],
            "mov v0, a1"
        );
        // The unlisted string got a synthetic offset.
        let hello = file.strings.get("hello").unwrap();
        assert!(file.entity_map.values().any(|&sid| sid == hello));
        // Emit side: hex immediates, scientific floats (inf/-nan included),
        // jump label naming, method signature rendering, STRING section.
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        for line in [
            "\tldai 0x7\n",
            "\tsta a0\n",
            "\tmov v0, a1\n",
            "\tfldai 1.500000e+00\n",
            "\tfldai 0.000000e+00\n",
            "\tfldai inf\n",
            "\tfldai -nan\n",
            "\tjmp jump_label_0\n",
            "jump_label_0:\n",
            "\tdefinefunc 0x0, g:(any), 0x0\n",
            "\tlda.str \"hello\"\n",
            "name_value:hello]",
        ] {
            assert!(text.contains(line), "missing {line:?} in {text}");
        }
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn out_of_bounds_jump_prints_raw_decimal() {
        let input = doc(b"", b"", &one_function(b"\tjmp 5\n"), b"");
        let file = parse_file(&input).expect("decimal jump parses");
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        // The upstream OOB-jump quirk round-trips the raw decimal index.
        assert!(text.contains("\tjmp 5\n"), "{text}");
    }

    #[test]
    fn jump_to_trailing_empty_label() {
        let input = doc(b"", b"", &one_function(b"\tnop\n\tjmp l_missing\n:\n"), b"");
        let file = parse_file(&input).expect("trailing-label jump parses");
        let global = file.class_by_str("L_GLOBAL;").unwrap();
        let body = global.methods[0].body.as_ref().unwrap();
        assert_eq!(body.bytecodes.len(), 2);
        assert_eq!(
            body.bytecodes[1].operands(),
            [abcd_isa::Operand::Label(2)],
            "one past the last instruction"
        );
    }

    #[test]
    fn typed_and_catchall_catches_share_a_try_range() {
        let input = doc(
            b"",
            b".record R {\n}\n",
            b".language ECMAScript\n.function any R.f() <static> {\nt0:\n\tnop\nh0:\n\treturnundefined\nt1:\nh1:\n\n.catch R, t0, t1, h0, h1\n.catchall t0, t1, h0\n}\n",
            b"",
        );
        let file = parse_file(&input).expect("typed catch parses");
        let r = file.class_by_str("LR;").unwrap();
        let body = r.methods[0].body.as_ref().unwrap();
        assert_eq!(body.try_blocks.len(), 1, "same range groups");
        let tb = &body.try_blocks[0];
        assert_eq!((tb.start, tb.len), (0, 2));
        assert_eq!(tb.catches.len(), 2, "second catch joins the range");
        assert_ne!(tb.catches[0].type_idx, u32::MAX, "typed catch record");
        assert_eq!(tb.catches[1].type_idx, u32::MAX, "catchall");
        // The typed record interned its descriptor.
        assert!(
            file.entity_map
                .values()
                .any(|&sid| file.strings.resolve(sid) == Some("LR;"))
        );
        // Emit side: `.catch <record>, …` rendering and the trailing `:`
        // (the try end binds one past the last instruction).
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        assert!(
            text.contains(
                ".catch R, try_begin_label_0, try_end_label_0, handler_begin_label_0_0, try_end_label_0\n"
            ),
            "{text}"
        );
        assert!(
            text.contains(
                ".catchall try_begin_label_0, try_end_label_0, handler_begin_label_0_0\n"
            ),
            "{text}"
        );
        assert!(text.contains("\treturnundefined\n:\n"), "{text}");
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn literals_all_tags_at_12x_round_trip() {
        let input = doc(
            b"0 0x10 { 12 [ u1:1, i8:5, i32:-7, f32:1.5, f64:2.5, string:\"lit\", ets_implements:\"Iface\", method:foo, generator_method:gen, accessor:2, null_value:0, method_affiliate:9, ]}\n1 0x20 { 3 [ getter:getf, setter:setf, async_generator_method:agen, ]}\n2 0x30 { 2 [ lit_index:2, builtin_type:3, ]}\n3 0x40 \n4 0x50 { 1 [ lit_offset:0x20, ]}\n",
            b"",
            b".language ECMAScript\n.function any foo() <static> {\n\treturnundefined\n}\n.language ECMAScript\n.function any gen() <static> {\n\treturnundefined\n}\n.language ECMAScript\n.function any getf() <static> {\n\treturnundefined\n}\n.language ECMAScript\n.function any setf() <static> {\n\treturnundefined\n}\n.language ECMAScript\n.function any agen() <static> {\n\treturnundefined\n}\n",
            b"",
        );
        let file = parse_file_with_version(&input, Version::new(12, 0, 6, 0))
            .expect("12.x literals parse");
        // Header table is rebuilt from the keys.
        assert_eq!(
            file.literal_array_header_offsets,
            [0x10, 0x20, 0x30, 0x40, 0x50]
        );
        let idx = |off: u32| file.literal_array_offsets[&off] as usize;
        let values = &file.literal_arrays[idx(0x10)].values;
        assert_eq!(values[0], LiteralValue::Bool(true));
        assert_eq!(values[1], LiteralValue::Integer8(5));
        assert_eq!(values[2], LiteralValue::Integer(-7i32 as u32));
        assert_eq!(values[3], LiteralValue::Float(1.5));
        assert_eq!(values[4], LiteralValue::Double(2.5));
        assert!(matches!(values[5], LiteralValue::String(_)));
        assert!(matches!(values[6], LiteralValue::EtsImplements(_)));
        assert!(matches!(values[7], LiteralValue::Method(_)));
        assert!(matches!(values[8], LiteralValue::GeneratorMethod(_)));
        assert_eq!(values[9], LiteralValue::Accessor(2));
        assert_eq!(values[10], LiteralValue::NullValue(0));
        assert_eq!(values[11], LiteralValue::MethodAffiliate(9));
        let accessors = &file.literal_arrays[idx(0x20)].values;
        assert!(matches!(accessors[0], LiteralValue::Getter(_)));
        assert!(matches!(accessors[1], LiteralValue::Setter(_)));
        assert!(matches!(
            accessors[2],
            LiteralValue::AsyncGeneratorMethod(_)
        ));
        let misc = &file.literal_arrays[idx(0x30)].values;
        assert_eq!(
            misc[0],
            LiteralValue::LiteralBufferIndex(LiteralArrayIdx(2))
        );
        assert_eq!(misc[1], LiteralValue::BuiltinTypeIndex(3));
        // The empty value stays empty.
        assert!(file.literal_arrays[idx(0x40)].values.is_empty());
        // lit_offset rewires to the target's table index.
        assert_eq!(
            file.literal_arrays[idx(0x50)].values[0],
            LiteralValue::LiteralArray(LiteralArrayIdx(idx(0x20) as u32))
        );
        // Emit side: all the non-corpus item tags print (Integer8 is the
        // upstream-dropped TAGVALUE).
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        for frag in [
            "u1:1",
            "i32:-7",
            "f32:1.5",
            "f64:2.5",
            "string:\"lit\"",
            "ets_implements:\"Iface\"",
            "method:foo",
            "generator_method:gen",
            "getter:getf",
            "setter:setf",
            "async_generator_method:agen",
            "accessor:2",
            "null_value:0",
            "method_affiliate:9",
            "lit_index:2",
            "builtin_type:3",
            "lit_offset:0x20",
        ] {
            assert!(text.contains(frag), "missing {frag:?} in {text}");
        }
        assert!(!text.contains("i8:"), "TAGVALUE items are dropped: {text}");
        // The empty array prints as nothing after the key's trailing space.
        assert!(text.contains("3 0x40 \n"), "{text}");
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn header_table_gap_fills_with_phase_offsets() {
        let input = doc(
            b"0 0x10 { 1 [ i32:1, ]}\n2 0x30 { 1 [ i32:2, ]}\n",
            b".record _ModuleRequestPhaseRecord {\n\tu32 moduleRequestPhaseIdx = 0x200\n}\n",
            b"",
            b"",
        );
        let file =
            parse_file_with_version(&input, Version::new(12, 0, 6, 0)).expect("12.x gap parse");
        assert_eq!(
            file.literal_array_header_offsets,
            [0x10, 0x200, 0x30],
            "the gap slot takes the phase-blob offset"
        );
        let phase = &file
            .class_by_str("L_ModuleRequestPhaseRecord;")
            .unwrap()
            .fields[0];
        assert!(matches!(
            phase.initial_value,
            Some(FieldValue::ModuleRequestPhase(_))
        ));
        // Emit side: the phase slot is excluded from the LITERALS listing
        // (the FIELD value itself prints, upstream-style).
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        assert!(text.contains("0 0x10 { 1 [ i32:1, ]}"), "{text}");
        assert!(text.contains("2 0x30 { 1 [ i32:2, ]}"), "{text}");
        assert!(!text.contains("1 0x200"), "phase slots never list: {text}");
        assert!(
            text.contains("\tu32 moduleRequestPhaseIdx = 0x200\n"),
            "{text}"
        );
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn strings_multiline_4byte_lossy_and_duplicates() {
        // STRING entries: a duplicate content (two offsets), an empty
        // content, a raw 4-byte UTF-8 content, and two lone-surrogate raw
        // forms whose lossy identities collide.
        let mut strings = b"[offset:0x40, name_value:dup]\n[offset:0x50, name_value:dup]\n[offset:0x80, name_value:]\n".to_vec();
        strings.extend_from_slice(b"[offset:0x60, name_value:");
        strings.extend_from_slice(&[0xF0, 0x9F, 0x98, 0x80]); // U+1F600, raw 4-byte
        strings.extend_from_slice(b"]\n[offset:0x70, name_value:");
        strings.extend_from_slice(&[0xED, 0xA0, 0xBD]); // lone high surrogate U+D83D
        strings.extend_from_slice(b"]\n[offset:0x78, name_value:");
        strings.extend_from_slice(&[0xED, 0xA0, 0xBE]); // lone high surrogate U+D83E
        strings.extend_from_slice(b"]\n");
        let mut methods =
            b".language ECMAScript\n.function any f() <static> {\n\tlda.str \"dup\"\n\tlda.str \"\"\n\tlda.str \"".to_vec();
        methods.extend_from_slice(&[0xF0, 0x9F, 0x98, 0x80]);
        methods.extend_from_slice(b"\"\n\tlda.str \"");
        methods.extend_from_slice(&[0xED, 0xA0, 0xBD]);
        methods.extend_from_slice(b"\"\n\tlda.str \"");
        // Same lossy raw form again: the duplicate-intern path.
        methods.extend_from_slice(&[0xED, 0xA0, 0xBD]);
        methods.extend_from_slice(b"\"\n\tlda.str \"");
        methods.extend_from_slice(&[0xED, 0xA0, 0xBE]);
        methods.extend_from_slice(b"\"\n\treturnundefined\n}\n");
        let input = doc(b"", b"", &methods, &strings);
        let file = parse_file(&input).expect("exotic strings parse");
        // The 4-byte form decoded to the astral character.
        assert!(file.strings.get("\u{1F600}").is_some());
        // Both lone-surrogate raw forms are registered (collision →
        // disambiguated identity).
        assert_eq!(
            file.string_raw_bytes.len(),
            2,
            "{:?}",
            file.string_raw_bytes
        );
        // Emit side: the raw bytes are re-emitted verbatim at their listed
        // offsets (the 4-byte form goes out as CESU-8, so anchor the
        // surrogate checks on their STRING entry headers).
        let out = super::super::emit_file(&file, "t.abc");
        for (off, raw) in [(0x70u8, [0xED, 0xA0, 0xBD]), (0x78, [0xED, 0xA0, 0xBE])] {
            let mut needle = format!("[offset:0x{off:x}, name_value:").into_bytes();
            needle.extend_from_slice(&raw);
            needle.push(b']');
            assert!(
                out.windows(needle.len()).any(|w| w == needle),
                "raw surrogate bytes preserved at {off:#x}"
            );
        }
        let dup = b"[offset:0x40, name_value:dup]";
        assert!(
            out.windows(dup.len()).any(|w| w == dup),
            "dup entry prints at its first listed offset"
        );
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn module_blob_13x_collects_and_round_trips() {
        let input = doc(
            b"0 0x100 { 5 [\n\tMODULE_REQUEST_ARRAY: {\n\t\t0 : req_a,\n\t\t1 : req_b,\n\t};\n\tModuleTag: REGULAR_IMPORT, local_name: la, import_name: ia, module_request: req_a;\n\tModuleTag: NAMESPACE_IMPORT, local_name: ln, module_request: req_b;\n\tModuleTag: LOCAL_EXPORT, local_name: ll, export_name: el;\n\tModuleTag: INDIRECT_EXPORT, export_name: ei, import_name: ii, module_request: req_a;\n\tModuleTag: STAR_EXPORT, module_request: req_b;\n\n]}\n",
            b".record _ESModuleRecord {\n\tu32 moduleRecordIdx = 0x100\n}\n.record _ESScopeNamesRecord {\n\tu32 scopeNames = 0x10\n}\n.record _ModuleRequestPhaseRecord {\n\tu32 moduleRequestPhaseIdx = 0x200\n}\n.record Ext <external>\n",
            b"",
            b"",
        );
        let file = parse_file(&input).expect("module blob parses");
        let class = file.class_by_str("L_ESModuleRecord;").unwrap();
        let Some(FieldValue::ModuleData(md)) = &class.fields[0].initial_value else {
            panic!("module field carries ModuleData");
        };
        assert_eq!(md.source_offset, 0x100);
        assert_eq!(md.requests.len(), 2);
        assert_eq!(md.records.len(), 5);
        assert!(matches!(md.records[0], ModuleRecord::RegularImport { .. }));
        assert!(matches!(
            md.records[1],
            ModuleRecord::NamespaceImport { .. }
        ));
        assert!(matches!(md.records[2], ModuleRecord::LocalExport { .. }));
        assert!(matches!(md.records[3], ModuleRecord::IndirectExport { .. }));
        assert!(matches!(md.records[4], ModuleRecord::StarExport { .. }));
        // The scope-names field references a synthesized empty array.
        let scope = &file.class_by_str("L_ESScopeNamesRecord;").unwrap().fields[0];
        assert_eq!(scope.initial_value, Some(FieldValue::LiteralArrayRef(0x10)));
        let idx = file.literal_array_offsets[&0x10] as usize;
        assert!(file.literal_arrays[idx].values.is_empty());
        // Emit side (13.x/24.x collector): the module blob routes to the
        // module table via the field-driven classification.
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        for frag in [
            "MODULE_REQUEST_ARRAY: {",
            "\t\t0 : req_a,",
            "ModuleTag: REGULAR_IMPORT, local_name: la, import_name: ia, module_request: req_a;",
            "ModuleTag: NAMESPACE_IMPORT, local_name: ln, module_request: req_b;",
            "ModuleTag: LOCAL_EXPORT, local_name: ll, export_name: el;",
            "ModuleTag: INDIRECT_EXPORT, export_name: ei, import_name: ii, module_request: req_a;",
            "ModuleTag: STAR_EXPORT, module_request: req_b;",
            ".record Ext <external>",
        ] {
            assert!(text.contains(frag), "missing {frag:?} in {text}");
        }
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn module_blob_leading_junk_is_tolerated() {
        // Handwritten tolerance: the section path requires the value to
        // START with `{`, but lines before the `{ N [` line are skipped.
        let input = doc(
            b"0 0x100 {}\n{ 0 [\n\tMODULE_REQUEST_ARRAY: {\n\t};\n]}\n",
            b"",
            b"",
            b"",
        );
        parse_file(&input).expect("leading junk before `{ N [` is skipped");
    }

    #[test]
    fn inline_literals_synthetic_registration_and_empty_operand() {
        let input = doc(
            b"0 0x10 { 1 [ i32:1, ]}\n",
            b"",
            b".language ECMAScript\n.function any f() <static> {\n\tcreatearraywithbuffer 0x0, { 1 [ i32:1, ]}\n\tcreatearraywithbuffer 0x1, { 2 [ i32:9, string:\"s\", ]}\n\tcreatearraywithbuffer 0x2\n\treturnundefined\n}\n.language ECMAScript\n.function  f.codeless() <static> {\n}\n",
            b"",
        );
        let file = parse_file(&input).expect("inline literals parse");
        let global = file.class_by_str("L_GLOBAL;").unwrap();
        let f = &global.methods[0];
        let body = f.body.as_ref().unwrap();
        assert_eq!(body.bytecodes.len(), 4);
        // The listed text resolves to its printed offset; the other two get
        // synthetic offsets.
        let offsets: Vec<u32> = body.entity_offsets.values().copied().collect();
        assert!(
            offsets.contains(&0x10),
            "listed literal offset: {offsets:?}"
        );
        assert!(
            offsets
                .iter()
                .filter(|&&o| o >= SYNTHETIC_OFFSET_BASE)
                .count()
                == 2
        );
        // The implicit empty operand parsed as an empty array.
        let synth: Vec<u32> = offsets
            .iter()
            .copied()
            .filter(|&o| o >= SYNTHETIC_OFFSET_BASE)
            .collect();
        let mut saw_empty = false;
        for off in synth {
            let idx = file.literal_array_offsets[&off] as usize;
            if file.literal_arrays[idx].values.is_empty() {
                saw_empty = true;
            }
        }
        assert!(saw_empty, "omitted literal operand = empty array");
        // Emit side (24.x collector): referenced arrays print.
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        assert!(text.contains("{ 1 [ i32:1, ]}"), "{text}");
        assert!(text.contains("{ 2 [ i32:9, string:\"s\", ]}"), "{text}");
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn nested_literal_arrays_via_lit_offset() {
        let input = doc(
            b"0 0x10 { 1 [ lit_offset:0x20, ]}\n1 0x20 { 1 [ i32:7, ]}\n",
            b"",
            b".language ECMAScript\n.function any f() <static> {\n\tcreatearraywithbuffer 0x0, { 1 [ lit_offset:0x20, ]}\n\treturnundefined\n}\n",
            b"",
        );
        let file = parse_file(&input).expect("nested literals parse");
        // 24.x emit: the nested array is collected transitively.
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        assert!(text.contains("{ 1 [ lit_offset:0x20, ]}"), "{text}");
        assert!(text.contains("{ 1 [ i32:7, ]}"), "{text}");
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn duplicate_signature_is_dropped_on_emit() {
        let input = doc(
            b"",
            b".record R {\n}\n",
            b".language ECMAScript\n.function any R.f() <static> {\n\tlda.str \"dupsig\"\n\treturnundefined\n}\n.language ECMAScript\n.function any R.f() <static> {\n\treturnundefined\n}\n",
            b"",
        );
        let file = parse_file(&input).expect("duplicate signatures parse");
        let r = file.class_by_str("LR;").unwrap();
        assert_eq!(r.methods.len(), 2, "the model keeps both");
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        assert_eq!(
            text.matches(".function any R.f() <static> {").count(),
            1,
            "the second same-signature function is dropped: {text}"
        );
    }

    #[test]
    fn non_static_method_gains_this_param() {
        let input = doc(
            b"",
            b".record R {\n}\n",
            b".language ECMAScript\n.function any R.m(R a0) {\n\treturnundefined\n}\n",
            b"",
        );
        let file = parse_file(&input).expect("non-static method parses");
        let r = file.class_by_str("LR;").unwrap();
        let m = &r.methods[0];
        assert!(!m.is_static());
        let body = m.body.as_ref().unwrap();
        assert_eq!(body.num_args, 0, "the printed param is `this`");
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        assert!(text.contains(".function any R.m(R a0) {"), "{text}");
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn non_ascii_method_names_and_signatures() {
        let mut methods = b".language ECMAScript\n.function any ".to_vec();
        methods.push(0xE9); // non-ASCII bare name
        methods.extend_from_slice(b"() <static> {\n\treturnundefined\n}\n.language ECMAScript\n.function any f() <static> {\n\tdefinefunc 0x0, ");
        methods.push(0xE9);
        methods.extend_from_slice(b":(), 0x0\n\tjmp ");
        methods.push(0xE9);
        methods.push(b'\n');
        methods.push(0xE9);
        methods.extend_from_slice(b":\n\treturnundefined\n}\n");
        let input = doc(b"", b"", &methods, b"");
        let file = parse_file(&input).expect("non-ASCII method ref parses");
        let global = file.class_by_str("L_GLOBAL;").unwrap();
        assert_eq!(global.methods.len(), 2);
        let f = global
            .methods
            .iter()
            .find(|m| file.strings.resolve(m.name) == Some("f"))
            .unwrap();
        let body = f.body.as_ref().unwrap();
        assert_eq!(body.bytecodes[0].mnemonic(), "definefunc");
        // The non-ASCII bare label resolved to the final instruction index.
        assert_eq!(
            body.bytecodes[1].operands(),
            [abcd_isa::Operand::Label(2)],
            "non-ASCII label"
        );
    }

    #[test]
    fn blank_lines_are_tolerated_in_record_bodies() {
        let input = doc(b"", b".record R {\n\n\tu32 x = 0x1\n\n}\n", b"", b"");
        let file = parse_file(&input).expect("blank lines in records parse");
        let r = file.class_by_str("LR;").unwrap();
        assert_eq!(r.fields.len(), 1);
    }

    #[test]
    fn parse_error_display_and_error_trait() {
        let err = parse_file(b"garbage").expect_err("garbage rejected");
        assert_eq!(
            format!("{err}"),
            "pandasm parse error at line 0: expected exactly four section banners (LITERALS/RECORDS/METHODS/STRING)"
        );
        assert_eq!(err.line, 0);
        // The std::error::Error impl is usable as a trait object.
        let _: &dyn std::error::Error = &err;
    }

    #[test]
    fn catch_may_target_the_trailing_empty_label() {
        // A catch label absent from the label table but covered by the
        // trailing `:` quirk binds one past the last instruction.
        let input = doc(
            b"",
            b"",
            b".language ECMAScript\n.function any f() <static> {\n\tnop\nl1:\nh:\n:\n.catchall l1, missing_end, h\n}\n",
            b"",
        );
        let file = parse_file(&input).expect("trailing-label catch parses");
        let global = file.class_by_str("L_GLOBAL;").unwrap();
        let body = global.methods[0].body.as_ref().unwrap();
        assert_eq!(body.try_blocks.len(), 1);
        let tb = &body.try_blocks[0];
        assert_eq!((tb.start, tb.len), (1, 0), "try end = insn_count");
        assert_eq!((tb.catches[0].handler, tb.catches[0].len), (1, 0));
    }

    #[test]
    fn module_field_without_a_printed_blob_builds_empty() {
        // 13.x/24.x handwritten shape: the module blob offset the field
        // names was never printed, so the model gets an empty blob.
        let input = doc(
            b"",
            b".record _ESModuleRecord {\n\tu32 moduleRecordIdx = 0x999\n}\n",
            b"",
            b"",
        );
        let file = parse_file(&input).expect("blob-less module field parses");
        let class = file.class_by_str("L_ESModuleRecord;").unwrap();
        let Some(FieldValue::ModuleData(md)) = &class.fields[0].initial_value else {
            panic!("module field carries ModuleData");
        };
        assert_eq!(md.source_offset, 0x999);
        assert!(md.requests.is_empty());
        assert!(md.records.is_empty());
        // Emit side (24.x): the empty blob routes to the module table.
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        assert!(
            text.contains("0 0x999 { 0 [\n\tMODULE_REQUEST_ARRAY: {\n\t};\n]}\n"),
            "{text}"
        );
    }

    #[test]
    fn module_blob_via_the_12x_header_table() {
        let input = doc(
            b"0 0x100 { 1 [\n\tMODULE_REQUEST_ARRAY: {\n\t\t0 : r,\n\t};\n\tModuleTag: STAR_EXPORT, module_request: r;\n]}\n",
            b".record _ESModuleRecord {\n\tu32 moduleRecordIdx = 0x100\n}\n",
            b"",
            b"",
        );
        let file = parse_file_with_version(&input, Version::new(12, 0, 6, 0))
            .expect("12.x module blob parses");
        assert_eq!(file.literal_array_header_offsets, [0x100]);
        // Emit side: the header-table walk routes the offset to the module
        // table (module_data_at hit).
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        assert!(
            text.contains("0 0x100 { 1 [\n\tMODULE_REQUEST_ARRAY: {\n\t\t0 : r,\n\t};\n\tModuleTag: STAR_EXPORT, module_request: r;\n]}\n"),
            "{text}"
        );
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn multiline_literal_string_via_the_oracle() {
        // A literal-array string spanning physical lines whose content the
        // STRING section lists: the completeness scan closes it via the
        // oracle (not the same-line fallback).
        let input = doc(
            b"0 0x10 { 1 [ string:\"x\ny\", ]}\n",
            b"",
            b"",
            b"[offset:0x40, name_value:x\ny]",
        );
        let file = parse_file(&input).expect("multi-line literal string parses");
        let idx = file.literal_array_offsets[&0x10] as usize;
        let expected = file.strings.get("x\ny").unwrap();
        assert_eq!(
            file.literal_arrays[idx].values,
            [LiteralValue::String(expected)]
        );
    }

    #[test]
    fn same_content_arrays_distribute_round_robin() {
        // Fourteen identical literal arrays: the build rank-orders the
        // same-content group by printed index, references bind round-robin,
        // and the 13.x collector's unordered_set simulation rehashes.
        let offsets: [u32; 14] = [
            0x10, 0x1d, 0x2d, 0x24, 0x28, 0x2c, 0x30, 0x34, 0x38, 0x3c, 0x40, 0x44, 0x48, 0x4c,
        ];
        let mut literals = Vec::new();
        for (i, off) in offsets.iter().enumerate() {
            literals.extend_from_slice(format!("{i} 0x{off:x} {{ 1 [ i32:0, ]}}\n").as_bytes());
        }
        let mut methods = b".language ECMAScript\n.function any f() <static> {\n".to_vec();
        for i in 0..14u8 {
            methods.extend_from_slice(
                format!("\tcreatearraywithbuffer 0x{i:x}, {{ 1 [ i32:0, ]}}\n").as_bytes(),
            );
        }
        methods.extend_from_slice(b"\treturnundefined\n}\n");
        let input = doc(&literals, b"", &methods, b"");
        let file = parse_file(&input).expect("same-content arrays parse");
        let global = file.class_by_str("L_GLOBAL;").unwrap();
        let body = global.methods[0].body.as_ref().unwrap();
        // Every printed offset is referenced exactly once, in rank order.
        let got: Vec<u32> = (0..14u32)
            .map(|id| body.entity_offsets[&(EntityKind::LiteralarrayId, id)])
            .collect();
        assert_eq!(got, offsets, "rank order = printed index order");
        // Emit side: all fourteen collect (rehash + same-bucket inserts) —
        // once each in the LITERALS listing and once per inline operand.
        let out = super::super::emit_file(&file, "t.abc");
        let text = String::from_utf8_lossy(&out);
        assert_eq!(text.matches("{ 1 [ i32:0, ]}").count(), 28, "{text}");
        crate::encode(&file).expect("encodes");
    }

    #[test]
    fn multiline_operand_prefers_the_longest_oracle_match() {
        // Oracle: "ab" and "ab\"\nq". The one-line reading already parses,
        // but the tail after the close quote is still an oracle prefix, so
        // the lookahead extends and the two-line reading wins on matched
        // string bytes.
        let input = doc(
            b"",
            b"",
            b".language ECMAScript\n.function any f() <static> {\n\tlda.str \"ab\"\nq\"\n\treturnundefined\n}\n",
            b"[offset:0x40, name_value:ab]\n[offset:0x50, name_value:ab\"\nq]",
        );
        let file = parse_file(&input).expect("longest match parses");
        let global = file.class_by_str("L_GLOBAL;").unwrap();
        let body = global.methods[0].body.as_ref().unwrap();
        assert_eq!(body.bytecodes.len(), 2, "the insn spans two lines");
        // The operand is the two-line string at its listed offset.
        assert_eq!(body.entity_offsets[&(EntityKind::StringId, 0)], 0x50);
        assert!(file.strings.get("ab\"\nq").is_some());
    }

    // -- Mainline batch: a moderate document, byte-exact ---------------------

    #[test]
    fn moderate_document_round_trip_is_byte_exact() {
        let input: &[u8] = b"# source binary: t.abc\n\n# ====================\n# LITERALS\n\n0 0x10 { 1 [ i32:7, ]}\n\n# ====================\n# RECORDS\n\n.language ECMAScript\n.record R {\n\tu32 x = 0x2a\n}\n\n# ====================\n# METHODS\n\n.language ECMAScript\n.function any R.f() <static> {\n\tcreatearraywithbuffer 0x0, { 1 [ i32:7, ]}\n\treturnundefined\n}\n\n# ====================\n# STRING\n\n";
        let file =
            parse_file_with_version(input, Version::new(12, 0, 6, 0)).expect("moderate doc parses");
        let out = super::super::emit_file(&file, "t.abc");
        assert_eq!(out, input, "parse->emit must be byte-exact");
        // The emitted text is a parse fixpoint.
        let file2 = parse_file_with_version(&out, Version::new(12, 0, 6, 0)).expect("re-parse");
        assert_eq!(super::super::emit_file(&file2, "t.abc"), input);
        crate::encode(&file).expect("encodes");
    }
}
