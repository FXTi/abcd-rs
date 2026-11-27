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
//! model (`LiteralArray::source_offset` / `literal_array_header_offsets` /
//! `MethodBody::entities` / `FieldValue::LiteralArrayRef`), so `parse_file` →
//! `emit_file` is a byte-exact round trip. A fresh `encode` re-lays the file out (the
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

mod build;
mod scan;

#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, HashMap, HashSet};

use abcd_isa::Version;

use crate::model::File;
use crate::types::SourceLang;
use crate::{StringId, StringPool};

use build::record_descriptor;
pub(crate) use scan::parse_literal_key;
use scan::{
    LiteralCompleteScanner, Oracle, compute_oracle_hash, insn_ops_parse_ext,
    is_quote_followed_by_separator, parse_catch_line, parse_language, parse_module_record,
    parse_operand_token, split_operands, split_sections, step_oracle_hash,
};

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
    ArrayU1(Vec<bool>),
    ArrayU8(Vec<u8>),
    ArrayI8(Vec<i8>),
    ArrayU16(Vec<u16>),
    ArrayI16(Vec<i16>),
    ArrayU32(Vec<u32>),
    ArrayI32(Vec<i32>),
    ArrayU64(Vec<u64>),
    ArrayI64(Vec<i64>),
    ArrayF32(Vec<f32>),
    ArrayF64(Vec<f64>),
    ArrayString(Vec<Vec<u8>>),
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
    /// Lossless MUTF-8 / UTF-8 string pool (#30).
    strings: StringPool,
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
    /// Module blob offset → parsed module data (`BTreeMap` for `N20` deterministic fallback order).
    modules: BTreeMap<u32, PaModule>,
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
            string_offsets: HashMap::new(),
            regular: Vec::new(),
            lit_by_text: HashMap::new(),
            lit_by_offset: HashMap::new(),
            modules: BTreeMap::new(),
            nested_targets: HashSet::new(),
            key_index_to_offset: Vec::new(),
            records: Vec::new(),
            functions: Vec::new(),
        }
    }

    /// Intern raw MUTF-8 bytes losslessly into [`StringPool`] (#30).
    fn intern(&mut self, raw: &[u8]) -> Result<StringId, ParseError> {
        Ok(self.strings.intern_mutf8(raw))
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
        let mut line_no = base;
        while pos < body.len() {
            if body[pos..].starts_with(b"[offset:0x") {
                starts.push((pos, line_no));
            }
            match body[pos..].iter().position(|&b| b == b'\n') {
                Some(nl) => {
                    pos += nl + 1;
                    line_no += 1;
                }
                None => break,
            }
        }
        for (i, &(start, line)) in starts.iter().enumerate() {
            let end = starts.get(i + 1).map_or(body.len(), |&(next, _)| next);
            let entry = trim_end(&body[start..end]);
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
            // incremental oracle-aware scanner finds the closing `]}`.
            let mut acc = line[value_start..].to_vec();
            let mut scanner = LiteralCompleteScanner::default();
            let mut j = i + 1;
            let value = loop {
                if scanner.is_complete(&acc, &self.oracle) {
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
                    let mut strings: Vec<Vec<u8>> = Vec::new();
                    for item in items {
                        match item {
                            PaItem::Str(s) | PaItem::EtsImplements(s) => strings.push(s.clone()),
                            PaItem::ArrayString(arr) => strings.extend(arr.iter().cloned()),
                            _ => {}
                        }
                    }
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
            b"array_u1" | b"array_u8" | b"array_i8" | b"array_u16" | b"array_i16"
            | b"array_u32" | b"array_i32" | b"array_u64" | b"array_i64" | b"array_f32"
            | b"array_f64" | b"array_string" => self.parse_typed_literal_array(tag, value, line)?,
            other => {
                return err(
                    line,
                    format!("unknown literal tag `{}`", String::from_utf8_lossy(other)),
                );
            }
        })
    }

    fn parse_typed_literal_array(
        &self,
        tag: &[u8],
        value: &[u8],
        line: usize,
    ) -> Result<PaItem, ParseError> {
        let Some(inner) = value.strip_prefix(b"[").and_then(|s| s.strip_suffix(b"]")) else {
            return err(line, "typed literal array value must be bracketed `[...]`");
        };
        let (tokens, _, _) = split_operands(inner, &self.oracle).ok_or_else(|| ParseError {
            line,
            message: "unterminated string in typed literal array".to_owned(),
        })?;
        fn parse_ascii(raw: &[u8], line: usize) -> Result<&str, ParseError> {
            std::str::from_utf8(raw).map_err(|_| ParseError {
                line,
                message: "typed literal array element is not ASCII".to_owned(),
            })
        }
        match tag {
            b"array_u1" => {
                let mut out = Vec::with_capacity(tokens.len());
                for t in &tokens {
                    let s = parse_ascii(t, line)?;
                    let v = s.parse::<i64>().map_err(|_| ParseError {
                        line,
                        message: format!("array_u1 element `{s}` does not parse"),
                    })?;
                    out.push(v != 0);
                }
                Ok(PaItem::ArrayU1(out))
            }
            b"array_u8" => {
                let mut out = Vec::with_capacity(tokens.len());
                for t in &tokens {
                    let s = parse_ascii(t, line)?;
                    out.push(s.parse::<u8>().map_err(|_| ParseError {
                        line,
                        message: format!("array_u8 element `{s}` does not parse"),
                    })?);
                }
                Ok(PaItem::ArrayU8(out))
            }
            b"array_i8" => {
                let mut out = Vec::with_capacity(tokens.len());
                for t in &tokens {
                    let s = parse_ascii(t, line)?;
                    out.push(s.parse::<i8>().map_err(|_| ParseError {
                        line,
                        message: format!("array_i8 element `{s}` does not parse"),
                    })?);
                }
                Ok(PaItem::ArrayI8(out))
            }
            b"array_u16" => {
                let mut out = Vec::with_capacity(tokens.len());
                for t in &tokens {
                    let s = parse_ascii(t, line)?;
                    out.push(s.parse::<u16>().map_err(|_| ParseError {
                        line,
                        message: format!("array_u16 element `{s}` does not parse"),
                    })?);
                }
                Ok(PaItem::ArrayU16(out))
            }
            b"array_i16" => {
                let mut out = Vec::with_capacity(tokens.len());
                for t in &tokens {
                    let s = parse_ascii(t, line)?;
                    out.push(s.parse::<i16>().map_err(|_| ParseError {
                        line,
                        message: format!("array_i16 element `{s}` does not parse"),
                    })?);
                }
                Ok(PaItem::ArrayI16(out))
            }
            b"array_u32" => {
                let mut out = Vec::with_capacity(tokens.len());
                for t in &tokens {
                    let s = parse_ascii(t, line)?;
                    out.push(s.parse::<u32>().map_err(|_| ParseError {
                        line,
                        message: format!("array_u32 element `{s}` does not parse"),
                    })?);
                }
                Ok(PaItem::ArrayU32(out))
            }
            b"array_i32" => {
                let mut out = Vec::with_capacity(tokens.len());
                for t in &tokens {
                    let s = parse_ascii(t, line)?;
                    out.push(s.parse::<i32>().map_err(|_| ParseError {
                        line,
                        message: format!("array_i32 element `{s}` does not parse"),
                    })?);
                }
                Ok(PaItem::ArrayI32(out))
            }
            b"array_u64" => {
                let mut out = Vec::with_capacity(tokens.len());
                for t in &tokens {
                    let s = parse_ascii(t, line)?;
                    out.push(s.parse::<u64>().map_err(|_| ParseError {
                        line,
                        message: format!("array_u64 element `{s}` does not parse"),
                    })?);
                }
                Ok(PaItem::ArrayU64(out))
            }
            b"array_i64" => {
                let mut out = Vec::with_capacity(tokens.len());
                for t in &tokens {
                    let s = parse_ascii(t, line)?;
                    out.push(s.parse::<i64>().map_err(|_| ParseError {
                        line,
                        message: format!("array_i64 element `{s}` does not parse"),
                    })?);
                }
                Ok(PaItem::ArrayI64(out))
            }
            b"array_f32" => {
                let mut out = Vec::with_capacity(tokens.len());
                for t in &tokens {
                    let s = parse_ascii(t, line)?;
                    let v = if let Some(hex) = s.strip_prefix("bits:0x") {
                        let bits = u32::from_str_radix(hex, 16).map_err(|_| ParseError {
                            line,
                            message: format!("array_f32 bits `{s}` does not parse"),
                        })?;
                        f32::from_bits(bits)
                    } else {
                        s.parse::<f32>().map_err(|_| ParseError {
                            line,
                            message: format!("array_f32 element `{s}` does not parse"),
                        })?
                    };
                    out.push(v);
                }
                Ok(PaItem::ArrayF32(out))
            }
            b"array_f64" => {
                let mut out = Vec::with_capacity(tokens.len());
                for t in &tokens {
                    let s = parse_ascii(t, line)?;
                    let v = if let Some(hex) = s.strip_prefix("bits:0x") {
                        let bits = u64::from_str_radix(hex, 16).map_err(|_| ParseError {
                            line,
                            message: format!("array_f64 bits `{s}` does not parse"),
                        })?;
                        f64::from_bits(bits)
                    } else {
                        s.parse::<f64>().map_err(|_| ParseError {
                            line,
                            message: format!("array_f64 element `{s}` does not parse"),
                        })?
                    };
                    out.push(v);
                }
                Ok(PaItem::ArrayF64(out))
            }
            b"array_string" => {
                let mut out = Vec::with_capacity(tokens.len());
                for t in &tokens {
                    if t.len() >= 2 && t[0] == b'"' && t[t.len() - 1] == b'"' {
                        out.push(t[1..t.len() - 1].to_vec());
                    } else {
                        return err(line, "array_string element is not quoted");
                    }
                }
                Ok(PaItem::ArrayString(out))
            }
            _ => unreachable!(),
        }
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
        let mut seen_descriptors: HashSet<Vec<u8>> = HashSet::new();
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
            let record_line = base + i;
            let Some(rest) = line.strip_prefix(b".record ") else {
                return err(record_line, "expected `.record` or `.language`");
            };
            if let Some(name) = rest.strip_suffix(b" <external>") {
                if !seen_descriptors.insert(record_descriptor(name)) {
                    return err(
                        record_line,
                        format!("duplicate .record `{}`", String::from_utf8_lossy(name)),
                    );
                }
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
                return err(record_line, "malformed `.record` header");
            };
            if !seen_descriptors.insert(record_descriptor(name)) {
                return err(
                    record_line,
                    format!("duplicate .record `{}`", String::from_utf8_lossy(name)),
                );
            }
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

    /// Parse one instruction starting at physical line `i`, with
    /// oracle-guided multi-line lookahead for raw strings that span lines.
    /// Returns the next unconsumed line index.
    fn parse_instruction(
        &mut self,
        lines: &[&[u8]],
        i: usize,
        fun: &mut PaFunction,
        base: usize,
    ) -> Result<usize, ParseError> {
        type BestCandidate = (usize, Vec<u8>, Vec<Vec<u8>>, usize);
        let first_line = trim_start(lines[i]);
        let mut acc = first_line.to_vec();
        let mut best: Option<BestCandidate> = None;
        let mut j = i + 1;

        let active_open = match insn_ops_parse_ext(&acc, &self.oracle, true) {
            Ok((mnemonic, tokens, string_bytes, probe_open)) => {
                best = Some((j, mnemonic, tokens, string_bytes));
                probe_open.filter(|&o| self.oracle.has_string_prefix(&acc[o + 1..]))
            }
            Err(open) => self
                .oracle
                .has_string_prefix(&acc[open + 1..])
                .then_some(open),
        };

        if let Some(mut open_idx) = active_open
            && let Some(mut witness) = self.oracle.first_multi_with_prefix(&acc[open_idx + 1..])
        {
            let mut cur_hash = compute_oracle_hash(&acc[open_idx + 1..]);
            let mut witness_checked = acc.len() - (open_idx + 1);

            while j < lines.len() {
                let prev_len = acc.len();
                acc.push(b'\n');
                acc.extend_from_slice(lines[j]);
                j += 1;

                let mut line_had_oracle_close = false;
                for pos in prev_len..acc.len() {
                    let b = acc[pos];
                    if b == b'"'
                        && is_quote_followed_by_separator(&acc, pos, false)
                        && self
                            .oracle
                            .contains_hashed(&acc[open_idx + 1..pos], cur_hash)
                    {
                        line_had_oracle_close = true;
                    }
                    cur_hash = step_oracle_hash(cur_hash, b);
                }

                let full_len = acc.len() - (open_idx + 1);
                let mut still_prefix = if full_len > self.oracle.max_multi_len {
                    false
                } else if witness.len() >= full_len
                    && witness[witness_checked..full_len] == acc[open_idx + 1 + witness_checked..]
                {
                    witness_checked = full_len;
                    true
                } else if let Some(new_w) =
                    self.oracle.first_multi_with_prefix(&acc[open_idx + 1..])
                {
                    witness = new_w;
                    witness_checked = full_len;
                    true
                } else {
                    false
                };

                if line_had_oracle_close {
                    match insn_ops_parse_ext(&acc, &self.oracle, true) {
                        Ok((mnemonic, tokens, string_bytes, probe_open)) => {
                            let better = match &best {
                                None => true,
                                Some((_, _, _, prev)) => string_bytes > *prev,
                            };
                            if better {
                                best = Some((j, mnemonic, tokens, string_bytes));
                            }
                            match probe_open {
                                Some(po) if po == open_idx => {}
                                Some(po) => {
                                    if let Some(w2) =
                                        self.oracle.first_multi_with_prefix(&acc[po + 1..])
                                    {
                                        open_idx = po;
                                        cur_hash = compute_oracle_hash(&acc[open_idx + 1..]);
                                        witness = w2;
                                        witness_checked = acc.len() - (open_idx + 1);
                                        still_prefix = true;
                                    } else {
                                        still_prefix = false;
                                    }
                                }
                                None => still_prefix = false,
                            }
                        }
                        Err(new_open) => {
                            if new_open != open_idx {
                                if let Some(w2) =
                                    self.oracle.first_multi_with_prefix(&acc[new_open + 1..])
                                {
                                    open_idx = new_open;
                                    cur_hash = compute_oracle_hash(&acc[open_idx + 1..]);
                                    witness = w2;
                                    witness_checked = acc.len() - (open_idx + 1);
                                    still_prefix = true;
                                } else {
                                    still_prefix = false;
                                }
                            }
                        }
                    }
                }

                if !still_prefix {
                    break;
                }
            }
        }

        if best.is_none()
            && let Ok((mnemonic, tokens, string_bytes, _)) =
                insn_ops_parse_ext(first_line, &self.oracle, false)
        {
            best = Some((i + 1, mnemonic, tokens, string_bytes));
        }
        let Some((end, mnemonic, tokens, _)) = best else {
            return err(base + i, "unterminated string in instruction");
        };
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
}
