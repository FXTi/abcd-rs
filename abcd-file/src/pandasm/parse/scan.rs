//! Byte-level lexing, `STRING`-section quote oracle, incremental literal
//! completeness scanning, and line-level token/directive parsers.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::types::SourceLang;

use super::{PaCatch, PaModuleRecord, PaOp, ParseError, err, trim, trim_start};

// The string oracle (raw contents may contain quotes/commas/newlines)
// ---------------------------------------------------------------------------

#[inline]
pub(super) fn step_oracle_hash(h: u64, b: u8) -> u64 {
    h.wrapping_mul(0x0100_0000_01b3)
        .wrapping_add(u64::from(b).wrapping_add(1))
}

pub(super) fn compute_oracle_hash(bytes: &[u8]) -> u64 {
    let mut h = 0u64;
    for &b in bytes {
        h = step_oracle_hash(h, b);
    }
    h
}

/// Candidate string contents used to delimit raw-printed strings. Seeded
/// from the STRING section (exhaustive for instruction string operands)
/// and extended with every literal-array string as it is parsed. `multi`
/// holds the quote/newline-bearing contents, sorted, for prefix probes.
#[derive(Default)]
pub(super) struct Oracle {
    set: HashSet<Vec<u8>>,
    len_hashes: HashSet<(usize, u64)>,
    multi: BTreeSet<Box<[u8]>>,
    pub(super) max_multi_len: usize,
}

impl Oracle {
    pub(super) fn add(&mut self, content: &[u8]) {
        if !self.set.insert(content.to_vec()) {
            return;
        }
        self.len_hashes
            .insert((content.len(), compute_oracle_hash(content)));
        if content.contains(&b'"') || content.contains(&b'\n') {
            self.max_multi_len = self.max_multi_len.max(content.len());
            self.multi.insert(content.into());
        }
    }

    #[inline]
    pub(super) fn contains_hashed(&self, content: &[u8], hash: u64) -> bool {
        self.len_hashes.contains(&(content.len(), hash)) && self.set.contains(content)
    }

    pub(super) fn first_multi_with_prefix(&self, prefix: &[u8]) -> Option<&[u8]> {
        if self.multi.is_empty() || prefix.len() > self.max_multi_len {
            return None;
        }
        use std::ops::Bound;
        self.multi
            .range::<[u8], _>((Bound::Included(prefix), Bound::Unbounded))
            .next()
            .and_then(|s| s.starts_with(prefix).then_some(s.as_ref()))
    }

    /// Does any quote/newline-bearing oracle string start with `prefix`?
    pub(super) fn has_string_prefix(&self, prefix: &[u8]) -> bool {
        self.first_multi_with_prefix(prefix).is_some()
    }
}

#[inline]
pub(super) fn is_quote_followed_by_separator(
    buf: &[u8],
    quote_pos: usize,
    allow_newline_ws: bool,
) -> bool {
    let mut k = quote_pos + 1;
    while k < buf.len()
        && (matches!(buf[k], b' ' | b'\t' | b'\r') || (allow_newline_ws && buf[k] == b'\n'))
    {
        k += 1;
    }
    k == buf.len() || matches!(buf[k], b',' | b']' | b'}')
}

/// Scan forward from an opening quote at `open` in `O(matched_len)` time using
/// rolling hashes and incremental `oracle.multi` prefix pruning.
///
/// Returns `(best_oracle_close, first_same_line_quote, tail_is_multi_prefix)`.
fn scan_quote_forward(
    buf: &[u8],
    open: usize,
    oracle: &Oracle,
    allow_newline_ws_after_close: bool,
) -> (Option<usize>, Option<usize>, bool) {
    let start = open + 1;
    let mut cur_hash = 0u64;
    let mut seen_newline = false;
    let mut first_same_line_quote = None;
    let mut best_oracle_close = None;
    let mut witness: Option<&[u8]> = None;
    let mut witness_checked = 0usize;
    let mut prefix_dead = oracle.multi.is_empty();

    let mut pos = start;
    while pos < buf.len() {
        let b = buf[pos];
        if b == b'"' {
            if !seen_newline && first_same_line_quote.is_none() {
                first_same_line_quote = Some(pos);
            }
            if is_quote_followed_by_separator(buf, pos, allow_newline_ws_after_close)
                && oracle.contains_hashed(&buf[start..pos], cur_hash)
            {
                best_oracle_close = Some(pos);
            }
            cur_hash = step_oracle_hash(cur_hash, b);
            let prefix_len = pos + 1 - start;
            if prefix_dead || prefix_len > oracle.max_multi_len {
                prefix_dead = true;
                break;
            }
            let still_matches = match witness {
                Some(w)
                    if w.len() >= prefix_len
                        && w[witness_checked..prefix_len] == buf[start + witness_checked..=pos] =>
                {
                    witness_checked = prefix_len;
                    true
                }
                _ => match oracle.first_multi_with_prefix(&buf[start..=pos]) {
                    Some(w) => {
                        witness = Some(w);
                        witness_checked = prefix_len;
                        true
                    }
                    None => false,
                },
            };
            if !still_matches {
                prefix_dead = true;
                break;
            }
        } else {
            if b == b'\n' {
                seen_newline = true;
            }
            cur_hash = step_oracle_hash(cur_hash, b);
            let prefix_len = pos + 1 - start;
            if !prefix_dead && prefix_len > oracle.max_multi_len {
                prefix_dead = true;
                if best_oracle_close.is_some() || first_same_line_quote.is_some() || seen_newline {
                    break;
                }
            }
        }
        pos += 1;
    }

    let full_len = buf.len() - start;
    let tail_is_multi_prefix = if prefix_dead || full_len > oracle.max_multi_len {
        false
    } else {
        match witness {
            Some(w)
                if w.len() >= full_len
                    && w[witness_checked..full_len] == buf[start + witness_checked..] =>
            {
                true
            }
            _ => oracle.has_string_prefix(&buf[start..]),
        }
    };

    (
        best_oracle_close,
        first_same_line_quote,
        tail_is_multi_prefix,
    )
}

/// Split a pandasm operand list at top-level commas, respecting
/// `()`/`{}`/`[]` groups and oracle-delimited raw strings (ported from the
/// dis-side comparison harness).
///
/// When `defer_oracle_prefix` is true, an opening quote whose remainder
/// `&rest[i + 1..]` is an active prefix of a quote/newline-bearing oracle
/// entry will NOT prematurely close on an embedded same-line `"`, and any
/// unclosed string reports the earliest active-prefix opening quote (or the
/// unclosed quote `i`) via `Err(open_idx)`.
type SplitOperandsOk = (Vec<Vec<u8>>, usize, Option<usize>);

fn split_operands_ext(
    rest: &[u8],
    oracle: &Oracle,
    defer_oracle_prefix: bool,
) -> Result<SplitOperandsOk, usize> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut cur: Vec<u8> = Vec::new();
    let mut string_bytes = 0usize;
    let mut last_open = None;
    let mut prefix_open: Option<usize> = None;
    let mut depth = 0i32;
    let mut i = 0usize;
    while i < rest.len() {
        let b = rest[i];
        if b == b'"' {
            let (oracle_close, first_quote, tail_is_prefix) =
                scan_quote_forward(rest, i, oracle, !defer_oracle_prefix);
            if defer_oracle_prefix && prefix_open.is_none() && tail_is_prefix {
                prefix_open = Some(i);
            }
            let close = match oracle_close {
                Some(c) => c,
                None => {
                    // Defer same-line quote pairing while the opened string
                    // is a prefix of a quote/newline-bearing oracle entry so
                    // embedded `"` characters on line 1 never split early.
                    if defer_oracle_prefix && tail_is_prefix {
                        return Err(prefix_open.unwrap_or(i));
                    }
                    // Fallback for hand-written single-line strings absent
                    // from the STRING oracle: next quote on the same line.
                    match first_quote {
                        Some(cand) => {
                            if defer_oracle_prefix {
                                if is_quote_followed_by_separator(rest, cand, false) {
                                    cand
                                } else {
                                    return Err(prefix_open.unwrap_or(i));
                                }
                            } else {
                                cand
                            }
                        }
                        None => return Err(prefix_open.unwrap_or(i)),
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
    Ok((out, string_bytes, prefix_open.or(last_open)))
}

pub(super) fn split_operands(
    rest: &[u8],
    oracle: &Oracle,
) -> Option<(Vec<Vec<u8>>, usize, Option<usize>)> {
    split_operands_ext(rest, oracle, false).ok()
}

// Section parsing
// ---------------------------------------------------------------------------

/// The four banner-delimited sections, each with the 1-based line number
/// of its first body line (for error reporting).
pub(super) struct Sections<'a> {
    pub(super) literals: (&'a [u8], usize),
    pub(super) records: (&'a [u8], usize),
    pub(super) methods: (&'a [u8], usize),
    pub(super) strings: (&'a [u8], usize),
}

/// 1-based line number of the line starting at byte offset `off`.
fn line_of(text: &[u8], off: usize) -> usize {
    1 + text[..off.min(text.len())]
        .iter()
        .filter(|&&b| b == b'\n')
        .count()
}

pub(super) fn split_sections(text: &[u8]) -> Result<Sections<'_>, ParseError> {
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
    let value_start = sp.checked_add(4)?.checked_add(hex_len)?;
    if value_start > line.len() {
        return None;
    }
    Some((index, offset, value_start))
}

#[derive(Default)]
pub(super) struct LiteralCompleteScanner {
    pos: usize,
    depth: i32,
    open_quote: Option<LiteralQuoteState>,
}

struct LiteralQuoteState {
    open: usize,
    cur_hash: u64,
    seen_newline: bool,
    first_same_line_quote: Option<usize>,
    best_oracle_close: Option<usize>,
}

impl LiteralCompleteScanner {
    /// Incrementally scan `acc` for balanced braces/brackets ending with `]}`,
    /// keeping `O(N)` total work across multi-line module and string arrays.
    pub(super) fn is_complete(&mut self, acc: &[u8], oracle: &Oracle) -> bool {
        if self.pos == 0 && self.open_quote.is_none() && trim(acc).is_empty() {
            return true; // the empty array prints as nothing
        }
        loop {
            if let Some(mut qs) = self.open_quote.take() {
                let mut closed_at = None;
                while self.pos < acc.len() {
                    let b = acc[self.pos];
                    if b == b'"' {
                        let mut k = self.pos + 1;
                        while k < acc.len() && acc[k].is_ascii_whitespace() {
                            k += 1;
                        }
                        if k == acc.len() {
                            // Trailing quote at current buffer end: cannot end with `]}`
                            // yet; wait for the next line to reveal whether a separator
                            // or string continuation follows.
                            self.open_quote = Some(qs);
                            return false;
                        }
                        if qs.first_same_line_quote.is_none() {
                            qs.first_same_line_quote = Some(self.pos);
                        }
                        if matches!(acc[k], b',' | b']' | b'}')
                            && oracle.contains_hashed(&acc[qs.open + 1..self.pos], qs.cur_hash)
                        {
                            qs.best_oracle_close = Some(self.pos);
                        }
                        qs.cur_hash = step_oracle_hash(qs.cur_hash, b);
                        if !oracle.has_string_prefix(&acc[qs.open + 1..=self.pos]) {
                            if let Some(c) = qs.best_oracle_close.or(qs.first_same_line_quote) {
                                closed_at = Some(c);
                                break;
                            }
                            self.pos += 1;
                            self.open_quote = Some(qs);
                            return false;
                        }
                    } else {
                        if b == b'\n' {
                            qs.seen_newline = true;
                        }
                        qs.cur_hash = step_oracle_hash(qs.cur_hash, b);
                    }
                    self.pos += 1;
                }
                if let Some(c) = closed_at {
                    self.pos = c + 1;
                    continue;
                }
                if oracle.has_string_prefix(&acc[qs.open + 1..]) {
                    self.open_quote = Some(qs);
                    return false;
                }
                if let Some(c) = qs.best_oracle_close.or(qs.first_same_line_quote) {
                    self.pos = c + 1;
                    continue;
                }
                self.open_quote = Some(qs);
                return false;
            }

            let mut entered_quote = false;
            while self.pos < acc.len() {
                let b = acc[self.pos];
                if b == b'"' {
                    self.open_quote = Some(LiteralQuoteState {
                        open: self.pos,
                        cur_hash: 0,
                        seen_newline: false,
                        first_same_line_quote: None,
                        best_oracle_close: None,
                    });
                    self.pos += 1;
                    entered_quote = true;
                    break;
                }
                match b {
                    b'{' | b'[' => self.depth += 1,
                    b'}' | b']' => self.depth -= 1,
                    _ => {}
                }
                self.pos += 1;
            }
            if !entered_quote {
                return self.depth == 0 && acc.ends_with(b"]}");
            }
        }
    }
}

/// Try to split the mnemonic and operand list of one accumulated instruction
/// text; `Ok((mnemonic, tokens, matched_string_bytes, probe_open_quote))` on
/// success, `Err(open_quote)` when an opened string is unclosed.
type ParsedInsnOps = (Vec<u8>, Vec<Vec<u8>>, usize, Option<usize>);

pub(super) fn insn_ops_parse_ext(
    text: &[u8],
    oracle: &Oracle,
    defer_oracle_prefix: bool,
) -> Result<ParsedInsnOps, usize> {
    let split = text
        .iter()
        .position(|b| b.is_ascii_whitespace())
        .unwrap_or(text.len());
    match split_operands_ext(&text[split..], oracle, defer_oracle_prefix) {
        Ok((tokens, n, probe_open)) => Ok((
            text[..split].to_vec(),
            tokens,
            n,
            probe_open.map(|o| split + o),
        )),
        Err(open) => Err(split + open),
    }
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
pub(super) fn parse_operand_token(token: &[u8], line: usize) -> Result<PaOp, ParseError> {
    if token.len() >= 2 && token[0] == b'"' && token[token.len() - 1] == b'"' {
        return Ok(PaOp::Str(token[1..token.len() - 1].to_vec()));
    }
    if token.starts_with(b"{") {
        return Ok(PaOp::Literal(token.to_vec()));
    }
    if let Ok(text) = std::str::from_utf8(token)
        && text.is_ascii()
    {
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
pub(super) fn parse_catch_line(line: &[u8], line_no: usize) -> Result<PaCatch, ParseError> {
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
pub(super) fn parse_module_record(text: &[u8], line: usize) -> Result<PaModuleRecord, ParseError> {
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

pub(super) fn parse_language(text: &[u8]) -> Option<SourceLang> {
    Some(match text {
        b"ECMAScript" => SourceLang::EcmaScript,
        b"JavaScript" => SourceLang::JavaScript,
        b"TypeScript" => SourceLang::TypeScript,
        b"ArkTS" => SourceLang::ArkTs,
        b"PandaAssembly" => SourceLang::PandaAssembly,
        _ => return None,
    })
}
