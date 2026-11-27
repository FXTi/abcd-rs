//! [`Const`] → [`Lit`] conversion and literal rendering (f64 bit-exact,
//! shortest round-trip; JS string escaping).
//!
//! Number rendering contract (design/decompile.md §5 row 5): raw bits are
//! preserved, so NaN payloads and `-0.0` round-trip exactly; the printed
//! form is the **shortest round-trip representation** — Rust's `Debug`
//! formatter for `f64` emits exactly that (with exponent notation when
//! shorter), and the non-finite values are mapped to their JS spellings
//! (`NaN`, `Infinity`, `-Infinity`).

use std::collections::{BTreeSet, HashSet};
use std::sync::Arc;

use abcd_ir::consts::Const;
use abcd_ir::module::Module;
use abcd_ir::{ConstId, FuncId, Sym};

use crate::expr::Lit;

/// Resolve a [`Sym`] to its string; foreign/unknown ids (library rule:
/// no panics on data) become a visible placeholder.
pub fn sym_str(module: &Module, sym: Sym) -> String {
    module
        .sym
        .resolve(sym)
        .map(str::to_string)
        .unwrap_or_else(|| format!("<sym#{}>", sym.index()))
}

/// Convert a pooled constant to a [`Lit`]; `None` for a [`ConstId`] the
/// pool never issued or a cyclic shape (data, not a panic).
pub fn lit_of(module: &Module, id: ConstId) -> Option<Lit> {
    let mut active = HashSet::new();
    active.insert(id);
    const_to_lit_with_active(module, module.consts.get(id)?, &mut active)
}

/// Convert a [`Sym`] to its lossless [`Lit`] (`Lit::String` for valid UTF-8,
/// `Lit::Utf16` for lone-surrogate strings, #30).
pub fn lit_of_sym(module: &Module, sym: Sym) -> Lit {
    if let Some(s) = module.sym.as_str(sym) {
        Lit::String(s.to_string())
    } else if let Some(units) = module.sym.utf16_units(sym) {
        Lit::Utf16(units)
    } else {
        Lit::String(format!("<sym#{}>", sym.index()))
    }
}

/// Convert a [`Const`] entry (and any child [`ConstId`]s in `module.consts`)
/// to a [`Lit`] tree iteratively with an active-ancestor cycle guard.
pub fn const_to_lit(module: &Module, c: &Const) -> Option<Lit> {
    let mut active = HashSet::new();
    const_to_lit_with_active(module, c, &mut active)
}

enum ConstBuildFrame<'a> {
    Array {
        owner: Option<ConstId>,
        items: &'a [ConstId],
        idx: usize,
        out: Vec<Lit>,
    },
    Object {
        owner: Option<ConstId>,
        keys: &'a [ConstId],
        values: &'a [ConstId],
        idx: usize,
        pending_key: Option<Lit>,
        out: Vec<(Lit, Lit)>,
    },
    Ref {
        owner: Option<ConstId>,
        target: ConstId,
        resolved: bool,
    },
}

fn scalar_const_to_lit(module: &Module, c: &Const) -> Option<Lit> {
    Some(match c {
        Const::Undefined => Lit::Undefined,
        Const::Hole => Lit::Hole,
        Const::Null | Const::LitNull(_) => Lit::Null,
        Const::Bool(b) => Lit::Bool(*b),
        Const::Int8(n) => Lit::Number((*n as f64).to_bits()),
        Const::Int32(n) => Lit::Number(((*n as i32) as f64).to_bits()),
        Const::Float32(bits) => Lit::Number((f32::from_bits(*bits) as f64).to_bits()),
        Const::Number(bits) => Lit::Number(*bits),
        Const::Int64(v) => Lit::Int64(*v),
        Const::UInt64(v) => Lit::UInt64(*v),
        Const::Accessor(n) | Const::BuiltinTypeIndex(n) => Lit::Number((*n as f64).to_bits()),
        Const::MethodAffiliate(n) => Lit::Number((*n as f64).to_bits()),
        Const::String(s) | Const::EtsImplements(s) => lit_of_sym(module, *s),
        Const::BigInt(s) => Lit::BigInt(sym_str(module, *s)),
        Const::MethodRef { func, .. } => Lit::MethodRef(*func),
        Const::ArrayLiteral(_)
        | Const::TypedArrayLiteral { .. }
        | Const::ObjectLiteral { .. }
        | Const::LiteralBufferRef(_) => return None,
    })
}

fn push_const_frame<'a>(
    c: &'a Const,
    owner: Option<ConstId>,
    frames: &mut Vec<ConstBuildFrame<'a>>,
) {
    match c {
        Const::ArrayLiteral(items) | Const::TypedArrayLiteral { items, .. } => {
            frames.push(ConstBuildFrame::Array {
                owner,
                items,
                idx: 0,
                out: Vec::with_capacity(items.len()),
            });
        }
        Const::ObjectLiteral { keys, values } => frames.push(ConstBuildFrame::Object {
            owner,
            keys,
            values,
            idx: 0,
            pending_key: None,
            out: Vec::with_capacity(keys.len().min(values.len())),
        }),
        Const::LiteralBufferRef(target) => frames.push(ConstBuildFrame::Ref {
            owner,
            target: *target,
            resolved: false,
        }),
        _ => {}
    }
}

/// Maximum number of expanded [`Lit`] nodes permitted when unfolding a single
/// [`Const`] entry (guards against `O(2^N)` tree blowup on shared DAGs in
/// untrusted constant pools; exceeding this cap returns `None` so Stage A
/// emits a documented fallback instead of exhausting memory).
pub(crate) const MAX_LIT_NODES: usize = 16_384;

/// Maximum exact safe integer magnitude in IEEE-754 `f64` (`2^53 - 1`).
const MAX_SAFE_INTEGER_MAGNITUDE: u64 = 9_007_199_254_740_991;

fn const_to_lit_with_active(
    module: &Module,
    root: &Const,
    active: &mut HashSet<ConstId>,
) -> Option<Lit> {
    if let Some(lit) = scalar_const_to_lit(module, root) {
        return Some(lit);
    }
    let mut expanded_nodes: usize = 1;
    let mut frames: Vec<ConstBuildFrame<'_>> = Vec::new();
    push_const_frame(root, None, &mut frames);
    let mut completed: Option<Lit> = None;

    while let Some(top) = frames.last_mut() {
        match top {
            ConstBuildFrame::Array {
                owner,
                items,
                idx,
                out,
            } => {
                if let Some(child_lit) = completed.take() {
                    out.push(child_lit);
                }
                if *idx < items.len() {
                    let cid = items[*idx];
                    *idx += 1;
                    expanded_nodes += 1;
                    if expanded_nodes > MAX_LIT_NODES {
                        return None;
                    }
                    let child = module.consts.get(cid)?;
                    if let Some(lit) = scalar_const_to_lit(module, child) {
                        out.push(lit);
                    } else {
                        if !active.insert(cid) {
                            return None;
                        }
                        push_const_frame(child, Some(cid), &mut frames);
                    }
                } else {
                    if let Some(id) = *owner {
                        active.remove(&id);
                    }
                    let done = Lit::Array(std::mem::take(out));
                    frames.pop();
                    if frames.is_empty() {
                        return Some(done);
                    }
                    completed = Some(done);
                }
            }
            ConstBuildFrame::Object {
                owner,
                keys,
                values,
                idx,
                pending_key,
                out,
            } => {
                let len = keys.len().min(values.len());
                if let Some(child_lit) = completed.take() {
                    if let Some(k_lit) = pending_key.take() {
                        out.push((k_lit, child_lit));
                    } else {
                        *pending_key = Some(child_lit);
                    }
                }
                if let Some(k_lit) = pending_key.take() {
                    expanded_nodes += 1;
                    if expanded_nodes > MAX_LIT_NODES {
                        return None;
                    }
                    let vcid = values[*idx - 1];
                    let vchild = module.consts.get(vcid)?;
                    if let Some(vlit) = scalar_const_to_lit(module, vchild) {
                        out.push((k_lit, vlit));
                    } else {
                        *pending_key = Some(k_lit);
                        if !active.insert(vcid) {
                            return None;
                        }
                        push_const_frame(vchild, Some(vcid), &mut frames);
                    }
                } else if *idx < len {
                    expanded_nodes += 1;
                    if expanded_nodes > MAX_LIT_NODES {
                        return None;
                    }
                    let kcid = keys[*idx];
                    *idx += 1;
                    let kchild = module.consts.get(kcid)?;
                    if let Some(klit) = scalar_const_to_lit(module, kchild) {
                        *pending_key = Some(klit);
                    } else {
                        if !active.insert(kcid) {
                            return None;
                        }
                        push_const_frame(kchild, Some(kcid), &mut frames);
                    }
                } else {
                    if let Some(id) = *owner {
                        active.remove(&id);
                    }
                    let done = Lit::Object(std::mem::take(out));
                    frames.pop();
                    if frames.is_empty() {
                        return Some(done);
                    }
                    completed = Some(done);
                }
            }
            ConstBuildFrame::Ref {
                owner,
                target,
                resolved,
            } => {
                if *resolved {
                    if let Some(id) = *owner {
                        active.remove(&id);
                    }
                    let done = completed.take()?;
                    frames.pop();
                    if frames.is_empty() {
                        return Some(done);
                    }
                    completed = Some(done);
                } else {
                    *resolved = true;
                    expanded_nodes += 1;
                    if expanded_nodes > MAX_LIT_NODES {
                        return None;
                    }
                    let tcid = *target;
                    let child = module.consts.get(tcid)?;
                    if let Some(lit) = scalar_const_to_lit(module, child) {
                        completed = Some(lit);
                    } else {
                        if !active.insert(tcid) {
                            return None;
                        }
                        push_const_frame(child, Some(tcid), &mut frames);
                    }
                }
            }
        }
    }
    None
}

/// Module-wide memoized lookup table mapping each [`ConstId`] in `module.consts`
/// to the sorted, deduplicated [`FuncId`]s reachable via nested [`Const::MethodRef`]
/// entries (`#103` `P3-DEC-1`).
///
/// Built iteratively once per [`Module`] in `O(|ConstPool|)` time (single pass
/// over append-only constant pools, plus iterative Tarjan SCC consolidation when
/// forward or cyclic [`ConstId`] edges exist), sharing [`Arc<[FuncId]>`] slices
/// across shared diamond DAGs so every `DefineClass` / `AllocObject` site
/// resolves nested method references in `O(1)` time with zero per-site allocation.
#[derive(Clone, Debug, Default)]
pub struct ConstMethodRefCache {
    entries: Vec<Option<Arc<[FuncId]>>>,
}

#[inline]
fn for_each_const_child(c: &Const, mut f: impl FnMut(ConstId)) {
    match c {
        Const::ArrayLiteral(items) | Const::TypedArrayLiteral { items, .. } => {
            for &cid in items {
                f(cid);
            }
        }
        Const::ObjectLiteral { keys, values } => {
            for &cid in keys.iter().chain(values.iter()) {
                f(cid);
            }
        }
        Const::LiteralBufferRef(inner) => f(*inner),
        _ => {}
    }
}

#[derive(Default)]
struct RefAccumulator {
    single: Option<Arc<[FuncId]>>,
    merged: Option<BTreeSet<FuncId>>,
}

impl RefAccumulator {
    #[inline]
    fn include(&mut self, child: Option<&Arc<[FuncId]>>) {
        let Some(arc) = child else {
            return;
        };
        if arc.is_empty() {
            return;
        }
        if let Some(set) = &mut self.merged {
            set.extend(arc.iter().copied());
            return;
        }
        match &self.single {
            None => self.single = Some(Arc::clone(arc)),
            Some(cur) if Arc::ptr_eq(cur, arc) || cur.as_ref() == arc.as_ref() => {}
            Some(cur) => {
                let mut set: BTreeSet<FuncId> = cur.iter().copied().collect();
                set.extend(arc.iter().copied());
                self.merged = Some(set);
            }
        }
    }

    #[inline]
    fn finish(self) -> Option<Arc<[FuncId]>> {
        if let Some(set) = self.merged {
            let vec: Vec<FuncId> = set.into_iter().collect();
            Some(Arc::from(vec))
        } else {
            self.single
        }
    }
}

impl ConstMethodRefCache {
    /// Build the memoized [`ConstId`] → [`FuncId`] table for `module.consts`
    /// iteratively in `O(|ConstPool|)` time with cycle safety.
    #[must_use]
    pub fn build(module: &Module) -> Self {
        let n = module.consts.len();
        let mut entries: Vec<Option<Arc<[FuncId]>>> = vec![None; n];
        let mut done: Vec<bool> = vec![false; n];
        let mut has_unresolved = false;

        // Fast single-pass bottom-up sweep: resolves all scalar constants and
        // every append-only composite constant whose children precede it (`cid < i`).
        for i in 0..n {
            let Some(c) = module.consts.get(ConstId::new(i as u32)) else {
                done[i] = true;
                continue;
            };
            match c {
                Const::MethodRef { func, .. } => {
                    entries[i] = Some(Arc::from([*func]));
                    done[i] = true;
                }
                Const::ArrayLiteral(_)
                | Const::TypedArrayLiteral { .. }
                | Const::ObjectLiteral { .. }
                | Const::LiteralBufferRef(_) => {
                    let mut all_children_done = true;
                    for_each_const_child(c, |child| {
                        let ci = child.index();
                        if ci < n && !done[ci] {
                            all_children_done = false;
                        }
                    });
                    if all_children_done {
                        let mut acc = RefAccumulator::default();
                        for_each_const_child(c, |child| {
                            if let Some(slot) = entries.get(child.index()) {
                                acc.include(slot.as_ref());
                            }
                        });
                        entries[i] = acc.finish();
                        done[i] = true;
                    } else {
                        has_unresolved = true;
                    }
                }
                _ => {
                    done[i] = true;
                }
            }
        }

        if !has_unresolved {
            return Self { entries };
        }

        // Fallback for forward or cyclic `ConstId` edges: iterative Tarjan SCC
        // over the remaining `!done[i]` composite nodes.
        let mut dfn: Vec<u32> = vec![0; n];
        let mut low: Vec<u32> = vec![0; n];
        let mut on_stack: Vec<bool> = vec![false; n];
        let mut scc_stack: Vec<usize> = Vec::new();
        let mut scc_nodes: Vec<usize> = Vec::new();
        let mut dfs_stack: Vec<(usize, Vec<usize>, usize)> = Vec::new();
        let mut timer: u32 = 0;

        let collect_children = |idx: usize| -> Vec<usize> {
            let mut out = Vec::new();
            if let Some(c) = module.consts.get(ConstId::new(idx as u32)) {
                for_each_const_child(c, |child| {
                    let ci = child.index();
                    if ci < n {
                        out.push(ci);
                    }
                });
            }
            out
        };

        for start in 0..n {
            if done[start] {
                continue;
            }
            timer = timer.saturating_add(1);
            dfn[start] = timer;
            low[start] = timer;
            on_stack[start] = true;
            scc_stack.push(start);
            dfs_stack.push((start, collect_children(start), 0));

            while let Some((u, children, cursor)) = dfs_stack.last_mut() {
                let u = *u;
                if *cursor < children.len() {
                    let v = children[*cursor];
                    *cursor += 1;
                    if done[v] {
                        continue;
                    }
                    if dfn[v] == 0 {
                        timer = timer.saturating_add(1);
                        dfn[v] = timer;
                        low[v] = timer;
                        on_stack[v] = true;
                        scc_stack.push(v);
                        dfs_stack.push((v, collect_children(v), 0));
                    } else if on_stack[v] && dfn[v] < low[u] {
                        low[u] = dfn[v];
                    }
                } else {
                    let (_, u_children, _) = dfs_stack.pop().unwrap_or_default();
                    if let Some((parent, _, _)) = dfs_stack.last() {
                        let p = *parent;
                        if low[u] < low[p] {
                            low[p] = low[u];
                        }
                    }
                    if low[u] == dfn[u] {
                        if scc_stack.last() == Some(&u) {
                            scc_stack.pop();
                            on_stack[u] = false;
                            let mut acc = RefAccumulator::default();
                            for &v in &u_children {
                                if v != u && done[v] {
                                    acc.include(entries[v].as_ref());
                                }
                            }
                            entries[u] = acc.finish();
                            done[u] = true;
                        } else {
                            scc_nodes.clear();
                            while let Some(w) = scc_stack.pop() {
                                on_stack[w] = false;
                                scc_nodes.push(w);
                                if w == u {
                                    break;
                                }
                            }
                            let mut acc = RefAccumulator::default();
                            for &w in &scc_nodes {
                                if let Some(c) = module.consts.get(ConstId::new(w as u32)) {
                                    for_each_const_child(c, |child| {
                                        let v = child.index();
                                        if v < n && done[v] {
                                            acc.include(entries[v].as_ref());
                                        }
                                    });
                                }
                            }
                            let shared = acc.finish();
                            for &w in &scc_nodes {
                                entries[w] = shared.clone();
                                done[w] = true;
                            }
                        }
                    }
                }
            }
        }

        Self { entries }
    }

    /// Return the sorted, deduplicated [`FuncId`]s reachable via [`Const::MethodRef`]
    /// from `cid` in `O(1)` time (`&[]` when none or when `cid` is out of bounds).
    #[inline]
    #[must_use]
    pub fn get(&self, cid: ConstId) -> &[FuncId] {
        self.entries
            .get(cid.index())
            .and_then(Option::as_deref)
            .unwrap_or(&[])
    }

    #[cfg(test)]
    pub(crate) fn arc_of(&self, cid: ConstId) -> Option<&Arc<[FuncId]>> {
        self.entries.get(cid.index()).and_then(Option::as_ref)
    }
}

/// Render an `f64` bit pattern as the shortest JS number literal that
/// round-trips to the same bits.
pub fn render_number(bits: u64) -> String {
    let v = f64::from_bits(bits);
    if v.is_nan() {
        // All NaN payloads print as `NaN` (JS has a single NaN literal;
        // the payload survives in the IR but cannot be spelled in JS).
        return "NaN".to_string();
    }
    if v == f64::INFINITY {
        return "Infinity".to_string();
    }
    if v == f64::NEG_INFINITY {
        return "-Infinity".to_string();
    }
    // `{:?}` is the shortest round-trip form (exponent notation when
    // shorter); it prints `-0.0` for negative zero, which JS reads back
    // as exactly -0.
    format!("{v:?}")
}

/// Render a string as a JS double-quoted string literal (deterministic
/// escaping: control characters as short escapes where they exist,
/// `\u{XXXX}` otherwise; non-ASCII printable characters pass through
/// verbatim).
pub fn render_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        let next_is_digit = chars.peek().is_some_and(char::is_ascii_digit);
        push_js_char(&mut out, c, next_is_digit);
    }
    out.push('"');
    out
}

/// One scalar value inside a JS double-quoted string literal, per
/// [`render_string`]'s escaping contract (shared with the raw-bytes
/// renderer below so both spellings stay in lockstep).
///
/// When `c == '\0'` is followed by an ASCII digit (`'0'..='9'`), `\x00`
/// is emitted instead of `\0` because `\01` is a legacy octal escape and
/// a `SyntaxError` in strict mode / ES modules / template strings.
fn push_js_char(out: &mut String, c: char, next_is_digit: bool) {
    match c {
        '"' => out.push_str("\\\""),
        '\\' => out.push_str("\\\\"),
        '\n' => out.push_str("\\n"),
        '\r' => out.push_str("\\r"),
        '\t' => out.push_str("\\t"),
        '\u{08}' => out.push_str("\\b"),
        '\u{0C}' => out.push_str("\\f"),
        '\u{0B}' => out.push_str("\\v"),
        '\0' if next_is_digit => out.push_str("\\x00"),
        '\0' => out.push_str("\\0"),
        c if (c as u32) < 0x20 || (0x7F..0xA0).contains(&(c as u32)) => {
            out.push_str(&format!("\\u{{{:X}}}", c as u32));
        }
        // Line/paragraph separators are valid in string literals since
        // ES2019 but escaped for maximal parser compatibility.
        '\u{2028}' => out.push_str("\\u{2028}"),
        '\u{2029}' => out.push_str("\\u{2029}"),
        c => out.push(c),
    }
}

/// Decode MUTF-8 bytes (CESU-8: every UTF-16 code unit encoded as up to
/// three bytes; U+0000 as `C0 80`) to UTF-16 code units. A 4-byte UTF-8
/// sequence (not MUTF-8-canonical; defensive) decodes to its scalar's
/// UTF-16 units; a truncated/invalid lead degrades to U+FFFD — data,
/// never a panic.
pub fn mutf8_units(raw: &[u8]) -> Vec<u16> {
    let mut units = Vec::with_capacity(raw.len());
    let mut i = 0;
    while i < raw.len() {
        let b = raw[i];
        if b < 0x80 {
            units.push(b as u16);
            i += 1;
        } else if b >> 5 == 0b110 && i + 1 < raw.len() {
            units.push((((b as u16) & 0x1F) << 6) | ((raw[i + 1] as u16) & 0x3F));
            i += 2;
        } else if b >> 4 == 0b1110 && i + 2 < raw.len() {
            units.push(
                (((b as u16) & 0x0F) << 12)
                    | (((raw[i + 1] as u16) & 0x3F) << 6)
                    | ((raw[i + 2] as u16) & 0x3F),
            );
            i += 3;
        } else if b >> 3 == 0b11110 && i + 3 < raw.len() {
            let cp = (((b as u32) & 0x07) << 18)
                | (((raw[i + 1] as u32) & 0x3F) << 12)
                | (((raw[i + 2] as u32) & 0x3F) << 6)
                | ((raw[i + 3] as u32) & 0x3F);
            match char::from_u32(cp) {
                Some(c) => {
                    let mut buf = [0u16; 2];
                    units.extend_from_slice(c.encode_utf16(&mut buf));
                }
                None => units.push(0xFFFD),
            }
            i += 4;
        } else {
            units.push(0xFFFD);
            i += 1;
        }
    }
    units
}

/// Render UTF-16 code units as the BODY of a JS double-quoted string
/// literal: a well-formed surrogate pair renders as its astral
/// character (es2abc's CESU-8 re-encode is byte-identical to the
/// original pair), a LONE surrogate unit — which has no valid UTF-8
/// spelling — renders as a `\uXXXX` escape (valid JS that es2abc
/// recompiles to exactly the original MUTF-8 bytes, N75); every other
/// unit follows [`render_string`]'s escaping contract.
fn push_units_string_body(out: &mut String, units: &[u16]) {
    let mut i = 0;
    while i < units.len() {
        let u = units[i];
        if (0xD800..0xDC00).contains(&u)
            && i + 1 < units.len()
            && (0xDC00..0xE000).contains(&units[i + 1])
        {
            let cp = 0x10000 + (((u as u32) - 0xD800) << 10) + ((units[i + 1] as u32) - 0xDC00);
            let next_is_digit = units.get(i + 2).is_some_and(|n| (0x30..=0x39).contains(n));
            // A well-formed pair always decodes to a scalar value.
            if let Some(c) = char::from_u32(cp) {
                push_js_char(out, c, next_is_digit);
            }
            i += 2;
        } else if (0xD800..0xE000).contains(&u) {
            out.push_str(&format!("\\u{u:04X}"));
            i += 1;
        } else {
            let next_is_digit = units.get(i + 1).is_some_and(|n| (0x30..=0x39).contains(n));
            // A BMP unit is always a scalar value.
            if let Some(c) = char::from_u32(u as u32) {
                push_js_char(out, c, next_is_digit);
            }
            i += 1;
        }
    }
}

/// Render UTF-16 code units (including lone surrogates) as a JS
/// double-quoted string literal (#30).
pub fn render_utf16_string(units: &[u16]) -> String {
    let mut out = String::with_capacity(units.len() + 2);
    out.push('"');
    push_units_string_body(&mut out, units);
    out.push('"');
    out
}

/// Render raw MUTF-8 string bytes as a JS double-quoted string literal
/// (see `push_units_string_body`).
pub fn render_mutf8_string(raw: &[u8]) -> String {
    render_utf16_string(&mutf8_units(raw))
}

/// Escape a RegExp pattern body for `/pattern/flags` literal emission:
/// an empty pattern becomes `(?:)` (so `//` never turns into a line comment),
/// `/` is escaped as `\/` ONLY when preceded by an even number of `\`
/// characters (preserving already-escaped `\/` while escaping `\\/`), and
/// line terminators are escaped.
pub(crate) fn escape_regexp_body(pattern: &str) -> String {
    if pattern.is_empty() {
        return "(?:)".to_string();
    }
    let mut out = String::with_capacity(pattern.len() + 2);
    let mut backslashes = 0usize;
    for c in pattern.chars() {
        match c {
            '\\' => {
                backslashes += 1;
                out.push('\\');
            }
            '/' => {
                if backslashes.is_multiple_of(2) {
                    out.push_str("\\/");
                } else {
                    out.push('/');
                }
                backslashes = 0;
            }
            '\n' => {
                backslashes = 0;
                out.push_str("\\n");
            }
            '\r' => {
                backslashes = 0;
                out.push_str("\\r");
            }
            '\u{2028}' => {
                backslashes = 0;
                out.push_str("\\u2028");
            }
            '\u{2029}' => {
                backslashes = 0;
                out.push_str("\\u2029");
            }
            _ => {
                backslashes = 0;
                out.push(c);
            }
        }
    }
    out
}

/// Render raw MUTF-8 bytes of a REGEXP pattern: no quotes, unescaped `/`
/// escaped as `\/`, lone surrogates as `\uXXXX` escapes.
pub fn render_mutf8_regexp(raw: &[u8]) -> String {
    let units = mutf8_units(raw);
    let mut body = String::with_capacity(units.len());
    let mut i = 0;
    while i < units.len() {
        let u = units[i];
        if (0xD800..0xDC00).contains(&u)
            && i + 1 < units.len()
            && (0xDC00..0xE000).contains(&units[i + 1])
        {
            let cp = 0x10000 + (((u as u32) - 0xD800) << 10) + ((units[i + 1] as u32) - 0xDC00);
            if let Some(c) = char::from_u32(cp) {
                body.push(c);
            }
            i += 2;
        } else if (0xD800..0xE000).contains(&u) {
            body.push_str(&format!("\\u{u:04X}"));
            i += 1;
        } else {
            if let Some(c) = char::from_u32(u as u32) {
                body.push(c);
            }
            i += 1;
        }
    }
    escape_regexp_body(&body)
}

/// Resolve a [`Sym`] for an `AllocRegExp` pattern (#30): valid UTF-8 passes
/// through verbatim (preserving regexp escapes like `\d`); lone-surrogate
/// symbols escape lone surrogate units as `\uXXXX` while keeping valid code
/// points intact.
pub fn sym_regexp_pattern(module: &Module, sym: Sym) -> String {
    if let Some(s) = module.sym.as_str(sym) {
        return s.to_string();
    }
    let Some(units) = module.sym.utf16_units(sym) else {
        return format!("<sym#{}>", sym.index());
    };
    let mut out = String::with_capacity(units.len());
    let mut i = 0;
    while i < units.len() {
        let u = units[i];
        if (0xD800..=0xDBFF).contains(&u)
            && i + 1 < units.len()
            && (0xDC00..=0xDFFF).contains(&units[i + 1])
        {
            let hi = (u - 0xD800) as u32;
            let lo = (units[i + 1] - 0xDC00) as u32;
            let cp = 0x10000 + ((hi << 10) | lo);
            if let Some(ch) = char::from_u32(cp) {
                out.push(ch);
            }
            i += 2;
        } else if (0xD800..=0xDFFF).contains(&u) {
            out.push_str(&format!("\\u{u:04X}"));
            i += 1;
        } else {
            match char::from_u32(u as u32) {
                Some('\n') => out.push_str("\\n"),
                Some('\r') => out.push_str("\\r"),
                Some('\u{2028}') => out.push_str("\\u2028"),
                Some('\u{2029}') => out.push_str("\\u2029"),
                Some(ch) => out.push(ch),
                None => out.push_str(&format!("\\u{u:04X}")),
            }
            i += 1;
        }
    }
    out
}

/// Render a [`Sym`] directly from `module.sym` as a JS string literal (#30).
pub fn render_sym_string(module: &Module, sym: Sym) -> String {
    if let Some(raw) = module.sym.raw_mutf8(sym) {
        render_mutf8_string(raw)
    } else {
        render_string(&sym_str(module, sym))
    }
}

/// Render a UTF-8 string as a JS string literal (compatibility alias).
pub fn render_pool_string(_module: &Module, s: &str) -> String {
    render_string(s)
}

/// Render a [`Lit`] as its JS literal text (used by the dump; Stage C
/// reuses the same renderer).
pub fn render_lit(lit: &Lit) -> String {
    render_lit_ex(lit, false)
}

/// [`render_lit`] with module context (Stage C entry point).
pub fn render_lit_m(_module: &Module, lit: &Lit) -> String {
    render_lit_ex(lit, false)
}

/// Iterative [`Lit`] renderer shared between Stage-A dumps (`js_method_ref = false`)
/// and Stage-C JS emission (`js_method_ref = true`).
pub(crate) fn render_lit_ex(root: &Lit, js_method_ref: bool) -> String {
    enum RenderFrame<'a> {
        Array {
            items: &'a [Lit],
            idx: usize,
            parts: Vec<String>,
        },
        Object {
            entries: &'a [(Lit, Lit)],
            idx: usize,
            pending_key: Option<String>,
            parts: Vec<String>,
        },
    }
    let scalar = |lit: &Lit| -> Option<String> {
        Some(match lit {
            Lit::Undefined => "undefined".to_string(),
            Lit::Hole => "undefined/*hole*/".to_string(),
            Lit::Null => "null".to_string(),
            Lit::Bool(b) => b.to_string(),
            Lit::Number(bits) => render_number(*bits),
            Lit::Int64(v) => {
                if v.unsigned_abs() > MAX_SAFE_INTEGER_MAGNITUDE {
                    format!("{v}n")
                } else {
                    v.to_string()
                }
            }
            Lit::UInt64(v) => {
                if *v > MAX_SAFE_INTEGER_MAGNITUDE {
                    format!("{v}n")
                } else {
                    v.to_string()
                }
            }
            Lit::String(s) => render_string(s),
            Lit::Utf16(units) => render_utf16_string(units),
            Lit::BigInt(s) => format!("{s}n"),
            Lit::MethodRef(f) => {
                if js_method_ref {
                    format!("undefined /*method fn#{}*/", f.index())
                } else {
                    format!("<method fn#{}>", f.index())
                }
            }
            Lit::Array(_) | Lit::Object(_) => return None,
        })
    };
    if let Some(s) = scalar(root) {
        return s;
    }
    let mut stack: Vec<RenderFrame<'_>> = Vec::new();
    match root {
        Lit::Array(items) => stack.push(RenderFrame::Array {
            items,
            idx: 0,
            parts: Vec::with_capacity(items.len()),
        }),
        Lit::Object(entries) => stack.push(RenderFrame::Object {
            entries,
            idx: 0,
            pending_key: None,
            parts: Vec::with_capacity(entries.len()),
        }),
        _ => return String::new(),
    }
    let mut completed: Option<String> = None;

    while let Some(top) = stack.last_mut() {
        match top {
            RenderFrame::Array { items, idx, parts } => {
                if let Some(done) = completed.take() {
                    parts.push(done);
                }
                if *idx < items.len() {
                    let item = &items[*idx];
                    *idx += 1;
                    if let Some(s) = scalar(item) {
                        parts.push(s);
                    } else if let Lit::Array(sub) = item {
                        stack.push(RenderFrame::Array {
                            items: sub,
                            idx: 0,
                            parts: Vec::with_capacity(sub.len()),
                        });
                    } else if let Lit::Object(sub) = item {
                        stack.push(RenderFrame::Object {
                            entries: sub,
                            idx: 0,
                            pending_key: None,
                            parts: Vec::with_capacity(sub.len()),
                        });
                    }
                } else {
                    let s = format!("[{}]", parts.join(", "));
                    stack.pop();
                    if stack.is_empty() {
                        return s;
                    }
                    completed = Some(s);
                }
            }
            RenderFrame::Object {
                entries,
                idx,
                pending_key,
                parts,
            } => {
                if let Some(done) = completed.take() {
                    if let Some(k_str) = pending_key.take() {
                        parts.push(format!("{k_str}: {done}"));
                    } else {
                        *pending_key = Some(done);
                    }
                }
                if let Some(k_str) = pending_key.take() {
                    let (_, v) = &entries[*idx - 1];
                    if let Some(vs) = scalar(v) {
                        parts.push(format!("{k_str}: {vs}"));
                    } else if let Lit::Array(sub) = v {
                        *pending_key = Some(k_str);
                        stack.push(RenderFrame::Array {
                            items: sub,
                            idx: 0,
                            parts: Vec::with_capacity(sub.len()),
                        });
                    } else if let Lit::Object(sub) = v {
                        *pending_key = Some(k_str);
                        stack.push(RenderFrame::Object {
                            entries: sub,
                            idx: 0,
                            pending_key: None,
                            parts: Vec::with_capacity(sub.len()),
                        });
                    }
                } else if *idx < entries.len() {
                    let (k, _) = &entries[*idx];
                    *idx += 1;
                    if js_method_ref
                        && let Lit::String(s) = k
                        && s == "__proto__"
                    {
                        *pending_key = Some(format!("[{}]", render_string(s)));
                    } else if let Lit::String(s) = k
                        && crate::legalize::is_legal_ident(s)
                    {
                        *pending_key = Some(s.clone());
                    } else if let Some(ks) = scalar(k) {
                        if js_method_ref && (ks.starts_with('-') || ks.ends_with('n')) {
                            *pending_key = Some(format!("[{ks}]"));
                        } else {
                            *pending_key = Some(ks);
                        }
                    } else if let Lit::Array(sub) = k {
                        stack.push(RenderFrame::Array {
                            items: sub,
                            idx: 0,
                            parts: Vec::with_capacity(sub.len()),
                        });
                    } else if let Lit::Object(sub) = k {
                        stack.push(RenderFrame::Object {
                            entries: sub,
                            idx: 0,
                            pending_key: None,
                            parts: Vec::with_capacity(sub.len()),
                        });
                    }
                } else {
                    let s = format!("{{{}}}", parts.join(", "));
                    stack.pop();
                    if stack.is_empty() {
                        return s;
                    }
                    completed = Some(s);
                }
            }
        }
    }
    String::new()
}

/// Map the vendor RegExp flag bits (arkcompiler
/// `ecmascript/regexp/regexp_parser.h`: FLAG_GLOBAL=1, IGNORECASE=2,
/// MULTILINE=4, DOTALL=8, UTF16=16, STICKY=32, HASINDICES=64) to the JS
/// flag string in canonical `dgimsuy` order.
pub fn render_regexp_flags(bits: u32) -> String {
    let mut out = String::new();
    let table = [
        (1 << 6, 'd'),
        (1 << 0, 'g'),
        (1 << 1, 'i'),
        (1 << 2, 'm'),
        (1 << 3, 's'),
        (1 << 4, 'u'),
        (1 << 5, 'y'),
    ];
    for (bit, flag) in table {
        if bits & bit != 0 {
            out.push(flag);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn number_rendering_is_shortest_round_trip() {
        let cases = [
            0.0f64,
            -0.0,
            1.0,
            -1.5,
            0.1,
            1e300,
            5e-324,
            123456789.0,
            f64::MAX,
            f64::MIN_POSITIVE,
        ];
        for v in cases {
            let text = render_number(v.to_bits());
            let back: f64 = if text == "Infinity" {
                f64::INFINITY
            } else if text == "-Infinity" {
                f64::NEG_INFINITY
            } else {
                text.parse().expect("parseable as JS/Rust number")
            };
            assert_eq!(back.to_bits(), v.to_bits(), "round-trip of {text}");
        }
        assert_eq!(render_number(f64::NAN.to_bits()), "NaN");
        assert_eq!(render_number(f64::INFINITY.to_bits()), "Infinity");
        assert_eq!(render_number(f64::NEG_INFINITY.to_bits()), "-Infinity");
        assert_eq!(render_number((-0.0f64).to_bits()), "-0.0");
        assert_eq!(render_number(1.0f64.to_bits()), "1.0");
        assert_eq!(render_number((1e300f64).to_bits()), "1e300");
    }

    #[test]
    fn string_escaping() {
        assert_eq!(render_string("hello"), "\"hello\"");
        assert_eq!(render_string("a\"b\\c\n"), "\"a\\\"b\\\\c\\n\"");
        assert_eq!(render_string("\u{1}"), "\"\\u{1}\"");
        assert_eq!(render_string("héllo"), "\"héllo\"");
        assert_eq!(render_string("\u{2028}"), "\"\\u{2028}\"");
    }

    #[test]
    fn regexp_flags() {
        assert_eq!(render_regexp_flags(0), "");
        assert_eq!(render_regexp_flags(1), "g");
        assert_eq!(render_regexp_flags(1 | 2 | 16), "giu");
        assert_eq!(render_regexp_flags(64 | 1), "dg");
    }

    #[test]
    fn mutf8_units_decoding() {
        // ASCII.
        assert_eq!(mutf8_units(b"a"), vec![0x61]);
        // 2-byte form (U+00E9).
        assert_eq!(mutf8_units(&[0xC3, 0xA9]), vec![0xE9]);
        // 3-byte form (U+4E2D).
        assert_eq!(mutf8_units(&[0xE4, 0xB8, 0xAD]), vec![0x4E2D]);
        // MUTF-8 NUL (C0 80).
        assert_eq!(mutf8_units(&[0xC0, 0x80]), vec![0x0000]);
        // CESU-8 encoded UTF-16 surrogate unit (no scalar decoding).
        assert_eq!(mutf8_units(&[0xED, 0xA0, 0x80]), vec![0xD800]);
        // A 4-byte UTF-8 sequence (non-canonical MUTF-8) decodes to the
        // scalar's UTF-16 surrogate pair (U+1F600).
        assert_eq!(mutf8_units(&[0xF0, 0x9F, 0x98, 0x80]), vec![0xD83D, 0xDE00]);
        // A 4-byte sequence above U+10FFFF is not a scalar: U+FFFD.
        assert_eq!(mutf8_units(&[0xF4, 0x90, 0x80, 0x80]), vec![0xFFFD]);
        // Truncated / invalid leads degrade to U+FFFD PER BYTE, never
        // panic (a truncated multi-byte lead leaves its continuation
        // bytes to degrade individually).
        assert_eq!(mutf8_units(&[0xC3]), vec![0xFFFD]);
        assert_eq!(mutf8_units(&[0xE4, 0xB8]), vec![0xFFFD, 0xFFFD]);
        assert_eq!(
            mutf8_units(&[0xF0, 0x9F, 0x98]),
            vec![0xFFFD, 0xFFFD, 0xFFFD]
        );
        assert_eq!(mutf8_units(&[0x80]), vec![0xFFFD]);
        // Mixed stream: valid, 2-byte, invalid lead, ASCII.
        assert_eq!(
            mutf8_units(b"a\xC3\xA9\xFFb"),
            vec![0x61, 0xE9, 0xFFFD, 0x62]
        );
    }

    #[test]
    fn mutf8_string_rendering() {
        // A lone surrogate unit renders as a \uXXXX escape (N75).
        assert_eq!(
            render_mutf8_string(&[0x61, 0xED, 0xA0, 0x80]),
            "\"a\\uD800\""
        );
        // A well-formed CESU-8 pair renders as its astral character.
        assert_eq!(
            render_mutf8_string(&[0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80]),
            "\"\u{1F600}\""
        );
        // Ordinary escapes still apply on the unit path.
        assert_eq!(render_mutf8_string(b"a\"b"), "\"a\\\"b\"");
    }

    #[test]
    fn mutf8_regexp_rendering() {
        // `/` is escaped in the regexp body; lone surrogates escape.
        assert_eq!(render_mutf8_regexp(b"a/b"), "a\\/b");
        assert_eq!(render_mutf8_regexp(&[0xED, 0xA0, 0x80]), "\\uD800");
    }

    #[test]
    fn pool_sym_lone_surrogates_and_pua() {
        let mut m = Module::new();
        let raw_sym = m.sym.intern_raw_mutf8(&[0xED, 0xA0, 0x80]);
        let pua_sym = m.sym.intern("\u{E000}icon");
        assert_eq!(render_sym_string(&m, raw_sym), "\"\\uD800\"");
        assert_eq!(render_sym_string(&m, pua_sym), "\"\u{E000}icon\"");
        assert_eq!(render_pool_string(&m, "plain"), "\"plain\"");
    }

    #[test]
    fn int64_uint64_and_deep_const_pool_shapes_on_256k_stack() {
        let mut m = Module::new();
        let ci = m.consts.intern(Const::Int64(i64::MIN));
        let cu = m.consts.intern(Const::UInt64(u64::MAX));
        let ksym = m.sym.intern("id");
        let ck = m.consts.intern(Const::String(ksym));
        let obj = m.consts.push_object(vec![ck], vec![ci]);
        let arr = m.consts.push_array(vec![obj, cu]);
        let lit = lit_of(&m, arr).expect("resolve flat ConstPool graph");
        assert_eq!(
            render_lit(&lit),
            format!("[{{id: {}n}}, {}n]", i64::MIN, u64::MAX)
        );

        let mut deep_cid = cu;
        for _ in 0..3_000 {
            deep_cid = m.consts.push_array(vec![deep_cid]);
        }

        std::thread::scope(|s| {
            let handle = std::thread::Builder::new()
                .name("consts-256k-stack".to_string())
                .stack_size(256 * 1024)
                .spawn_scoped(s, || {
                    let deep_lit = lit_of(&m, deep_cid).expect("deep array literal");
                    let rendered = render_lit(&deep_lit);
                    assert!(rendered.starts_with("[[["));
                    drop(deep_lit);
                })
                .expect("spawn 256k thread");
            handle.join().expect("256k thread must not stack-overflow");
        });
    }

    #[test]
    fn round3_const_variants_and_literal_buffer_ref_cycles_and_256k_stack() {
        use abcd_ir::FuncId;
        use abcd_ir::consts::{LitMethodKind, TypedArrayTag};

        let mut m = Module::new();
        let iface = m.sym.intern("IFoo");
        let c_i8 = m.consts.push(Const::Int8(255));
        let c_i32_neg = m.consts.push(Const::Int32((-7i32) as u32));
        let c_f32 = m.consts.push(Const::Float32(1.5f32.to_bits()));
        let c_acc = m.consts.push(Const::Accessor(0));
        let c_aff = m.consts.push(Const::MethodAffiliate(3));
        let c_bti = m.consts.push(Const::BuiltinTypeIndex(21));
        let c_ets = m.consts.push(Const::EtsImplements(iface));
        let c_null = m.consts.push(Const::LitNull(0));
        let c_mref = m.consts.push(Const::method_ref_with_kind(
            FuncId::new(9),
            LitMethodKind::GeneratorMethod,
        ));
        assert_eq!(lit_of(&m, c_mref), Some(Lit::MethodRef(FuncId::new(9))));

        let typed = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::I32,
            items: vec![c_i8, c_i32_neg, c_f32, c_acc, c_aff, c_bti, c_ets, c_null],
        });
        let buf_ref = m.consts.push(Const::LiteralBufferRef(typed));
        let resolved = lit_of(&m, buf_ref).expect("resolve LiteralBufferRef -> TypedArrayLiteral");
        assert_eq!(
            render_lit(&resolved),
            "[255.0, -7.0, 1.5, 0.0, 3.0, 21.0, \"IFoo\", null]"
        );

        // Cycle safety: `cyc_a -> cyc_b -> cyc_a` returns `None` without panicking.
        let cyc_a = m.consts.push(Const::Undefined);
        let cyc_b = m.consts.push(Const::LiteralBufferRef(cyc_a));
        // Overwrite via fresh pool or direct cycle check: self-referential ref.
        let mut cyc_mod = Module::new();
        let self_ref = abcd_ir::ConstId::new(0);
        let pushed = cyc_mod.consts.push(Const::LiteralBufferRef(self_ref));
        assert_eq!(pushed, self_ref);
        assert_eq!(lit_of(&cyc_mod, self_ref), None);
        let _ = cyc_b;

        // Deep 3,000-node `LiteralBufferRef` chain on a 256 KiB stack.
        let mut deep_ref = c_i32_neg;
        for _ in 0..3_000 {
            deep_ref = m.consts.push(Const::LiteralBufferRef(deep_ref));
        }
        std::thread::scope(|s| {
            let handle = std::thread::Builder::new()
                .name("consts-ref-256k".to_string())
                .stack_size(256 * 1024)
                .spawn_scoped(s, || {
                    let deep_lit = lit_of(&m, deep_ref).expect("deep LiteralBufferRef");
                    assert_eq!(render_lit(&deep_lit), "-7.0");
                })
                .expect("spawn 256k thread");
            handle.join().expect("256k thread must not stack-overflow");
        });
    }

    #[test]
    fn const_method_ref_cache_handles_forward_and_cyclic_edges() {
        let mut m = Module::new();
        // 0 -> [1, 3] (forward edges), 1 -> 2, 2 -> 0 (3-cycle), 3 -> MethodRef(7), 4 -> LiteralBufferRef(0)
        let c0 = m
            .consts
            .push_array(vec![ConstId::new(1), ConstId::new(3), ConstId::new(999)]);
        let c1 = m.consts.push(Const::LiteralBufferRef(ConstId::new(2)));
        let c2 = m.consts.push_array(vec![ConstId::new(0), ConstId::new(5)]);
        let c3 = m.consts.push(Const::method_ref(FuncId::new(7)));
        let c4 = m.consts.push(Const::LiteralBufferRef(c0));
        let c5 = m.consts.push(Const::method_ref(FuncId::new(3)));

        let cache = ConstMethodRefCache::build(&m);
        let want = &[FuncId::new(3), FuncId::new(7)];
        for cid in [c0, c1, c2, c4] {
            assert_eq!(cache.get(cid), want, "cid={cid:?}");
        }
        assert_eq!(cache.get(c3), &[FuncId::new(7)]);
        assert_eq!(cache.get(c5), &[FuncId::new(3)]);
        assert_eq!(cache.get(ConstId::new(999)), &[]);
        assert!(Arc::ptr_eq(
            cache.arc_of(c0).unwrap(),
            cache.arc_of(c2).unwrap()
        ));
    }
}
