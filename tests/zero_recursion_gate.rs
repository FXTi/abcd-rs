//! Workspace-wide Zero-Recursion Conformance Gate (`#95`, `ADR-22`).
//!
//! Enforces the project-wide zero-recursion mandate across all 13 Rust crates,
//! hand-written C/C++ bridges and shims, Python maintenance scripts, and this
//! gate file itself:
//!
//! 1. `[workspace.lints.rust] unconditional_recursion = "deny"` in root
//!    `Cargo.toml` and `[lints] workspace = true` in every member crate.
//! 2. Zero compiler-derived recursive traits (`Clone`, `Debug`, `PartialEq`,
//!    `Eq`, `PartialOrd`, `Ord`, `Hash`) on self-recursive or mutually
//!    recursive Rust `struct` / `enum` type SCCs, plus an explicit `impl Drop`
//!    on every heap-owning recursive type SCC so compiler drop glue never
//!    recurses on stack depth.
//! 3. Zero direct (`f -> f`) or mutual (`f -> g -> ... -> f`) intra-crate
//!    function/method call cycles in non-test Rust code (`abcd-*/src/**/*.rs`,
//!    excluding `generated/` and `#[cfg(test)]` items).
//! 4. Zero direct or mutual C/C++ call cycles in `abcd-*-sys/bridge/**` and
//!    `vendor/shim/**` (excluding `generated/`).
//! 5. Zero direct or mutual `def` call cycles (and zero `eval`/`exec`) in
//!    `scripts/*.py`.
//!
//! All graph and lexical walks in this test are implemented iteratively using
//! explicit heap workstacks and iterative Tarjan SCC (`O(V + E)`).

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::{Path, PathBuf};

const CRATES: &[&str] = &[
    "abcd-isa-sys",
    "abcd-isa",
    "abcd-file-sys",
    "abcd-file",
    "abcd-hap",
    "abcd-ir",
    "abcd-lift",
    "abcd-opt",
    "abcd-lower",
    "abcd-analysis",
    "abcd-taint",
    "abcd-decompile",
    "abcd-cli",
];

const RECURSIVE_DERIVE_TRAITS: &[&str] = &[
    "Clone",
    "Debug",
    "PartialEq",
    "Eq",
    "PartialOrd",
    "Ord",
    "Hash",
];

const HEAP_CONTAINERS: &[&str] = &[
    "Box", "Vec", "VecDeque", "BTreeMap", "BTreeSet", "HashMap", "HashSet", "Arc", "Rc",
];

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

// ============================================================================
// Iterative Tarjan Strongly Connected Components (`O(V + E)`, zero recursion)
// ============================================================================

/// Returns every non-trivial strongly connected component:
/// - any component with `len() >= 2` (mutual cycle), or
/// - any single-node component `u` with an explicit self-edge `u -> u`.
fn tarjan_nontrivial_sccs(adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = adj.len();
    let mut index_of = vec![u32::MAX; n];
    let mut lowlink = vec![0u32; n];
    let mut on_stack = vec![false; n];
    let mut scc_stack: Vec<usize> = Vec::new();
    let mut dfs_stack: Vec<(usize, usize)> = Vec::new();
    let mut next_index = 0u32;
    let mut cycles: Vec<Vec<usize>> = Vec::new();

    for start in 0..n {
        if index_of[start] != u32::MAX {
            continue;
        }
        index_of[start] = next_index;
        lowlink[start] = next_index;
        next_index += 1;
        on_stack[start] = true;
        scc_stack.push(start);
        dfs_stack.push((start, 0));

        while let Some((v, edge_idx)) = dfs_stack.last_mut() {
            let v_node = *v;
            if *edge_idx < adj[v_node].len() {
                let w = adj[v_node][*edge_idx];
                *edge_idx += 1;
                if index_of[w] == u32::MAX {
                    index_of[w] = next_index;
                    lowlink[w] = next_index;
                    next_index += 1;
                    on_stack[w] = true;
                    scc_stack.push(w);
                    dfs_stack.push((w, 0));
                } else if on_stack[w] && index_of[w] < lowlink[v_node] {
                    lowlink[v_node] = index_of[w];
                }
            } else {
                dfs_stack.pop();
                if let Some(&(parent, _)) = dfs_stack.last()
                    && lowlink[v_node] < lowlink[parent]
                {
                    lowlink[parent] = lowlink[v_node];
                }
                if lowlink[v_node] == index_of[v_node] {
                    let mut comp = Vec::new();
                    while let Some(w) = scc_stack.pop() {
                        on_stack[w] = false;
                        comp.push(w);
                        if w == v_node {
                            break;
                        }
                    }
                    comp.reverse();
                    let is_cycle =
                        comp.len() >= 2 || (comp.len() == 1 && adj[v_node].contains(&v_node));
                    if is_cycle {
                        cycles.push(comp);
                    }
                }
            }
        }
    }

    cycles
}

// ============================================================================
// Iterative Directory Walk
// ============================================================================

fn collect_files_iteratively(root: &Path, skip_generated: bool, exts: &[&str]) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut dirs = vec![root.to_path_buf()];
    while let Some(dir) = dirs.pop() {
        let Ok(rd) = fs::read_dir(&dir) else {
            continue;
        };
        let mut entries: Vec<PathBuf> = rd.filter_map(|e| e.ok().map(|x| x.path())).collect();
        entries.sort();
        for path in entries {
            let name = path
                .file_name()
                .map(|s| s.to_string_lossy().into_owned())
                .unwrap_or_default();
            if path.is_dir() {
                if skip_generated && name == "generated" {
                    continue;
                }
                dirs.push(path);
            } else if let Some(ext) = path.extension().and_then(|e| e.to_str())
                && exts.contains(&ext)
            {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

// ============================================================================
// Iterative Rust Tokenizer (strips comments, strings, raw strings, char lits)
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
enum RTok {
    Ident(String),
    Lifetime,
    ColonColon,
    Arrow,
    FatArrow,
    Punct(char),
    Literal,
}

#[derive(Clone, Debug)]
struct SpannedTok {
    tok: RTok,
    line: usize,
}

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

fn is_ident_continue(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn count_raw_hashes(bytes: &[u8], start: usize) -> Option<(usize, usize)> {
    let mut i = start;
    let mut hashes = 0usize;
    while i < bytes.len() && bytes[i] == b'#' {
        hashes += 1;
        i += 1;
    }
    if i < bytes.len() && bytes[i] == b'"' {
        Some((hashes, i + 1))
    } else {
        None
    }
}

fn tokenize_rust(src: &str) -> Vec<SpannedTok> {
    let bytes = src.as_bytes();
    let n = bytes.len();
    let mut i = 0usize;
    let mut line = 1usize;
    let mut out = Vec::new();

    while i < n {
        let b = bytes[i];
        if b == b'\n' {
            line += 1;
            i += 1;
            continue;
        }
        if b.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        // Line comment
        if b == b'/' && i + 1 < n && bytes[i + 1] == b'/' {
            i += 2;
            while i < n && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        // Nested block comment
        if b == b'/' && i + 1 < n && bytes[i + 1] == b'*' {
            let mut depth = 1usize;
            i += 2;
            while i < n && depth > 0 {
                if bytes[i] == b'\n' {
                    line += 1;
                    i += 1;
                } else if i + 1 < n && bytes[i] == b'/' && bytes[i + 1] == b'*' {
                    depth += 1;
                    i += 2;
                } else if i + 1 < n && bytes[i] == b'*' && bytes[i + 1] == b'/' {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            continue;
        }
        // Raw string / byte-string / c-string: r#"..."#, br#"..."#, cr#"..."#
        let raw_prefix_end = if b == b'r' {
            Some(i + 1)
        } else if (b == b'b' || b == b'c') && i + 1 < n && bytes[i + 1] == b'r' {
            Some(i + 2)
        } else {
            None
        };
        if let Some(p_end) = raw_prefix_end
            && let Some((hashes, body_start)) = count_raw_hashes(bytes, p_end)
        {
            let start_line = line;
            i = body_start;
            while i < n {
                if bytes[i] == b'\n' {
                    line += 1;
                    i += 1;
                } else if bytes[i] == b'"' {
                    let mut h = 0usize;
                    let mut j = i + 1;
                    while h < hashes && j < n && bytes[j] == b'#' {
                        h += 1;
                        j += 1;
                    }
                    if h == hashes {
                        i = j;
                        break;
                    }
                    i += 1;
                } else {
                    i += 1;
                }
            }
            out.push(SpannedTok {
                tok: RTok::Literal,
                line: start_line,
            });
            continue;
        }
        // Byte/c string prefix b"..." or c"..." or b'x'
        if (b == b'b' || b == b'c') && i + 1 < n && bytes[i + 1] == b'"' {
            let start_line = line;
            i += 2;
            while i < n {
                if bytes[i] == b'\n' {
                    line += 1;
                    i += 1;
                } else if bytes[i] == b'\\' {
                    i += 2.min(n - i);
                } else if bytes[i] == b'"' {
                    i += 1;
                    break;
                } else {
                    i += 1;
                }
            }
            out.push(SpannedTok {
                tok: RTok::Literal,
                line: start_line,
            });
            continue;
        }
        if b == b'b' && i + 1 < n && bytes[i + 1] == b'\'' {
            let start_line = line;
            i += 2;
            while i < n {
                if bytes[i] == b'\\' {
                    i += 2.min(n - i);
                } else if bytes[i] == b'\'' {
                    i += 1;
                    break;
                } else {
                    i += 1;
                }
            }
            out.push(SpannedTok {
                tok: RTok::Literal,
                line: start_line,
            });
            continue;
        }
        // Normal string literal
        if b == b'"' {
            let start_line = line;
            i += 1;
            while i < n {
                if bytes[i] == b'\n' {
                    line += 1;
                    i += 1;
                } else if bytes[i] == b'\\' {
                    if i + 1 < n && bytes[i + 1] == b'\n' {
                        line += 1;
                    }
                    i += 2.min(n - i);
                } else if bytes[i] == b'"' {
                    i += 1;
                    break;
                } else {
                    i += 1;
                }
            }
            out.push(SpannedTok {
                tok: RTok::Literal,
                line: start_line,
            });
            continue;
        }
        // Char literal vs lifetime ('a vs 'a')
        if b == b'\'' {
            let start_line = line;
            if i + 1 < n && bytes[i + 1] == b'\\' {
                i += 2;
                while i < n && bytes[i] != b'\'' && bytes[i] != b'\n' {
                    i += 1;
                }
                if i < n && bytes[i] == b'\'' {
                    i += 1;
                }
                out.push(SpannedTok {
                    tok: RTok::Literal,
                    line: start_line,
                });
                continue;
            }
            if i + 2 < n && bytes[i + 2] == b'\'' && bytes[i + 1] != b'\n' {
                i += 3;
                out.push(SpannedTok {
                    tok: RTok::Literal,
                    line: start_line,
                });
                continue;
            }
            // Lifetime ('static, '_, 'a)
            i += 1;
            while i < n && is_ident_continue(bytes[i]) {
                i += 1;
            }
            out.push(SpannedTok {
                tok: RTok::Lifetime,
                line: start_line,
            });
            continue;
        }
        // Raw identifier r#ident or ordinary identifier
        if b == b'r' && i + 2 < n && bytes[i + 1] == b'#' && is_ident_start(bytes[i + 2]) {
            let start = i + 2;
            i += 3;
            while i < n && is_ident_continue(bytes[i]) {
                i += 1;
            }
            let s = String::from_utf8_lossy(&bytes[start..i]).into_owned();
            out.push(SpannedTok {
                tok: RTok::Ident(s),
                line,
            });
            continue;
        }
        if is_ident_start(b) {
            let start = i;
            i += 1;
            while i < n && is_ident_continue(bytes[i]) {
                i += 1;
            }
            let s = String::from_utf8_lossy(&bytes[start..i]).into_owned();
            out.push(SpannedTok {
                tok: RTok::Ident(s),
                line,
            });
            continue;
        }
        // Numeric literal
        if b.is_ascii_digit() {
            let start_line = line;
            i += 1;
            while i < n && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            out.push(SpannedTok {
                tok: RTok::Literal,
                line: start_line,
            });
            continue;
        }
        // Multi-char operators we care about
        if b == b':' && i + 1 < n && bytes[i + 1] == b':' {
            out.push(SpannedTok {
                tok: RTok::ColonColon,
                line,
            });
            i += 2;
            continue;
        }
        if b == b'-' && i + 1 < n && bytes[i + 1] == b'>' {
            out.push(SpannedTok {
                tok: RTok::Arrow,
                line,
            });
            i += 2;
            continue;
        }
        if b == b'=' && i + 1 < n && bytes[i + 1] == b'>' {
            out.push(SpannedTok {
                tok: RTok::FatArrow,
                line,
            });
            i += 2;
            continue;
        }
        out.push(SpannedTok {
            tok: RTok::Punct(b as char),
            line,
        });
        i += 1;
    }

    out
}

fn find_matching_delim(toks: &[SpannedTok], open_idx: usize, open: char, close: char) -> usize {
    let mut depth = 0usize;
    let mut idx = open_idx;
    while idx < toks.len() {
        if toks[idx].tok == RTok::Punct(open) {
            depth += 1;
        } else if toks[idx].tok == RTok::Punct(close) {
            depth = depth.saturating_sub(1);
            if depth == 0 {
                return idx;
            }
        }
        idx += 1;
    }
    toks.len().saturating_sub(1)
}

/// Inspect leading `#[...]` outer attributes starting at `start`, returning
/// `(after_attrs_idx, is_cfg_test, derived_traits)`.
fn parse_outer_attrs(toks: &[SpannedTok], mut idx: usize) -> (usize, bool, Vec<String>) {
    let mut is_cfg_test = false;
    let mut derives = Vec::new();
    while idx + 1 < toks.len()
        && toks[idx].tok == RTok::Punct('#')
        && toks[idx + 1].tok == RTok::Punct('[')
    {
        let close = find_matching_delim(toks, idx + 1, '[', ']');
        let inner = &toks[idx + 2..close];
        if let Some(SpannedTok {
            tok: RTok::Ident(head),
            ..
        }) = inner.first()
        {
            if head == "cfg" {
                // #[cfg(test)] (but NOT #[cfg(not(test))])
                let has_not = inner
                    .iter()
                    .any(|t| matches!(&t.tok, RTok::Ident(s) if s == "not"));
                let has_test = inner
                    .iter()
                    .any(|t| matches!(&t.tok, RTok::Ident(s) if s == "test"));
                if has_test && !has_not {
                    is_cfg_test = true;
                }
            } else if head == "derive" {
                for t in &inner[1..] {
                    if let RTok::Ident(tr) = &t.tok {
                        derives.push(tr.clone());
                    }
                }
            }
        }
        idx = close + 1;
    }
    (idx, is_cfg_test, derives)
}

fn skip_vis_and_qualifiers(toks: &[SpannedTok], mut idx: usize) -> usize {
    while idx < toks.len() {
        match &toks[idx].tok {
            RTok::Ident(s) if s == "pub" => {
                idx += 1;
                if idx < toks.len() && toks[idx].tok == RTok::Punct('(') {
                    idx = find_matching_delim(toks, idx, '(', ')') + 1;
                }
            }
            RTok::Ident(s) if matches!(s.as_str(), "const" | "async" | "unsafe" | "default") => {
                idx += 1;
            }
            RTok::Ident(s) if s == "extern" => {
                idx += 1;
                if idx < toks.len() && toks[idx].tok == RTok::Literal {
                    idx += 1;
                }
            }
            _ => break,
        }
    }
    idx
}

fn skip_angle_generics(toks: &[SpannedTok], mut idx: usize) -> usize {
    if idx < toks.len() && toks[idx].tok == RTok::Punct('<') {
        let mut depth = 0usize;
        while idx < toks.len() {
            match &toks[idx].tok {
                RTok::Punct('<') => depth += 1,
                RTok::Punct('>') => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        return idx + 1;
                    }
                }
                _ => {}
            }
            idx += 1;
        }
    }
    idx
}

// ============================================================================
// Rust Crate Type & Function Call Graph Extraction
// ============================================================================

#[derive(Debug)]
struct RustTypeDef {
    name: String,
    file: PathBuf,
    line: usize,
    derives: Vec<String>,
    field_type_idents: BTreeSet<String>,
    uses_heap_container: bool,
    has_manual_drop: bool,
}

#[derive(Debug, Clone)]
struct RustFnDef {
    qual_name: String,
    short_name: String,
    mod_path: String,
    impl_type: Option<String>,
    param_types: HashMap<String, String>,
    file: PathBuf,
    line: usize,
    body_toks: Vec<SpannedTok>,
}

fn extract_type_refs_from_type_expr(
    slice: &[SpannedTok],
    refs: &mut BTreeSet<String>,
    uses_heap: &mut bool,
) {
    let mut i = 0usize;
    while i < slice.len() {
        // Skip raw pointers `*const T` / `*mut T`
        if slice[i].tok == RTok::Punct('*')
            && i + 1 < slice.len()
            && matches!(&slice[i + 1].tok, RTok::Ident(kw) if kw == "const" || kw == "mut")
        {
            return;
        }
        if let RTok::Ident(ident) = &slice[i].tok {
            if ident == "PhantomData" {
                i = skip_angle_generics(slice, i + 1);
                continue;
            }
            if ident == "fn" {
                if i + 1 < slice.len() && slice[i + 1].tok == RTok::Punct('(') {
                    i = find_matching_delim(slice, i + 1, '(', ')') + 1;
                } else {
                    i += 1;
                }
                continue;
            }
            if HEAP_CONTAINERS.contains(&ident.as_str()) {
                *uses_heap = true;
            }
            if ident.bytes().next().is_some_and(|c| c.is_ascii_uppercase()) {
                refs.insert(ident.clone());
            }
        }
        i += 1;
    }
}

/// Extract referenced type identifiers from a named-field block `{ f: Ty, ... }`.
fn extract_named_fields_types(
    body: &[SpannedTok],
    refs: &mut BTreeSet<String>,
    uses_heap: &mut bool,
) {
    let mut i = 0usize;
    while i < body.len() {
        if body[i].tok == RTok::Punct(':') {
            let start = i + 1;
            let mut end = start;
            let mut depth = 0usize;
            while end < body.len() {
                match body[end].tok {
                    RTok::Punct('<') | RTok::Punct('(') | RTok::Punct('[') | RTok::Punct('{') => {
                        depth += 1;
                    }
                    RTok::Punct('>') | RTok::Punct(')') | RTok::Punct(']') | RTok::Punct('}') => {
                        depth = depth.saturating_sub(1);
                    }
                    RTok::Punct(',') if depth == 0 => break,
                    _ => {}
                }
                end += 1;
            }
            extract_type_refs_from_type_expr(&body[start..end], refs, uses_heap);
            i = end + 1;
        } else {
            i += 1;
        }
    }
}

fn extract_struct_or_enum_types(
    is_enum: bool,
    is_tuple_struct: bool,
    body: &[SpannedTok],
) -> (BTreeSet<String>, bool) {
    let mut refs = BTreeSet::new();
    let mut uses_heap = false;
    if !is_enum {
        if is_tuple_struct {
            extract_type_refs_from_type_expr(body, &mut refs, &mut uses_heap);
        } else {
            extract_named_fields_types(body, &mut refs, &mut uses_heap);
        }
        return (refs, uses_heap);
    }

    // Enum body: skip outer attributes & variant names; inspect only `( ... )` or `{ ... }` payloads!
    let mut i = 0usize;
    while i < body.len() {
        let (after_attrs, _, _) = parse_outer_attrs(body, i);
        i = after_attrs;
        if i >= body.len() {
            break;
        }
        // Variant name is `body[i]`; advance to `(`, `{`, `=`, or `,`.
        i += 1;
        while i < body.len() {
            match body[i].tok {
                RTok::Punct('(') => {
                    let close = find_matching_delim(body, i, '(', ')');
                    extract_type_refs_from_type_expr(
                        &body[i + 1..close],
                        &mut refs,
                        &mut uses_heap,
                    );
                    i = close + 1;
                }
                RTok::Punct('{') => {
                    let close = find_matching_delim(body, i, '{', '}');
                    extract_named_fields_types(&body[i + 1..close], &mut refs, &mut uses_heap);
                    i = close + 1;
                }
                RTok::Punct('=') => {
                    // Skip discriminant expression up to top-level `,`
                    i += 1;
                    let mut depth = 0usize;
                    while i < body.len() {
                        match body[i].tok {
                            RTok::Punct('(') | RTok::Punct('[') | RTok::Punct('{') => depth += 1,
                            RTok::Punct(')') | RTok::Punct(']') | RTok::Punct('}') => {
                                depth = depth.saturating_sub(1);
                            }
                            RTok::Punct(',') if depth == 0 => break,
                            _ => {}
                        }
                        i += 1;
                    }
                }
                RTok::Punct(',') => {
                    i += 1;
                    break;
                }
                _ => {
                    i += 1;
                }
            }
        }
    }
    (refs, uses_heap)
}

fn extract_fn_param_types(params_slice: &[SpannedTok]) -> HashMap<String, String> {
    let mut map = HashMap::new();
    let mut i = 0usize;
    while i < params_slice.len() {
        if params_slice[i].tok == RTok::Punct(':') && i > 0 {
            let pname = match &params_slice[i - 1].tok {
                RTok::Ident(s) => Some(s.clone()),
                _ => None,
            };
            let start = i + 1;
            let mut end = start;
            let mut depth = 0usize;
            while end < params_slice.len() {
                match params_slice[end].tok {
                    RTok::Punct('<') | RTok::Punct('(') | RTok::Punct('[') => depth += 1,
                    RTok::Punct('>') | RTok::Punct(')') | RTok::Punct(']') => {
                        depth = depth.saturating_sub(1);
                    }
                    RTok::Punct(',') if depth == 0 => break,
                    _ => {}
                }
                end += 1;
            }
            if let Some(p) = pname {
                // Find first PascalCase type identifier before `<`
                for t in &params_slice[start..end] {
                    if t.tok == RTok::Punct('<') {
                        break;
                    }
                    if let RTok::Ident(id) = &t.tok
                        && id.bytes().next().is_some_and(|b| b.is_ascii_uppercase())
                    {
                        map.insert(p, id.clone());
                        break;
                    }
                }
            }
            i = end + 1;
        } else {
            i += 1;
        }
    }
    map
}

fn module_path_for_file(src_dir: &Path, file: &Path) -> String {
    let rel = file.strip_prefix(src_dir).unwrap_or(file);
    let mut parts: Vec<String> = rel
        .components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect();
    if let Some(last) = parts.last_mut() {
        if last == "lib.rs" || last == "main.rs" || last == "mod.rs" {
            parts.pop();
        } else if let Some(stem) = last.strip_suffix(".rs") {
            *last = stem.to_string();
        }
    }
    parts.join("::")
}

#[derive(Debug)]
struct ScopeFrame {
    end_brace: usize,
    mod_path: String,
    impl_type: Option<String>,
}

fn parse_rust_file_items(
    file: &Path,
    base_mod: &str,
    toks: &[SpannedTok],
    types: &mut Vec<RustTypeDef>,
    drop_impls: &mut BTreeSet<String>,
    fns: &mut Vec<RustFnDef>,
    mod_imports: &mut HashMap<String, HashMap<String, String>>,
) {
    let mut scope_stack: Vec<ScopeFrame> = Vec::new();
    let mut idx = 0usize;

    while idx < toks.len() {
        while let Some(top) = scope_stack.last() {
            if idx >= top.end_brace {
                scope_stack.pop();
            } else {
                break;
            }
        }
        let cur_mod = scope_stack
            .last()
            .map(|s| s.mod_path.clone())
            .unwrap_or_else(|| base_mod.to_string());
        let cur_impl = scope_stack.last().and_then(|s| s.impl_type.clone());

        // Skip inner attributes `#![...]`
        if idx + 2 < toks.len()
            && toks[idx].tok == RTok::Punct('#')
            && toks[idx + 1].tok == RTok::Punct('!')
            && toks[idx + 2].tok == RTok::Punct('[')
        {
            idx = find_matching_delim(toks, idx + 2, '[', ']') + 1;
            continue;
        }

        let (after_attrs, is_cfg_test, derives) = parse_outer_attrs(toks, idx);
        if after_attrs > idx && is_cfg_test {
            // Skip the entire `#[cfg(test)]` item (`mod tests { ... }` or `fn ... { ... }`).
            let mut k = after_attrs;
            while k < toks.len() {
                if toks[k].tok == RTok::Punct('{') {
                    idx = find_matching_delim(toks, k, '{', '}') + 1;
                    break;
                } else if toks[k].tok == RTok::Punct(';') {
                    idx = k + 1;
                    break;
                }
                k += 1;
            }
            if k >= toks.len() {
                break;
            }
            continue;
        }
        idx = after_attrs;
        if idx >= toks.len() {
            break;
        }

        let item_idx = skip_vis_and_qualifiers(toks, idx);
        if item_idx >= toks.len() {
            break;
        }

        match &toks[item_idx].tok {
            RTok::Ident(kw) if kw == "use" => {
                // Record simple `use crate::a::b::foo;` or `use super::foo;` imports.
                let mut end = item_idx + 1;
                while end < toks.len() && toks[end].tok != RTok::Punct(';') {
                    end += 1;
                }
                let mut segs = Vec::new();
                for t in &toks[item_idx + 1..end] {
                    if let RTok::Ident(s) = &t.tok {
                        segs.push(s.clone());
                    } else if t.tok == RTok::Punct('{') || t.tok == RTok::Punct('*') {
                        segs.clear();
                        break;
                    }
                }
                if segs.len() >= 2
                    && let Some(last) = segs.last().cloned()
                {
                    let resolved = if segs[0] == "crate" {
                        segs[1..].join("::")
                    } else if segs[0] == "super" {
                        let parent = cur_mod
                            .rsplit_once("::")
                            .map(|(p, _)| p.to_string())
                            .unwrap_or_default();
                        if parent.is_empty() {
                            segs[1..].join("::")
                        } else {
                            format!("{parent}::{}", segs[1..].join("::"))
                        }
                    } else {
                        segs.join("::")
                    };
                    mod_imports
                        .entry(cur_mod.clone())
                        .or_default()
                        .insert(last, resolved);
                }
                idx = (end + 1).min(toks.len());
            }
            RTok::Ident(kw) if kw == "mod" => {
                if let Some(SpannedTok {
                    tok: RTok::Ident(mname),
                    ..
                }) = toks.get(item_idx + 1)
                    && toks.get(item_idx + 2).map(|t| &t.tok) == Some(&RTok::Punct('{'))
                {
                    let close = find_matching_delim(toks, item_idx + 2, '{', '}');
                    let sub_mod = if cur_mod.is_empty() {
                        mname.clone()
                    } else {
                        format!("{cur_mod}::{mname}")
                    };
                    scope_stack.push(ScopeFrame {
                        end_brace: close,
                        mod_path: sub_mod,
                        impl_type: None,
                    });
                    idx = item_idx + 3;
                    continue;
                }
                idx = item_idx + 1;
            }
            RTok::Ident(kw) if kw == "struct" || kw == "enum" => {
                let is_enum = kw == "enum";
                let line = toks[item_idx].line;
                if let Some(SpannedTok {
                    tok: RTok::Ident(tname),
                    ..
                }) = toks.get(item_idx + 1)
                {
                    let mut scan = skip_angle_generics(toks, item_idx + 2);
                    while scan < toks.len()
                        && toks[scan].tok != RTok::Punct('{')
                        && toks[scan].tok != RTok::Punct('(')
                        && toks[scan].tok != RTok::Punct(';')
                    {
                        scan += 1;
                    }
                    let mut is_tuple_struct = false;
                    let (body_slice, next_i) =
                        if scan < toks.len() && toks[scan].tok == RTok::Punct('{') {
                            let close = find_matching_delim(toks, scan, '{', '}');
                            (&toks[scan + 1..close], close + 1)
                        } else if scan < toks.len() && toks[scan].tok == RTok::Punct('(') {
                            is_tuple_struct = true;
                            let close = find_matching_delim(toks, scan, '(', ')');
                            (&toks[scan + 1..close], close + 1)
                        } else {
                            (&[][..], (scan + 1).min(toks.len()))
                        };
                    let (mut refs, uses_heap) =
                        extract_struct_or_enum_types(is_enum, is_tuple_struct, body_slice);
                    if refs.remove("Self") {
                        refs.insert(tname.clone());
                    }
                    types.push(RustTypeDef {
                        name: tname.clone(),
                        file: file.to_path_buf(),
                        line,
                        derives,
                        field_type_idents: refs,
                        uses_heap_container: uses_heap,
                        has_manual_drop: false,
                    });
                    idx = next_i;
                    continue;
                }
                idx = item_idx + 1;
            }
            RTok::Ident(kw) if kw == "impl" => {
                let mut scan = skip_angle_generics(toks, item_idx + 1);
                let mut header_idents: Vec<String> = Vec::new();
                let mut saw_for = false;
                let mut trait_name: Option<String> = None;
                let target_type: Option<String>;
                while scan < toks.len()
                    && toks[scan].tok != RTok::Punct('{')
                    && toks[scan].tok != RTok::Punct(';')
                {
                    if let RTok::Ident(id) = &toks[scan].tok {
                        if id == "where" {
                            while scan < toks.len() && toks[scan].tok != RTok::Punct('{') {
                                scan += 1;
                            }
                            break;
                        } else if id == "for" {
                            saw_for = true;
                            trait_name = header_idents.last().cloned();
                            header_idents.clear();
                        } else {
                            header_idents.push(id.clone());
                        }
                    } else if toks[scan].tok == RTok::Punct('<') {
                        scan = skip_angle_generics(toks, scan);
                        continue;
                    }
                    scan += 1;
                }
                if saw_for {
                    target_type = header_idents.last().cloned();
                    if trait_name.as_deref() == Some("Drop")
                        && let Some(tt) = &target_type
                    {
                        drop_impls.insert(tt.clone());
                    }
                } else {
                    target_type = header_idents.last().cloned();
                }
                if scan < toks.len() && toks[scan].tok == RTok::Punct('{') {
                    let close = find_matching_delim(toks, scan, '{', '}');
                    scope_stack.push(ScopeFrame {
                        end_brace: close,
                        mod_path: cur_mod,
                        impl_type: target_type,
                    });
                    idx = scan + 1;
                    continue;
                }
                idx = (scan + 1).min(toks.len());
            }
            RTok::Ident(kw) if kw == "trait" => {
                // Skip trait declaration blocks (default methods are checked at concrete impls
                // unless they self-recurse; skip to closing brace only for bodyless prototypes).
                let mut scan = item_idx + 1;
                while scan < toks.len()
                    && toks[scan].tok != RTok::Punct('{')
                    && toks[scan].tok != RTok::Punct(';')
                {
                    scan += 1;
                }
                if scan < toks.len() && toks[scan].tok == RTok::Punct('{') {
                    let close = find_matching_delim(toks, scan, '{', '}');
                    let tname = toks.get(item_idx + 1).and_then(|t| match &t.tok {
                        RTok::Ident(s) => Some(s.clone()),
                        _ => None,
                    });
                    scope_stack.push(ScopeFrame {
                        end_brace: close,
                        mod_path: cur_mod,
                        impl_type: tname,
                    });
                    idx = scan + 1;
                    continue;
                }
                idx = (scan + 1).min(toks.len());
            }
            RTok::Ident(kw) if kw == "fn" => {
                let line = toks[item_idx].line;
                if let Some(SpannedTok {
                    tok: RTok::Ident(fname),
                    ..
                }) = toks.get(item_idx + 1)
                {
                    let mut scan = skip_angle_generics(toks, item_idx + 2);
                    let mut param_types = HashMap::new();
                    if scan < toks.len() && toks[scan].tok == RTok::Punct('(') {
                        let close_p = find_matching_delim(toks, scan, '(', ')');
                        param_types = extract_fn_param_types(&toks[scan + 1..close_p]);
                        scan = close_p + 1;
                    }
                    while scan < toks.len()
                        && toks[scan].tok != RTok::Punct('{')
                        && toks[scan].tok != RTok::Punct(';')
                    {
                        scan += 1;
                    }
                    if scan < toks.len() && toks[scan].tok == RTok::Punct('{') {
                        let close = find_matching_delim(toks, scan, '{', '}');
                        let qual_name = if let Some(ty) = &cur_impl {
                            if cur_mod.is_empty() {
                                format!("{ty}::{fname}")
                            } else {
                                format!("{cur_mod}::{ty}::{fname}")
                            }
                        } else if cur_mod.is_empty() {
                            fname.clone()
                        } else {
                            format!("{cur_mod}::{fname}")
                        };
                        fns.push(RustFnDef {
                            qual_name,
                            short_name: fname.clone(),
                            mod_path: cur_mod,
                            impl_type: cur_impl,
                            param_types,
                            file: file.to_path_buf(),
                            line,
                            body_toks: toks[scan + 1..close].to_vec(),
                        });
                        idx = close + 1;
                        continue;
                    } else if scan < toks.len() && toks[scan].tok == RTok::Punct(';') {
                        idx = scan + 1;
                        continue;
                    }
                }
                idx = item_idx + 1;
            }
            RTok::Ident(kw) if kw == "macro_rules" => {
                // Skip macro_rules! definition body
                let mut scan = item_idx + 1;
                while scan < toks.len()
                    && toks[scan].tok != RTok::Punct('{')
                    && toks[scan].tok != RTok::Punct('(')
                    && toks[scan].tok != RTok::Punct('[')
                {
                    scan += 1;
                }
                if scan < toks.len() {
                    let close = match toks[scan].tok {
                        RTok::Punct('{') => find_matching_delim(toks, scan, '{', '}'),
                        RTok::Punct('(') => find_matching_delim(toks, scan, '(', ')'),
                        RTok::Punct('[') => find_matching_delim(toks, scan, '[', ']'),
                        _ => scan,
                    };
                    idx = close + 1;
                    continue;
                }
                idx = item_idx + 1;
            }
            _ => {
                idx = item_idx + 1;
            }
        }
    }
}

fn check_rust_crate(crate_name: &str, files: &[PathBuf], src_dir: &Path, errors: &mut Vec<String>) {
    let mut types: Vec<RustTypeDef> = Vec::new();
    let mut drop_impls: BTreeSet<String> = BTreeSet::new();
    let mut fns: Vec<RustFnDef> = Vec::new();
    let mut mod_imports: HashMap<String, HashMap<String, String>> = HashMap::new();

    for file in files {
        let src = fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("failed reading {}: {e}", file.display()));
        let toks = tokenize_rust(&src);
        let base_mod = module_path_for_file(src_dir, file);
        parse_rust_file_items(
            file,
            &base_mod,
            &toks,
            &mut types,
            &mut drop_impls,
            &mut fns,
            &mut mod_imports,
        );
    }

    for td in &mut types {
        if drop_impls.contains(&td.name) {
            td.has_manual_drop = true;
        }
    }

    // --- Check A: Recursive Type SCCs vs. Derived Traits & Drop Glue ---
    let mut type_indices_by_name: HashMap<String, Vec<usize>> = HashMap::new();
    for (idx, td) in types.iter().enumerate() {
        type_indices_by_name
            .entry(td.name.clone())
            .or_default()
            .push(idx);
    }
    let mut type_adj = vec![Vec::new(); types.len()];
    for (i, td) in types.iter().enumerate() {
        // Only link unambiguous or same-file type definitions to avoid false cross-module name collisions.
        for ref_name in &td.field_type_idents {
            if let Some(cands) = type_indices_by_name.get(ref_name) {
                if cands.len() == 1 {
                    type_adj[i].push(cands[0]);
                } else {
                    for &c in cands {
                        if types[c].file == td.file {
                            type_adj[i].push(c);
                        }
                    }
                }
            }
        }
        type_adj[i].sort_unstable();
        type_adj[i].dedup();
    }

    for scc in tarjan_nontrivial_sccs(&type_adj) {
        let cycle_names: Vec<String> = scc
            .iter()
            .map(|&idx| {
                format!(
                    "{} ({}:{})",
                    types[idx].name,
                    types[idx].file.display(),
                    types[idx].line
                )
            })
            .collect();
        for &idx in &scc {
            for d in &types[idx].derives {
                if RECURSIVE_DERIVE_TRAITS.contains(&d.as_str()) {
                    errors.push(format!(
                        "[{crate_name}] recursive type `{}` derives `{d}` at {}:{} (cycle: {})",
                        types[idx].name,
                        types[idx].file.display(),
                        types[idx].line,
                        cycle_names.join(" -> ")
                    ));
                }
            }
        }
        let any_heap = scc.iter().any(|&idx| types[idx].uses_heap_container);
        let any_drop = scc.iter().any(|&idx| types[idx].has_manual_drop);
        if any_heap && !any_drop {
            let first = &types[scc[0]];
            errors.push(format!(
                "[{crate_name}] heap-owning recursive type cycle lacks iterative `impl Drop` at {}:{} (cycle: {})",
                first.file.display(),
                first.line,
                cycle_names.join(" -> ")
            ));
        }
    }

    // --- Check B: Intra-Crate Direct & Mutual Function/Method Call Cycles ---
    let mut fn_by_qual: HashMap<String, Vec<usize>> = HashMap::new();
    let mut fn_by_mod_short: HashMap<(String, String), Vec<usize>> = HashMap::new();
    let mut fn_by_type_method: HashMap<(String, String), Vec<usize>> = HashMap::new();

    for (idx, f) in fns.iter().enumerate() {
        fn_by_qual.entry(f.qual_name.clone()).or_default().push(idx);
        if f.impl_type.is_none() {
            fn_by_mod_short
                .entry((f.mod_path.clone(), f.short_name.clone()))
                .or_default()
                .push(idx);
        }
        if let Some(ty) = &f.impl_type {
            fn_by_type_method
                .entry((ty.clone(), f.short_name.clone()))
                .or_default()
                .push(idx);
        }
    }

    let mut fn_adj = vec![Vec::new(); fns.len()];
    for (caller_idx, f) in fns.iter().enumerate() {
        // Also strip nested local `fn` items inside `f.body_toks`? No — nested local `fn`s
        // inside a function are ALSO forbidden from recursing! If a local `fn helper()` calls
        // `helper()`, catch that directly as a self-recursion error too!
        let mut local_fns: BTreeSet<String> = BTreeSet::new();
        let body = &f.body_toks;
        let mut k = 0usize;
        while k + 1 < body.len() {
            if matches!(&body[k].tok, RTok::Ident(kw) if kw == "fn")
                && let RTok::Ident(lfn) = &body[k + 1].tok
            {
                local_fns.insert(lfn.clone());
            }
            k += 1;
        }

        let mut i = 0usize;
        while i < body.len() {
            // Check `self.method(` on `impl_type` OR `param.method(` on typed parameter `param: &Type`
            if i + 3 < body.len()
                && let RTok::Ident(recv) = &body[i].tok
                && body[i + 1].tok == RTok::Punct('.')
                && let RTok::Ident(mname) = &body[i + 2].tok
            {
                let after = skip_turbofish(body, i + 3);
                let recv_ty = if recv == "self" {
                    f.impl_type.as_deref()
                } else {
                    f.param_types.get(recv).map(String::as_str)
                };
                if after < body.len()
                    && body[after].tok == RTok::Punct('(')
                    && let Some(ty) = recv_ty
                    && let Some(targets) = fn_by_type_method.get(&(ty.to_string(), mname.clone()))
                {
                    for &t in targets {
                        if targets.len() == 1 || fns[t].file == f.file {
                            fn_adj[caller_idx].push(t);
                        }
                    }
                    i = after;
                    continue;
                }
            }

            // Skip field/method chains `expr.foo(` where receiver is NOT `self`
            if i > 0 && body[i - 1].tok == RTok::Punct('.') {
                i += 1;
                continue;
            }

            // Parse `seg1::seg2::...::last(` or bare `ident(`
            if let RTok::Ident(first) = &body[i].tok {
                let mut segs = vec![first.clone()];
                let mut j = i + 1;
                loop {
                    if j + 1 < body.len() && body[j].tok == RTok::ColonColon {
                        if body[j + 1].tok == RTok::Punct('<') {
                            j = skip_angle_generics(body, j + 1);
                            continue;
                        }
                        if let RTok::Ident(next_seg) = &body[j + 1].tok {
                            segs.push(next_seg.clone());
                            j += 2;
                            continue;
                        }
                    }
                    break;
                }
                // Skip macro invocations `foo!(...)`
                if j < body.len() && body[j].tok == RTok::Punct('!') {
                    i = j + 1;
                    continue;
                }
                if j < body.len() && body[j].tok == RTok::Punct('(') {
                    if segs.len() == 1 {
                        let callee = &segs[0];
                        if local_fns.contains(callee) {
                            // Check if local fn calls itself inside its own body!
                            check_local_fn_recursion(crate_name, f, callee, errors);
                        }
                        // Free function in same module
                        if f.impl_type.is_none() || callee != &f.short_name {
                            if let Some(targets) =
                                fn_by_mod_short.get(&(f.mod_path.clone(), callee.clone()))
                            {
                                fn_adj[caller_idx].extend(targets.iter().copied());
                            } else if let Some(imp_map) = mod_imports.get(&f.mod_path)
                                && let Some(qual) = imp_map.get(callee)
                                && let Some(targets) = fn_by_qual.get(qual)
                            {
                                fn_adj[caller_idx].extend(targets.iter().copied());
                            }
                        } else if f.impl_type.is_none() && callee == &f.short_name {
                            fn_adj[caller_idx].push(caller_idx);
                        }
                    } else if segs.len() == 2
                        && (segs[0] == "Self" || Some(&segs[0]) == f.impl_type.as_ref())
                    {
                        let ty = f.impl_type.as_ref().unwrap_or(&segs[0]);
                        if let Some(targets) = fn_by_type_method.get(&(ty.clone(), segs[1].clone()))
                        {
                            for &t in targets {
                                if targets.len() == 1 || fns[t].file == f.file {
                                    fn_adj[caller_idx].push(t);
                                }
                            }
                        }
                    } else {
                        // Qualified path call: `crate::a::b`, `super::b`, `Type::method`, or `submod::func`
                        let last = segs.last().cloned().unwrap_or_default();
                        let penult = segs[segs.len() - 2].clone();
                        if penult
                            .bytes()
                            .next()
                            .is_some_and(|c| c.is_ascii_uppercase())
                        {
                            if let Some(targets) = fn_by_type_method.get(&(penult, last))
                                && targets.len() == 1
                            {
                                fn_adj[caller_idx].push(targets[0]);
                            }
                        } else {
                            let cand_qual = if segs[0] == "crate" {
                                segs[1..].join("::")
                            } else if segs[0] == "super" {
                                let parent = f
                                    .mod_path
                                    .rsplit_once("::")
                                    .map(|(p, _)| p.to_string())
                                    .unwrap_or_default();
                                if parent.is_empty() {
                                    segs[1..].join("::")
                                } else {
                                    format!("{parent}::{}", segs[1..].join("::"))
                                }
                            } else if f.mod_path.is_empty() {
                                segs.join("::")
                            } else {
                                format!("{}::{}", f.mod_path, segs.join("::"))
                            };
                            if let Some(targets) = fn_by_qual.get(&cand_qual) {
                                fn_adj[caller_idx].extend(targets.iter().copied());
                            } else if let Some(targets) = fn_by_qual.get(&segs.join("::")) {
                                fn_adj[caller_idx].extend(targets.iter().copied());
                            }
                        }
                    }
                    i = j + 1;
                    continue;
                }
            }
            i += 1;
        }
        fn_adj[caller_idx].sort_unstable();
        fn_adj[caller_idx].dedup();
    }

    for scc in tarjan_nontrivial_sccs(&fn_adj) {
        let trace: Vec<String> = scc
            .iter()
            .map(|&idx| {
                format!(
                    "{} ({}:{})",
                    fns[idx].qual_name,
                    fns[idx].file.display(),
                    fns[idx].line
                )
            })
            .collect();
        errors.push(format!(
            "[{crate_name}] recursive function/method call cycle detected: {}",
            trace.join(" -> ")
        ));
    }
}

fn skip_turbofish(toks: &[SpannedTok], idx: usize) -> usize {
    if idx + 1 < toks.len()
        && toks[idx].tok == RTok::ColonColon
        && toks[idx + 1].tok == RTok::Punct('<')
    {
        skip_angle_generics(toks, idx + 1)
    } else {
        idx
    }
}

fn check_local_fn_recursion(
    crate_name: &str,
    outer: &RustFnDef,
    local_name: &str,
    errors: &mut Vec<String>,
) {
    let body = &outer.body_toks;
    let mut i = 0usize;
    while i + 1 < body.len() {
        if matches!(&body[i].tok, RTok::Ident(kw) if kw == "fn")
            && matches!(&body[i + 1].tok, RTok::Ident(n) if n == local_name)
        {
            let def_line = body[i].line;
            let mut scan = skip_angle_generics(body, i + 2);
            if scan < body.len() && body[scan].tok == RTok::Punct('(') {
                scan = find_matching_delim(body, scan, '(', ')') + 1;
            }
            while scan < body.len()
                && body[scan].tok != RTok::Punct('{')
                && body[scan].tok != RTok::Punct(';')
            {
                scan += 1;
            }
            if scan < body.len() && body[scan].tok == RTok::Punct('{') {
                let close = find_matching_delim(body, scan, '{', '}');
                for k in scan + 1..close {
                    let prev_dot = k > 0 && body[k - 1].tok == RTok::Punct('.');
                    if !prev_dot
                        && matches!(&body[k].tok, RTok::Ident(id) if id == local_name)
                        && k + 1 < close
                        && body[k + 1].tok == RTok::Punct('(')
                    {
                        errors.push(format!(
                            "[{crate_name}] nested local fn `{local_name}` inside `{}` recurses at {}:{}",
                            outer.qual_name,
                            outer.file.display(),
                            def_line
                        ));
                        break;
                    }
                }
                i = close + 1;
                continue;
            }
        }
        i += 1;
    }
}

// ============================================================================
// C / C++ Bridge & Shim Zero-Recursion Check
// ============================================================================

const C_CONTROL_KEYWORDS: &[&str] = &[
    "if",
    "for",
    "while",
    "switch",
    "catch",
    "return",
    "sizeof",
    "alignof",
    "decltype",
    "static_assert",
    "new",
    "delete",
    "throw",
];

fn check_cpp_directory(label: &str, dir: &Path, errors: &mut Vec<String>) {
    let files = collect_files_iteratively(dir, true, &["c", "cpp", "h", "hpp"]);
    #[derive(Debug)]
    struct CppFn {
        name: String,
        file: PathBuf,
        line: usize,
        calls: BTreeSet<String>,
    }
    let mut defs: Vec<CppFn> = Vec::new();

    for file in &files {
        let src = fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("failed reading {}: {e}", file.display()));
        // Reuse comment/string-stripping tokenizer
        let toks = tokenize_rust(&src);
        let mut idx = 0usize;
        while idx + 2 < toks.len() {
            if let RTok::Ident(name) = &toks[idx].tok
                && !C_CONTROL_KEYWORDS.contains(&name.as_str())
                && !name
                    .chars()
                    .all(|c| c.is_ascii_uppercase() || c == '_' || c.is_ascii_digit())
                && toks[idx + 1].tok == RTok::Punct('(')
            {
                let close_paren = find_matching_delim(&toks, idx + 1, '(', ')');
                let mut scan = close_paren + 1;
                while scan < toks.len()
                    && matches!(&toks[scan].tok, RTok::Ident(q) if q == "const" || q == "noexcept" || q == "override")
                {
                    scan += 1;
                }
                // Skip constructor initializer lists `: a(...), b(...) {`
                if scan < toks.len() && toks[scan].tok == RTok::Punct(':') {
                    while scan < toks.len()
                        && toks[scan].tok != RTok::Punct('{')
                        && toks[scan].tok != RTok::Punct(';')
                    {
                        scan += 1;
                    }
                }
                if scan < toks.len() && toks[scan].tok == RTok::Punct('{') {
                    let close_brace = find_matching_delim(&toks, scan, '{', '}');
                    let mut calls = BTreeSet::new();
                    for k in scan + 1..close_brace {
                        let prev_member = k > 0
                            && (toks[k - 1].tok == RTok::Punct('.')
                                || toks[k - 1].tok == RTok::Arrow);
                        if !prev_member
                            && let RTok::Ident(callee) = &toks[k].tok
                            && !C_CONTROL_KEYWORDS.contains(&callee.as_str())
                            && k + 1 < close_brace
                            && toks[k + 1].tok == RTok::Punct('(')
                        {
                            calls.insert(callee.clone());
                        }
                    }
                    defs.push(CppFn {
                        name: name.clone(),
                        file: file.clone(),
                        line: toks[idx].line,
                        calls,
                    });
                    idx = close_brace + 1;
                    continue;
                }
            }
            idx += 1;
        }
    }

    let mut by_name: HashMap<String, Vec<usize>> = HashMap::new();
    for (i, d) in defs.iter().enumerate() {
        by_name.entry(d.name.clone()).or_default().push(i);
    }
    let mut adj = vec![Vec::new(); defs.len()];
    for (i, d) in defs.iter().enumerate() {
        for c in &d.calls {
            // Skip C++ ctor calls (`Span(...)` constructing a fresh Span inside `SubSpan`)
            if c.bytes().next().is_some_and(|b| b.is_ascii_uppercase()) {
                continue;
            }
            if let Some(targets) = by_name.get(c) {
                adj[i].extend(targets.iter().copied());
            }
        }
        adj[i].sort_unstable();
        adj[i].dedup();
    }

    for scc in tarjan_nontrivial_sccs(&adj) {
        let trace: Vec<String> = scc
            .iter()
            .map(|&idx| {
                format!(
                    "{} ({}:{})",
                    defs[idx].name,
                    defs[idx].file.display(),
                    defs[idx].line
                )
            })
            .collect();
        errors.push(format!(
            "[{label}] C/C++ recursive call cycle detected: {}",
            trace.join(" -> ")
        ));
    }
}

// ============================================================================
// Python Script Zero-Recursion & No-`eval` Check (`scripts/*.py`)
// ============================================================================

fn strip_python_line(line: &str) -> String {
    let bytes = line.as_bytes();
    let mut out = String::with_capacity(bytes.len());
    let mut i = 0usize;
    while i < bytes.len() {
        let b = bytes[i];
        if b == b'#' {
            break;
        }
        if b == b'\'' || b == b'"' {
            let q = b;
            i += 1;
            while i < bytes.len() {
                if bytes[i] == b'\\' {
                    i += 2.min(bytes.len() - i);
                } else if bytes[i] == q {
                    i += 1;
                    break;
                } else {
                    i += 1;
                }
            }
            out.push(' ');
            continue;
        }
        out.push(b as char);
        i += 1;
    }
    out
}

fn check_python_scripts(scripts_dir: &Path, errors: &mut Vec<String>) {
    let files = collect_files_iteratively(scripts_dir, false, &["py"]);
    for file in files {
        let src = fs::read_to_string(&file)
            .unwrap_or_else(|e| panic!("failed reading {}: {e}", file.display()));
        #[derive(Debug)]
        struct PyFn {
            name: String,
            indent: usize,
            line: usize,
            calls: BTreeSet<String>,
        }
        let mut active: Vec<PyFn> = Vec::new();
        let mut finished: Vec<PyFn> = Vec::new();
        let mut in_triple: Option<&str> = None;

        for (line_idx, raw_line) in src.lines().enumerate() {
            let line_no = line_idx + 1;
            let trimmed_start = raw_line.trim_start();
            if let Some(delim) = in_triple {
                if trimmed_start.contains(delim) {
                    in_triple = None;
                }
                continue;
            }
            if trimmed_start.starts_with("\"\"\"") && !trimmed_start[3..].contains("\"\"\"") {
                in_triple = Some("\"\"\"");
                continue;
            }
            if trimmed_start.starts_with("'''") && !trimmed_start[3..].contains("'''") {
                in_triple = Some("'''");
                continue;
            }

            let clean = strip_python_line(raw_line);
            let clean_trim = clean.trim();
            if clean_trim.is_empty() {
                continue;
            }
            let indent = clean.len() - clean.trim_start().len();
            while let Some(top) = active.last() {
                if indent <= top.indent {
                    finished.push(active.pop().expect("non-empty"));
                } else {
                    break;
                }
            }

            if let Some(rest) = clean_trim.strip_prefix("def ")
                && let Some(paren) = rest.find('(')
            {
                let fname = rest[..paren].trim().to_string();
                active.push(PyFn {
                    name: fname,
                    indent,
                    line: line_no,
                    calls: BTreeSet::new(),
                });
                continue;
            }

            let cb = clean.as_bytes();
            let mut k = 0usize;
            while k < cb.len() {
                if is_ident_start(cb[k]) {
                    let prev_dot = k > 0 && cb[k - 1] == b'.';
                    let start = k;
                    k += 1;
                    while k < cb.len() && is_ident_continue(cb[k]) {
                        k += 1;
                    }
                    let ident = &clean[start..k];
                    let mut p = k;
                    while p < cb.len() && cb[p].is_ascii_whitespace() {
                        p += 1;
                    }
                    if p < cb.len() && cb[p] == b'(' && !prev_dot {
                        if ident == "eval" || ident == "exec" {
                            errors.push(format!(
                                "[scripts] forbidden `{ident}(...)` in {}:{}",
                                file.display(),
                                line_no
                            ));
                        }
                        if let Some(cur) = active.last_mut() {
                            cur.calls.insert(ident.to_string());
                        }
                    }
                } else {
                    k += 1;
                }
            }
        }
        while let Some(top) = active.pop() {
            finished.push(top);
        }

        let mut by_name: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        for (idx, f) in finished.iter().enumerate() {
            by_name.entry(f.name.clone()).or_default().push(idx);
        }
        let mut adj = vec![Vec::new(); finished.len()];
        for (idx, f) in finished.iter().enumerate() {
            for c in &f.calls {
                if let Some(targets) = by_name.get(c) {
                    adj[idx].extend(targets.iter().copied());
                }
            }
            adj[idx].sort_unstable();
            adj[idx].dedup();
        }
        for scc in tarjan_nontrivial_sccs(&adj) {
            let trace: Vec<String> = scc
                .iter()
                .map(|&idx| {
                    format!(
                        "{} ({}:{})",
                        finished[idx].name,
                        file.display(),
                        finished[idx].line
                    )
                })
                .collect();
            errors.push(format!(
                "[scripts] Python recursive call cycle detected: {}",
                trace.join(" -> ")
            ));
        }
    }
}

// ============================================================================
// Top-Level Conformance Tests
// ============================================================================

#[test]
fn workspace_enforces_unconditional_recursion_lint() {
    let root = workspace_root();
    let root_toml = fs::read_to_string(root.join("Cargo.toml")).expect("read root Cargo.toml");
    assert!(
        root_toml.contains("unconditional_recursion = \"deny\""),
        "root Cargo.toml must set `unconditional_recursion = \"deny\"` under [workspace.lints.rust]"
    );
    for &krate in CRATES {
        let manifest = fs::read_to_string(root.join(krate).join("Cargo.toml"))
            .unwrap_or_else(|e| panic!("read {krate}/Cargo.toml: {e}"));
        assert!(
            manifest.contains("[lints]") && manifest.contains("workspace = true"),
            "{krate}/Cargo.toml must inherit `[lints] workspace = true`"
        );
    }
}

#[test]
fn zero_recursion_across_all_rust_crates_cpp_bridges_and_python_scripts() {
    let root = workspace_root();
    let mut errors: Vec<String> = Vec::new();

    // 1. All 13 Rust member crates (`src/**/*.rs`, skipping `generated/` and `#[cfg(test)]`).
    for &krate in CRATES {
        let src_dir = root.join(krate).join("src");
        let files = collect_files_iteratively(&src_dir, true, &["rs"]);
        assert!(!files.is_empty(), "{krate}/src must contain Rust sources");
        check_rust_crate(krate, &files, &src_dir, &mut errors);
    }

    // 2. Self-scan this gate file to guarantee zero recursion in the gate itself.
    let gate_file = root.join("tests").join("zero_recursion_gate.rs");
    check_rust_crate(
        "zero_recursion_gate",
        std::slice::from_ref(&gate_file),
        &root.join("tests"),
        &mut errors,
    );

    // 3. Hand-written C/C++ bridges & shims (`abcd-*-sys/bridge` and `vendor/shim`).
    check_cpp_directory(
        "abcd-isa-sys/bridge",
        &root.join("abcd-isa-sys").join("bridge"),
        &mut errors,
    );
    check_cpp_directory(
        "abcd-file-sys/bridge",
        &root.join("abcd-file-sys").join("bridge"),
        &mut errors,
    );
    check_cpp_directory(
        "vendor/shim",
        &root.join("vendor").join("shim"),
        &mut errors,
    );

    // 4. Python maintenance scripts (`scripts/*.py`).
    check_python_scripts(&root.join("scripts"), &mut errors);

    assert!(
        errors.is_empty(),
        "Workspace zero-recursion gate found {} violation(s):\n  - {}",
        errors.len(),
        errors.join("\n  - ")
    );
}
