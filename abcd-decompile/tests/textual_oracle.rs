//! The d-P4 secondary textual oracle (design/decompile.md §7):
//! fixtures' recorded original source gives a TEXTUAL reference for
//! the decompiled output.
//!
//! Source substrate note: the design hoped `DebugData.source_code`
//! would carry the original text on the debug-info profile — in
//! practice es2abc bakes the literal placeholder `"not supported"`
//! there (verified across the corpus: 929 fixtures carry exactly that
//! placeholder). The corpus manifest's `source` field points at the
//! tracked true original (`exports/corpus/sources/…`) for all 2787
//! fixtures, so the oracle uses it instead.
//!
//! Comparison is a whitespace-insensitive token-stream match (a small
//! JS tokenizer: comments stripped, numbers value-normalized). This is
//! NOT an automated gate — formatting, legalized names, temporaries,
//! and deliberate elisions (the guard family) differ by design — so the
//! test reports:
//!
//! - exact token-stream match rate,
//! - token-multiset containment (fraction of source tokens present in
//!   the decompiled output, multiplicity-aware),
//! - LCS ratio (order-aware similarity),
//! - first-divergence classes (what token kind diverges first, and
//!   whether the source token is absent from the output entirely —
//!   elided — or present under a different position/name).
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-decompile --test textual_oracle --release -- --ignored --nocapture
//! ```

mod common;

use abcd_decompile::emit::{EmitOptions, decompile_module};

/// A normalized token: identifiers/literals/punctuation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Tok {
    /// Identifier or keyword.
    Ident(String),
    /// Numeric literal, value-normalized.
    Num(u64),
    /// String/template literal (raw text — escaping differs by design).
    Str,
    /// Punctuation/operator.
    Punct(String),
}

impl Tok {
    fn kind(&self) -> &'static str {
        match self {
            Tok::Ident(_) => "ident",
            Tok::Num(_) => "number",
            Tok::Str => "string",
            Tok::Punct(_) => "punct",
        }
    }
}

/// Tokenize JS source: strip comments/whitespace, normalize numbers.
fn tokenize(src: &str) -> Vec<Tok> {
    let b = src.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    while i < b.len() {
        let c = b[i] as char;
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        // Comments.
        if c == '/' && i + 1 < b.len() && b[i + 1] == b'/' {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if c == '/' && i + 1 < b.len() && b[i + 1] == b'*' {
            i += 2;
            while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') {
                i += 1;
            }
            i = (i + 2).min(b.len());
            continue;
        }
        // Strings / templates (skip to the matching quote, no escape
        // resolution — a backslash skips the next byte).
        if c == '"' || c == '\'' || c == '`' {
            let q = b[i];
            i += 1;
            while i < b.len() && b[i] != q {
                if b[i] == b'\\' {
                    i += 1;
                }
                i += 1;
            }
            i = (i + 1).min(b.len());
            out.push(Tok::Str);
            continue;
        }
        // Numbers (decimal/hex/exp — value-normalized via f64 bits).
        if c.is_ascii_digit()
            || (c == '.' && i + 1 < b.len() && (b[i + 1] as char).is_ascii_digit())
        {
            let start = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'.' || b[i] == b'_') {
                i += 1;
            }
            let text = &src[start..i];
            let v = if let Some(hex) = text.strip_prefix("0x").or(text.strip_prefix("0X")) {
                u64::from_str_radix(hex, 16)
                    .map(|v| v as f64)
                    .unwrap_or(f64::NAN)
            } else {
                text.parse::<f64>().unwrap_or(f64::NAN)
            };
            out.push(Tok::Num(v.to_bits()));
            continue;
        }
        // Identifiers/keywords.
        if c.is_alphabetic() || c == '_' || c == '$' {
            let start = i;
            while i < b.len() && ((b[i] as char).is_alphanumeric() || b[i] == b'_' || b[i] == b'$')
            {
                i += 1;
            }
            out.push(Tok::Ident(src[start..i].to_string()));
            continue;
        }
        // Multi-char operators, longest first.
        let rest = &src[i..];
        let ops = [
            ">>>=", "===", "!==", ">>>", "**=", "<<=", ">>=", "&&=", "||=", "??=", "...", "=>",
            "==", "!=", "<=", ">=", "&&", "||", "??", "++", "--", "+=", "-=", "*=", "/=", "%=",
            "&=", "|=", "^=", "<<", ">>", "**", "?.",
        ];
        if let Some(op) = ops.iter().find(|op| rest.starts_with(**op)) {
            out.push(Tok::Punct((*op).to_string()));
            i += op.len();
            continue;
        }
        out.push(Tok::Punct(c.to_string()));
        i += 1;
    }
    out
}

/// Longest common subsequence length (Ukkonen-free DP; tokens are short
/// enough here — corpus sources are small).
fn lcs_len(a: &[Tok], b: &[Tok]) -> usize {
    let mut dp = vec![0usize; b.len() + 1];
    for x in a {
        let mut prev = 0;
        for (j, y) in b.iter().enumerate() {
            let t = dp[j + 1];
            if x == y {
                dp[j + 1] = prev + 1;
            } else {
                dp[j + 1] = dp[j + 1].max(dp[j]);
            }
            prev = t;
        }
    }
    dp[b.len()]
}

/// Manifest rows as `abc<TAB>source` pairs (python3 parses the JSON).
fn manifest_sources(root: &std::path::Path) -> Vec<(String, String)> {
    let output = std::process::Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, sys
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        abc, src = row["abc"], row.get("source") or ""
        assert "\t" not in abc and "\t" not in src
        print(f"{abc}\t{src}")
"#,
        )
        .arg(root.join("index.jsonl"))
        .output()
        .expect("python3 is required by corpus tooling");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("UTF-8 manifest")
        .lines()
        .map(|l| {
            let (a, b) = l.split_once('\t').expect("abc<TAB>source");
            (a.to_string(), b.to_string())
        })
        .collect()
}

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn textual_oracle() {
    let root = common::corpus_root();
    let rows = manifest_sources(&root);

    let mut total = 0usize;
    let mut exact = 0usize;
    let mut containment_sum = 0.0f64;
    let mut lcs_sum = 0.0f64;
    let mut divergence: std::collections::BTreeMap<String, usize> = Default::default();
    let mut worst: Vec<(f64, String)> = Vec::new();

    for (relative, source_rel) in &rows {
        if source_rel.is_empty() {
            continue;
        }
        let source = std::fs::read_to_string(root.join(source_rel)).expect("read source");
        if source_rel.ends_with(".ts") {
            continue; // the decompiler emits JS; TS sources are out of the oracle's scope
        }
        let data = std::fs::read(root.join(relative)).expect("read fixture");
        let file = abcd_file::decode(&data).expect("decode fixture");
        let module = abcd_lift::lift_file(&file).expect("lift fixture");
        total += 1;
        let d = decompile_module(&module, &EmitOptions::default());
        let want = tokenize(&source);
        let got = tokenize(&d.text);
        if want == got {
            exact += 1;
        }
        // Multiset containment of source tokens in the output.
        let mut pool: std::collections::BTreeMap<&Tok, usize> = Default::default();
        for t in &got {
            *pool.entry(t).or_insert(0) += 1;
        }
        let mut covered = 0usize;
        for t in &want {
            if let Some(n) = pool.get_mut(t)
                && *n > 0
            {
                *n -= 1;
                covered += 1;
            }
        }
        let containment = covered as f64 / want.len().max(1) as f64;
        containment_sum += containment;
        let lcs = lcs_len(&want, &got);
        let ratio = 2.0 * lcs as f64 / (want.len() + got.len()).max(1) as f64;
        lcs_sum += ratio;
        if ratio < 1.0 {
            worst.push((ratio, relative.clone()));
        }

        // First-divergence class.
        if want != got {
            let m = want.iter().zip(got.iter()).position(|(a, b)| a != b);
            let class = match m {
                None => "prefix (length differs only)".to_string(),
                Some(pos) => {
                    let absent = !got.contains(&want[pos]);
                    format!(
                        "{} vs {} ({})",
                        want[pos].kind(),
                        got[pos].kind(),
                        if absent {
                            "source token absent"
                        } else {
                            "repositioned"
                        }
                    )
                }
            };
            *divergence.entry(class).or_insert(0) += 1;
        }
    }

    eprintln!("TEXTUAL-ORACLE fixtures_with_source={total}");
    eprintln!(
        "TEXTUAL-ORACLE exact_match={exact} ({:.1}%)",
        100.0 * exact as f64 / total.max(1) as f64
    );
    eprintln!(
        "TEXTUAL-ORACLE mean_token_containment={:.3} mean_lcs_ratio={:.3}",
        containment_sum / total.max(1) as f64,
        lcs_sum / total.max(1) as f64
    );
    eprintln!("TEXTUAL-ORACLE first-divergence classes:");
    for (class, n) in &divergence {
        eprintln!("TEXTUAL-DIVERGENCE {n:5}  {class}");
    }
    worst.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
    eprintln!("TEXTUAL-ORACLE lowest-similarity fixtures:");
    for (r, p) in worst.iter().take(10) {
        eprintln!("TEXTUAL-LOW {r:.3}  {p}");
    }
    assert!(total > 1200, "expected the corpus' JS-sourced fixtures");
}
