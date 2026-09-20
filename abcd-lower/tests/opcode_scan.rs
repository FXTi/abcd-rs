//! TEMPORARY corpus opcode scan (diagnostic for the P2 port): histograms
//! the bytecode variants whose v0.2 normalization is lossy, over the full
//! corpus, cross-referenced with the manifest runtime status. Deleted
//! before the final push.

use std::collections::BTreeMap;
use std::path::PathBuf;

use abcd_isa::Bytecode;

#[test]
#[ignore = "diagnostic scan"]
fn scan_ambiguous_call_opcodes() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("exports")
        .join("corpus");

    // runtime status per manifest-relative abc path.
    let output = std::process::Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, sys
with open(sys.argv[1], encoding="utf-8") as m:
    for line in m:
        row = json.loads(line)
        print(row["abc"], row["runtime"]["status"])
"#,
        )
        .arg(root.join("index.jsonl"))
        .output()
        .expect("python3");
    let mut status: BTreeMap<String, String> = BTreeMap::new();
    for line in String::from_utf8(output.stdout).unwrap().lines() {
        let (p, s) = line.rsplit_once(' ').unwrap();
        status.insert(p.to_string(), s.to_string());
    }

    let mut files: Vec<PathBuf> = Vec::new();
    let mut stack = vec![root.clone()];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "abc") {
                files.push(path);
            }
        }
    }
    files.sort();

    let mut hist: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut hist_passed: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut files_passed: BTreeMap<&'static str, Vec<String>> = BTreeMap::new();
    for path in &files {
        let rel = path.strip_prefix(&root).unwrap().display().to_string();
        let data = std::fs::read(path).unwrap();
        let file = match abcd_file::decode(&data) {
            Ok(f) => f,
            Err(_) => continue,
        };
        for (_, method) in file.all_methods() {
            let Some(body) = &method.body else { continue };
            for bc in &body.bytecodes {
                use Bytecode as B;
                let tag: &'static str = match bc {
                    B::Apply(..) => "apply",
                    B::Supercallspread(..) => "supercallspread",
                    B::Newobjapply(..) => "newobjapply",
                    B::Supercallthisrange(..) | B::WideSupercallthisrange(..) => {
                        "supercallthisrange"
                    }
                    B::Supercallarrowrange(..) | B::WideSupercallarrowrange(..) => {
                        "supercallarrowrange"
                    }
                    B::DeprecatedCallspread(..) => "deprecated.callspread",
                    B::Ldthis => "ldthis",
                    B::Stownbyname(..) | B::Stownbynamewithnameset(..) => "stownbyname",
                    B::Stownbyvalue(..) | B::Stownbyvaluewithnameset(..) => "stownbyvalue",
                    B::Stownbyindex(..) | B::WideStownbyindex(..) => "stownbyindex",
                    B::Definefieldbyname(..) | B::Definepropertybyname(..) => "definefield/propbyname",
                    B::CallruntimeDefinefieldbyvalue(..) => "callrt.definefieldbyvalue",
                    B::CallruntimeDefinefieldbyindex(..) => "callrt.definefieldbyindex",
                    B::Trystglobalbyname(..) => "trystglobalbyname",
                    B::Ldexternalmodulevar(..) | B::WideLdexternalmodulevar(..) => {
                        "ldexternalmodulevar"
                    }
                    B::Createasyncgeneratorobj(..) => "createasyncgeneratorobj",
                    B::CallruntimeDefinesendableclass(..) => "callrt.definesendableclass",
                    B::CallruntimeLdsendableclass(..) => "callrt.ldsendableclass",
                    B::CallruntimeLdsendableexternalmodulevar(..)
                    | B::CallruntimeWideldsendableexternalmodulevar(..) => {
                        "callrt.ldsendableexternalmodulevar"
                    }
                    B::CallruntimeLdsendablelocalmodulevar(..)
                    | B::CallruntimeWideldsendablelocalmodulevar(..) => {
                        "callrt.ldsendablelocalmodulevar"
                    }
                    B::CallruntimeLdlazymodulevar(..) | B::CallruntimeWideldlazymodulevar(..) => {
                        "callrt.ldlazymodulevar"
                    }
                    B::CallruntimeLdlazysendablemodulevar(..)
                    | B::CallruntimeWideldlazysendablemodulevar(..) => {
                        "callrt.ldlazysendablemodulevar"
                    }
                    B::CallruntimeNewsendableenv(..) | B::CallruntimeWidenewsendableenv(..) => {
                        "callrt.newsendableenv"
                    }
                    B::CallruntimeStsendablevar(..) | B::CallruntimeWidestsendablevar(..) => {
                        "callrt.stsendablevar"
                    }
                    B::CallruntimeLdsendablevar(..) | B::CallruntimeWideldsendablevar(..) => {
                        "callrt.ldsendablevar"
                    }
                    B::CallruntimeSupercallforwardallargs(..) => "callrt.supercallforwardallargs",
                    B::Callthis0withname(..)
                    | B::Callthis1withname(..)
                    | B::Callthis2withname(..)
                    | B::Callthis3withname(..)
                    | B::Callthisrangewithname(..)
                    | B::WideCallthisrangewithname(..) => "callthis*withname",
                    B::Getasynciterator(..) => "getasynciterator",
                    B::Sttoglobalrecord(..) | B::Stconsttoglobalrecord(..) => "sttoglobalrecord",
                    _ => continue,
                };
                *hist.entry(tag).or_default() += 1;
                if status.get(&rel).is_some_and(|s| s == "passed") {
                    *hist_passed.entry(tag).or_default() += 1;
                    let list = files_passed.entry(tag).or_default();
                    if list.last() != Some(&rel) {
                        list.push(rel.clone());
                    }
                }
            }
        }
    }
    eprintln!("{:<36} {:>8} {:>8}", "opcode", "all", "passed");
    for (tag, n) in &hist {
        let p = hist_passed.get(tag).copied().unwrap_or(0);
        eprintln!("{tag:<36} {n:>8} {p:>8}");
        for f in files_passed.get(tag).into_iter().flatten().take(4) {
            eprintln!("    {f}");
        }
    }
}
