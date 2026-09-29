//! Command-line definition (clap derive) for the `abcd` binary.
//!
//! Kept separate from `main` so argument-parsing unit tests can drive
//! [`Cli::try_parse_from`] without spawning a process.

use std::path::PathBuf;

use clap::{Args, Parser, Subcommand};

/// ArkCompiler .abc toolkit.
#[derive(Debug, Parser)]
#[command(
    name = "abcd",
    version,
    about = "ArkCompiler .abc toolkit: extract / info / decompile",
    long_about = "ArkCompiler .abc toolkit.\n\nEvery command that takes bytecode accepts both a bare .abc file and a\ncontainer (.hap/.hsp/.app/.hqf); the input kind is sniffed by magic bytes.\nMulti-module containers require --module <name> or --all."
)]
pub struct Cli {
    /// The subcommand to run.
    #[command(subcommand)]
    pub command: Command,
}

/// Top-level subcommands.
#[derive(Debug, Subcommand)]
pub enum Command {
    /// Extract .abc bytecode (and module.json) from a container.
    Extract(ExtractArgs),
    /// Print a summary of an .abc file or bytecode-carrying container.
    Info(InfoArgs),
    /// Disassemble to pandasm .pa text (byte-identical to ark_disasm).
    Dis(DisArgs),
    /// Assemble pandasm .pa text into .abc (round-trip direction of dis).
    Asm(AsmArgs),
    /// Decompile bytecode to JavaScript.
    Decompile(DecompileArgs),
    /// Rewrite bytecode through the lift→[opt]→lower pipeline.
    Rewrite(RewriteArgs),
    /// Static analysis report (call graph, dominators).
    Analyze(AnalyzeArgs),
    /// Taint analysis driven by a TOML config file.
    Taint(TaintArgs),
}

/// Module-selection flags shared by commands that consume bytecode.
#[derive(Debug, Default, Args)]
pub struct SelectArgs {
    /// Select a single module of a multi-module container by name.
    #[arg(long, value_name = "NAME", conflicts_with = "all")]
    pub module: Option<String>,
    /// Select every module of a multi-module container.
    #[arg(long)]
    pub all: bool,
}

/// `abcd extract <container> [-o DIR]`.
#[derive(Debug, Args)]
pub struct ExtractArgs {
    /// Container file (.hap/.hsp/.app/.hqf) to extract bytecode from.
    pub container: PathBuf,
    /// Output directory (created if missing). Defaults to the current
    /// directory. Existing files are never overwritten without --force.
    #[arg(short = 'o', long = "out-dir", value_name = "DIR")]
    pub out_dir: Option<PathBuf>,
    /// Overwrite existing output files.
    #[arg(long)]
    pub force: bool,
}

/// `abcd info [--verify] [--json] <input>`.
#[derive(Debug, Args)]
pub struct InfoArgs {
    /// Input file: bare .abc or a container (.hap/.hsp/.app/.hqf).
    pub input: PathBuf,
    /// Fully decode the file and verify every method's bytecode stream;
    /// the exit code carries the verdict (0 pass, 2 fail).
    #[arg(long)]
    pub verify: bool,
    /// Emit a machine-readable JSON report instead of text.
    #[arg(long)]
    pub json: bool,
    /// Module selection for multi-module containers.
    #[command(flatten)]
    pub select: SelectArgs,
}

/// `abcd dis <input> [-o out.pa]`.
#[derive(Debug, Args)]
pub struct DisArgs {
    /// Input file: bare .abc or a container (.hap/.hsp/.app/.hqf).
    pub input: PathBuf,
    /// Output path. With a single module this is the .pa file (stdout if
    /// omitted); with --all this is a directory receiving
    /// <module-name>.pa per module and is required.
    #[arg(short = 'o', long = "output", value_name = "PATH")]
    pub output: Option<PathBuf>,
    /// Module selection for multi-module containers.
    #[command(flatten)]
    pub select: SelectArgs,
}

/// `abcd asm <input.pa> [-o out.abc] [--version M.m.p.b] [--check]`.
#[derive(Debug, Args)]
pub struct AsmArgs {
    /// Pandasm text file to assemble.
    pub input: PathBuf,
    /// Output .abc path (stdout if omitted).
    #[arg(short = 'o', long = "output", value_name = "PATH")]
    pub output: Option<PathBuf>,
    /// .abc format version to write (a .pa carries no version; defaults to
    /// the current version, matching upstream ark_asm).
    #[arg(long, value_name = "M.m.p.b", value_parser = parse_version)]
    pub version: Option<abcd_file::Version>,
    /// Re-decode the emitted bytes before they leave the process
    /// (writer self-check; a failure is a tool error and nothing is
    /// written).
    #[arg(long)]
    pub check: bool,
}

/// Parse a `major.minor.patch.build` version string.
fn parse_version(s: &str) -> Result<abcd_file::Version, String> {
    let parts: Vec<&str> = s.split('.').collect();
    if parts.len() != 4 {
        return Err(format!("expected four dot-separated numbers, got {s:?}"));
    }
    let mut bytes = [0u8; 4];
    for (slot, part) in bytes.iter_mut().zip(parts) {
        *slot = part
            .parse::<u8>()
            .map_err(|_| format!("{part:?} is not a number in 0..=255"))?;
    }
    Ok(abcd_file::Version::new(
        bytes[0], bytes[1], bytes[2], bytes[3],
    ))
}

/// `abcd rewrite <input> [-o out.abc] [--opt] [--check]`.
#[derive(Debug, Args)]
pub struct RewriteArgs {
    /// Input file: bare .abc or a container (.hap/.hsp/.app/.hqf).
    pub input: PathBuf,
    /// Output path. With a single module this is the .abc file (stdout if
    /// omitted); with --all this is a directory receiving
    /// <module-name>.abc per module and is required.
    #[arg(short = 'o', long = "output", value_name = "PATH")]
    pub output: Option<PathBuf>,
    /// Run the abcd-opt optimization pipeline between lift and lower.
    #[arg(long)]
    pub opt: bool,
    /// Re-decode the emitted bytes before they leave the process
    /// (writer self-check; a failure is a tool error and nothing is
    /// written).
    #[arg(long)]
    pub check: bool,
    /// Module selection for multi-module containers.
    #[command(flatten)]
    pub select: SelectArgs,
}

/// `abcd analyze <input> [--callgraph] [--dominators] [--json]`.
#[derive(Debug, Args)]
pub struct AnalyzeArgs {
    /// Input file: bare .abc or a container (.hap/.hsp/.app/.hqf).
    pub input: PathBuf,
    /// Include the per-function call-site listing with resolved targets.
    #[arg(long)]
    pub callgraph: bool,
    /// Include the per-function immediate-dominator tree.
    #[arg(long)]
    pub dominators: bool,
    /// Emit a machine-readable JSON report instead of text.
    #[arg(long)]
    pub json: bool,
    /// Module selection for multi-module containers.
    #[command(flatten)]
    pub select: SelectArgs,
}

/// `abcd taint <input> --config <PATH> [--json]`.
#[derive(Debug, Args)]
pub struct TaintArgs {
    /// Input file: bare .abc or a container (.hap/.hsp/.app/.hqf).
    pub input: PathBuf,
    /// TOML taint configuration (sources, sinks, summaries).
    #[arg(long, value_name = "PATH")]
    pub config: PathBuf,
    /// Emit a machine-readable JSON report instead of text.
    #[arg(long)]
    pub json: bool,
    /// Module selection for multi-module containers.
    #[command(flatten)]
    pub select: SelectArgs,
}

/// `abcd decompile <input> [-o out.js] [--ts] [--line-anchors]`.
#[derive(Debug, Args)]
pub struct DecompileArgs {
    /// Input file: bare .abc or a container (.hap/.hsp/.app/.hqf).
    pub input: PathBuf,
    /// Output path. With a single module this is the .js file (stdout if
    /// omitted); with --all this is a directory receiving
    /// <module-name>.js per module and is required.
    #[arg(short = 'o', long = "output", value_name = "PATH")]
    pub output: Option<PathBuf>,
    /// Emit TypeScript annotations where the file format carries signature
    /// metadata (≤11-format files only; bare parameter lists elsewhere).
    #[arg(long)]
    pub ts: bool,
    /// Print `// line N` anchors before statements with a source location.
    #[arg(long = "line-anchors")]
    pub line_anchors: bool,
    /// Append a `func_main_0.call(this);` entry-point invocation after the
    /// top-level functions (off by default: human-facing output stays clean).
    #[arg(long = "call-entry")]
    pub call_entry: bool,
    /// Module selection for multi-module containers.
    #[command(flatten)]
    pub select: SelectArgs,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(argv: &[&str]) -> Result<Cli, clap::Error> {
        Cli::try_parse_from(argv)
    }

    // ---- extract ----

    #[test]
    fn extract_minimal() {
        let cli = parse(&["abcd", "extract", "app.hap"]).unwrap();
        let Command::Extract(a) = cli.command else {
            panic!("expected extract");
        };
        assert_eq!(a.container, PathBuf::from("app.hap"));
        assert_eq!(a.out_dir, None);
        assert!(!a.force);
    }

    #[test]
    fn extract_out_dir_and_force() {
        let cli = parse(&["abcd", "extract", "a.app", "-o", "out", "--force"]).unwrap();
        let Command::Extract(a) = cli.command else {
            panic!("expected extract");
        };
        assert_eq!(a.out_dir, Some(PathBuf::from("out")));
        assert!(a.force);
    }

    #[test]
    fn extract_missing_container_is_error() {
        assert!(parse(&["abcd", "extract"]).is_err());
    }

    #[test]
    fn extract_rejects_module_flag() {
        // Module selection belongs to bytecode-consuming commands; extract
        // always writes every module.
        assert!(parse(&["abcd", "extract", "a.app", "--module", "entry"]).is_err());
        assert!(parse(&["abcd", "extract", "a.app", "--all"]).is_err());
    }

    // ---- info ----

    #[test]
    fn info_minimal() {
        let cli = parse(&["abcd", "info", "modules.abc"]).unwrap();
        let Command::Info(a) = cli.command else {
            panic!("expected info");
        };
        assert_eq!(a.input, PathBuf::from("modules.abc"));
        assert!(!a.verify);
        assert!(!a.json);
        assert_eq!(a.select.module, None);
        assert!(!a.select.all);
    }

    #[test]
    fn info_all_flags() {
        let cli = parse(&["abcd", "info", "--verify", "--json", "x.abc"]).unwrap();
        let Command::Info(a) = cli.command else {
            panic!("expected info");
        };
        assert!(a.verify && a.json);
    }

    #[test]
    fn info_module_selection() {
        let cli = parse(&["abcd", "info", "a.app", "--module", "entry"]).unwrap();
        let Command::Info(a) = cli.command else {
            panic!("expected info");
        };
        assert_eq!(a.select.module.as_deref(), Some("entry"));
    }

    #[test]
    fn info_module_and_all_conflict() {
        assert!(parse(&["abcd", "info", "a.app", "--module", "entry", "--all"]).is_err());
    }

    #[test]
    fn info_missing_input_is_error() {
        assert!(parse(&["abcd", "info"]).is_err());
    }

    // ---- decompile ----

    #[test]
    fn decompile_minimal() {
        let cli = parse(&["abcd", "decompile", "modules.abc"]).unwrap();
        let Command::Decompile(a) = cli.command else {
            panic!("expected decompile");
        };
        assert_eq!(a.input, PathBuf::from("modules.abc"));
        assert_eq!(a.output, None);
        assert!(!a.ts && !a.line_anchors && !a.call_entry);
    }

    #[test]
    fn decompile_all_emit_flags() {
        let cli = parse(&[
            "abcd",
            "decompile",
            "m.abc",
            "-o",
            "out.js",
            "--ts",
            "--line-anchors",
            "--call-entry",
        ])
        .unwrap();
        let Command::Decompile(a) = cli.command else {
            panic!("expected decompile");
        };
        assert_eq!(a.output, Some(PathBuf::from("out.js")));
        assert!(a.ts && a.line_anchors && a.call_entry);
    }

    #[test]
    fn decompile_module_selection() {
        let cli = parse(&["abcd", "decompile", "a.app", "--all", "-o", "outdir"]).unwrap();
        let Command::Decompile(a) = cli.command else {
            panic!("expected decompile");
        };
        assert!(a.select.all);
        assert_eq!(a.output, Some(PathBuf::from("outdir")));
    }

    #[test]
    fn decompile_module_and_all_conflict() {
        assert!(parse(&["abcd", "decompile", "a.app", "--module", "entry", "--all"]).is_err());
    }

    #[test]
    fn decompile_missing_input_is_error() {
        assert!(parse(&["abcd", "decompile", "--ts"]).is_err());
    }

    // ---- top level ----

    #[test]
    fn no_subcommand_is_error() {
        assert!(parse(&["abcd"]).is_err());
    }

    #[test]
    fn unknown_subcommand_is_error() {
        assert!(parse(&["abcd", "frobnicate", "x.abc"]).is_err());
    }

    // ---- dis ----

    #[test]
    fn dis_minimal() {
        let cli = parse(&["abcd", "dis", "modules.abc"]).unwrap();
        let Command::Dis(a) = cli.command else {
            panic!("expected dis");
        };
        assert_eq!(a.input, PathBuf::from("modules.abc"));
        assert_eq!(a.output, None);
        assert_eq!(a.select.module, None);
        assert!(!a.select.all);
    }

    #[test]
    fn dis_all_with_out_dir() {
        let cli = parse(&["abcd", "dis", "a.app", "--all", "-o", "outdir"]).unwrap();
        let Command::Dis(a) = cli.command else {
            panic!("expected dis");
        };
        assert!(a.select.all);
        assert_eq!(a.output, Some(PathBuf::from("outdir")));
    }

    // ---- rewrite ----

    #[test]
    fn rewrite_minimal() {
        let cli = parse(&["abcd", "rewrite", "m.abc"]).unwrap();
        let Command::Rewrite(a) = cli.command else {
            panic!("expected rewrite");
        };
        assert_eq!(a.input, PathBuf::from("m.abc"));
        assert!(!a.opt && !a.check);
        assert_eq!(a.output, None);
    }

    #[test]
    fn rewrite_all_flags() {
        let cli = parse(&[
            "abcd", "rewrite", "m.abc", "--opt", "--check", "-o", "out.abc",
        ])
        .unwrap();
        let Command::Rewrite(a) = cli.command else {
            panic!("expected rewrite");
        };
        assert!(a.opt && a.check);
        assert_eq!(a.output, Some(PathBuf::from("out.abc")));
    }

    // ---- analyze ----

    #[test]
    fn analyze_minimal() {
        let cli = parse(&["abcd", "analyze", "m.abc"]).unwrap();
        let Command::Analyze(a) = cli.command else {
            panic!("expected analyze");
        };
        assert!(!a.callgraph && !a.dominators && !a.json);
    }

    #[test]
    fn analyze_all_flags() {
        let cli = parse(&[
            "abcd",
            "analyze",
            "m.abc",
            "--callgraph",
            "--dominators",
            "--json",
        ])
        .unwrap();
        let Command::Analyze(a) = cli.command else {
            panic!("expected analyze");
        };
        assert!(a.callgraph && a.dominators && a.json);
    }

    // ---- taint ----

    #[test]
    fn taint_requires_config() {
        assert!(parse(&["abcd", "taint", "m.abc"]).is_err());
        let cli = parse(&["abcd", "taint", "m.abc", "--config", "t.toml", "--json"]).unwrap();
        let Command::Taint(a) = cli.command else {
            panic!("expected taint");
        };
        assert_eq!(a.config, PathBuf::from("t.toml"));
        assert!(a.json);
    }

    // ---- asm ----

    #[test]
    fn asm_minimal() {
        let cli = parse(&["abcd", "asm", "input.pa"]).unwrap();
        let Command::Asm(a) = cli.command else {
            panic!("expected asm");
        };
        assert_eq!(a.input, PathBuf::from("input.pa"));
        assert_eq!(a.output, None);
        assert_eq!(a.version, None);
        assert!(!a.check);
    }

    #[test]
    fn asm_version_and_check() {
        let cli = parse(&[
            "abcd",
            "asm",
            "x.pa",
            "--version",
            "12.0.6.0",
            "--check",
            "-o",
            "x.abc",
        ])
        .unwrap();
        let Command::Asm(a) = cli.command else {
            panic!("expected asm");
        };
        assert_eq!(a.version, Some(abcd_file::Version::new(12, 0, 6, 0)));
        assert!(a.check);
        assert_eq!(a.output, Some(PathBuf::from("x.abc")));
    }

    #[test]
    fn asm_bad_version_is_error() {
        assert!(parse(&["abcd", "asm", "x.pa", "--version", "12.0"]).is_err());
        assert!(parse(&["abcd", "asm", "x.pa", "--version", "a.b.c.d"]).is_err());
        assert!(parse(&["abcd", "asm", "x.pa", "--version", "1.2.3.256"]).is_err());
    }
}
