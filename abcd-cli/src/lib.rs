//! abcd-cli — the `abcd` command-line binary (design/cli-plan.md §3).
//!
//! Subcommands: `extract` (container → .abc files), `info` (file summary,
//! `--verify`, `--json`), `dis` (.abc → pandasm .pa, byte-identical to
//! ark_disasm), `decompile` (.abc → .js). All bytecode-consuming
//! commands share the [`input`] layer: bare `.abc` and containers are
//! sniffed by magic bytes, and multi-module containers require an explicit
//! `--module` / `--all` choice.
//!
//! Output conventions (§3.4): results on stdout, diagnostics on stderr,
//! exit codes 0 ok / 1 user error / 2 tool error, no panics on data.

pub mod analyze;
pub mod asm;
pub mod cli;
pub mod decompile;
pub mod dis;
pub mod extract;
pub mod info;
pub mod input;
pub mod rewrite;
pub mod taint;
pub mod taint_config;

use std::path::PathBuf;

use cli::{
    AnalyzeArgs, AsmArgs, Command, DecompileArgs, DisArgs, ExtractArgs, InfoArgs, RewriteArgs,
    TaintArgs,
};
use decompile::DecompileOptions;
use input::ModuleSelection;

/// Error channel of the CLI: user errors exit 1, tool errors exit 2.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CliError {
    /// Bad arguments, unreadable input files, ambiguous module selection —
    /// things the user can fix. Exit code 1.
    User(String),
    /// Decode/lift/write failures — the tool could not complete. Exit 2.
    Tool(String),
}

impl CliError {
    /// Process exit code per design §3.4.
    pub fn exit_code(&self) -> u8 {
        match self {
            CliError::User(_) => 1,
            CliError::Tool(_) => 2,
        }
    }
}

impl std::fmt::Display for CliError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CliError::User(msg) | CliError::Tool(msg) => f.write_str(msg),
        }
    }
}

impl std::error::Error for CliError {}

/// Dispatch a parsed command line. Prints results to stdout; diagnostics
/// are the caller's job (see `main`).
pub fn run(cli: cli::Cli) -> Result<(), CliError> {
    match cli.command {
        Command::Extract(args) => run_extract(&args),
        Command::Info(args) => run_info(&args),
        Command::Dis(args) => run_dis(&args),
        Command::Asm(args) => {
            asm::run_asm(&args.input, args.output.as_ref(), args.version, args.check)
        }
        Command::Decompile(args) => run_decompile(&args),
        Command::Rewrite(args) => run_rewrite(&args),
        Command::Analyze(args) => run_analyze(&args),
        Command::Taint(args) => run_taint(&args),
    }
}

fn run_rewrite(args: &RewriteArgs) -> Result<(), CliError> {
    let opts = rewrite::RewriteOptions {
        optimize: args.opt,
        check: args.check,
    };
    let selection = selection_of(&args.select.module, args.select.all);
    let modules = input::load(&args.input, selection)?;

    if args.select.all {
        // Per-module artifacts: -o is the output directory and required.
        let out_dir = match &args.output {
            Some(dir) => dir.clone(),
            None => {
                return Err(CliError::User(
                    "--all requires -o <dir> (one <module>.abc per module)".to_string(),
                ));
            }
        };
        let written = rewrite::write_all(&modules, &out_dir, opts)?;
        for (name, path, size) in &written {
            println!("{name}: {size} bytes -> {}", path.display());
        }
        return Ok(());
    }

    let module = modules
        .first()
        .expect("input layer guarantees at least one module");
    let out = rewrite::rewrite(module, opts)?;
    match &args.output {
        Some(path) => {
            std::fs::write(path, &out.abc)
                .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())))?;
            println!(
                "{}: {} bytes -> {} ({} methods, {} lowered, instructions {} -> {}{})",
                module.name,
                out.abc.len(),
                path.display(),
                out.stats.methods,
                out.stats.lowered,
                out.stats.input_instructions,
                out.stats.output_instructions,
                if out.stats.optimized_changed {
                    ", optimized"
                } else {
                    ""
                },
            );
        }
        None => dis::print_raw(&out.abc)?,
    }
    Ok(())
}

fn run_analyze(args: &AnalyzeArgs) -> Result<(), CliError> {
    let opts = analyze::AnalyzeOptions {
        callgraph: args.callgraph,
        dominators: args.dominators,
    };
    let selection = selection_of(&args.select.module, args.select.all);
    let modules = input::load(&args.input, selection)?;
    let reports: Vec<analyze::AnalyzeReport> = modules
        .iter()
        .map(|m| analyze::report(m, opts))
        .collect::<Result<_, _>>()?;
    println!("{}", analyze::render(&reports, args.json)?);
    Ok(())
}

fn run_taint(args: &TaintArgs) -> Result<(), CliError> {
    let config = taint::load_config(&args.config)?;
    let selection = selection_of(&args.select.module, args.select.all);
    let modules = input::load(&args.input, selection)?;
    let reports: Vec<taint::TaintCliReport> = modules
        .iter()
        .map(|m| taint::report(m, &config))
        .collect::<Result<_, _>>()?;
    println!("{}", taint::render(&reports, args.json)?);
    Ok(())
}

fn run_dis(args: &DisArgs) -> Result<(), CliError> {
    let selection = selection_of(&args.select.module, args.select.all);
    let modules = input::load(&args.input, selection)?;

    if args.select.all {
        // Per-module artifacts: -o is the output directory and required.
        let out_dir = match &args.output {
            Some(dir) => dir.clone(),
            None => {
                return Err(CliError::User(
                    "--all requires -o <dir> (one <module>.pa per module)".to_string(),
                ));
            }
        };
        let written = dis::write_all(&modules, &out_dir)?;
        for (name, path, size) in &written {
            println!("{name}: {size} bytes -> {}", path.display());
        }
        return Ok(());
    }

    let module = modules
        .first()
        .expect("input layer guarantees at least one module");
    let pa = dis::disassemble(module)?;
    match &args.output {
        Some(path) => {
            std::fs::write(path, &pa)
                .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())))?;
            println!("{}: {} bytes -> {}", module.name, pa.len(), path.display());
        }
        None => dis::print_raw(&pa)?,
    }
    Ok(())
}

fn run_extract(args: &ExtractArgs) -> Result<(), CliError> {
    let out_dir = args.out_dir.clone().unwrap_or_else(|| PathBuf::from("."));
    let modules = extract::extract_path(&args.container, &out_dir, args.force)?;
    print!(
        "{}",
        extract::render_summary(&args.container.display().to_string(), &out_dir, &modules)
    );
    Ok(())
}

fn run_info(args: &InfoArgs) -> Result<(), CliError> {
    let selection = selection_of(&args.select.module, args.select.all);
    let modules = input::load(&args.input, selection)?;
    let reports: Vec<info::InfoReport> = modules
        .iter()
        .map(|m| info::report(m, args.verify))
        .collect::<Result<_, _>>()?;
    println!("{}", info::render(&reports, args.json)?);
    Ok(())
}

fn run_decompile(args: &DecompileArgs) -> Result<(), CliError> {
    let opts = DecompileOptions {
        ts: args.ts,
        line_anchors: args.line_anchors,
        call_entry: args.call_entry,
    };
    let selection = selection_of(&args.select.module, args.select.all);
    let modules = input::load(&args.input, selection)?;

    if args.select.all {
        // Per-module artifacts: -o is the output directory and required.
        let out_dir = match &args.output {
            Some(dir) => dir.clone(),
            None => {
                return Err(CliError::User(
                    "--all requires -o <dir> (one <module>.js per module)".to_string(),
                ));
            }
        };
        let written = decompile::write_all(&modules, &out_dir, opts)?;
        for (name, path, size) in &written {
            println!("{name}: {size} bytes -> {}", path.display());
        }
        return Ok(());
    }

    let module = modules
        .first()
        .expect("input layer guarantees at least one module");
    let js = decompile::decompile(module, opts)?.text;
    match &args.output {
        Some(path) => {
            std::fs::write(path, &js)
                .map_err(|e| CliError::Tool(format!("cannot write {}: {e}", path.display())))?;
            println!("{}: {} bytes -> {}", module.name, js.len(), path.display());
        }
        None => print!("{js}"),
    }
    Ok(())
}

fn selection_of(module: &Option<String>, all: bool) -> ModuleSelection<'_> {
    if all {
        ModuleSelection::All
    } else if let Some(name) = module {
        ModuleSelection::Named(name)
    } else {
        ModuleSelection::Single
    }
}
