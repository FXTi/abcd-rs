//! `abcd` binary entry point: parse, dispatch, map errors to exit codes.
//!
//! Exit codes (design/cli.md §3): 0 ok, 1 user error (bad args,
//! unreadable input, ambiguous module selection), 2 tool error (decode
//! failure, write failure). Clap's own parse errors — which would exit 2
//! by default — are remapped to 1 to fit that contract.

#![forbid(unsafe_code)]
#![deny(clippy::unwrap_used)]

use std::process::ExitCode;

use clap::Parser;

// The final binary owns the global allocator (libraries never set one).
// mimalloc is used across all target platforms (Linux, macOS, Windows MSVC);
// see design/cli.md §4 and design/decisions.md (ADR-12).
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() -> ExitCode {
    let cli = match abcd_cli::cli::Cli::try_parse() {
        Ok(cli) => cli,
        Err(e) => {
            // --help/--version want stdout + 0; real parse errors want
            // stderr + 1 (not clap's default 2, which means "tool error"
            // in this binary's contract).
            if e.use_stderr() {
                eprint!("{e}");
                return ExitCode::from(1);
            }
            if let Err(io_err) = abcd_cli::write_stdout_fmt(format_args!("{e}")) {
                eprintln!("error: {io_err}");
                return ExitCode::from(io_err.exit_code());
            }
            return ExitCode::SUCCESS;
        }
    };
    match abcd_cli::run(cli) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(e.exit_code())
        }
    }
}
