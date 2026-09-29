//! `abcd` binary entry point: parse, dispatch, map errors to exit codes.
//!
//! Exit codes (design/cli-plan.md §3.4): 0 ok, 1 user error (bad args,
//! unreadable input, ambiguous module selection), 2 tool error (decode
//! failure, write failure). Clap's own parse errors — which would exit 2
//! by default — are remapped to 1 to fit that contract.

use std::process::ExitCode;

use clap::Parser;

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
            print!("{e}");
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
