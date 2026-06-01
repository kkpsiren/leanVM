//! Soak driver for the compiler fuzzer.
//!
//! ```text
//! cargo run --release -p compiler_fuzzer -- [--seed S] [--iters N] [--out DIR] [--quiet] [--stop-on-critical]
//! ```
//!
//! Each iteration generates a program from a consecutive seed, compiles it, and runs every
//! oracle. Findings are printed (one line each) and, with `--out DIR`, written as replayable
//! `.py` + `.json` reproducers. Exit code is non-zero if any Critical/High finding appeared.

use std::path::PathBuf;
use std::process::ExitCode;

use compiler_fuzzer::campaign::{CampaignConfig, run_campaign};
use compiler_fuzzer::triage::Severity;

fn main() -> ExitCode {
    let mut cfg = CampaignConfig {
        verbose: true,
        ..Default::default()
    };

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--seed" => cfg.start_seed = args.next().and_then(|v| v.parse().ok()).unwrap_or(0),
            "--iters" => cfg.iterations = args.next().and_then(|v| v.parse().ok()).unwrap_or(1000),
            "--out" => cfg.out_dir = args.next().map(PathBuf::from),
            "--quiet" => cfg.verbose = false,
            "--stop-on-critical" => cfg.stop_on_critical = true,
            other => {
                eprintln!("unknown argument: {other}");
                return ExitCode::from(2);
            }
        }
    }

    println!(
        "fuzzing: seeds [{}, {}), out={:?}",
        cfg.start_seed,
        cfg.start_seed.wrapping_add(cfg.iterations),
        cfg.out_dir
    );

    let report = run_campaign(&cfg);

    let crit = report.criticals();
    let high = report.highs();
    let info = report.count(Severity::Info);
    println!(
        "\ndone: {} iterations, {crit} critical, {high} high, {info} info findings",
        report.iterations_run
    );

    if crit > 0 || high > 0 {
        println!("\nactionable findings:");
        for f in report.actionable() {
            println!("  {}", f.summary());
        }
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
