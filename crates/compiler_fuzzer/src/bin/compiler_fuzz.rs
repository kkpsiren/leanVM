//! Soak driver for the compiler fuzzer.
//!
//! ```text
//! cargo run --release -p compiler_fuzzer -- [--seed S] [--iters N] [--out DIR] [--quiet] [--stop-on-critical]
//! ```
//!
//! Each iteration generates a program from a consecutive seed, compiles it, and runs every
//! oracle. Findings are printed (one line each) and, with `--out DIR`, written as replayable
//! `.py` + `.json` reproducers. Exit code is non-zero if any Critical/High finding appeared.

use std::io::Read;
use std::path::PathBuf;
use std::process::ExitCode;

use compiler_fuzzer::campaign::{CampaignConfig, run_campaign};
use compiler_fuzzer::subprocess::REJECTED_EXIT;
use compiler_fuzzer::triage::Severity;

fn main() -> ExitCode {
    // Child mode used by the subprocess crash-probe runner: read a program from stdin, compile
    // it, exit 0 (compiled) / REJECTED_EXIT (clean error). Panics are intentionally *not*
    // caught here so the parent observes them as a non-zero exit / signal.
    if std::env::args().any(|a| a == "--compile-stdin") {
        return compile_stdin_child();
    }

    let mut cfg = CampaignConfig {
        verbose: true,
        ..Default::default()
    };

    let mut run_probes = false;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--seed" => cfg.start_seed = args.next().and_then(|v| v.parse().ok()).unwrap_or(0),
            "--iters" => cfg.iterations = args.next().and_then(|v| v.parse().ok()).unwrap_or(1000),
            "--out" => cfg.out_dir = args.next().map(PathBuf::from),
            "--quiet" => cfg.verbose = false,
            "--stop-on-critical" => cfg.stop_on_critical = true,
            "--probes" => run_probes = true,
            other => {
                eprintln!("unknown argument: {other}");
                return ExitCode::from(2);
            }
        }
    }

    if run_probes {
        let bin = std::env::current_exe().expect("current exe path");
        let findings = compiler_fuzzer::probes::run_probes(&bin);
        println!(
            "probes: {} / {} crashed the compiler (panic/hang/crash)",
            findings.len(),
            compiler_fuzzer::probes::PROBES.len()
        );
        for f in &findings {
            println!("  {}", f.summary());
        }
        return if findings.is_empty() {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        };
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

/// Child entry point for `--compile-stdin`: compile a program read from stdin. Exit `0` on
/// success, [`REJECTED_EXIT`] on a clean compile error. Panics propagate (no `catch_unwind`).
fn compile_stdin_child() -> ExitCode {
    let mut source = String::new();
    if std::io::stdin().read_to_string(&mut source).is_err() {
        return ExitCode::from(4);
    }
    match lean_compiler::try_compile_program(&lean_compiler::ProgramSource::Raw(source)) {
        Ok(_) => ExitCode::SUCCESS,
        Err(_) => ExitCode::from(REJECTED_EXIT as u8),
    }
}
