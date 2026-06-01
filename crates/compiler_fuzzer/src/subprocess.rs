//! Out-of-process compilation, for crash modes that `catch_unwind` cannot catch.
//!
//! In-process [`crate::harness::compile_source`] catches Rust *unwinds*, but a handwritten
//! compiler can also die in ways that take the whole process down: an `abort`, a stack
//! overflow (SIGSEGV), an out-of-memory kill, or simply *hanging* (e.g. trying to unroll a
//! loop `10^11` times). To probe those safely, we run the compiler in a child process with a
//! wall-clock timeout and an address-space rlimit, and classify how it died.
//!
//! The child is this same binary invoked with `--compile-stdin`; it reads a program from stdin,
//! compiles it, and exits `0` (compiled) / [`REJECTED_EXIT`] (clean error). A panic exits with
//! the Rust default (`101`); a fatal signal is reported by the OS.

use std::io::{Read, Write};
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// Exit code the `--compile-stdin` child uses for a clean `CompileError`.
pub const REJECTED_EXIT: i32 = 3;

/// How an out-of-process compilation ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubprocessOutcome {
    /// Compiled to bytecode.
    Compiled,
    /// Rejected with a clean `CompileError`.
    Rejected,
    /// The compiler unwound (exit 101). Carries captured stderr.
    Panicked(String),
    /// Exceeded the wall-clock timeout (hang / pathological blowup).
    Timeout,
    /// Killed by a fatal signal (abort, SIGSEGV stack overflow, OOM kill, …).
    Crashed { signal: i32, stderr: String },
    /// Exited with an unexpected non-zero code. Carries the code + stderr.
    UnexpectedExit { code: i32, stderr: String },
}

impl SubprocessOutcome {
    /// Whether this outcome is a compiler bug (anything other than a clean compile/reject).
    #[must_use]
    pub fn is_crash(&self) -> bool {
        !matches!(self, Self::Compiled | Self::Rejected)
    }
}

/// Compile `source` in a child process bounded by `timeout` and `mem_limit_bytes` of address
/// space. `bin` is the path to this crate's binary (`env!("CARGO_BIN_EXE_compiler_fuzz")` in
/// tests, or `std::env::current_exe()` at runtime).
pub fn compile_in_subprocess(
    bin: &Path,
    source: &str,
    timeout: Duration,
    mem_limit_bytes: u64,
) -> std::io::Result<SubprocessOutcome> {
    let mut cmd = Command::new(bin);
    cmd.arg("--compile-stdin")
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::piped());

    // Bound address space so an OOM blowup kills only the child, not the machine.
    // SAFETY: `setrlimit` is async-signal-safe and touches no Rust heap state.
    unsafe {
        cmd.pre_exec(move || {
            let lim = libc::rlimit {
                rlim_cur: mem_limit_bytes,
                rlim_max: mem_limit_bytes,
            };
            libc::setrlimit(libc::RLIMIT_AS, &lim);
            Ok(())
        });
    }

    let mut child = cmd.spawn()?;
    if let Some(mut stdin) = child.stdin.take() {
        // Best-effort: the child may exit before reading all input.
        let _ = stdin.write_all(source.as_bytes());
    }

    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait()? {
            break status;
        }
        if start.elapsed() > timeout {
            let _ = child.kill();
            let _ = child.wait();
            return Ok(SubprocessOutcome::Timeout);
        }
        std::thread::sleep(Duration::from_millis(5));
    };

    let mut stderr = String::new();
    if let Some(mut e) = child.stderr.take() {
        let _ = e.read_to_string(&mut stderr);
    }

    Ok(match (status.code(), status.signal()) {
        (Some(0), _) => SubprocessOutcome::Compiled,
        (Some(REJECTED_EXIT), _) => SubprocessOutcome::Rejected,
        (Some(101), _) => SubprocessOutcome::Panicked(last_panic_line(&stderr)),
        (Some(code), _) => SubprocessOutcome::UnexpectedExit { code, stderr },
        (None, Some(signal)) => SubprocessOutcome::Crashed { signal, stderr },
        (None, None) => SubprocessOutcome::UnexpectedExit { code: -1, stderr },
    })
}

/// Extract the most informative line from captured panic stderr.
fn last_panic_line(stderr: &str) -> String {
    stderr
        .lines()
        .find(|l| l.contains("panicked at") || l.contains("panic"))
        .or_else(|| stderr.lines().next_back())
        .unwrap_or("")
        .trim()
        .to_string()
}
