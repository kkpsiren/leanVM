//! The thin layer that drives the real compiler and VM while:
//!
//! - catching (and *capturing the message of*) any panic the compiler raises — a panic is a
//!   finding, not a crash of the fuzzer;
//! - suppressing the runner's per-error stack-trace spam (it `eprintln!`s a full trace on
//!   every failure, and the fuzzer deliberately triggers thousands of failures);
//! - reducing the VM's rich result to the observations the oracles need.

mod classify;

pub use classify::{CheckKind, FailureClass};

use std::cell::RefCell;
use std::panic::AssertUnwindSafe;
use std::sync::Once;

use lean_compiler::{CompileError, ProgramSource, try_compile_program};
use lean_vm::{Bytecode, ExecutionResult, ExecutionWitness, F, PUBLIC_INPUT_LEN, RunnerError, try_execute_bytecode};

/// What a panic looked like (message + source location), captured by our panic hook.
#[derive(Debug, Clone)]
pub struct PanicInfo {
    pub message: String,
    pub location: Option<String>,
}

/// Result of asking the compiler to turn source into bytecode.
#[derive(Debug)]
pub enum CompileOutcome {
    /// Compiled successfully.
    Ok(Box<Bytecode>),
    /// Rejected cleanly with a `CompileError` (the desired behaviour for bad input).
    Rejected(String),
    /// The compiler panicked — a bug.
    Panicked(PanicInfo),
}

/// Result of executing bytecode against a public input + witness.
#[derive(Debug)]
pub enum RunOutcome {
    /// Ran to completion. Carries the full result for differential inspection.
    Ok(Box<ExecutionResult>),
    /// Halted with a clean runtime error (the desired behaviour for a violated check).
    Error(RunnerError),
    /// The VM itself panicked — out of scope for this crate's primary goal, but recorded.
    Panicked(PanicInfo),
}

impl CompileOutcome {
    #[must_use]
    pub const fn bytecode(&self) -> Option<&Bytecode> {
        match self {
            Self::Ok(b) => Some(b),
            _ => None,
        }
    }
}

thread_local! {
    static LAST_PANIC: RefCell<Option<PanicInfo>> = const { RefCell::new(None) };
}

static HOOK_INIT: Once = Once::new();

/// Install (once) a panic hook that records the message/location into a thread-local and
/// suppresses the default stderr backtrace print. Idempotent and cheap.
fn install_panic_hook() {
    HOOK_INIT.call_once(|| {
        std::panic::set_hook(Box::new(|info| {
            let location = info
                .location()
                .map(|l| format!("{}:{}:{}", l.file(), l.line(), l.column()));
            // `PanicHookInfo`'s Display includes the payload message; good enough and robust.
            let message = info.to_string();
            LAST_PANIC.with(|c| {
                *c.borrow_mut() = Some(PanicInfo { message, location });
            });
        }));
    });
}

/// Run `f`, returning `Err(PanicInfo)` if it unwinds.
fn catch<T>(f: impl FnOnce() -> T) -> Result<T, PanicInfo> {
    install_panic_hook();
    LAST_PANIC.with(|c| *c.borrow_mut() = None);
    match std::panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(v) => Ok(v),
        Err(_) => Err(LAST_PANIC.with(|c| c.borrow_mut().take()).unwrap_or_else(|| PanicInfo {
            message: "<panic with no captured message>".to_string(),
            location: None,
        })),
    }
}

/// Compile zkDSL source, catching panics.
#[must_use]
pub fn compile_source(source: &str) -> CompileOutcome {
    let src = ProgramSource::Raw(source.to_string());
    match catch(|| try_compile_program(&src)) {
        Ok(Ok(bytecode)) => CompileOutcome::Ok(Box::new(bytecode)),
        Ok(Err(err)) => CompileOutcome::Rejected(format_compile_error(&err)),
        Err(panic) => CompileOutcome::Panicked(panic),
    }
}

fn format_compile_error(err: &CompileError) -> String {
    err.to_string()
}

/// Execute `bytecode`, catching panics and gagging the runner's stderr trace.
#[must_use]
pub fn run(bytecode: &Bytecode, public_input: &[F; PUBLIC_INPUT_LEN], witness: &ExecutionWitness) -> RunOutcome {
    let _gag = StderrGag::new();
    match catch(|| try_execute_bytecode(bytecode, public_input, witness, false)) {
        Ok(Ok(result)) => RunOutcome::Ok(Box::new(result)),
        Ok(Err(err)) => RunOutcome::Error(err),
        Err(panic) => RunOutcome::Panicked(panic),
    }
}

/// RAII guard that redirects fd 2 (stderr) to `/dev/null` for its lifetime, then restores it.
///
/// The runner prints a full stack trace and the program's stdout to stderr on *every* error.
/// The fuzzer triggers errors by design (a violated check must be rejected), so without this
/// a campaign would emit thousands of traces. fd-level redirection catches the C-style
/// `eprintln!` writes that a Rust-level capture would miss.
///
/// Gags are **reference-counted under a global mutex**: nested gags (the campaign gags, then
/// each `run` gags again) and concurrent gags from multiple test threads compose without racing
/// on fd 2. Only the outermost gag performs the actual `dup2`, and only the last drop restores.
pub struct StderrGag {
    _private: (),
}

struct GagState {
    depth: usize,
    saved_fd: i32,
}

static GAG: std::sync::Mutex<GagState> = std::sync::Mutex::new(GagState { depth: 0, saved_fd: -1 });

impl StderrGag {
    /// Begin gagging (idempotent / nestable). If `/dev/null` can't be opened, this is a no-op.
    #[must_use]
    pub fn new() -> Self {
        let mut g = GAG.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        if g.depth == 0 {
            // SAFETY: standard fd plumbing; all fds are checked before use.
            unsafe {
                let devnull = libc::open(c"/dev/null".as_ptr(), libc::O_WRONLY);
                if devnull >= 0 {
                    let saved = libc::dup(libc::STDERR_FILENO);
                    if saved >= 0 {
                        libc::dup2(devnull, libc::STDERR_FILENO);
                        g.saved_fd = saved;
                    }
                    libc::close(devnull);
                }
            }
        }
        g.depth += 1;
        Self { _private: () }
    }
}

impl Default for StderrGag {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for StderrGag {
    fn drop(&mut self) {
        let mut g = GAG.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        g.depth -= 1;
        if g.depth == 0 && g.saved_fd >= 0 {
            // SAFETY: `saved_fd` is a valid dup of the original stderr taken by the outer gag.
            unsafe {
                libc::dup2(g.saved_fd, libc::STDERR_FILENO);
                libc::close(g.saved_fd);
            }
            g.saved_fd = -1;
        }
    }
}

impl std::fmt::Debug for StderrGag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StderrGag").finish()
    }
}
