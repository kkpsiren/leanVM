//! In-crate test suites. This crate keeps all tests under `src` (no `tests/` integration
//! directory), so they run as library unit tests.

mod fuzzer;
mod handwritten;

/// Path to the `compiler_fuzz` binary, derived from the running test executable.
///
/// Library unit tests do **not** get `CARGO_BIN_EXE_compiler_fuzz` (that is only set for
/// integration tests / examples), but `cargo test` still builds the binary, so it sits next to
/// the test runner's profile directory: `target/<profile>/deps/<test> → target/<profile>/compiler_fuzz`.
pub(crate) fn fuzz_bin() -> std::path::PathBuf {
    let exe = std::env::current_exe().expect("current exe path");
    let dir = exe.parent().expect("test exe directory");
    let profile_dir = if dir.ends_with("deps") {
        dir.parent().expect("profile directory")
    } else {
        dir
    };
    profile_dir.join("compiler_fuzz")
}
