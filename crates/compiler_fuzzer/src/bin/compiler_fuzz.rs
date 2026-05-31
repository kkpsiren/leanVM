//! Soak driver for the compiler fuzzer.
//!
//! Wired to the campaign runner once it lands. For now it sanity-checks the harness so the
//! `[[bin]]` target builds and `cargo run -p compiler_fuzzer` does something meaningful.

use compiler_fuzzer::harness::{CompileOutcome, compile_source};

fn main() {
    let src = "from snark_lib import *\ndef main():\n    x = 10\n    assert x == 10\n    return\n";
    match compile_source(src) {
        CompileOutcome::Ok(_) => println!("harness OK: trivial program compiled"),
        other => println!("harness unexpected outcome: {other:?}"),
    }
}
