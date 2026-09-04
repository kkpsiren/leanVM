//! Lean VM - A minimal virtual machine implementation

mod core;
mod diagnostics;
mod execution;
mod isa;
mod tables;

pub use core::*;
pub use diagnostics::*;
pub use execution::*;
pub use isa::*;
pub use tables::*;
pub use tables::ed25519;
pub use tables::ed25519::{ED_DECOMPRESS_NAME, ED_SIG_NAME, EdDecompressTable, EdSigTable, SCALAR_L_NAME, SHA512_NAME, SIGNER_SCALAR_NAME, EdAddTable, ScalarLTable, Sha512Table, SignerScalarTable};

/// `multibus-toy` tamper switch (test-only): when set, the ExtensionOp toy pull column is zeroed so the
/// toy bus is unbalanced, and the prover's own LogUp sanity assert is skipped — the VERIFIER must catch it.
#[cfg(feature = "multibus-toy")]
pub static MULTIBUS_TOY_TAMPER: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
#[cfg(feature = "multibus-toy")]
pub static MULTIBUS_TOY_RANGE_TAMPER: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
/// `multibus-toy` range tamper: the ExtensionOp toy range column holds 256 instead of 255 (no AIR
/// constraint touches it) — only the U8 range section can reject it.
pub fn multibus_toy_range_tamper() -> bool {
    #[cfg(feature = "multibus-toy")]
    {
        MULTIBUS_TOY_RANGE_TAMPER.load(std::sync::atomic::Ordering::Relaxed)
    }
    #[cfg(not(feature = "multibus-toy"))]
    {
        false
    }
}
pub fn multibus_toy_tamper() -> bool {
    #[cfg(feature = "multibus-toy")]
    {
        MULTIBUS_TOY_TAMPER.load(std::sync::atomic::Ordering::Relaxed)
    }
    #[cfg(not(feature = "multibus-toy"))]
    {
        false
    }
}
