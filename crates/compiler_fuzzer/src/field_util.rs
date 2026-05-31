//! Helpers for moving between plain integers and the KoalaBear base field `F` / its quintic
//! extension `EF`, plus seeded random field elements.
//!
//! The generator reasons about values as integers in `[0, P)` (the "canonical" view) and only
//! converts to `F`/`EF` when building public input and hint buffers. Keeping a canonical-integer
//! reference model is what lets the [`crate::model`] act as an oracle for the VM.

use backend::*;
use lean_vm::{DIMENSION, EF, F};

use crate::rng::Rng;

/// The KoalaBear prime, `p = 2^31 - 2^24 + 1`.
pub const P: u64 = (1 << 31) - (1 << 24) + 1;

/// Build an `F` from an arbitrary integer (reduced mod `p`).
#[must_use]
pub fn f(v: u64) -> F {
    F::new((v % P) as u32)
}

/// Canonical integer in `[0, P)` of a base-field element.
#[must_use]
pub fn f_canonical(x: F) -> u64 {
    u64::from(x.as_canonical_u32())
}

/// Modular addition in the canonical-integer view.
#[must_use]
pub fn add_mod(a: u64, b: u64) -> u64 {
    (a + b) % P
}

/// Modular subtraction in the canonical-integer view.
#[must_use]
pub fn sub_mod(a: u64, b: u64) -> u64 {
    (a + P - (b % P)) % P
}

/// Modular multiplication in the canonical-integer view.
#[must_use]
pub fn mul_mod(a: u64, b: u64) -> u64 {
    ((a % P) * (b % P)) % P
}

/// Build an extension element from its 5 base coordinates.
#[must_use]
pub fn ef_from_coeffs(coeffs: [F; DIMENSION]) -> EF {
    EF::from_basis_coefficients_slice(&coeffs).expect("DIMENSION basis coefficients")
}

/// The 5 base coordinates of an extension element, in basis order.
#[must_use]
pub fn ef_coeffs(x: EF) -> [F; DIMENSION] {
    let s = x.as_basis_coefficients_slice();
    std::array::from_fn(|i| s[i])
}

/// Append the base-field encoding of an extension element to `buf` (5 cells).
pub fn push_ef(buf: &mut Vec<F>, x: EF) {
    buf.extend_from_slice(x.as_basis_coefficients_slice());
}

/// Uniform base-field element in `[0, P)`.
pub fn rand_f(rng: &mut Rng) -> F {
    f(rng.next_u64() % P)
}

/// Uniform base-field element, returned as its canonical integer.
pub fn rand_canonical(rng: &mut Rng) -> u64 {
    rng.next_u64() % P
}

/// Uniform non-zero base-field element (canonical integer in `[1, P)`).
pub fn rand_canonical_nonzero(rng: &mut Rng) -> u64 {
    1 + rng.next_u64() % (P - 1)
}

/// Uniform extension element.
pub fn rand_ef(rng: &mut Rng) -> EF {
    ef_from_coeffs(std::array::from_fn(|_| rand_f(rng)))
}
