//! Helpers for moving between plain integers and the KoalaBear base field `F` / its quintic
//! extension `EF`, plus seeded random field elements.
//!
//! The generator reasons about values as integers in `[0, P)` (the "canonical" view) and only
//! converts to `F`/`EF` when building public input and hint buffers. Keeping a canonical-integer
//! reference model is what lets the [`crate::model`] act as an oracle for the VM.

use backend::*;
use lean_vm::{DIMENSION, EF, F, PUBLIC_INPUT_LEN};

use crate::rng::Rng;

/// The all-zero public input. Generated programs feed their data through hint buffers, not the
/// public input, so this is the default.
pub fn zero_public_input() -> [F; PUBLIC_INPUT_LEN] {
    [F::ZERO; PUBLIC_INPUT_LEN]
}

/// The KoalaBear prime, `p = 2^31 - 2^24 + 1`.
pub const P: u64 = (1 << 31) - (1 << 24) + 1;

/// Build an `F` from an arbitrary integer (reduced mod `p`).
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
pub fn ef_from_coeffs(coeffs: [F; DIMENSION]) -> EF {
    EF::from_basis_coefficients_slice(&coeffs).expect("DIMENSION basis coefficients")
}

/// The 5 base coordinates of an extension element, in basis order.
pub fn ef_coeffs(x: EF) -> [F; DIMENSION] {
    let s = x.as_basis_coefficients_slice();
    std::array::from_fn(|i| s[i])
}

/// Append the base-field encoding of an extension element to `buf` (5 cells).
pub fn push_ef(buf: &mut Vec<F>, x: EF) {
    buf.extend_from_slice(x.as_basis_coefficients_slice());
}

/// Multiply two extension elements given as canonical base coordinates; returns the product's
/// canonical coordinates. The reference for `dot_product_ee(a, b, _)` with length 1.
#[must_use]
pub fn ef_mul_canonical(a: [u64; DIMENSION], b: [u64; DIMENSION]) -> [u64; DIMENSION] {
    let ea = ef_from_coeffs(a.map(f));
    let eb = ef_from_coeffs(b.map(f));
    ef_coeffs(ea * eb).map(f_canonical)
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
