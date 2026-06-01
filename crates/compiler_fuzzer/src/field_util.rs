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

/// Modular exponentiation `base^exp mod p`, computed independently of the compiler's field code
/// (square-and-multiply over `u128`). The reference for the compile-time `**` operator, which the
/// compiler evaluates as `F::exp_u64` — i.e. also `base^exp mod p`. Keeping this independent is
/// what makes the const-fold gadget a real differential test.
#[must_use]
pub fn pow_mod(base: u64, exp: u64) -> u64 {
    let mut acc: u128 = 1;
    let b = u128::from(base % P);
    let m = u128::from(P);
    let mut e = exp;
    let mut p = b % m;
    while e > 0 {
        if e & 1 == 1 {
            acc = (acc * p) % m;
        }
        p = (p * p) % m;
        e >>= 1;
    }
    acc as u64
}

/// Field division `a / b` (i.e. `a * b^{-1}`) as a canonical integer. `b` must be non-zero. This is
/// the semantic reference for the runtime `/` operator.
#[must_use]
pub fn div_canonical(a: u64, b: u64) -> u64 {
    debug_assert!(!b.is_multiple_of(P), "division by zero");
    f_canonical(f(a) * f(b).inverse())
}

// --- Independent integer references for the compile-time built-ins (matching the compiler's
// `MathOperation::eval`, which computes these on canonical integers). Kept separate from the
// compiler so the const-fold gadget is a genuine differential. ---

/// `a / b` (floor) — reference for `div_floor`. `b` must be non-zero.
#[must_use]
pub const fn div_floor_int(a: u64, b: u64) -> u64 {
    a / b
}

/// `ceil(a / b)` — reference for `div_ceil`. `b` must be non-zero.
#[must_use]
pub const fn div_ceil_int(a: u64, b: u64) -> u64 {
    a.div_ceil(b)
}

/// `ceil(log2(n))` for `n >= 1` — reference for `log2_ceil`.
#[must_use]
pub const fn log2_ceil_int(n: u64) -> u64 {
    if n <= 1 { 0 } else { 64 - (n - 1).leading_zeros() as u64 }
}

/// Smallest multiple of `m` that is `>= x` — reference for `next_multiple_of`. `m` must be non-zero.
#[must_use]
pub const fn next_multiple_int(x: u64, m: u64) -> u64 {
    x.next_multiple_of(m)
}

/// An extension-field precompile operation ([`add_ee`-family]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExtOp {
    /// `result = sum_i (a_i + b_i)` (additive accumulation).
    Add,
    /// `result = sum_i (a_i * b_i)` (dot product).
    Dot,
    /// `result = prod_i (a_i*b_i + (1-a_i)*(1-b_i))` (multiplicative, the eq-poly).
    PolyEq,
}

/// Operand mode of an extension-field precompile.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExtMode {
    /// Both operands are extension-field vectors (`DIMENSION` cells each).
    Ee,
    /// `a` is a base-field vector (1 cell each); `b` is extension-field.
    Be,
}

impl ExtOp {
    #[must_use]
    pub const fn fn_name(self, mode: ExtMode) -> &'static str {
        match (self, mode) {
            (Self::Add, ExtMode::Ee) => "add_ee",
            (Self::Add, ExtMode::Be) => "add_be",
            (Self::Dot, ExtMode::Ee) => "dot_product_ee",
            (Self::Dot, ExtMode::Be) => "dot_product_be",
            (Self::PolyEq, ExtMode::Ee) => "poly_eq_ee",
            (Self::PolyEq, ExtMode::Be) => "poly_eq_be",
        }
    }
}

/// Number of buffer cells the `a` operand of an extension precompile occupies for length `n`.
#[must_use]
pub const fn ext_a_len(mode: ExtMode, n: usize) -> usize {
    match mode {
        ExtMode::Ee => n * DIMENSION,
        ExtMode::Be => n,
    }
}

/// Reference evaluation of an extension-field precompile over canonical integers. `a` holds the
/// `a`-operand cells ([`ext_a_len`] of them), `b` holds `n * DIMENSION` cells; the result is one
/// extension element (`DIMENSION` canonical coordinates). This *defines* the honest result, so it
/// uses the real field arithmetic (the gadget tests the compiler's lowering of the call, not the
/// field implementation).
#[must_use]
pub fn ext_op_eval(op: ExtOp, mode: ExtMode, a: &[u64], b: &[u64], n: usize) -> [u64; DIMENSION] {
    let lift_a = |i: usize| -> EF {
        match mode {
            ExtMode::Ee => ef_from_coeffs(std::array::from_fn(|j| f(a[i * DIMENSION + j]))),
            ExtMode::Be => ef_from_coeffs(std::array::from_fn(|j| if j == 0 { f(a[i]) } else { F::ZERO })),
        }
    };
    let lift_b = |i: usize| -> EF { ef_from_coeffs(std::array::from_fn(|j| f(b[i * DIMENSION + j]))) };

    let mut acc = match op {
        ExtOp::PolyEq => EF::ONE,
        _ => EF::ZERO,
    };
    for i in 0..n {
        let ai = lift_a(i);
        let bi = lift_b(i);
        match op {
            ExtOp::Add => acc += ai + bi,
            ExtOp::Dot => acc += ai * bi,
            ExtOp::PolyEq => acc *= ai * bi + (EF::ONE - ai) * (EF::ONE - bi),
        }
    }
    ef_coeffs(acc).map(f_canonical)
}
