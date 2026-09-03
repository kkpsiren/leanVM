//! Milestone 1b of `docs/zk-aggregate-spec.md` (farcaster-blobs): measure the AIR-sumcheck cost
//! of wide non-native identity checks over 2^255-19 in leanMultisig's standalone harness.
//!
//! `LimbMulAir` rows hold `K` independent "G8" identity checks `r ≡ a·b (mod p)` with
//! 32 unsigned 8-bit limbs, a hinted quotient `q` (33 limbs) and the SP1-style witness
//! polynomial `W` (64 limbs, offset 2^15):
//!
//! ```text
//! V(X) = a(X)·b(X) − r(X) − q(X)·p(X)             (X ↔ 256, 65 coefficients)
//! V(X) = (X − 256) · W'(X),  W'_i = W_i − 2^15    (64 coefficients)
//! ```
//! i.e. one constraint per coefficient: `V_i − W'_{i−1} + 256·W'_i = 0` (`W'_{−1} = W'_{64} = 0`).
//! Range checks (bytes, W) are *not* part of this AIR — they are LogUp fractions and are
//! measured elsewhere; this AIR isolates the sumcheck cost of the limb convolutions.
//!
//! `boost = true` reproduces the spec's T3 shape (degree 4): the `a` operand is selected
//! between two column sets by a boolean `s` (`a_eff = s·a + (1−s)·a2`, degree 2 → products
//! degree 3) and every constraint is gated by a boolean `sel` (degree 4).

pub mod edadd;
pub mod edsig;
pub mod gadgets;
pub mod harness;
pub mod scalar;
pub mod signer;
pub mod sha512;

use backend::*;
use lean_vm::{EF, ExtraDataForBuses, F};

pub const LIMBS: usize = 32;
pub const QL: usize = 33;
pub const WL: usize = 64;
pub const NV: usize = 65;
pub const W_OFFSET: usize = 1 << 15;

/// p = 2^255 − 19, little-endian bytes.
pub const P_BYTES: [u8; 32] = {
    let mut p = [0xFFu8; 32];
    p[0] = 0xED;
    p[31] = 0x7F;
    p
};

/// Column layout of one check inside a row.
#[derive(Debug, Clone, Copy)]
pub struct CheckLayout {
    pub a: usize,
    pub b: usize,
    pub r: usize,
    pub q: usize,
    pub w: usize,
    pub a2: usize,
    pub s: usize,
    pub sel: usize,
    pub width: usize,
}

pub const fn check_layout(boost: bool) -> CheckLayout {
    let a = 0;
    let b = a + LIMBS;
    let r = b + LIMBS;
    let q = r + LIMBS;
    let w = q + QL;
    let mut width = w + WL;
    let (a2, s, sel) = if boost {
        let a2 = width;
        let s = a2 + LIMBS;
        let sel = s + 1;
        width = sel + 1;
        (a2, s, sel)
    } else {
        (usize::MAX, usize::MAX, usize::MAX)
    };
    CheckLayout { a, b, r, q, w, a2, s, sel, width }
}

#[derive(Debug, Clone, Copy)]
pub struct LimbMulAir {
    pub k: usize,
    pub boost: bool,
}

impl LimbMulAir {
    pub const fn new(k: usize, boost: bool) -> Self {
        Self { k, boost }
    }
    pub const fn layout(&self) -> CheckLayout {
        check_layout(self.boost)
    }
}

impl Air for LimbMulAir {
    type ExtraData = ExtraDataForBuses<EF>;

    fn degree_air(&self) -> usize {
        if self.boost { 4 } else { 2 }
    }

    fn n_columns(&self) -> usize {
        self.k * self.layout().width
    }

    fn n_constraints(&self) -> usize {
        self.k * (NV + if self.boost { 2 } else { 0 })
    }

    fn n_shift_columns(&self) -> usize {
        0
    }

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, _extra_data: &Self::ExtraData) {
        let lay = self.layout();
        let flat: Vec<AB::IF> = builder.flat().to_vec();
        let off = AB::IF::from_usize(W_OFFSET);
        let c256 = AB::F::from_usize(256);
        let p: Vec<AB::F> = P_BYTES.iter().map(|&x| AB::F::from_usize(x as usize)).collect();

        for c in 0..self.k {
            let base = c * lay.width;
            let col = |i: usize| flat[base + i].clone();

            // Effective `a` operand (degree 1, or degree 2 when boosted).
            let a: Vec<AB::IF> = if self.boost {
                let s = col(lay.s);
                let one_minus_s = AB::IF::ONE - s.clone();
                (0..LIMBS)
                    .map(|i| s.clone() * col(lay.a + i) + one_minus_s.clone() * col(lay.a2 + i))
                    .collect()
            } else {
                (0..LIMBS).map(|i| col(lay.a + i)).collect()
            };
            let b: Vec<AB::IF> = (0..LIMBS).map(|i| col(lay.b + i)).collect();
            let r: Vec<AB::IF> = (0..LIMBS).map(|i| col(lay.r + i)).collect();
            let q: Vec<AB::IF> = (0..QL).map(|i| col(lay.q + i)).collect();
            let w: Vec<AB::IF> = (0..WL).map(|i| col(lay.w + i)).collect();
            let sel = if self.boost { Some(col(lay.sel)) } else { None };

            if self.boost {
                builder.assert_bool(col(lay.s));
                builder.assert_bool(col(lay.sel));
            }

            for i in 0..NV {
                // V_i = Σ_{j+k=i} a_j b_k − r_i − Σ_{j+k=i} q_j p_k
                let mut v = AB::IF::ZERO;
                let jlo = i.saturating_sub(LIMBS - 1);
                let jhi = i.min(LIMBS - 1);
                for j in jlo..=jhi {
                    v += a[j].clone() * b[i - j].clone();
                }
                if i < LIMBS {
                    v -= r[i].clone();
                }
                let jlo = i.saturating_sub(LIMBS - 1);
                let jhi = i.min(QL - 1);
                for j in jlo..=jhi {
                    let k = i - j;
                    if k < LIMBS {
                        v -= q[j].clone() * p[k].clone();
                    }
                }
                // V_i − W'_{i−1} + 256·W'_i = 0
                let w_prev = if i == 0 { AB::IF::ZERO } else { w[i - 1].clone() - off.clone() };
                let w_cur = if i < WL { w[i].clone() - off.clone() } else { AB::IF::ZERO };
                let mut constraint = v - w_prev + w_cur * c256;
                if let Some(sel) = &sel {
                    constraint = constraint * sel.clone();
                }
                builder.assert_zero(constraint);
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Witness generation (native): tiny fixed-width big-uint, little-endian u64 limbs (576 bits).
// ---------------------------------------------------------------------------------------------

type Big = [u64; 9];

fn big_from_bytes(bytes: &[u8]) -> Big {
    let mut out = [0u64; 9];
    for (i, &b) in bytes.iter().enumerate() {
        out[i / 8] |= (b as u64) << (8 * (i % 8));
    }
    out
}

fn big_to_bytes(x: &Big) -> [u8; 72] {
    let mut out = [0u8; 72];
    for (i, limb) in x.iter().enumerate() {
        out[8 * i..8 * i + 8].copy_from_slice(&limb.to_le_bytes());
    }
    out
}

fn big_mul(a: &Big, b: &Big) -> Big {
    let mut acc = [0u128; 18];
    for i in 0..9 {
        if a[i] == 0 {
            continue;
        }
        for j in 0..9 {
            if i + j < 18 {
                acc[i + j] += (a[i] as u128) * (b[j] as u128);
                // propagate eagerly to avoid overflow
                let mut k = i + j;
                while acc[k] >> 64 != 0 && k + 1 < 18 {
                    let carry = acc[k] >> 64;
                    acc[k] &= u128::from(u64::MAX);
                    acc[k + 1] += carry;
                    k += 1;
                }
            }
        }
    }
    let mut out = [0u64; 9];
    for i in 0..9 {
        out[i] = acc[i] as u64;
    }
    for a in acc.iter().skip(9) {
        assert_eq!(*a, 0, "product exceeds 576 bits");
    }
    out
}

fn big_add(a: &Big, b: &Big) -> Big {
    let mut out = [0u64; 9];
    let mut carry = 0u128;
    for i in 0..9 {
        let s = a[i] as u128 + b[i] as u128 + carry;
        out[i] = s as u64;
        carry = s >> 64;
    }
    assert_eq!(carry, 0);
    out
}

fn big_sub(a: &Big, b: &Big) -> Big {
    let mut out = [0u64; 9];
    let mut borrow = 0i128;
    for i in 0..9 {
        let d = a[i] as i128 - b[i] as i128 - borrow;
        if d < 0 {
            out[i] = (d + (1i128 << 64)) as u64;
            borrow = 1;
        } else {
            out[i] = d as u64;
            borrow = 0;
        }
    }
    assert_eq!(borrow, 0, "negative subtraction");
    out
}

fn big_cmp(a: &Big, b: &Big) -> core::cmp::Ordering {
    for i in (0..9).rev() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
    }
    core::cmp::Ordering::Equal
}

fn big_mul_small(a: &Big, m: u64) -> Big {
    let mut out = [0u64; 9];
    let mut carry = 0u128;
    for i in 0..9 {
        let s = a[i] as u128 * m as u128 + carry;
        out[i] = s as u64;
        carry = s >> 64;
    }
    assert_eq!(carry, 0);
    out
}

fn big_is_zero(a: &Big) -> bool {
    a.iter().all(|&x| x == 0)
}

/// Split x = hi·2^255 + lo.
fn split255(x: &Big) -> (Big, Big) {
    let mut lo = *x;
    lo[4..].iter_mut().for_each(|l| *l = 0);
    lo[3] &= (1u64 << 63) - 1;
    // hi = x >> 255
    let mut hi = [0u64; 9];
    for i in 0..9 {
        let src = i + 3; // shift by 192 bits = 3 limbs, then 63 more bits
        let lo_part = if src < 9 { x[src] >> 63 } else { 0 };
        let hi_part = if src + 1 < 9 { x[src + 1] << 1 } else { 0 };
        hi[i] = lo_part | hi_part;
    }
    (hi, lo)
}

/// Returns (q, r) with x = q·p + r, 0 ≤ r < p, using p = 2^255 − 19.
pub fn divmod_p(x: &Big) -> (Big, Big) {
    let p = big_from_bytes(&P_BYTES);
    let mut q = [0u64; 9];
    let mut y = *x;
    loop {
        let (hi, lo) = split255(&y);
        if big_is_zero(&hi) {
            break;
        }
        q = big_add(&q, &hi);
        y = big_add(&lo, &big_mul_small(&hi, 19));
    }
    while big_cmp(&y, &p) != core::cmp::Ordering::Less {
        y = big_sub(&y, &p);
        q = big_add(&q, &[1, 0, 0, 0, 0, 0, 0, 0, 0]);
    }
    (q, y)
}

/// One check's witness as byte limbs (plus W as u16 offset values).
#[derive(Debug, Clone)]
pub struct CheckWitness {
    pub a: [u8; 32],
    pub b: [u8; 32],
    pub r: [u8; 32],
    pub q: [u8; 33],
    pub w: [u16; 64],
}

pub fn make_check(a: [u8; 32], b: [u8; 32]) -> CheckWitness {
    let x = big_mul(&big_from_bytes(&a), &big_from_bytes(&b));
    let (q, r) = divmod_p(&x);
    let qb = big_to_bytes(&q);
    let rb = big_to_bytes(&r);
    assert!(qb[33..].iter().all(|&v| v == 0), "q exceeds 33 bytes");
    assert!(rb[32..].iter().all(|&v| v == 0), "r exceeds 32 bytes");
    let mut q33 = [0u8; 33];
    q33.copy_from_slice(&qb[..33]);
    let mut r32 = [0u8; 32];
    r32.copy_from_slice(&rb[..32]);

    // V coefficients in i64.
    let mut v = [0i64; NV];
    for j in 0..LIMBS {
        for k in 0..LIMBS {
            v[j + k] += a[j] as i64 * b[k] as i64;
        }
    }
    for i in 0..LIMBS {
        v[i] -= r32[i] as i64;
    }
    for j in 0..QL {
        for k in 0..LIMBS {
            v[j + k] -= q33[j] as i64 * P_BYTES[k] as i64;
        }
    }
    // Synthetic division by (X − 256): V_i = W'_{i−1} − 256·W'_i.
    let mut wp = [0i64; WL];
    let mut prev = 0i64;
    for i in 0..NV {
        if i < WL {
            let num = prev - v[i];
            assert_eq!(num % 256, 0, "V not divisible by (X-256) at {i}");
            wp[i] = num / 256;
            prev = wp[i];
        } else {
            assert_eq!(v[i], prev, "V(256) != 0");
        }
    }
    let mut w = [0u16; WL];
    for i in 0..WL {
        let val = wp[i] + W_OFFSET as i64;
        assert!((0..65536).contains(&val), "W'_{i} = {} out of 16-bit range", wp[i]);
        w[i] = val as u16;
    }
    CheckWitness { a, b, r: r32, q: q33, w }
}

/// Column-major trace (`n_columns` columns of `n_rows` field elements).
pub fn generate_trace(air: &LimbMulAir, n_rows: usize, mut next_byte: impl FnMut() -> u8) -> Vec<Vec<F>> {
    let lay = air.layout();
    let n_cols = air.n_columns();
    let mut cols: Vec<Vec<F>> = (0..n_cols).map(|_| vec![F::ZERO; n_rows]).collect();
    let f = |x: usize| F::from_usize(x);
    for row in 0..n_rows {
        for c in 0..air.k {
            let base = c * lay.width;
            let mut a = [0u8; 32];
            let mut b = [0u8; 32];
            let mut a2 = [0u8; 32];
            a.iter_mut().for_each(|x| *x = next_byte());
            b.iter_mut().for_each(|x| *x = next_byte());
            let s = if air.boost { next_byte() & 1 } else { 1 };
            if air.boost {
                a2.iter_mut().for_each(|x| *x = next_byte());
            }
            let a_eff = if s == 1 { a } else { a2 };
            let wit = make_check(a_eff, b);
            for i in 0..LIMBS {
                cols[base + lay.a + i][row] = f(a[i] as usize);
                cols[base + lay.b + i][row] = f(b[i] as usize);
                cols[base + lay.r + i][row] = f(wit.r[i] as usize);
            }
            for i in 0..QL {
                cols[base + lay.q + i][row] = f(wit.q[i] as usize);
            }
            for i in 0..WL {
                cols[base + lay.w + i][row] = f(wit.w[i] as usize);
            }
            if air.boost {
                for i in 0..LIMBS {
                    cols[base + lay.a2 + i][row] = f(a2[i] as usize);
                }
                cols[base + lay.s][row] = f(s as usize);
                cols[base + lay.sel][row] = F::ONE;
            }
        }
    }
    cols
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn divmod_roundtrip() {
        let mut seed = 0x9E37_79B9_7F4A_7C15u64;
        let mut nb = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed >> 24) as u8
        };
        for _ in 0..64 {
            let mut a = [0u8; 32];
            let mut b = [0u8; 32];
            a.iter_mut().for_each(|x| *x = nb());
            b.iter_mut().for_each(|x| *x = nb());
            let w = make_check(a, b);
            // x == q*p + r
            let x = big_mul(&big_from_bytes(&a), &big_from_bytes(&b));
            let qp = big_mul(&big_from_bytes(&w.q), &big_from_bytes(&P_BYTES));
            let back = big_add(&qp, &big_from_bytes(&w.r));
            assert_eq!(big_cmp(&x, &back), core::cmp::Ordering::Equal);
        }
        // edge: a = b = p-1
        let mut pm1 = P_BYTES;
        pm1[0] -= 1;
        let w = make_check(pm1, pm1);
        assert_eq!(w.r, {
            let mut one = [0u8; 32];
            one[0] = 1;
            one
        });
    }
}
