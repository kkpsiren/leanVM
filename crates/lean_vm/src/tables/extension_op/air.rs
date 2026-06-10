use crate::{
    DIMENSION, EF, EXT_OP_FLAG_ADD, EXT_OP_FLAG_BE, EXT_OP_FLAG_DOT_PRODUCT, EXT_OP_FLAG_EQ, ExtraDataForBuses,
    eval_bus_virtual,
    tables::extension_op::{EXT_OP_LEN_MULTIPLIER, ExtensionOpPrecompile},
};
use backend::*;

// ---------- Column layout (cubic extension, DIMENSION = 3) ----------
// Shift columns first, in positions 0..11 (see `n_shift_columns` below).
// Flat-only columns follow.
pub(super) const COL_FLAG_BE: usize = 0;
pub(super) const COL_FLAG_START: usize = 1;
pub(super) const COL_LEN: usize = 2;
pub(super) const COL_FLAG_ADD: usize = 3;
pub(super) const COL_FLAG_DOT_PRODUCT: usize = 4;
pub(super) const COL_FLAG_EQ: usize = 5;
pub(super) const COL_IDX_A: usize = 6;
pub(super) const COL_IDX_B: usize = 7;
/// acc (running accumulator) coordinates (3 cols).
pub(super) const COL_ACC: usize = 8;
// --- flat-only columns ---
pub(super) const COL_IDX_RES: usize = 11;
/// v_A coordinates (3 cols).
pub(super) const COL_V_A: usize = 12;
/// v_B coordinates (3 cols).
pub(super) const COL_V_B: usize = 15;
/// res coordinates (3 cols).
pub(super) const COL_RES: usize = 18;

// Virtual columns (not explicitely in AIR)
pub(super) const COL_MULTIPLICITY_EXTENSION_OP: usize = 21;
pub(super) const COL_DOMAINSEP_EXTENSION_OP: usize = 22;

pub(super) const AIR_N_COLUMNS: usize = 21;

// ---------- Cubic multiplication gate (`F[X] / (X^3 - X - 1)`, so `X^3 = X + 1`) ----------
//
// (a0 + a1·X + a2·X^2)·(b0 + b1·X + b2·X^2), reduced:
//   c0 = a0·b0 + a1·b2 + a2·b1
//   c1 = a0·b1 + a1·b0 + a1·b2 + a2·b1 + a2·b2
//   c2 = a0·b2 + a1·b1 + a2·b0 + a2·b2
#[inline]
fn cubic_mul_air<T: PrimeCharacteristicRing + Copy>(a: &[T; 3], b: &[T; 3]) -> [T; 3] {
    let a1b2 = a[1] * b[2];
    let a2b1 = a[2] * b[1];
    let a2b2 = a[2] * b[2];
    [
        a[0] * b[0] + a1b2 + a2b1,
        a[0] * b[1] + a[1] * b[0] + a1b2 + a2b1 + a2b2,
        a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + a2b2,
    ]
}

impl<const BUS: bool> Air for ExtensionOpPrecompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns(&self) -> usize {
        AIR_N_COLUMNS
    }
    fn degree_air(&self) -> usize {
        // cubic_mul has degree 2 (elementwise), wrapped in `* flag_mul` gives 3; poly_eq
        // squares that via another cubic_mul so needs degree 4? In the KoalaBear case the
        // eval used `6` — we retain a conservative upper bound.
        6
    }
    fn n_constraints(&self) -> usize {
        // 5 boolean gates
        // + 3 * flag_add
        // + 3 * flag_mul
        // + 3 * flag_poly_eq
        // + 3 * start (vres vs comp)
        // + 7 transition gates (len/is_be/flags/idx_a/idx_b) + 1 start-row-length
        // + 2 bus (multiplicity + fingerprint) if BUS
        5 + 3 + 3 + 3 + 3 + 8 + if BUS { 2 } else { 0 }
    }
    fn n_shift_columns(&self) -> usize {
        COL_ACC + 3
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let flat = builder.flat();
        let shift = builder.shift();

        let flag_be = flat[COL_FLAG_BE];
        let flag_start = flat[COL_FLAG_START];
        let flag_add = flat[COL_FLAG_ADD];
        let flag_dot_product = flat[COL_FLAG_DOT_PRODUCT];
        let flag_eq = flat[COL_FLAG_EQ];
        let len = flat[COL_LEN];
        let idx_a = flat[COL_IDX_A];
        let idx_b = flat[COL_IDX_B];

        let v_a: [AB::IF; 3] = std::array::from_fn(|k| flat[COL_V_A + k]);
        let v_b: [AB::IF; 3] = std::array::from_fn(|k| flat[COL_V_B + k]);
        let res: [AB::IF; 3] = std::array::from_fn(|k| flat[COL_RES + k]);
        let acc: [AB::IF; 3] = std::array::from_fn(|k| flat[COL_ACC + k]);

        // Shift columns map 1:1 onto the first 11 columns by convention.
        let flag_be_shift = shift[COL_FLAG_BE];
        let flag_start_shift = shift[COL_FLAG_START];
        let len_shift = shift[COL_LEN];
        let flag_add_shift = shift[COL_FLAG_ADD];
        let flag_dot_product_shift = shift[COL_FLAG_DOT_PRODUCT];
        let flag_eq_shift = shift[COL_FLAG_EQ];
        let idx_a_shift = shift[COL_IDX_A];
        let idx_b_shift = shift[COL_IDX_B];
        let acc_shift: [AB::IF; 3] = std::array::from_fn(|k| shift[COL_ACC + k]);

        let active = flag_add + flag_dot_product + flag_eq;
        let multiplicity = flag_start * active;

        let aux_2 = flag_be * AB::F::from_usize(EXT_OP_FLAG_BE)
            + flag_add * AB::F::from_usize(EXT_OP_FLAG_ADD)
            + flag_dot_product * AB::F::from_usize(EXT_OP_FLAG_DOT_PRODUCT)
            + flag_eq * AB::F::from_usize(EXT_OP_FLAG_EQ)
            + len * AB::F::from_usize(EXT_OP_LEN_MULTIPLIER);

        let idx_r = flat[COL_IDX_RES];

        if BUS {
            eval_bus_virtual::<AB, EF>(builder, extra_data, multiplicity, aux_2, &[idx_a, idx_b, idx_r]);
        } else {
            builder.declare_values(&[multiplicity]);
            builder.declare_values(&[idx_a, idx_b, idx_r, aux_2]);
        }

        let is_ee = -(flag_be - AB::F::ONE);
        let not_start_shift = -(flag_start_shift - AB::F::ONE);

        // For "base-extension" ops, v_a is a base-field scalar embedded into EF as
        // `(v_a[0], 0, 0)`: zero the upper coordinates when `flag_be` is 1.
        let v_a_tilde: [AB::IF; 3] = std::array::from_fn(|k| if k == 0 { v_a[0] } else { v_a[k] * is_ee });

        let acc_tail: [AB::IF; 3] = std::array::from_fn(|k| acc_shift[k] * not_start_shift);

        builder.assert_bool(flag_be);
        builder.assert_bool(flag_start);
        builder.assert_bool(flag_add);
        builder.assert_bool(flag_dot_product);
        builder.assert_bool(flag_eq);

        for k in 0..3 {
            builder.assert_zero((acc[k] - (v_a_tilde[k] + v_b[k] + acc_tail[k])) * flag_add);
        }

        let v_a_times_v_b = cubic_mul_air(&v_a_tilde, &v_b);

        for k in 0..3 {
            builder.assert_zero((acc[k] - (v_a_times_v_b[k] + acc_tail[k])) * flag_dot_product);
        }

        // eq per element: `2 a b - a - b + 1` (constant coord only gets +1),
        // accumulated via multiplication.
        let e_eq: [AB::IF; 3] = std::array::from_fn(|k| {
            let base = v_a_times_v_b[k].double() - v_a_tilde[k] - v_b[k];
            if k == 0 { base + AB::F::ONE } else { base }
        });
        let acc_tail_or_one: [AB::IF; 3] = std::array::from_fn(|k| {
            if k == 0 {
                acc_shift[0] * not_start_shift + flag_start_shift
            } else {
                acc_shift[k] * not_start_shift
            }
        });
        let eq_result = cubic_mul_air(&e_eq, &acc_tail_or_one);
        for k in 0..3 {
            builder.assert_zero((acc[k] - eq_result[k]) * flag_eq);
        }

        for k in 0..3 {
            builder.assert_zero((acc[k] - res[k]) * flag_start);
        }

        builder.assert_zero(not_start_shift * (len - len_shift - AB::F::ONE));
        builder.assert_zero(not_start_shift * (flag_be - flag_be_shift));
        builder.assert_zero(not_start_shift * (flag_add - flag_add_shift));
        builder.assert_zero(not_start_shift * (flag_dot_product - flag_dot_product_shift));
        builder.assert_zero(not_start_shift * (flag_eq - flag_eq_shift));
        let a_increment = flag_be + is_ee * AB::F::from_usize(DIMENSION);
        builder.assert_zero(not_start_shift * (idx_a_shift - idx_a - a_increment));
        builder.assert_zero(not_start_shift * (idx_b_shift - idx_b - AB::F::from_usize(DIMENSION)));

        builder.assert_zero(flag_start_shift * (len - AB::F::ONE));
    }
}
